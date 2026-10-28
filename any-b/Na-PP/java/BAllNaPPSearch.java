import java.math.BigInteger;
import java.time.Duration;
import java.util.Arrays;

/**
 * squares in sequences of the form (a+b^2*sqrt(d))*((t+u*sqrt(d))/2)^(2*k)
 */
public class BAllNaPPSearch
{
	private static final long[] PRIMES = new long[] { 3L, 5L, 7L, 11L, 13L, 17L, 19L, 23L, 29L, 31L, 37L, 41L, 43L, 47L, 53L, 59L, 61L}; // going to p=101 made things slower, not faster, 67L, 71L, 73L, 79L, 83L, 89L, 97L, 101L};

	private int kNegUB;
	private int kPosLB;

	// A bit represents a value of a. Reuse the buffers for successive (d,t,u).
	private long[] normBits = new long[0];
	private long[] candidateBits = new long[0];
	private long[] termBits = new long[0];
	private static final long[][][] NORM_MASKS = createNormMasks();
	private static final int[] SQUARE_MODULI = {64, 63, 65, 11, 17, 19};
	private static final boolean[][] SQUARE_RESIDUES = createSquareResidues();
	// Per-instance cache: masks for C + A*a modulo each modulus. Bounded in size.
	private final long[][][][] squareMasks = createSquareMaskCache();

	private BAllNaPPSearch(long b) {
		// interested in squares among y_k with k<=K-1 and k >=2
		this.kNegUB=1;
		this.kPosLB=2;
	}

	public static void main(String[] args) {
		if (args!=null && args.length==1) {
			long b=Long.parseLong(args[0]);
			BAllNaPPSearch app = new BAllNaPPSearch(b);
			app.doBWork(b);
		} else {
			for (long b=1L; b<8L; b=b+1L) {
				BAllNaPPSearch app = new BAllNaPPSearch(b);
				app.doBWork(b);
			}
		}
	}

	private void doBWork(long b) {
		long uUB = 2L;
		double dUB = getDUpperBound(b, uUB+1)[0];
		while (dUB>1.999) {
			uUB=uUB+1L;
			dUB = getDUpperBound(b, uUB+1)[0];
		}
		double dUB1=getDUpperBound(b,1)[0];
		double dUB2=getDUpperBound(b,2)[0];
		System.out.printf("b=%2d, dUB(u=%3d)=%9.6f, dUB(u=1)=%10d=%9.6e, dUB(u=2)=%9.6e\n",b,uUB+1,dUB,(long) Math.ceil(dUB1),dUB1,dUB2);
		long startTime=System.currentTimeMillis();
		long[] cArray = new long[2];
		for (long u=1L; u<=uUB; u++) {
			double dUB_app = getDUpperBound(b, u)[0];
			System.out.printf("for b=%2d, u=%2d, dUB=%s\n",b,u,dUB_app);
			doBUWork(b, u, dUB_app, cArray);
		}
		System.out.println("for b="+b+", total time="+(System.currentTimeMillis()-startTime)+"(ms).");
	}

	// side-effect: cArray gets updated
	private void doBUWork(long b, long u, double dUB, long[] cArray) {
		long uStartTime = System.currentTimeMillis();
		long c1 = cArray[0];
		long c2 = cArray[1];
		double tUB = Math.sqrt(u*u*dUB+4L);
		long tMod = (long) Math.floor(tUB/100.0);
		tMod = Math.max(100, tMod);
		long tLB = 1L;
		for (long t = tLB; t <= tUB; t++) {
			long d = t*t+4L;
			if (d % (u*u) == 0L) {
				d = d/u/u;
				long[] cArray1=doBDTUWork(b, d, t, u, dUB);
				c1=c1+cArray1[0];
				c2=c2+cArray1[1];
			}
			d = t*t-4L;
			if (d > 0 && d % (u*u) == 0L) {
				d = d/u/u;
				long[] cArray1=doBDTUWork(b, d, t, u, dUB);
				c1=c1+cArray1[0];
				c2=c2+cArray1[1];
			}
			if (t % tMod == 0L) {
				long millis = System.currentTimeMillis()-uStartTime;
				Duration duration = Duration.ofMillis(millis);
				String s = String.format("%2dh, %2dmin, %2ds, %3dms", duration.toHours(), duration.toMinutesPart(), duration.toSecondsPart(), duration.toMillisPart());
				System.out.printf("b=%2d, t=%6d (u=%3d is %5.2f percent done), d=%11d, c1=%12d, c2=%4d, total time=%9d(ms)=%s\n", b, t, u, (100.0*t/tUB), d+8L, c1, c2, millis, s);
			}
		}
		System.out.println("done b="+b+", u="+u+": total found "+c1+" equations, c2="+c2+". uTime="+(System.currentTimeMillis()-uStartTime));
		cArray[0]=c1;
		cArray[1]=c2;
	}

	// returns [c1,c2], where
	// c1=the number of values a accepted by the original small-prime norm test
	// c2=the number of equations to try in Magma
	private long[] doBDTUWork(long b, long d, long t, long u, double dBnd) {
		long c1 = 0;
		long c2 = 0;
		if (d <= dBnd) {
			long b2 = Math.multiplyExact(b, b);
			long db4 = Math.multiplyExact(d, Math.multiplyExact(b2, b2));
			long aMax = (long) (Math.sqrt(d)*b*b);
			// Preserve the old upper bound and its strict negative-norm condition.
			while (aMax > 0 && aMax > (db4-1)/aMax)
				--aMax;
			if (aMax == 0)
				return new long[] {0, 0};
			int words = Math.toIntExact((aMax >>> 6) + 1);
			ensureSieveCapacity(words);
			sieveNorms(db4, aMax, words);
			for (int w = 0; w < words; w++)
				c1 += Long.bitCount(normBits[w]);
			double ykUB = getYM1UpperBound(1L, b, d, t, u);
			sieveSquares(b, d, t, u, aMax, words, 4.0*ykUB);
			for (int w = 0; w < words; w++) {
				long bits = candidateBits[w];
				while (bits != 0) {
					long a = 64L*w + Long.numberOfTrailingZeros(bits);
					c2 += processBigIntegerTuple(a, b, d, t, u, ykUB);
					bits &= bits-1;
				}
			}
		}
		return new long[] {c1,c2};
	}

	private void ensureSieveCapacity(int words) {
		if (normBits.length < words) {
			int capacity = Math.max(words, normBits.length + normBits.length/2 + 1);
			normBits = new long[capacity];
			candidateBits = new long[capacity];
			termBits = new long[capacity];
		}
	}

	private static long[][][] createNormMasks() {
		long[][][] result = new long[PRIMES.length][][];
		for (int i = 0; i < PRIMES.length; i++) {
			int p = (int) PRIMES[i];
			result[i] = new long[p][p];
			for (long[] row : result[i]) Arrays.fill(row, -1L);
			for (int w = 0; w < p; w++) {
				for (int bit = 0; bit < 64; bit++) {
					int a = (64*w + bit) % p;
					result[i][a*a % p][w] &= ~(1L << bit);
				}
			}
		}
		return result;
	}

	private void sieveNorms(long db4, long aMax, int words) {
		Arrays.fill(normBits, 0, words, -1L);
		for (int i = 0; i < PRIMES.length; i++) {
			long[] masks = NORM_MASKS[i][(int) (db4 % PRIMES[i])];
			// Every p <= 61 fits in the first word: all ones means no roots.
			if (masks[0] != -1L) intersect(normBits, masks, words);
		}
		// The original predicate also accepts N=2^e*p^k for a listed prime p.
		// Restore precisely these exceptions. Powers of two survived already.
		for (int i = 0; i < PRIMES.length; i++) {
			long p = PRIMES[i];
			if (NORM_MASKS[i][(int) (db4 % p)][0] == -1L) continue;
			for (long power = p; power < db4;) {
				for (long n = power; n < db4;) {
					long a2 = db4-n;
					long a = (long) Math.sqrt(a2);
					// Division avoids overflow near the largest signed long.
					while (a > a2/a)
						a--;
					while (a+1 <= a2/(a+1))
						a++;
					if (a <= aMax && a*a == a2) {
						normBits[(int) (a >>> 6)] |= 1L << (a & 63);
					}
					if (n > (db4-1)/2) break;
					n *= 2;
				}
				if (power > (db4-1)/p) break;
				power *= p;
			}
		}
		normBits[0] &= ~1L; // a=0 is not searched
		int lastBits = (int) (aMax & 63) + 1;
		if (lastBits < 64) normBits[words-1] &= (1L << lastBits)-1;
	}

	private static boolean[][] createSquareResidues() {
		boolean[][] result = new boolean[SQUARE_MODULI.length][];
		for (int i = 0; i < result.length; i++) {
			int m = SQUARE_MODULI[i];
			result[i] = new boolean[m];
			for (int r = 0; r < m; r++)
				result[i][r*r % m] = true;
		}
		return result;
	}

	private static long[][][][] createSquareMaskCache() {
		long[][][][] result = new long[SQUARE_MODULI.length][][][];
		for (int i = 0; i < result.length; i++) {
			int m = SQUARE_MODULI[i];
			result[i] = new long[m][m][];
		}
		return result;
	}

	private long[] squareMasks(int i, int constant, int slope) {
		long[] masks = squareMasks[i][constant][slope];
		if (masks == null) {
			int m = SQUARE_MODULI[i];
			// Advancing a word adds 64 to a. For modulus 64 one word suffices.
			masks = new long[m == 64 ? 1 : m];
			for (int w = 0; w < masks.length; w++) {
				int residue = (constant + slope*(64*w % m)) % m;
				for (int bit = 0; bit < 64; bit++) {
					if (SQUARE_RESIDUES[i][residue]) masks[w] |= 1L << bit;
					residue = (residue+slope) % m;
				}
			}
			squareMasks[i][constant][slope] = masks;
		}
		return masks;
	}

	private static void intersect(long[] bits, long[] masks, int words) {
		int phase = 0;
		for (int w = 0; w < words; w++) {
			bits[w] &= masks[phase];
			if (++phase == masks.length) phase = 0;
		}
	}

	private void addSquareCandidates(BigInteger constant, BigInteger slope,
			boolean negative, int words) {
		System.arraycopy(normBits, 0, termBits, 0, words);
		for (int i = 0; i < SQUARE_MODULI.length; i++) {
			BigInteger modulus = BigInteger.valueOf(SQUARE_MODULI[i]);
			int c = constant.mod(modulus).intValue();
			int a = slope.mod(modulus).intValue();
			if (negative && a != 0)
				a = SQUARE_MODULI[i]-a;
			intersect(termBits, squareMasks(i, c, a), words);
		}
		for (int w = 0; w < words; w++)
			candidateBits[w] |= termBits[w];
	}

	private void sieveSquares(long b, long d, long t, long u, long aMax,
			int words, double limit) {
		Arrays.fill(candidateBits, 0, words, 0L);
		if (!(limit > 0)) return;
		BigInteger v1 = BigInteger.valueOf(t*t+d*u*u);
		BigInteger multiplier = v1.divide(BigInteger.TWO);
		BigInteger y0 = BigInteger.valueOf(4L*b*b);
		BigInteger previousA0 = y0;
		BigInteger previousA1 = BigInteger.ZERO;
		BigInteger a0 = BigInteger.valueOf(b*b).multiply(v1); // a0 is the constant (in "a") term in expression for y_k
		BigInteger a1 = BigInteger.valueOf(2L*t*u); // a1 is the linear coefficient of a in expression for y_k
		BigInteger maxA = BigInteger.valueOf(aMax);
		for (int j = 1; ; j++) {
			// Every term, 4*y_k can be written as a0 +/- a1*a.
			// The minimum over both signs and all searched a is a0-a1*aMax.
			// All terms are positive since a^2<d*b^4.
			// With multiplier>=3 the sequence is strictly convex;
			// once this minimum exceeds y0 it is increasing forever.
			BigInteger minimum = a0.subtract(a1.multiply(maxA));
			if (minimum.doubleValue() >= limit && minimum.compareTo(y0) > 0) break;
			if (j >= kPosLB) addSquareCandidates(a0, a1, false, words);
			// K<=-1, so no negative-index square can qualify before this j.
			// Ignoring the remaining K restriction only admits extra candidates.
			if (j >= 1+kNegUB) addSquareCandidates(a0, a1, true, words);
			BigInteger nextA0 = multiplier.multiply(a0).subtract(previousA0);
			BigInteger nextA1 = multiplier.multiply(a1).subtract(previousA1);
			previousA1 = a1;
			previousA0 = a0;
			a0 = nextA0;
			a1 = nextA1;
		}
	}

	// the y_k's here are 4*y_k in my sequence so that the quantities are integers
	long processBigIntegerTuple(long a, long b, long d, long t, long u, double ykUB) {
		long c2=0;
		BigInteger v1=BigInteger.valueOf(t*t+d*u*u);
		BigInteger v1a=v1.divide(BigInteger.TWO);
		BigInteger v2=BigInteger.valueOf(2L*a).multiply(BigInteger.valueOf(t*u));
		BigInteger bSqr = BigInteger.valueOf(b*b);

		// check positive-indexed elements
		BigInteger y0=BigInteger.valueOf(4L*b*b);
		BigInteger yPrev = y0;
		long k=1L;
		BigInteger yCurr=bSqr.multiply(v1).add(v2);
		double yCurrD = yCurr.doubleValue();
		boolean isChecked=false;
		while (!isChecked && yCurrD<4.0*ykUB) {
			// recall that m_1 \geq 2 for the positively-indexed elements
			// m_2 \geq 3 for all nrmA code
			if (k >= kPosLB) {
				BigInteger[] sqrtArray = yCurr.sqrtAndRemainder();
				if (sqrtArray[1].equals(BigInteger.ZERO)) {
					System.out.printf("adding d=%8d, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, 4*yCurr=%8d\n",d,a,b,t,u,k,yCurr);
					isChecked=true;
				}
			}
			BigInteger yT=v1a.multiply(yCurr).subtract(yPrev);
			yPrev=yCurr;
			yCurr=yT;
			yCurrD=yCurr.doubleValue();
			k=k+1;
		}

		// check negative-indexed elements
		if (!isChecked) {
			yPrev=y0;
			k=-1;
			yCurr=bSqr.multiply(v1).subtract(v2);
			yCurrD = yCurr.doubleValue();
			long bigK=0;
			while (!isChecked && yCurrD<4.0*ykUB) {
				if (bigK==0 && yCurrD>4.0*b*b) {
					bigK=k;
				}
				if (bigK!=0 && k<=bigK-kNegUB) {
					BigInteger[] sqrtArray = yCurr.sqrtAndRemainder();
					if (sqrtArray[1].equals(BigInteger.ZERO)) {
						System.out.printf("adding d=%8d, a=%6d, b=%3d, t=%6d, u=%3d, K=%2d, k=%2d, 4*yCurr=%8d\n",d,a,b,t,u,bigK,k,yCurr);
						isChecked=true;
					}
				}
				BigInteger yT=v1a.multiply(yCurr).subtract(yPrev);
				yPrev=yCurr;
				yCurr=yT;
				yCurrD=yCurr.doubleValue();
				k=k-1;
			}
		}
		if (isChecked) {
			// MAGMA output
			//System.out.println("d:="+d+";nrmA:="+(a*a-d*b*b*b*b)+";s:=IntegralQuarticPoints([d,0,0,0,nrmA]);printf \"d=%o, nrmA=%o, number=%o, solns=%o\\n\",d, nrmA, #s, s;");
			// PARI output
			System.out.println("d="+d+";nrmA="+(a*a-d*b*b*b*b)+";check_d_n(d,nrmA,dbg);");
			c2=c2+1;
		}
		return c2;
	}

	private double getYM1UpperBound(long aLB, long b, long d, long t, long u) {
		long absNrmA = d*b*b*b*b-aLB*aLB;
		double d12 = Math.sqrt(d);

		// from equation (4.15)
		double yM1Step1UB = 0.54*Math.pow(1.0*b*b*absNrmA,13.0/11)/Math.pow(d,12.0/11);

		// from equation (4.17)
		double yM1Step2UB = 0.23*Math.pow(1.0*absNrmA/d,7.0/6)*Math.pow(b,8.0/3);

		// from equation (4.21)
		double yM1Step3UB = 82.0*Math.pow(1.0*b*b*b*b*absNrmA*absNrmA*absNrmA*absNrmA*absNrmA, 1.0/3)/d12;

		// from equation (4.23)
		double yM1Step4UB = 423.0*b*b*absNrmA*absNrmA/d12;
		double yM1UB = Math.max(16.0*absNrmA/d12, 4.0*b*b*absNrmA/d);
		yM1UB = Math.max(yM1UB, yM1Step1UB);
		yM1UB = Math.max(yM1UB, yM1Step2UB);
		yM1UB = Math.max(yM1UB, yM1Step3UB);
		yM1UB = Math.max(yM1UB, yM1Step4UB);
		return yM1UB;
	}

	// uses (5.18)
	private double[] getDUpperBound(long b, long u) {
		long b4 = b*b*b*b;
		double b8 = 1.0*b4*b4;
		double b36 = b8*b8*b8*b8*b4;
		long u4 = u*u*u*u;
		double u8 = 1.0*u4*u4;
		double u24 = u8*u8*u8;
		double dBnd = 300.0/u/u; // (5.14)
		int ineqUsed = 0;

		double dTemp1 = 17*Math.pow(1.0*b4/u8, 1.0/3); // (5.16) via (5.18) rounding
		if (dTemp1 > dBnd) {
			dBnd = dTemp1;
		}

		double dTemp2 = 5*Math.sqrt(1.0*b*b/u/u); // (5.15) via (5.18) rounding
		if (dTemp2 > dBnd) {
			dBnd = dTemp2;
		}

		// step 1 bound:
		double b56 = b36*b8*b8*b4;
		double u44 = u24*u8*u8*u4;
		double d1 = 1.52*Math.pow(b56/u44, 1.0/21);
		if (d1 > dBnd) {
			dBnd = d1;
			ineqUsed = 1;
		}

		// step 2 bound:
		double d2 = 1.0*Math.pow(b, 8.0/3)/u/u;
		if (d2 > dBnd) {
			dBnd = d2;
			ineqUsed = 2;
		}

		// step 3 bound
		double d3 = 176.0*Math.pow(b36/u24, 1.0/7);
		if (d3 > dBnd) {
			dBnd = d3;
			ineqUsed = 3;
		}

		// step 4 bound
		double d4 = 2416.0*b4*b4/u4;
		if (d4 > dBnd) {
			dBnd = d4;
			ineqUsed = 5;
		}
		// if(dbg!=0,
		// printf("for u=%3d, used inequality %2d to obtain
		// dBnd=%10d\n",u,ineqUsed,dBnd);
		// );
		return new double[] {dBnd, d1,d2,d3,d4};
	}
}

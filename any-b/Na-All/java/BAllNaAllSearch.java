import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.Arrays;
import java.util.TreeSet;

/**
 * squares in sequences of the form (a+b^2*sqrt(d))*((t+u*sqrt(d))/2)^(2*k)
 * any changes in the paper to the bounds requires changing BOTH
 * getDUpperBound() and getYM1UpperBound()
 */
public class BAllNaAllSearch
{
	private static final boolean[] SQUARE_MOD_64 = new boolean[64];
	static {
		for (int i = 0; i < 64; i++) SQUARE_MOD_64[(i * i) & 63] = true;
	}

	private int kNegUB;
	private int kPosLB;

	private long actB; // for using threads

	private BAllNaAllSearch(long b) {
		this(2,3); // interested in squares among y_k with k<=K-2 and k >=3
		actB=b;
	}

	private BAllNaAllSearch(int kNegUB, int kPosLB) {
		this.kNegUB = kNegUB;
		this.kPosLB = kPosLB;
	}

	public static void main(String[] args) {
		if (args!=null && args.length==1) {
			long b=Long.parseLong(args[0]);
			BAllNaAllSearch app = new BAllNaAllSearch(b);
			app.doBWork(b);
		}
		else {
			for (long b=1L;b<5L; b=b+1L) {
				BAllNaAllSearch app = new BAllNaAllSearch(b);
				app.doBWork(b);
			}
		}
	}

	private void doBWork(long b) {
		long uUB = 1L;
		double dUB = getDUpperBound(b, uUB+1)[0];
		while (dUB>1.999) {
			uUB=uUB+1L;
			dUB = getDUpperBound(b, uUB+1)[0];
		}
		double dUB1=getDUpperBound(b,1)[0];
		double dUB2=getDUpperBound(b,2)[0];
		System.out.printf("b=%2d, dUB(u=%2d)=%9.6f, dUB(u=1)=%10d=%9.6e, dUB(u=2)=%9.6e\n",b,uUB+1,dUB,(long) Math.ceil(dUB1),dUB1,dUB2);
		LocalDateTime start = LocalDateTime.now();
		System.out.println("Start date and time: " + start);
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
		long tMod = (long) Math.floor(tUB/100L);
		tMod = Math.max(100, tMod);
		long tLB = 1L;
		// for breaking up u=1 calcs across processors: tLB=((long) (0.75*tUB/tMod))*tMod;
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

	// c1 counts ALL a with negative norm (the original isNrmAValid returned true).
	// c2 counts the equations requiring Magma.
	private long[] doBDTUWork(long b, long d, long t, long u, double dBound) {
		if (d > dBound) return new long[] {0, 0};
		long b2 = Math.multiplyExact(b, b);
		long db4 = Math.multiplyExact(d, Math.multiplyExact(b2, b2));
		// Strict negative norm: a*a < d*b^4. Correct the floating sqrt exactly.
		long aMax = floorSqrt(db4 - 1);
		if (aMax == 0) return new long[] {0, 0};
		double limit = 4.0 * getYM1UpperBound(1, b, d, t, u);
		TupleContext context = new TupleContext(b, d, t, u);
		long c2 = 0;
		if (aMax <= 256 || !Double.isFinite(limit) || limit <= context.y0.doubleValue()
				|| kPosLB < 1 || kNegUB < 0) {
			// Small searches avoid the sieve setup cost. Keep the original fallback.
			long[] ranges = candidateRanges(aMax, limit, context);
			for (int range = 0; range < ranges.length; range += 2) {
				for (long a = ranges[range]; a <= ranges[range + 1]; a++) {
					c2 += processTuple(a, b, d, t, u, limit, context);
				}
			}
		} else {
			// A square at an eligible index is necessary for a reported result.
			// Recheck in ascending a order with the original evaluator to preserve
			// K, floating-point stopping, positive-first priority, and output order.
			for (long a : squareCandidates(aMax, limit, context)) {
				c2 += processTuple(a, b, d, t, u, limit, context);
			}
		}
		return new long[] {aMax, c2};
	}


	/**
	 * Sieve one recurrence index at a time, using Y(+n)=A(n)+a*B(n) and
	 * Y(-n)=A(n)-a*B(n). The expensive recurrence coefficients are calculated
	 * once per index, rather than once for every a.
	 */
	private TreeSet<Long> squareCandidates(long aMax, double limit, TupleContext context) {
		TreeSet<Long> candidates = new TreeSet<>();
		// Exact conversion gives a conservative bound for doubleValue() < limit.
		BigInteger ceiling = new BigDecimal(limit).setScale(0, RoundingMode.CEILING).toBigIntegerExact().subtract(BigInteger.ONE);
		BigInteger maxA = BigInteger.valueOf(aMax);
		BigInteger aPrev = context.y0;
		BigInteger aCurr = context.base;
		BigInteger bPrev = BigInteger.ZERO;
		BigInteger bCurr = context.slope;
		long[] words = new long[(int) Math.min(4096L, (aMax + 63) / 64)];
		for (int n = 1; ; n++) {
			BigInteger minimum = aCurr.subtract(bCurr.multiply(maxA));
			// Every negative-direction sequence is positive and strictly convex.
			// Once its smallest value (at aMax) exceeds both Y0 and the bound,
			// every later term, for every a, is too large. Positive terms are larger.
			if (minimum.compareTo(ceiling) > 0 && minimum.compareTo(context.y0) > 0) break;
			if (n >= kPosLB) {
				BigInteger room = ceiling.subtract(aCurr);
				if (room.signum() >= 0) {
					long end = room.divide(bCurr).min(maxA).longValueExact();
					sieveSquares(aCurr, bCurr, 1, end, words, candidates);
				}
			}
			if (n >= (long) kNegUB + 1) {
				BigInteger need = aCurr.subtract(ceiling);
				long start = need.signum() <= 0 ? 1
						: need.add(bCurr).subtract(BigInteger.ONE).divide(bCurr)
								.min(maxA.add(BigInteger.ONE)).longValueExact();
				sieveSquares(aCurr, bCurr.negate(), start, aMax, words, candidates);
			}
			BigInteger aNext = context.trace.multiply(aCurr).subtract(aPrev);
			BigInteger bNext = context.trace.multiply(bCurr).subtract(bPrev);
			aPrev = aCurr;
			aCurr = aNext;
			bPrev = bCurr;
			bCurr = bNext;
		}
		return candidates;
	}

	/** Square residues for 64 consecutive values of an affine function. */
	private static final class SquareSieve {
		// The composite moduli cheaply combine the tests for 2, 3, 5, 7 and 13.
		static final SquareSieve[] FILTERS = createFilters();
		final int modulus;
		final BigInteger bigModulus;
		final long[][] masks;

		SquareSieve(int modulus) {
			this.modulus = modulus;
			bigModulus = BigInteger.valueOf(modulus);
			boolean[] square = new boolean[modulus];
			for (int i = 0; i < modulus; i++) square[i * i % modulus] = true;
			masks = new long[modulus][modulus];
			for (int slope = 0; slope < modulus; slope++) {
				for (int initial = 0; initial < modulus; initial++) {
					long mask = 0;
					int residue = initial;
					for (int bit = 0; bit < 64; bit++) {
						if (square[residue]) mask |= 1L << bit;
						residue += slope;
						if (residue >= modulus) residue -= modulus;
					}
					masks[slope][initial] = mask;
				}
			}
		}

		private static SquareSieve[] createFilters() {
			int[] moduli = {64, 63, 65, 11, 17, 19, 23, 29, 31, 37, 41, 43};
			SquareSieve[] filters = new SquareSieve[moduli.length];
			for (int i = 0; i < moduli.length; i++) filters[i] = new SquareSieve(moduli[i]);
			return filters;
		}
	}

	private static void sieveSquares(BigInteger constant, BigInteger slope, long first,
			long last, long[] words, TreeSet<Long> candidates) {
		if (first > last) return;
		SquareSieve[] filters = SquareSieve.FILTERS;
		long[][] masks = new long[filters.length][];
		int[] residues = new int[filters.length];
		int[] advances = new int[filters.length];
		int[] moduli = new int[filters.length];
		int active = 0;
		BigInteger initial = constant.add(slope.multiply(BigInteger.valueOf(first)));
		for (SquareSieve filter : filters) {
			int step = slope.mod(filter.bigModulus).intValue();
			int residue = initial.mod(filter.bigModulus).intValue();
			if (step == 0) {
				// A constant nonsquare residue rules out the entire interval.
				if (filter.masks[0][residue] == 0) return;
				continue;
			}
			masks[active] = filter.masks[step];
			residues[active] = residue;
			advances[active] = 64 * step % filter.modulus;
			moduli[active] = filter.modulus;
			active++;
		}
		for (long start = first; start <= last; ) {
			int count = (int) Math.min((long) words.length * 64, last - start + 1);
			int wordCount = (count + 63) / 64;
			Arrays.fill(words, 0, wordCount, -1L);
			for (int filter = 0; filter < active; filter++) {
				long[] row = masks[filter];
				int residue = residues[filter], advance = advances[filter], modulus = moduli[filter];
				for (int word = 0; word < wordCount; word++) {
					words[word] &= row[residue];
					residue += advance;
					if (residue >= modulus) residue -= modulus;
				}
				residues[filter] = residue;
			}
			int tail = count & 63;
			if (tail != 0) words[wordCount - 1] &= (1L << tail) - 1;
			for (int word = 0; word < wordCount; word++) {
				long bits = words[word];
				while (bits != 0) {
					long a = start + 64L * word + Long.numberOfTrailingZeros(bits);
					bits &= bits - 1;
					if (!candidates.contains(a)
							&& isSquare(constant.add(slope.multiply(BigInteger.valueOf(a))))) {
						candidates.add(a);
					}
				}
			}
			start += count;
		}
	}

	private static long floorSqrt(long n) {
		if (n < 0) throw new IllegalArgumentException("n="+n+" is negative");
		if (n == 0) return 0;
		long r = (long) Math.sqrt(n);
		while (r > n / r) r--;
		while (r + 1 <= n / (r + 1)) r++;
		return r;
	}

	private static final class TupleContext {
		final BigInteger y0, trace, base, slope;

		TupleContext(long b, long d, long t, long u) {
			BigInteger bb = BigInteger.valueOf(b).pow(2);
			BigInteger tt = BigInteger.valueOf(t);
			BigInteger uu = BigInteger.valueOf(u);
			BigInteger v1 = tt.multiply(tt).add(BigInteger.valueOf(d).multiply(uu.pow(2)));
			y0 = bb.shiftLeft(2);
			trace = v1.divide(BigInteger.TWO);
			base = bb.multiply(v1);
			slope = tt.multiply(uu).shiftLeft(1);
		}
	}

	/**
	 * Write the scaled terms as Y(+n) = A(n) + a*B(n), Y(-n) = A(n) - a*B(n).
	 * A and B satisfy the same recurrence, with (A0,B0)=(4*b*b,0) and
	 * (A1,B1)=(2*b*b*trace,2*t*u).
	 *
	 * Positive terms increase, so a positive hit requires Y(kPosLB) < limit.
	 * A negative hit has |k| >= kNegUB+1. The negative terms are positive and
	 * strictly convex: Y(n+1)-2*Y(n)+Y(n-1) = (trace-2)*Y(n) > 0.
	 * If Y(kNegUB+1) >= limit > Y0, all later terms are larger still; hence
	 * such an a cannot produce a negative hit. These are necessary conditions,
	 * not substitutes for the original recurrence, index and square checks.
	 */
	private long[] candidateRanges(long aMax, double limit, TupleContext context) {
		if (!Double.isFinite(limit) || limit <= context.y0.doubleValue() || kPosLB < 1 || kNegUB < 0) {
			return new long[] {1, aMax};
		}
		// BigDecimal(double), deliberately NOT valueOf, preserves the exact
		// binary floating-point bound. This is conservative for the original
		// BigInteger.doubleValue() < limit comparison, including rounding ties.
		BigInteger ceiling = new BigDecimal(limit).setScale(0, RoundingMode.CEILING).toBigIntegerExact().subtract(BigInteger.ONE);
		BigInteger[] positive = termCoefficients(kPosLB, context);
		BigInteger[] negative = kPosLB == kNegUB + 1 ? positive : termCoefficients(kNegUB + 1, context);
		BigInteger maxA = BigInteger.valueOf(aMax);
		BigInteger positiveRoom = ceiling.subtract(positive[0]);
		long positiveEnd = positiveRoom.signum() < 0 ? 0 : positiveRoom.divide(positive[1]).min(maxA).longValueExact();
		BigInteger negativeNeed = negative[0].subtract(ceiling);
		// ceil(negativeNeed / slope), clamped to [1, aMax+1].
		long negativeStart = negativeNeed.signum() <= 0 ? 1
				: negativeNeed.add(negative[1]).subtract(BigInteger.ONE)
						.divide(negative[1]).min(maxA.add(BigInteger.ONE)).longValueExact();
		if (negativeStart <= positiveEnd + 1) return new long[] {1, aMax};
		if (positiveEnd == 0) {
			return negativeStart > aMax ? new long[0] : new long[] {negativeStart, aMax};
		}
		if (negativeStart > aMax) return new long[] {1, positiveEnd};
		return new long[] {1, positiveEnd, negativeStart, aMax};
	}

	private static BigInteger[] termCoefficients(int n, TupleContext context) {
		BigInteger aPrev = context.y0, aCurr = context.base;
		BigInteger bPrev = BigInteger.ZERO, bCurr = context.slope;
		for (int i = 1; i < n; i++) {
			BigInteger aNext = context.trace.multiply(aCurr).subtract(aPrev);
			BigInteger bNext = context.trace.multiply(bCurr).subtract(bPrev);
			aPrev = aCurr;
			aCurr = aNext;
			bPrev = bCurr;
			bCurr = bNext;
		}
		return new BigInteger[] {aCurr, bCurr};
	}

	private static boolean isSquare(BigInteger value) {
		// An exact necessary test: reject 52 of the 64 low-bit patterns before sqrt.
		return SQUARE_MOD_64[value.intValue() & 63]	&& value.sqrtAndRemainder()[1].signum() == 0;
	}

	// All recurrence terms are 4*y_k, just as in the original implementation.
	private long processTuple(long a, long b, long d, long t, long u, double limit, TupleContext context) {
		BigInteger offset = context.slope.multiply(BigInteger.valueOf(a));
		BigInteger yPrev = context.y0;
		BigInteger yCurr = context.base.add(offset);
		long k = 1;
		boolean found = false;
		while (yCurr.doubleValue() < limit) {
			if (k >= kPosLB && isSquare(yCurr)) {
				System.out.printf("adding d=%8d, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, 4*yCurr=%8d\n",
						d, a, b, t, u, k, yCurr);
				found = true;
				break;
			}
			BigInteger next = context.trace.multiply(yCurr).subtract(yPrev);
			yPrev = yCurr;
			yCurr = next;
			k++;
		}
		if (!found) {
			yPrev = context.y0;
			yCurr = context.base.subtract(offset);
			k = -1;
			long bigK = 0;
			while (yCurr.doubleValue() < limit) {
				if (bigK == 0 && yCurr.doubleValue() > 4.0 * b * b) bigK = k;
				if (bigK != 0 && k <= bigK - kNegUB && isSquare(yCurr)) {
					System.out.printf("adding d=%8d, a=%6d, b=%3d, t=%6d, u=%3d, K=%2d, k=%2d, 4*yCurr=%8d\n",
							d, a, b, t, u, bigK, k, yCurr);
					found = true;
					break;
				}
				BigInteger next = context.trace.multiply(yCurr).subtract(yPrev);
				yPrev = yCurr;
				yCurr = next;
				k--;
			}
		}
		if (found) {
			System.out.println("d:="+d+";nrmA:="+(a*a-d*b*b*b*b)+";s:=IntegralQuarticPoints([d,0,0,0,nrmA]);printf \"d=%o, nrmA=%o, number=%o, solns=%o\\n\",d, nrmA, #s, s;");
			return 1;
		}
		return 0;
	}

	private double getYM1UpperBound(long aLB, long b, long d, long t, long u) {
		long absNrmA = d*b*b*b*b-aLB*aLB;
		double d12 = Math.sqrt(d);
		double b83 = Math.pow(b,8.0/3);
		//double b65 = Math.pow(b,6.0/5);

		// from equation (4.14)
		double yM1Step1UB = 10.9*Math.pow(1.0*b*absNrmA,26.0/11)/Math.pow(d,12.0/11);

		// from equation (4.16)
		double yM1Step2UB = 9.1*Math.pow(1.0*absNrmA/d,5.0/2)*b83/Math.pow(d,7.0/6);

		// from equation (4.20) (no longer needed. Smaller than bound in (4.22))
		//double yM1Step3UB = 260.0*b65*(1.0*absNrmA)*(1.0*absNrmA)*(1.0*absNrmA)/d;

		// from equation (4.22)
		double yM1Step4UB = 423.0*b*b*absNrmA*absNrmA*absNrmA/d12;
		double yM1UB = Math.max(yM1Step1UB, yM1Step2UB);
		//yM1UB = Math.max(yM1UB, yM1Step3UB);
		yM1UB = Math.max(yM1UB, yM1Step4UB);
		return yM1UB;
	}

	private double[] getDUpperBound(long b, long u) {
		long b4 = b*b*b*b;
		double b8 = 1.0*b4*b4;
		double b32 = b8*b8*b8*b8;
		double b36 = b32*b4;
		double b52 = b36*b8*b8;
		long u4 = u*u*u*u;
		double u6 = 1.0*u4*u*u;
		double u8 = 1.0*u4*u4;
		double u12 = u8*u4;
		double u18 = u12*u6;
		double u24 = u8*u8*u8;
		double u36 = u24*u12;
		double dBnd = 300.0/u/u; // (5.14)
		int ineqUsed = 0;

		double dTemp1 = 5.4*Math.pow(b4/u12, 1.0/5); // (5.15)
		if (dTemp1 > dBnd) {
			dBnd = dTemp1;
		}

		// step 1 bound:
		double b108 = b36*b36*b36;
		double u66 = u24*u24*u24/u6;
		double d1 = 10.0*Math.pow(b108/u66, 1.0/19);
		if (d1 > dBnd) {
			dBnd = d1;
			ineqUsed = 1;
		}

		// step 2 bound:
		double d2 = 9.0*Math.pow(b32/u18, 1.0/5);
		if (d2 > dBnd) {
			dBnd = d2;
			ineqUsed = 2;
		}

		// step 3 bound
		double d3 = 57.0*Math.pow(b52/u36, 1.0/9);
		if (d3 > dBnd) {
			dBnd = d3;
			ineqUsed = 3;
		}

		// step 4 bound
		double d4 = 2461.0*b4*b4*b4/u4/u/u;
		if (d4 > dBnd) {
			dBnd = d4;
			ineqUsed = 4;
		}
		return new double[] {dBnd, d1,d2,d3,d4};
	}
}

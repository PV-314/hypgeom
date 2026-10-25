import java.math.BigInteger;
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * squares in sequences of the form (a+b^2*sqrt(d))*((t+u*sqrt(d))/2)^(2*k)
 * i.e., my y_k's
 */
public class BAllNaSqrSearch
{
	private SumOfTwoSquares sumsOfSquares;

	public static void main(String[] args) {
		if (args!=null && args.length==1) {
			long b=Long.parseLong(args[0]);
			BAllNaSqrSearch app = new BAllNaSqrSearch();
			app.doBWork(b);
		} else {
			BAllNaSqrSearch app = new BAllNaSqrSearch();
			app.doBWork(17);
			// System.out.println("Usage: BAllNaSqrSearch b");
		}
	}

	private void doBWork(long b) {
		if (b < 1) throw new IllegalArgumentException("b must be positive");
		// Factor d once per tuple; b^4 has the same factorisation throughout.
		sumsOfSquares = new SumOfTwoSquares(b, (long) Math.ceil(getDBnd(b, 1)[0]));
		long uUB = 2L;
		double dUB = getDBnd(b, uUB+1)[0];
		while (dUB>1.999) {
			uUB=uUB+1L;
			dUB = getDBnd(b, uUB+1)[0];
		}
		double dUB1=getDBnd(b,1)[0];
		double dUB2=getDBnd(b,2)[0];
		System.out.printf("dUB(u=%2d)=%9.6f, dUB(u=1)=%10d=%9.6e, dUB(u=2)=%9.6e\n",uUB+1,dUB,(long) Math.ceil(dUB1),dUB1,dUB2);
		LocalDateTime start = LocalDateTime.now();
		System.out.println("Start date and time: " + start);
		long startTimeMillis=System.currentTimeMillis();
		long[] cArray = new long[2];
		for (long u=1L; u<=uUB; u++) {
			double dUB_app = getDBnd(b, u)[0];
			System.out.println("for u="+u+", dUB="+dUB_app);
			doBUWork(b, u, dUB_app, cArray);
		}
		System.out.println("total time="+(System.currentTimeMillis()-startTimeMillis)+"(ms).");
		LocalDateTime end = LocalDateTime.now();
		System.out.println("End date and time: " + end);
	}

	// side-effect: cArray gets updated
	private void doBUWork(long b, long u, double dUB, long[] cArray) {
		long uStartTime = System.currentTimeMillis();
		long c1 = cArray[0];
		long c2 = cArray[1];
		double tUB = Math.sqrt(u*u*dUB+4L);
		long tMod = (long) Math.floor(tUB/100L);
		tMod = Math.max(100, tMod);
		long b4 = b*b*b*b;
		long tLB = 1L;

		for (long t = tLB; t <= tUB; t++) {
			long du2 = t*t+4L;
			if (du2 % (u*u) == 0L) {
				long d = du2/u/u;
				long[] cArray1=doBDTUWork(b, d, t, u, b4);
				c1=c1+cArray1[0];
				c2=c2+cArray1[1];
			}
			du2 = t*t-4L;
			if (du2 > 0 && du2 % (u*u) == 0L) {
				long d = du2/u/u;
				long[] cArray1=doBDTUWork(b, d, t, u, b4);
				c1=c1+cArray1[0];
				c2=c2+cArray1[1];
			}
			if (t % tMod == 0L) {
				long millis = System.currentTimeMillis()-uStartTime;
				Duration duration = Duration.ofMillis(millis);
				String s = String.format("%2dh, %2dmin, %2ds, %3dms", duration.toHours(), duration.toMinutesPart(), duration.toSecondsPart(), duration.toMillisPart());
				System.out.printf("b=%2d, t=%6d (u=%3d is %5.2f percent done), d(est)=%11d, c1=%10d, c2=%4d, total time=%9d(ms)=%s\n", b, t, u, (100.0*t/tUB), Math.round(1.0d*du2/u/u), c1, c2, millis, s);
			}
		}
		System.out.println("done b="+b+", u="+u+": total found "+c1+" equations. uTime="+(System.currentTimeMillis()-uStartTime));
		cArray[0]=c1;
		cArray[1]=c2;
	}

	// returns [c1,c2], where
	// c1=the number of values, a, found with -N_a=db^4-a^2 a perfect square for b and d (for logging)
	// c2=the number of equations to try in Magma
	private long[] doBDTUWork(long b, long d, long t, long u, long b4) {
		long c1 = 0L;
		long c2 = 0L;
		double[] dBndInfo = getDBnd(b, u);
		double dBnd=dBndInfo[0];
		if (d <= dBnd) {
			long aLB = 1L;
			double aUB = Math.sqrt(d)*b*b;
			// the following gives very very little difference :-(
			// e.g., for b=17, t=7309, u=1, aUB=2112273.0, but sqrt(d*b^4)=2112301.079080584
			// aUB=getAUpperBound(b, d, u, new double[] {dBndInfo[1], dBndInfo[2], dBndInfo[3], dBndInfo[4]}, dPow11, dPow13, dPow23, b4, b8, b20, b28, b48, uPow4, uPow8, uPow24, uPow44);
			//System.out.println("for b="+b+", t="+t+", u="+u+", aUB="+aUB+", but sqrt(d*b^4)="+Math.sqrt(d*b*b*b*b));
			double ykUB = getYM1UpperBound(aLB, b, d, t, u);
			for (long a : sumsOfSquares.candidates(d)) {
				// Retain the original floating-point upper-bound comparison.
				if (a <= aUB) {
					c2=c2+processBigIntegerTuple(a, b, d, t, u, ykUB);
					c1 = c1+1L;
				}
			}
		}
		return new long[] {c1,c2};
	}

	/**
	 * Enumerates all positive a with a^2 + c^2 = d*b^4 and c > 0.
	 * Unique factorisation in Z[i] replaces the linear scan up to b^2*sqrt(d).
	 * A prime 3 mod 4 must have even exponent; a prime 1 mod 4 splits as
	 * (x+iy)(x-iy). For exponent e, all e+1 allocations between those two
	 * factors are enumerated. Units and conjugation are handled by taking
	 * absolute values of BOTH coordinates; a sorted set removes duplicates.
	 */
	static final class SumOfTwoSquares {
		private final long b4;
		private final int[] primes;
		private final Map<Long, Integer> bFactors;
		// Only cache small primes, so a long search cannot retain millions of entries.
		private final Map<Long, long[]> primeSquares = new TreeMap<>();

		SumOfTwoSquares(long b, long maxD) {
			long b2 = Math.multiplyExact(b, b);
			b4 = Math.multiplyExact(b2, b2);
			Math.multiplyExact(maxD, b4); // Fail explicitly if the long search would overflow.
			long limit = floorSqrt(Math.max(b, maxD));
			if (limit >= Integer.MAX_VALUE - 1L)
				throw new IllegalArgumentException("Factor sieve exceeds Java array limits");
			primes = sieve((int) limit);
			bFactors = factor(b);
			bFactors.replaceAll((p, exponent) -> 4 * exponent);
		}

		long[] candidates(long d) {
			long n = Math.multiplyExact(d, b4);
			if (n <= 1) return new long[0];
			Map<Long, Integer> factors = factor(d);
			for (Map.Entry<Long, Integer> entry : factors.entrySet()) {
				if ((entry.getKey() & 3) == 3 && (entry.getValue() & 1) != 0)
					return new long[0]; // b^4 cannot change exponent parity.
			}
			bFactors.forEach((p, exponent) -> factors.merge(p, exponent, Integer::sum));
			long real = 1, imaginary = 0;
			List<long[][]> choices = new ArrayList<>();
			for (Map.Entry<Long, Integer> entry : factors.entrySet()) {
				long p = entry.getKey();
				int exponent = entry.getValue();
				if (p == 2) {
					for (int i = 0; i < exponent; i++) {
						long nextReal = real - imaginary;
						imaginary += real;
						real = nextReal;
					}
				} else if ((p & 3) == 3) {
					for (int i = 0; i < exponent / 2; i++) {
						real *= p;
						imaginary *= p;
					}
				} else {
					long[] xy = primeSquares.get(p);
					if (xy == null) {
						xy = primeAsTwoSquares(p);
						if (p <= 1_000_000L) primeSquares.put(p, xy);
					}
					long[][] powers = new long[exponent + 1][2];
					powers[0][0] = 1;
					for (int i = 1; i <= exponent; i++) {
						powers[i][0] = powers[i-1][0]*xy[0] - powers[i-1][1]*xy[1];
						powers[i][1] = powers[i-1][0]*xy[1] + powers[i-1][1]*xy[0];
					}
					long[][] allocations = new long[exponent + 1][2];
					for (int i = 0; i <= exponent; i++) {
						long[] left = powers[i], right = powers[exponent - i];
						allocations[i][0] = left[0]*right[0] + left[1]*right[1];
						allocations[i][1] = left[1]*right[0] - left[0]*right[1];
					}
					choices.add(allocations);
				}
			}
			TreeSet<Long> result = new TreeSet<>();
			enumerate(choices, 0, real, imaginary, result);
			long[] values = new long[result.size()];
			int index = 0;
			for (long a : result) values[index++] = a;
			return values;
		}

		private static void enumerate(List<long[][]> choices, int index, long x, long y,
				TreeSet<Long> result) {
			if (index == choices.size()) {
				if (x != 0 && y != 0) {
					result.add(Math.abs(x));
					result.add(Math.abs(y));
				}
				return;
			}
			for (long[] z : choices.get(index))
				enumerate(choices, index + 1, x*z[0] - y*z[1], x*z[1] + y*z[0], result);
		}

		private Map<Long, Integer> factor(long n) {
			Map<Long, Integer> factors = new TreeMap<>();
			for (int p : primes) {
				if ((long) p*p > n) break;
				int exponent = 0;
				while (n % p == 0) {
					n /= p;
					exponent++;
				}
				if (exponent != 0) factors.put((long) p, exponent);
			}
			if (n > 1) factors.put(n, 1);
			return factors;
		}

		private static int[] sieve(int limit) {
			boolean[] composite = new boolean[limit + 1];
			for (int p = 2; (long) p*p <= limit; p++) {
				if (!composite[p]) {
					for (long multiple = (long) p*p; multiple <= limit; multiple += p)
						composite[(int) multiple] = true;
				}
			}
			int count = 0;
			for (int p = 2; p <= limit; p++) if (!composite[p]) count++;
			int[] primes = new int[count];
			int index = 0;
			for (int p = 2; p <= limit; p++) if (!composite[p]) primes[index++] = p;
			return primes;
		}

		private static long[] primeAsTwoSquares(long p) {
			// Cornacchia's algorithm, starting from a square root of -1 modulo p.
			// BigInteger modular powers avoid overflow for the larger prime factors.
			BigInteger modulus = BigInteger.valueOf(p);
			BigInteger exponent = BigInteger.valueOf((p - 1) / 4);
			long root;
			for (long base = 2; ; base++) {
				BigInteger r = BigInteger.valueOf(base).modPow(exponent, modulus);
				if (r.multiply(r).mod(modulus).equals(modulus.subtract(BigInteger.ONE))) {
					root = r.longValueExact();
					break;
				}
			}
			long previous = p, current = root;
			while (current > p / current) {
				long next = previous % current;
				previous = current;
				current = next;
			}
			long remainder = p - current*current;
			long other = floorSqrt(remainder);
			if (other*other != remainder)
				throw new ArithmeticException("Cannot represent prime as two squares: " + p);
			return new long[] {current, other};
		}

		private static long floorSqrt(long n) {
			if (n < 0) throw new IllegalArgumentException("Negative square root");
			long root = (long) Math.sqrt(n);
			while (root > 0 && root > n / root) root--;
			while (root + 1 <= n / (root + 1)) root++;
			return root;
		}
	}

	// the y_k's here are 4*y_k in my sequence so that the quantities are integers
	private long processBigIntegerTuple(long a, long b, long d, long t, long u, double ykUB) {
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
			// recall we need only check k_1 \geq 2 for the positively-indexed elements
			if (k >= 2L) {
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
			k=k+1L;
		}

		// check negative-indexed elements
		if (!isChecked) {
			yPrev=y0;
			k=-1L;
			yCurr=bSqr.multiply(v1).subtract(v2);
			yCurrD = yCurr.doubleValue();
			long bigK=0;
			while (!isChecked && yCurrD<4.0*ykUB) {
				if (bigK==0 && yCurrD>4.0*b*b) {
					bigK=k;
				}
				if (bigK!=0 && k<=bigK-1) {
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
				k=k-1L;
			}
		}
		if (isChecked) {
			System.out.println("d:="+d+";nrmA:="+(a*a-d*b*b*b*b)+";s:=IntegralQuarticPoints([d,0,0,0,nrmA]);printf \"d=%o, nrmA=%o, number=%o, solns=%o\\n\",d, nrmA, #s, s;");
			c2=c2+1L;
		}
		return c2;
	}

	private double getYM1UpperBound(long aLB, long b, long d, long t, long u) {
		long absNrmA = d*b*b*b*b-aLB*aLB;
		double nA12 = Math.sqrt(absNrmA);
		double b12 = Math.sqrt(b);
		double d12 = Math.sqrt(d);

		// the simplified (and weaker) bounds for steps 1 and 2 reduce the time by over half
		// from equation (4.18)
		double yM1Step1UB = 0.21*b*b*b12*absNrmA*nA12/d;

		// from equation (4.20)
		double yM1Step2UB = b*b*b*absNrmA*nA12/10.0/d;

		long gnd4Value = 2L; // 1/(gnd4)^(2-1/(2*r-1)) \leq 1/2^(2-1/(2*r-1))
		// from equation (4.25)
		double yM1Step3UBBase = 59.2*absNrmA*nA12/d12/gnd4Value/gnd4Value;
		// r_0=2 value: exponent=1/(2*r_0-1)=1/3.
		// if yM1Step3UBRem>1, then the max rem contribution comes from yM1Step3UBRem^(1/3)
		// if yM1Step3UBRem \leq 1, then as r_0->+infty, the rem^(1/(2*r_0-1)) term approaches 1 from below
		double yM1Step3UBRem = 0.653*nA12*b*b*b*b*gnd4Value/d;
		if (yM1Step3UBRem>1) {
			yM1Step3UBRem=Math.pow(yM1Step3UBRem, 1.0/3);
		} else {
			yM1Step3UBRem=1.0;
		}
		double yM1Step3UB = yM1Step3UBBase*yM1Step3UBRem;

		// from equation (4.28)
		double yM1Step4UBBase = 65.32*absNrmA*nA12/d12/gnd4Value/gnd4Value;
		// r_0=2 value: exponent=1/2/(r_0-1)=1/2.
		// if yM1Step4UBRem>1, then the max contribution comes from yM1Step4UBRem^(1/2)
		// if yM1Step4UBRem \leq 1, then as r_0->+infty, the rem^(1/2/(r_0-1)) term approaches 1 from below
		double yM1Step4UBRem = 5.233*absNrmA*b*b*b*b/d;
		if (yM1Step4UBRem>1) {
			yM1Step4UBRem=Math.sqrt(yM1Step4UBRem);
		} else {
			yM1Step4UBRem=1.0;
		}
		double yM1Step4UB = yM1Step4UBBase*yM1Step4UBRem;

		double yM1UB = Math.max(yM1Step1UB, yM1Step2UB);
		yM1UB = Math.max(yM1UB, yM1Step3UB);
		yM1UB = Math.max(yM1UB, yM1Step4UB);
		return yM1UB;
	}

	// returns new double [] {dBnd, d1,d2,d3,d4}
	double[] getDBnd(long b, long u) {
		long b4 = b*b*b*b;
		double b8 = 1.0*b4*b4;
		double b36 = b8*b8*b8*b8*b4;
		long u4 = u*u*u*u;
		double u8 = 1.0*u4*u4;
		double u24 = u8*u8*u8;
		double dBnd = 12.0*b*b/u/u;
		int ineqUsed = 0;

		// step 1 bound:
		double b56 = b36*b8*b8*b4;
		double u44 = u24*u8*u8*u4;
		double d1 = 0.92*Math.pow(b56/u44, 1.0/21); // (5.6)
		if (d1 > dBnd) {
			dBnd = d1;
			ineqUsed = 1;
		}

		// step 2 bound:
		double d2 = 0.64*Math.pow(b, 8.0/3)/u/u; // (5.8)
		if (d2 > dBnd) {
			dBnd = d2;
			ineqUsed = 2;
		}

		// step 3 bound
		double d3 = 60.0*Math.pow(b36/u24, 1.0/7); // (5.11)
		if (d3 > dBnd) {
			dBnd = d3;
			ineqUsed = 3;
		}

		// step 4 bound
		double d4 = 151.0*b4*b4/u4; // (5.14)
		if (d4 > dBnd) {
			dBnd = d4;
			ineqUsed = 5;
		}
		return new double[] {dBnd, d1,d2,d3,d4};
	}
}

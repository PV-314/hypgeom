import java.math.BigInteger;
import java.time.Duration;

/**
 * squares in sequences of the form (a+b^2*sqrt(d))*((t+u*sqrt(d))/2)^(2*k)
 * i.e., my y_k's
 */
public class BAllNaSqrSearch
{
	public static void main(String[] args) {
		if (args!=null && args.length==1) {
			long b=Long.parseLong(args[0]);
			BAllNaSqrSearch app = new BAllNaSqrSearch();
			app.doBWork(b);
		} else {
			long b = 13L;
			BAllNaSqrSearch app = new BAllNaSqrSearch();
			app.doBWork(b);
		}
	}

	private void doBWork(long b) {
		long uUB = 2L;
		double dUB = getDBnd(b, uUB+1)[0];
		while (dUB>1.999) {
			uUB=uUB+1L;
			dUB = getDBnd(b, uUB+1)[0];
		}
		double dUB1=getDBnd(b,1)[0];
		double dUB2=getDBnd(b,2)[0];
		System.out.printf("dUB(u=%2d)=%9.6f, dUB(u=1)=%10d=%9.6e, dUB(u=2)=%9.6e\n",uUB+1,dUB,(long) Math.ceil(dUB1),dUB1,dUB2);
		long startTime=System.currentTimeMillis();
		long[] cArray = new long[2];
		for (long u=1L; u<=uUB; u++) {
			double dUB_app = getDBnd(b, u)[0];
			System.out.println("for u="+u+", dUB="+dUB_app);
			doBUWork(b, u, dUB_app, cArray);
		}
		System.out.println("total time="+(System.currentTimeMillis()-startTime)+"(ms).");
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
		double b8 = 1.0*b4*b4;
		double b20 = b8*b8*b4;
		double b28 = b20*b8;
		double b48 = b8*b8*b8*b8*b8*b8;
		long u4 = u*u*u*u;
		double u8 = 1.0*u4*u4;
		double u24 = 1.0*u8*u8*u8;
		double u44 = u24*u8*u8*u4;
		long tLB = 1L;
		for (long t = tLB; t <= tUB; t++) {
			long d = t*t+4L;
			if (d % (u*u) == 0L) {
				d = d/u/u;
				double dPow11 = Math.pow(d/15.3, 11.0);
				double dPow13 = Math.pow(d/0.66, 13.0); // from step 2
				double dPow23 = Math.pow(d/0.882, 23.0); // from step 1
				long[] cArray1=doBDTUWork(b, d, t, u, dPow11, dPow13, dPow23, b4, b8, b20, b28, b48, u4, u8, u24, u44);
				c1=c1+cArray1[0];
				c2=c2+cArray1[1];
			}
			d = t*t-4L;
			if (d > 0 && d % (u*u) == 0L) {
				d = d/u/u;
				double dPow11 = Math.pow(d/15.3, 11.0);
				double dPow13 = Math.pow(d/0.66, 13.0); // from step 2
				double dPow23 = Math.pow(d/0.882, 23.0); // from step 1
				long[] cArray1=doBDTUWork(b, d, t, u, dPow11, dPow13, dPow23, b4, b8, b20, b28, b48, u4, u8, u24, u44);
				c1=c1+cArray1[0];
				c2=c2+cArray1[1];
			}
			if (t % tMod == 0L) {
				long millis = System.currentTimeMillis()-uStartTime;
				Duration duration = Duration.ofMillis(millis);
				String s = String.format("%2dh, %2dmin, %2ds, %3dms", duration.toHours(), duration.toMinutesPart(), duration.toSecondsPart(), duration.toMillisPart());
				System.out.printf("b=%2d, t=%6d (u=%3d is %5.2f percent done), d=%11d, c1=%10d, c2=%4d, total time=%9d(ms)=%s\n", b, t, u, (100.0*t/tUB), d+8L, c1, c2, millis, s);
			}
		}
		System.out.println("done b="+b+", u="+u+": total found "+c1+" equations. uTime="+(System.currentTimeMillis()-uStartTime));
		cArray[0]=c1;
		cArray[1]=c2;
	}

	// returns [c1,c2], where
	// c1=the number of values, a, found with -N_a=db^4-a^2 a perfect square for b and d (for logging)
	// c2=the number of equations to try in Magma
	private long[] doBDTUWork(long b, long d, long t, long u, double dPow11, double dPow13, double dPow23, long b4, double b8, double b20, double b28, double b48, double uPow4, double uPow8, double uPow24, double uPow44) {
		long c1 = 0L;
		long c2 = 0L;
		double[] dBndInfo = getDBnd(b, u);
		double dBnd=dBndInfo[0];
		if (d <= dBnd) {
			long aLB = getALowerBound(b, d, u, new double[] {dBndInfo[1], dBndInfo[2], dBndInfo[3], dBndInfo[4]}, dPow11, dPow13, dPow23, b4, b8, b20, b28, b48, uPow4, uPow8, uPow24, uPow44);
			double aUB = Math.sqrt(d*b4);
			double ykUB = getYM1UpperBound(aLB, b, d, t, u);
			for (long a = aLB; a <= aUB; a++) {
				long nrmA = a*a-d*b4;
				if (nrmA < 0 && isSquare(-nrmA)) {
					c2=c2+processBigIntegerTuple(a, b, d, t, u, ykUB);
					//aTupleList.add(new ATuple(a, b, d, t, u, ykUB));
					c1 = c1+1L;
				}
			}
		}
		return new long[] {c1,c2};
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
			// recall that m_1 \geq 2 for the positively-indexed elements
			// m_2 \geq 3 for all nrmA code
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

	private long getALowerBound(long b, long d, long u, double[] dBndInfo, double dPow11, double dPow13, double dPow23, double b4, double b8, double b20, double b28, double b48, double u4, double u8, double u24, double u44) {
		double aLB = Math.sqrt(d*b4);

		int ineqUsed = -1;
		// from r_0=1, p/q \neq stuff, (C-3a):
		if (d<dBndInfo[0]) {
			double a2LB = d*b4-Math.sqrt(dPow23*u44/b48);
			if (a2LB < aLB*aLB) {
				aLB = Math.sqrt(a2LB);
				ineqUsed = 1;
			}
		}

		// from r_0=1, p/q=stuff, (C-4a):
		if (d<dBndInfo[1]) {
			double a2LB = d*b4-dPow13*u24/b28;
			if (a2LB < aLB*aLB) {
				aLB = Math.sqrt(a2LB);
				ineqUsed = 2;
			}
		}

		// from r_0>1, p/q \neq stuff, (C-5a):
		if (d<dBndInfo[2]) {
			double a2LB = d*b4-Math.sqrt(Math.sqrt(dPow11*u24/b20));
			if (a2LB < aLB*aLB) {
				aLB = Math.sqrt(a2LB);
				ineqUsed = 3;
			}
		}

		// from r_0>1, p/q=stuff, (C-6a):
		if (d<dBndInfo[3]) {
			double a2LB = d*b4-((d/17.0)*(d/17.0)*u4/b4);
			if (a2LB < aLB*aLB) {
				aLB = Math.sqrt(a2LB);
				ineqUsed = 4;
			}
		}
		if (aLB<1)
			aLB=1;

		return (long) aLB;
	}

	private double getYM1UpperBound(long aLB, long b, long d, long t, long u) {
		long absNrmA = d*b*b*b*b-aLB*aLB;
		double d12 = Math.sqrt(d);
		double d34 = Math.sqrt(d12*d12*d12);
		// the simplified bounds for steps 1 and 2 reduce the time by over half
		// from equation (4.19)
		double yM1Step1UB = 0.19*b*b*absNrmA/d;

		// from equation (4.21)
		double yM1Step2UB = b*b*absNrmA/10.0/d;

		double sqrtNA = Math.sqrt(absNrmA);
		long gnd4Value = 2L; // 1/(gnd4)^(2-1/(2*r-1)) \leq 1/2^(2-1/(2*r-1))
		// from equation (4.27)
		double yM1Step3UBBase = 59.2*sqrtNA*sqrtNA*sqrtNA*b/d12/gnd4Value/gnd4Value;
		// r_0=2 value: exponent=1/(2*r_0-1)=1/3.
		// if 67.1*...>1, then the max contribution comes from (67.1*...)^(1/3)
		// if 67.1*... \leq 1, then as r_0->+infty, the rem^(1/(2*r_0-1)) term
		// approaches 1 from below
		double yM1Step3UBRem = Math.max(1,67.1*sqrtNA*sqrtNA*sqrtNA*sqrtNA*sqrtNA*b*b*b*b*b*b*b*gnd4Value/d);
		double yM1Step3UB = yM1Step3UBBase*Math.pow(yM1Step3UBRem, 1.0/3); // r_0=2 value
		// yM1Step3UB=max(yM1Step3UB,yM1Step3UBBase*yM1Step3UBRem^(1/5)); \\ r_0=3 value
		// yM1Step3UB=max(yM1Step3UB,yM1Step3UBBase*yM1Step3UBRem^(1/7)); \\ r_0=4 value

		// from equation (4.29)
		double yM1Step4UBBase = 65.32*sqrtNA*sqrtNA*sqrtNA/d12/gnd4Value/gnd4Value;
		// r_0=2 value: exponent=1/2/(r_0-1)=1/2.
		// if 422*...>1, then the max contribution comes from (422*...)^(1/2)
		// if 422*... \leq 1, then as r_0->+infty, the rem^(1/2/(r_0-1)) term approaches
		// 1 from below
		double yM1Step4UBRem = Math.max(1, 422*Math.abs(absNrmA*absNrmA*absNrmA)*b*b/d);
		double yM1Step4UB = yM1Step4UBBase*Math.sqrt(yM1Step4UBRem);
		// yM1Step4UB=max(yM1Step4UB,yM1Step4UBBase*yM1Step4UBRem^(1/4)); \\ r_0=3 value
		// yM1Step4UB=max(yM1Step4UB,yM1Step4UBBase*yM1Step4UBRem^(1/6)); \\ r_0=4 value
		double yM1UB = Math.max(yM1Step1UB, yM1Step2UB);
		yM1UB = Math.max(yM1UB, yM1Step3UB);
		yM1UB = Math.max(yM1UB, yM1Step4UB);
		return yM1UB;
	}

	private double[] getDBnd(long b, long u) {
		long b4 = b*b*b*b;
		double b8 = 1.0*b4*b4;
		double b36 = b8*b8*b8*b8*b4;
		long u4 = u*u*u*u;
		double u8 = 1.0*u4*u4;
		double u24 = u8*u8*u8;
		double dBnd = 300.0/u/u; // (5.13)
		int ineqUsed = 0;

		double dTemp1 = 7*Math.pow(1.0*b4/u8, 1.0/3); // (5.14)
		if (dTemp1 > dBnd) {
			dBnd = dTemp1;
		}

		double dTemp2 = 2.1*Math.sqrt(1.0*b*b/u/u); // (5.15)
		if (dTemp2 > dBnd) {
			dBnd = dTemp2;
		}

		// step 1 bound:
		double b56 = b36*b8*b8*b4;
		double u44 = u24*u8*u8*u4;
		double d1 = 0.88*Math.pow(b56/u44, 1.0/21);
		if (d1 > dBnd) {
			dBnd = d1;
			ineqUsed = 1;
		}

		// step 2 bound:
		double d2 = 0.64*Math.pow(b, 8.0/3)/u/u;
		if (d2 > dBnd) {
			dBnd = d2;
			ineqUsed = 2;
		}

		// step 3 bound
		double d3 = 60.0*Math.pow(b36/u24, 1.0/7);
		if (d3 > dBnd) {
			dBnd = d3;
			ineqUsed = 3;
		}

		// step 4 bound
		double d4 = 85.0*b4*b4/u4;
		if (d4 > dBnd) {
			dBnd = d4;
			ineqUsed = 5;
		}
		return new double[] {dBnd, d1,d2,d3,d4};
	}

	private boolean isSquare(long l) {
		if (l<0) return false;
		double sqrtD = Math.sqrt(l);
		long sqrtL = Math.round(sqrtD);
		return (sqrtL*sqrtL==l);
	}
}
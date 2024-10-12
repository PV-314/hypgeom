read("hypgeom\\general\\hypg-utils.gp");

\\ note this is for Prop 3.1 of the prime-power paper (hence the name).
\\ Based on b1-Prop41-sequence-proof-calcs.gp, which is based on Lemma41-sequence-proof-calcs.gp
\\ this is for checking the calculations and numerical values in the proof of Prop 3.1 (hence filename)
\\ 16 August 2023
bPP_check()={
	my(aLB,bLB,bLBEven,bLBOdd,bnd1,bnd2,bnd6,bnd7,bnd8,c0,c1,c2,c3,c42,cAct,
	cPolyMin,cUB,cUB1,cUB2,d,d4,dioLBConst,dLB,dLB_41,dUB,e2LB,eLB,eLBCnst,eLBDenom,eLBRecip,
	fk,fkEven,fl,flEven,gamma14LBConst,gamma34UBConst,gNd4Even,gNd4Min,gNd4Odd,gpLB,
	k0,l0UB,lhs1,lhs2,lhs3,lhs4,omega14UB,p,pRts,qBnd,qeUB,qLB,qrUB,qUBCnst,
	step2LBConst,step2UBConst,step2UBConsta,step3LHS1a,step3LHS2a,step4LBCnsta,step4LBCnstb,
	step4LBEvenCnsta,step4LBEvenCnstb,step4LBOddCnsta,step4LBOddCnstb,
	thUB,v1,v2,x1LBCnst,x1UB,x1LB2Cnst,x1LB3,x12LBCnst,
	y1LB,y1LB2,y1LBCnst,y1LBEvenDenom,y1LBOddDenom,y1UB2,
	y2UB1Cnst,y2UB1CnstWithC,y2UB1SqrCnst,y2UB2,y2UB2Cnst,y2UB2CnstWithC,yR0LBConst);

	\\ used in Step (ii) bSqr calcs that are actually done here in step (iv) first:
	gamma14LBConst=5/24; \\ from (2.3) in Lemma 2.3(b)
	gamma34UBConst=4/3; \\ from (2.3) in Lemma 2.3(b)
	yR0LBConst=1.072; \\ from Lemma 2.2(d)

	fk=4;     \\ max "constant" value in Prop 3.1
	fl=4;     \\ max "constant" value in Prop 3.1
	fkEven=2; \\ max "constant" value in Prop 3.1
	flEven=2; \\ max "constant" value in Prop 3.1
	
	c42=0.2; \\ from Lemma 2.3(a)
	d4=exp(1.68); \\ from Lemma 2.3(a)
	gNd4Even=2*sqrt(2);
	gNd4Odd=2;
	gNd4Min=min(gNd4Even,gNd4Odd);
	y1LBEvenDenom=256; \\ Lemma 2.1(a)
	y1LBOddDenom=16; \\ Lemma 2.1(a)
	k0=0.89;
	gpLB=15; \\ constant in the gap principle when -N_alpha=b is not a square
	thUB=0.6; \\ from Lemma 3.8(a)
	cAct=0.75; \\ the value of c (from the expression 1-c) that is used throughout proof of Prop 3.1
	
	\\aLB=-2201.8^55; \\ was 1. Now just a random number that hopefully breaks stuff (until fixed);
	bLBEven=2; \\ since b=1 done by Akhtari
	bLBOdd=3;
	bLB=min(bLBEven,bLBOdd);
	y1LB=4; \\=2^2 is the value with no assumptions like (4.1) on Y_1

	dLB=128;  \\ initial value
	eLB=1.13; \\ from b square paper
	qLB=217;  \\ from b square paper
	
	c0=2/y1LB; \\ c0 in the current gap principle proof
	c0=round_up(c0,1);
	printf("c0=%8.6f\n",c0);
	p=x^8-8*x^6+20*x^4-16*x^2+c0*c0;
	pRts=polrootsreal(p,[0,1]);
	if(length(pRts)!=1,
		print("ERROR: bad p=",p,", real roots are ",pRts);
		return();
	);
	c3=pRts[1]; \\ notation c3 is from Lemma 3.6(b) (lemma to prove gap principle)
	omega14UB=c3; \\ (2/y2LB/y2LB)^(1/4);
	omega14UB=round_up(omega14UB,3);
	printf("omega14 approximation UB=%8.6f (like eqn (3.31)\n",omega14UB);
	c1=omega14UB; \\0.16;
	c2=(2-c1*c1)*sqrt(4-c1*c1); \\ from Lemma 3.6(a)
	\\ 3 place in c2 gives 76.3 as the final constant in step 4:
	c2=round_down(c2,4);
	printf("c1=%8.6f, c2=%10.8f\n",c1,c2);
	
	print("\nx_k bounds:");
	x1LBCnst=(y1LB^2-1.0)/y1LB^2; \\ see equation {eq:25}
	x1LBCnst=round_down(x1LBCnst,4);
	printf("x_k^2>%12.11f*(a^2+b)*y_k^2\n",x1LBCnst);
	x1UBCnst=sqrt(1.0/x1LBCnst);
	x1UBCnst=round_up(x1UBCnst,3);
	printf("sqrt(x_k^2+b)<%8.6f*x_k\n",x1UBCnst);

	\\ E and Q calcs
	print("\nE and Q calcs:");
	eLBDenom=4*d4/2;
	eLBDenom=round_up(eLBDenom,4);
	printf("constant in E lb denom=%8.6f\n",eLBDenom);
	eLBCnst=(1+sqrt(x1LBCnst))/eLBDenom;
	eLBCnst=round_down(eLBCnst,4);
	printf("eLBCnst=%8.6f\n",eLBCnst);
	qUBCnst=d4*4; \\ in (4.9), the UB for Q
	qUBCnst=round_up(qUBCnst,4);
	printf("E geq %8.6f\n",eLB);
	printf("Q geq %8.6f\n",qLB);
	printf("constant in Q ub=%8.6f\n",qUBCnst);
	
	printf("recall k_0=%8.6f\n",k0);
	l0UB=c42*2.29;
	l0UB=round_up(l0UB,4);
	printf("l_0<%8.6f*sqrt(b)/x_k\n",l0UB);
	
	print("\nStep 1: Subsection 3.3");
	v1=qUBCnst/gNd4Min; \\ using v1 as we have 21.47/2, but in paper use 10.74
	v1=round_up(v1,6);
	printf("v1(temp)=%9.6f\n",v1);
	y2UB1Cnst=2*k0/c2;
	y2UB1Cnst=round_up(y2UB1Cnst,2);
	printf("y2UB1Cnst=%9.6f\n",y2UB1Cnst);
	y2UB1CnstWithC=round_up(y2UB1Cnst^4/(1-cAct)^4,3);
	printf("y2UB1CnstWithC=%9.6f (in eqn (3.10))\n",y2UB1CnstWithC);
	
	y2UB2Cnst=(y2UB1Cnst*v1)^4;
	y2UB2Cnst=round_up(y2UB2Cnst,3);
	y2UB2CnstWithC=y2UB1CnstWithC*v1^4;
	y2UB2CnstWithC=round_up(y2UB2CnstWithC,3); \\ we use 3 for precision, since with 4, we have y_l^3<139500.000000*(b*f_k*f_l)^2*y_k^5
	printf("y_l^3<%8.6f*(b*f_k*f_l)^2*y_k^5\n",y2UB2CnstWithC);
	
	y2UB2EvenCnst=(fkEven*flEven)^2*y2UB2CnstWithC; \\ replace f_k*f_ell
	y2UB2EvenCnst=ceil(y2UB2EvenCnst);
	printf("b even: y_l^3<%8.6f*b^2*y_k^5\n",y2UB2EvenCnst);
	
	cUB1=(y2UB2EvenCnst/gpLB^3)^(1/4)/dLB^(3/2);
	cUB1=floor(1/cUB1);
	printf("b even: y_k<b^2/%4d\n",cUB1);
	if(cUB1<y1LBEvenDenom,
		print("BAD: cUB1=",cUB1," must be bigger than ",y1LBEvenDenom);
		return();
	);
	
	y2UB2OddCnst=(fk*fl)^2*y2UB2CnstWithC; \\ replace f_k*f_ell
	y2UB2OddCnst=ceil(y2UB2OddCnst);
	printf("b odd : y_l^3<%8.6f*b^2*y_k^5\n",y2UB2OddCnst);

	cUB2=(y2UB2OddCnst/gpLB^3)^(1/4)/dLB^(3/2);
	cUB2=floor(1/cUB2);
	printf("b odd : y_k<b^2/%4d\n",cUB2);
	if(cUB2<y1LBOddDenom,
		print("BAD: cUB2=",cUB2," must be bigger than ",y1LBOddDenom);
		return();
	);

	print("\nStep 2: Subsection 3.4");
	dioLBConst=2/yR0LBConst*gamma14LBConst/gamma34UBConst;
	dioLBConst=round_down(dioLBConst,4);
	printf("dioLBConst(constant in lower bound for w^(1/4) approx)=%8.6f\n",dioLBConst);
	step2LBConst=c2*dioLBConst;
	step2LBConst=round_down(step2LBConst,4);
	printf("step2LBConst(constant in lower bound for 1/y_ell term)=%8.6f\n",step2LBConst);
	step2UBConst=2/step2LBConst;
	step2UBConst=round_up(step2UBConst,4);
	printf("%8.6f*r0^(1/2)*(4*(a*a+b)/b)^r0*y_k^(2r0+1) > y_ell\n",step2UBConst);
	step2UBConsta=4*step2UBConst;
	step2UBConsta=round_up(step2UBConsta,3);
	printf("for r_0=1: %8.6f*((a*a+b)/b)*y_k^3 > y_ell\n",step2UBConsta);
		
	print("\nStep 3: Subsection 3.6");
	\\ repeating step (iii) set-up from the bSqr script
	qBnd=(qLB-1)/qLB;
	qBnd=round_down(qBnd,3);
	printf("(Q-1)/(Q-1/E)>(Q-1)/Q>%8.6f\n",qBnd);
	bnd1=qBnd*sqrt(x1LBCnst)/l0UB;
	bnd1=round_down(bnd1,4);
	\\printf("(y_k*y_l)^(1/4)>%8.6f*c*sqrt(d)*y_k/sqrt(b*f_k*f_l)*(ELB)^(r0-1)\n",bnd1);
	bnd2=bnd1/eLBCnst;
	bnd2=round_down(bnd2,4);
	\\printf("y_l>(%8.6f/g/Nd4*sqrt(b/f_k/f_l))^4*stuff\n",bnd2);

	\\print("now apply upper bound for y_ell");
	step3LHS2a=qUBCnst^4/eLBCnst^12;
	step3LHS2a=sqrt(step3LHS2a);
	step3LHS2a=round_up(step3LHS2a,3);

	step3LHS1a=y2UB1Cnst^4/bnd2^12/cAct^12/(1-cAct)^4;
	step3LHS1a=step3LHS1a*step3LHS2a;
	step3LHS1a=round_up(step3LHS1a,2);
	printf("constant on LHS of (3.15)=%8.6e\n",step3LHS1a);
	printf("other constant on LHS of (3.15)=%8.6e\n",step3LHS2a);

	\\ constants for b an odd prime power:
	step3LB(fk,fl,gNd4Odd,step3LHS1a,step3LHS2a,bLBOdd,y1LBOddDenom,"b an odd prime power");

	\\ constants for b even, a square, p^m, 2p^m or 4p^m
	step3LB(fkEven,flEven,gNd4Even,step3LHS1a,step3LHS2a,bLBEven,y1LBEvenDenom,"b even=p^m, 2p^m, 4p^m, 8p^m or 16p^m");

	print("\nStep 4: Subsection 3.7");
	step4LBCnst=100;
	for(i=2,10,
		step4LBCnst=min(step4LBCnst,log(eLBCnst^(4*i)/sqrt(i))/4/i);
	);
	step4LBCnst=exp(step4LBCnst);
	step4LBCnst=round_down(step4LBCnst,5);
	\\printf("min of %8.6f^(4*r0)/r0^(1/2)>%8.6f^(4*r0)\n",eLBCnst,step4LBCnst);

	step4LBCnsta=step4LBCnst^4*bnd2^4*cAct^4/step2UBConst/4;
	step4LBCnsta=round_down(step4LBCnsta,4);
	printf("step4LBCnsta=    %8.6f\n",step4LBCnsta);

	step4LBCnstb=step4LBCnst^4/4;
	step4LBCnstb=round_down(step4LBCnstb,4);
	printf("step4LBCnstb=    %10.8f\n",step4LBCnstb);

	step4LBEvenCnsta=step4LBCnsta/(fkEven*flEven)^2;
	step4LBEvenCnsta=round_down(step4LBEvenCnsta,2);
	printf("step4LBEvenCnsta=%8.6f\n",step4LBEvenCnsta);

	step4LBEvenCnstb=step4LBCnstb*gNd4Even^4;
	step4LBEvenCnstb=round_down(step4LBEvenCnstb,2);
	printf("step4LBEvenCnstb=%8.6f\n",step4LBEvenCnstb);

	step4LBEvenCnstb=step4LBEvenCnsta*step4LBEvenCnstb;
	step4LBEvenCnstb=round_down(step4LBEvenCnstb,2);
	printf("step4LBEvenCnstb=%8.6f\n",step4LBEvenCnstb);

	step4LBEvenCnstb=step4LBEvenCnstb/y1LBEvenDenom^2;
	step4LBEvenCnstb=round_down(step4LBEvenCnstb,3);
	printf("step4LBEvenCnstb=%8.6e\n",step4LBEvenCnstb);

	step4LBOddCnsta=step4LBCnsta/(fk*fl)^2;
	step4LBOddCnsta=round_down(step4LBOddCnsta,2);
	printf("step4LBOddCnsta= %8.6f\n",step4LBOddCnsta);

	step4LBOddCnstb=step4LBCnstb*gNd4Odd^4;
	step4LBOddCnstb=round_down(step4LBOddCnstb,2);
	printf("step4LBOddCnstb= %8.6f\n",step4LBOddCnstb);

	step4LBOddCnstb=step4LBOddCnsta*step4LBOddCnstb;
	step4LBOddCnstb=round_down(step4LBOddCnstb,2);
	printf("step4LBOddCnstb= %10.8f\n",step4LBOddCnstb);

	step4LBOddCnstb=step4LBOddCnstb/y1LBOddDenom^2;
	step4LBOddCnstb=round_down(step4LBOddCnstb,3);
	printf("step4LBOddCnstb= %8.6e\n",step4LBOddCnstb);

	print("\nLarge y_k: Subsection 3.8");
	step5YLBCnst=1800; \\ from (3.20)
	step5XLBCnst=step5YLBCnst^2*x1LBCnst;
	step5XLBCnst=round_down(step5XLBCnst,1);
	step5XLBCnst=floor(step5XLBCnst);
	printf("x_k^2>%6d*(a^2+b)*b^3\n",step5XLBCnst);
	
	bigESqrLB=64*step5XLBCnst/16/d4^2;
	bigESqrLB=round_down(bigESqrLB,2);
	bigESqrLB=floor(bigESqrLB);
	printf("E^2>%5d*b\n",bigESqrLB);
	
	qeUBConsta = qUBCnst/gNd4Min;
	qeUBConsta=round_up(qeUBConsta,4);
	qeUBConstb= eLBCnst*gNd4Min;
	qeUBConstb=round_down(qeUBConstb,3);
	qeUBConstc=qeUBConsta/qeUBConstb;
	qeUBConstc=round_up(qeUBConstc,3);
	printf("Q/E < (%8.6f*sqrt(a*a+b)*yk)*b/(%8.6f*sqrt(a*a+b)*yk) < %8.6f*b\n",qeUBConsta,qeUBConstb,qeUBConstc);
	
	qR0UBConsta=qLB/(qLB-1)/cAct*l0UB;
	qR0UBConsta=round_up(qR0UBConsta,3);
	printf("Q^(r0-2) < E^(-3)*(%8.6f*stuff)^3\n",qR0UBConsta);
	
	step5DioLBCnsta=c2*(1-cAct)/k0;
	step5DioLBCnsta=round_down(step5DioLBCnsta,3);
	printf("diophantine constant(1)=%8.6f\n",step5DioLBCnsta);

	step5DioLBCnstb=step5DioLBCnsta/qeUBConstc^3/qR0UBConsta^3;
	step5DioLBCnstb=round_down(step5DioLBCnstb,2);
	printf("diophantine constant(2)=%8.6f\n",step5DioLBCnstb);

	step5Cnsta=(2/step5DioLBCnstb)^2;
	step5Cnsta=round_up(step5Cnsta,3);
	printf("%8.6e*(fk*fEll)^4*b^10*yk^2>...\n",step5Cnsta);

	step5Cnstb=step5Cnsta*(fk*fl)^4/x1LBCnst^3;
	step5Cnstb=round_up(step5Cnstb,1);
	step5Cnstc=step5Cnstb^(1/4);
	step5Cnstc=round_up(step5Cnstc,2);
	printf("%8.6f^4*b^6>%8.6e*b^10/(a*a+b)^4>...\n",step5Cnstc,step5Cnstb);
	
	print("use bPP-end-proof-check.gp for rest of proof");
}

\\ this works if y_k>b^2/y1LBDenom
step3LB(fk,fl,gnV,step3LHS1a,step3LHS2a,bLB,y1LBDenom,msg)={
	my(dLBa,dLBb,step3LHS1b,step3LHS2b);
	
	step3LHS1b=step3LHS1a*gnV^4*(fk*fl)^8;
	step3LHS1b=round_up(step3LHS1b,3);
	step3LHS2b=step3LHS2a/gnV^8;
	step3LHS2b=round_up(step3LHS2b,3);
	\\print("step3LHS1a=",step3LHS1a);
	\\print("step3LHS2a=",step3LHS2a);
	\\print("fk=",fk);
	\\print("fl=",fl);
	\\print("gnV=",gnV);
	\\print("y1LB=",y1LB);
	\\print("y1LBDenom=",y1LBDenom);
	printf("\n%s lhs cnst1=%8.6e, lhs cnst2=%8.4e\n",msg,step3LHS1b,step3LHS2b);
	
	dLBa=step3LHS1b;
	printf("%s for (a^2+b)^2>%6.0f, the LHS is <1\n",msg,dLBa);
	dLBa=sqrt(step3LHS1b);
	dLBa=round_up(dLBa,3);
	printf("%s for a^2+b>%6.0f, the LHS is <1\n",msg,dLBa);

	dLBb=step3LHS2b*y1LBDenom^4;
	dLBb=round_up(dLBb,3);
	printf("RHS constant=%9.6e\n",dLBb);
	\\dLBb=dLBb/bLB^2;
	\\dLBb=round_up(dLBb,3);
	\\printf("in square root=%9.6e\n",dLBb);
	dLBb=sqrt(dLBb);
	dLBb=round_up(dLBb,5);
	printf("%s for b(a^2+b)>%6.0f, the RHS is >1\n",msg,dLBb);
}
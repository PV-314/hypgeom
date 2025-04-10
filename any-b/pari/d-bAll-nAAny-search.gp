read("..\..\general\hypg-utils.gp");

\\ use this function
\\ output values of d (and the associated Magma commands) for all the values
\\ outstanding from the proof of the different values of r_0
\\ 25 Oct 2024
d_searchAny(b,uLB=1,dbg=0)={
	my(c,d,dUB,dUB1,dUB2,starttime,tLB,tMod,tUB,uStarttime,uUB);

	c=[0,0];
	uUB=21;
	dUB=get_dBnd(b,uUB+1);
	while(dUB>1.9999,
		uUB=uUB+1;
		dUB=get_dBnd(b,uUB+1);
	);
	dUB1=get_dBnd(b,1,1);
	dUB2=get_dBnd(b,2);
	printf("dUB(u=%2d)=%9.6f, dUB(u=1)=%10d=%9.6e, dUB(u=2)=%9.6e\n",uUB+1,dUB,dUB1,dUB1,dUB2);
	starttime=getwalltime();

	for(u=uLB,uUB,
		uStarttime=getwalltime();
		dUB=get_dBnd(b,u);
		tUB=sqrt(u*u*dUB+4);
		tMod=floor(tUB/100);
		tMod=max(100,tMod);
		if(dbg!=0,print("for b=",b,", u=",u,", tUB=",tUB));
		tLB=1;
		\\if(u==1,
		\\	tLB=133308;
		\\);
		for(t=tLB,tUB,
			if(dbg!=0,print("for u=",u,", starting t=",t));
			d=t*t+4;
			if(d%(u*u)==0,
				d=d/u/u;
				c=c+do_bdtu_work(b,d,t,u,dbg);
			);
			\\if(dbg!=0 && d%2000==0,printf("d=%11d, c1=%8d, c2=%6d, total time=%8d(ms)=%s\n",d,c[1],c[2],getwalltime()-starttime,strtime(getwalltime()-starttime)));
			d=t*t-4;
			if(d>0 && d%(u*u)==0,
				d=d/u/u;
				c=c+do_bdtu_work(b,d,t,u,dbg);
			);
			if(t%tMod==0,printf("b=%2d, t=%6d (u=%3d is %5.2f percent done), d=%11d, c1=%10d, c2=%4d, total time=%9d(ms)=%s\n",b,t,u,(100.0*t/tUB),floor((t*t+4)/u/u),c[1],c[2],getwalltime()-starttime,strtime(getwalltime()-starttime)));
		);
		print("done b=",b,", u=",u,": total found ",c," equations. uTime=",(getwalltime()-uStarttime),"=",strtime(getwalltime()-uStarttime),". totalTime=",(getwalltime()-starttime),"=",strtime(getwalltime()-starttime));
	);
}

\\ returns [c1,c2], where
\\ c1=the number of values, a, found with N_a=a^2-db^4<0 for b and d (for logging)
\\ c2=the number of equations to try in Magma
\\ 25 Oct 2024
do_bdtu_work(b,d,t,u,dbg=0)={
	my(aLB,aUB,b4,c1,c2,dBnd,e,nrmA);

	b4=b*b*b*b;
	c1=0; \\ c for count
	c2=0; \\ c for count
	e=(t+u*sqrt(d))/2;
	dBnd=get_dBnd(b,u,dbg);
	if(d<=dBnd,
		aLB=get_aLB(b,d,u,dbg);
		aUB=sqrt(d*b4);
		if(dbg!=0 && aLB>1,
			printf("for b=%2d, d=%5d, t=%4d, u=%2d: dBnd=%5d, aLB=%5d, aUB=%9.6f\n",b,d,t,u,dBnd,aLB,aUB);
		);
		ykUB=get_yM1UB(aLB,b,d,t,u,dbg);
		if(dbg!=0,printf("for b=%2d, d=%5d, t=%4d, u=%2d: dBnd=%5d, aLB=%5d, aUB=%9.6f, ykUB=%9.6f\n",b,d,t,u,dBnd,aLB,aUB,ykUB));
		for(a=aLB,aUB,
			nrmA=a*a-d*b4;
			if(nrmA<0,
				c1=c1+1;
				c2=c2+do_abdtu_work(a,b,d,t,u,ykUB,dbg);
			);
		);
		if(dbg!=0 && d%100==0,printf("d=%6d, aLB=%6d, aUB=%6d, c=%4d\n",d,aLB,aUB,[c1,c2]));
	);
	return([c1,c2]);
}

\\ returns 1 if further checking of the sequence associated with the arguments to function is needed
\\ returns 0 otherwise
\\ note that we do not use the lower bound for y_k from (4.4)
\\ pulled out (from 9 Dec 2024 version) and reinstated on 17 Jan 2025
do_abdtu_work(a,b,d,t,u,ykUB,dbg=0)={
	my(bigK,c2,isChecked,nrmA,k,yCurr,ykLB,yPrev,yT);
	
	nrmA=a*a-d*b*b*b*b;	
	c2=0;
	isChecked=0;

	\\ check positive-indexed elements
	yPrev=b*b;
	yCurr=(b*b*(t*t+d*u*u)+2*a*t*u)/4;
	k=1;
	while(isChecked==0 && yCurr<ykUB,
		if(dbg!=0,
			printf("do_abdtu_work(): d=%8d, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d\n",d,a,b,t,u,k,yCurr);
		);
		\\ recall that m_1 \geq 3 for the positively-indexed elements
		if(k>2 && issquare(yCurr), \\  && yCurr>ykLB,
			printf("adding d=%8d, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d\n",d,a,b,t,u,k,yCurr);
			isChecked=1;
		);
		yT=(t*t+d*u*u)*yCurr/2-yPrev;
		yPrev=yCurr;
		yCurr=yT;
		k=k+1;
	);

	\\ check negative-indexed elements
	if(isChecked==0,
		yPrev=b*b;
		yCurr=(b*b*(t*t+d*u*u)-2*a*t*u)/4;
		k=-1;
		bigK=0;
		while(isChecked==0 && yCurr<ykUB,
			if(bigK==0 && yCurr>b*b,
				bigK=k;
			);
			if(dbg!=0,
				printf("do_abdtu_work(): d=%8d, a=%6d, b=%3d, t=%6d, u=%3d, K=%2d, k=%2d, yCurr=%8d\n",d,a,b,t,u,bigK,k,yCurr);
			);
			\\ recall that m_1 \leq K-2 for the negatively-indexed elements
			if(bigK!=0 && k<bigK-1 && issquare(yCurr),
				printf("adding d=%8d, a=%6d, b=%3d, t=%6d, u=%3d, K=%2d, k=%2d, yCurr=%8d\n",d,a,b,t,u,bigK,k,yCurr);
				isChecked=1;
			);
			yT=(t*t+d*u*u)*yCurr/2-yPrev;
			yPrev=yCurr;
			yCurr=yT;
			k=k-1;
		);
	);
	if(isChecked!=0,
		print("d:=",d,";nrmA:=",nrmA,";s:=IntegralQuarticPoints([d,0,0,0,nrmA]);printf \"d=%o, nrmA=%o, number=%o, solns=%o\\n\",d, nrmA, #s, s;");
		c2=c2+1;
	);
	return(c2);
}

\\ upper bound comes from (4.15), (4.17), (4.20) and (4.22) -- the four main steps of the technique
\\ 14 March 2025 (pulled out)
get_yM1UB(a,b,d,t,u,dbg=0)={
	my(gnd4Value,nrmA,sqrtNA,yM1Step1UB,yM1Step2UB,yM1Step3UB,yM1Step3UBBase,yM1Step3UBRem,
	yM1Step4UB,yM1Step4UBBase,yM1Step4UBRem,yM1UB);

	nrmA=a*a-d*b*b*b*b;	
	d34=sqrt(sqrt(d*d*d));
	
	\\ the simplified bounds for steps 1 and 2 reduce the time by over half
	\\ from equation (4.15). Note that 42/55=0.763..., so the exponent 3/4 on d in denom is a bit smaller (and hence yM1Step1UB is a bit bigger than required)
	yM1Step1UB=2.7*b*b*abs(nrmA)*abs(nrmA)/d34;
	
	\\ from equation (4.17):
	\\ nrmA^2>|nrmA|^(24/13),
	\\ d exponent: 10/13=0.7692...>3/4
	yM1Step2UB=yM1Step1UB;
	\\ the following comes from b^(28/13)=b^2*b^(2/13) and b^(2/13)<2.7/1.24 for b \leq 157
	if(b>157,
		yM1Step2UB=yM1Step2UB*b^(2/13)/2.7*1.24;
	);
		
	
	sqrtNA=sqrt(abs(nrmA));
	gnd4Value=2; \\ 1/(gnd4)^(2-1/(2*r-1)) \leq 1/2^(2-1/(2*r-1))
	\\ from equation (4.20)
	yM1Step3UBBase=59.2*sqrtNA*sqrtNA*sqrtNA/sqrt(d)/gnd4Value/gnd4Value;
	\\ r_0=2 value: exponent=1/(2*r_0-1)=1/3.
	\\ if 67.1*...>1, then the max contribution comes from (67.1*...)^(1/3)
	\\ if 67.1*... \leq 1, then as r_0->+infty, the rem^(1/(2*r_0-1)) term approaches 1 from below
	yM1Step3UBRem=max(1,67.1*sqrtNA*sqrtNA*sqrtNA*sqrtNA*sqrtNA*b*b*b*b*b*b*b*gnd4Value/d);
	yM1Step3UB=yM1Step3UBBase*yM1Step3UBRem^(1/3); \\ r_0=2 value
	
	\\ from equation (4.22)
	yM1Step4UBBase=65.32*sqrtNA*sqrtNA*sqrtNA/sqrt(d)/gnd4Value/gnd4Value;
	\\ r_0=2 value: exponent=1/2/(r_0-1)=1/2.
	\\ if 422*...>1, then the max contribution comes from (422*...)^(1/2)
	\\ if 422*... \leq 1, then as r_0->+infty, the rem^(1/2/(r_0-1)) term approaches 1 from below
	yM1Step4UBRem=max(1,422*abs(nrmA*nrmA*nrmA)*b*b/d);
	yM1Step4UB=yM1Step4UBBase*sqrt(yM1Step4UBRem);

	yM1UB=max(yM1Step1UB,yM1Step2UB);
	yM1UB=max(yM1UB,yM1Step3UB);
	yM1UB=max(yM1UB,yM1Step4UB);
	return(yM1UB);
}

\\ pulled out of function above, using the N_a-based bounds for d
\\ 10 Dec 2024
get_aLB(b,d,u,dbg=0)={
	my(a2LB,aLB,b4,ineqUsed);
	
	b4=b*b*b*b;
	aLB=1;
	ineqUsed=0;
	\\ from (4.28) - the second term in the max in the gap principle lemma
	\\a2LB=d*b4-(3*d^4*u^6/320/b^6)^(1/3);
	a2LB=d*b4-(3*d/320.0)^(1/3)*d*u*u/b/b;
	if(a2LB>aLB*aLB,
		aLB=floor(sqrt(a2LB));
		ineqUsed=1;
	);

	\\ from r_0=1, p/q \neq stuff: commented out on 16 March 2025, as d*b4-(d^152*u^330/4.6^152/b^210)^(1/45)>0 can never occur)
	\\a2LB=d*b4-(d^152*u^330/4.6^152/b^210)^(1/45);
	\\if(a2LB>aLB*aLB,
	\\	aLB=floor(sqrt(a2LB));
	\\	ineqUsed=2;
	\\);

	\\ from r_0=1, p/q=stuff: commented out on 16 March 2025 for above reason
	\\a2LB=d*b4-(d^36*u^78/3.46^36/b^54)^(1/11);
	\\if(a2LB>aLB*aLB,
	\\	aLB=floor(sqrt(a2LB));
	\\	ineqUsed=3;
		\\1/0;
	\\);

	\\ from r_0>1, p/q \neq stuff: commented out on 16 March 2025 for above reason
	\\a2LB=d*b4-(d^17*u^36/15^17/b^26)^(1/8);
	\\if(a2LB>aLB*aLB,
	\\	aLB=floor(sqrt(a2LB));
	\\	ineqUsed=4;
		\\1/0;
	\\);

	\\ from r_0>1, p/q=stuff: commented out on 16 March 2025 for above reason
	\\a2LB=d*b4-sqrt(d^3*u^6/4.5^3/b^4);
	\\if(a2LB>aLB*aLB,
	\\	aLB=floor(sqrt(a2LB));
	\\	ineqUsed=5;
		\\1/0;
	\\);
	
	if(ineqUsed!=1 && t%101==0, \\ dbg!=0,
		printf("in get_aLB(): for b=%2d, d=%8d, u=%3d, used inequality %2d to obtain aLB=%10d, sqrt(d*b^4)=%9.6f\n\n\n",b,d,u,ineqUsed,aLB,sqrt(d*b4));
	);
	return(aLB);
}

\\ adding logging to log which inequality is used to get the max
\\ 25 Oct 2024
get_dBnd(b,u,dbg=0)={
	my(b4,dBnd,dBndTemp,ineqUsed);
	
	\\dbg=0;
	b4=b*b*b*b;
	dBnd=(10000.0*b4/u^12)^(1/5); \\ (5.10)
	ineqUsed=1;
	
	dBndTemp=9.47*b^18/u^6; \\ Lemma 5.1 LB
	\\ d LB hypothesis in Lemma 5.1
	if(dBndTemp<202,
		dBndTemp=320/3*dBndTemp/9.47;
	);
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=2;
	);
	
	dBndTemp=8.8*b^(390.0/107)/u^(330.0/107); \\ Subsection 5.1
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=3;
	);
	dBndTemp=6*b^(98.0/25)/u^(78.0/25); \\ Subsection 5.2
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=4;
	);
	dBndTemp=167.0*(b^58/u^36)^(1/9); \\ Subsection 5.3
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=5;
	);
	dBndTemp=92.0*(b*b/u)^6; \\ Subsection 5.4
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=6;
	);
	if(t%101==0,
		\\printf("in get_dBnd(): for u=%3d, used inequality %2d to obtain dBnd=%10d\n",u,ineqUsed,dBnd);
	);
	return(dBnd);
}

\\ from Table 2 in paper before 16 March 2025
\\ 16 March 2025
test_prev_values()={
	my(a,b,d,t,u);

	a=40;b=1;d=1940;t=44;u=1;
	print("\ntesting a=",a,", b=",b,", d=",d,", t=",t,", u=",u);
	do_bdtu_work(b,d,t,u,1);
	
	a=1;b=1;d=2;t=2;u=2;
	print("\ntesting a=",a,", b=",b,", d=",d,", t=",t,", u=",u);
	do_bdtu_work(b,d,t,u,1);
	
	a=8;b=2;d=5;t=1;u=1;
	print("\ntesting a=",a,", b=",b,", d=",d,", t=",t,", u=",u);
	do_bdtu_work(b,d,t,u,1);
	
	a=25;b=3;d=8;t=2;u=1;
	print("\ntesting a=",a,", b=",b,", d=",d,", t=",t,", u=",u);
	do_bdtu_work(b,d,t,u,1);
}
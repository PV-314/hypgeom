read("..\\..\\general\\hypg-utils.gp");

\\ output values of d (and the associated Magma commands) for all the values
\\ outstanding from the proof of the different values of r_0

d_search(b,uLB=1,dbg=0)={
	my(c,d,dUB,dUB1,dUB2,starttime,tMod,tUB,uStarttime,uUB);

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
		for(t=1,tUB,
			if(dbg!=0,print("for u=",u,", starting t=",t));
			d=t*t+4;
			if(d%(u*u)==0,
				d=d/u/u;
				c=c+do_d_u_work(b,d,t,u,dbg);
			);
			if(dbg!=0 && d%2000==0,printf("d=%10d, c1=%8d, c2=%6d, total time=%8d(ms)=%s\n",d,c[1],c[2],getwalltime()-starttime,strtime(getwalltime()-starttime)));
			d=t*t-4;
			if(d>0 && d%(u*u)==0,
				d=d/u/u;
				c=c+do_d_u_work(b,d,t,u,dbg);
			);
			if(t%tMod==0,printf("b=%2d, t=%6d (u=%3d is %5.2f percent done), d=%10d, c1=%8d, c2=%6d, total time=%8d(ms)=%s\n",b,t,u,(100.0*t/tUB),floor((t*t+4)/u/u),c[1],c[2],getwalltime()-starttime,strtime(getwalltime()-starttime)));
		);
		print("done b=",b,", u=",u,": total found ",c," equations. uTime=",(getwalltime()-uStarttime),"=",strtime(getwalltime()-uStarttime),". totalTime=",(getwalltime()-starttime),"=",strtime(getwalltime()-starttime));
	);
}

\\ returns [c1,c2], where
\\ c1=the number of values, a, found with N_a=a^2-db^4<0 for b and d (for logging)
\\ c2=the number of equations to try in Magma
do_d_u_work(b,d,t,u,dbg=0)={
	my(aLB,aUB,b4,c1,c2,dBnd,dBndR01,e,nrmA);

	b4=b*b*b*b;
	c1=0; \\ c for count
	c2=0; \\ c for count
	e=(t+u*sqrt(d))/2;
	dBnd=get_dBnd(b,u);
	dBndR01=get_dBnd_r0_1(b,u);
	if(d<=dBnd,
		aLB=get_aLB(b,d,u);
		aUB=sqrt(d*b*b*b*b);
		for(a=aLB,aUB,
			nrmA=a*a-d*b4;
			if(nrmA<0,
				c1=c1+1;
				c2=c2+do_a_b_d_t_u_work(a,b,d,nrmA,t,u,dbg);
			);
		);
		if(dbg!=0 && d%100==0,printf("d=%6d, aLB=%6d, aUB=%6d, c=%4d\n",d,aLB,aUB,[c1,c2]));
	);
	return([c1,c2]);
}

\\ returns 1 if further checking of the sequence associated with the arguments to function is needed
\\ returns 0 otherwise
\\ pulled out (from 9 Dec 2024 version) and reinstated on 17 Jan 2025
do_a_b_d_t_u_work(a,b,d,nrmA,t,u,dbg=0)={
	my(bigK,c2,dBndR01,isChecked,k,yCurr,ykLB,ykUB,yM1Step1UB,yM1Step2UB,yPrev,yT);
	
	c2=0;
	isChecked=0;
	dBndR01=get_dBnd_r0_1_with_a_and_d(a,b,d,u);

	\\ from equation (4.13) (just before (AS-3a)
	yM1Step1UB=2.7*(b*abs(nrmA))^(20.0/11)/d^(42.0/55);
	\\ from equation (4.15) (just before (AS-4a)
	yM1Step2UB=1.234*abs(nrmA)^(24.0/13)*b^(28.0/13)/d^(10.0/13);
	yPrev=b*b;
	yCurr=(b*b*(t*t+d*u*u)+2*a*t*u)/4;
	for(k=2,6,
		yT=(t*t+d*u*u)*yCurr/2-yPrev;
		yPrev=yCurr;
		yCurr=yT;
		if(issquare(yCurr) && yCurr<yM1Step1UB,
			printf("adding r0=1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d, yM1Step1UB=%9.6f\n",d,dBndR01,a,b,t,u,k,yCurr,yM1Step1UB);
			isChecked=1;
		);
		if(issquare(yCurr) && isChecked==0 && yCurr<yM1Step2UB,
			printf("adding r0=1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d, yM1Step2UB=%9.6f\n",d,dBndR01,a,b,t,u,k,yCurr,yM1Step2UB);
			isChecked=1;
		);
	);
	k=6;
	if(isChecked==0 && yCurr<yM1Step1UB,
		printf("adding r0=1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d, yM1Step1UB=%9.6f\n",d,dBndR01,a,b,t,u,k,yCurr,yM1Step1UB);
		isChecked=1;
	);
	if(isChecked==0 && yCurr<yM1Step2UB,
		printf("adding r0=1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d, yM1Step2UB=%9.6f\n",d,dBndR01,a,b,t,u,k,yCurr,yM1Step2UB);
		isChecked=1;
	);

	\\ check negative-indexed elements
	if(isChecked==0,
		yPrev=b*b;
		yCurr=(b*b*(t*t+d*u*u)-2*a*t*u)/4;
		k=-1;
		bigK=0;
		while(bigK==0 || k>bigK-2,
			if(bigK==0 && yCurr>b*b,
				bigK=k;
			);
			yT=(t*t+d*u*u)*yCurr/2-yPrev;
			yPrev=yCurr;
			yCurr=yT;
			k=k-1;
		);
		if(yCurr<yM1Step1UB,
			printf("adding r0=1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, K=%2d, k=%2d, yCurr=%8d\n",d,dBndR01,a,b,t,u,bigK,k,yCurr);
			isChecked=1;
		);
		if(isChecked==0 && yCurr<yM1Step2UB,
			printf("adding r0=1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d\n",d,dBndR01,a,b,t,u,k,yCurr);
			isChecked=1;
		);
	);

	if(isChecked==0 && d>dBndR01,
		ykLB=4*sqrt(abs(nrmA)/d);
		ykUB=1350*b*b*sqrt(abs(nrmA)^7/d);
		yPrev=b*b;
		yCurr=(b*b*(t*t+d*u*u)+2*a*t*u)/4;
		k=1;
		while(yCurr<ykUB,
			\\ recall that m_1 \geq 3 for the positively-indexed elements
			if(k>2 && issquare(yCurr) && yCurr>ykLB,
				printf("adding r0>1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d\n",d,dBndR01,a,b,t,u,k,yCurr);
				isChecked=1;
			);
			yT=(t*t+d*u*u)*yCurr/2-yPrev;
			yPrev=yCurr;
			yCurr=yT;
			k=k+1;
		);
		yPrev=b*b;
		yCurr=(b*b*(t*t+d*u*u)-2*a*t*u)/4;
		k=-1;
		bigK=0;
		while(yCurr<ykUB,
			if(bigK==0 && yCurr>b*b,
				bigK=k;
			);
			\\ recall that m_1 \leq K-2 for the negatively-indexed elements
			if(bigK!=0 && k<bigK-1 && issquare(yCurr) && yCurr>ykLB,
				printf("adding r0>1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, K=%2d, k=%2d, yCurr=%8d\n",d,dBndR01,a,b,t,u,bigK,k,yCurr);
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

\\ pulled out of function above
\\ 10 Dec 2024
get_aLB(b,d,u)={
	my(a2LB,aLB);
	
	aLB=1;
	\\ from (4.28) - the second term in the max in the gap principle lemma
	a2LB=d*b^4-(3*d^4*u^6/320/b^6)^(1/3);
	if(a2LB>aLB*aLB,
		aLB=floor(sqrt(a2LB));
	);

	\\ from r_0=1, p/q \neq stuff, (AS-3a):
	a2LB=d*b^4-(d^152*u^330/4.6^152/b^210)^(1/45);
	if(a2LB>aLB*aLB,
		aLB=floor(sqrt(a2LB));
	);

	\\ from r_0=1, p/q=stuff, (AS-4a):
	a2LB=d*b^4-(d^36*u^78/3.45^36/b^54)^(1/11);
	if(a2LB>aLB*aLB,
		aLB=floor(sqrt(a2LB));
	);

	\\ from r_0>1, p/q \neq stuff, (AS-5a):
	a2LB=d*b^4-(d^17*u^36/15^17/b^20)^(1/8);
	if(a2LB>aLB*aLB,
		aLB=floor(sqrt(a2LB));
	);

	\\ from r_0>1, p/q=stuff, (AS-6a):
	a2LB=d*b^4-sqrt(d^3*u^6/14^3/b^4);
	if(a2LB>aLB*aLB,
		aLB=floor(sqrt(a2LB));
	);
	return(aLB);
}

\\ adding logging to log which inequality is used to get the max
\\ 25 Oct 2024
get_dBnd(b,u,dbg=0)={
	my(b4,dBnd,dBndTemp,ineqUsed);
	
	b4=b*b*b*b;
	dBnd=(10000.0*b4/u^12)^(1/5); \\ (4.28)
	ineqUsed=1;
	dBndTemp=9.48*b^18/u^6; \\ (4.30) 1/60 value
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=2;
	);
	dBndTemp=8.74*b^(390.0/107)/u^(330.0/107); \\ (AS-3b)
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=3;
	);
	dBndTemp=5.95*b^(98.0/25)/u^(78.0/25); \\ (AS-4b)
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=4;
	);
	dBndTemp=167.0*(b^52/u^36)^(1/9); \\ (AS-5b)
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=5;
	);
	dBndTemp=3375.0*(b*b/u)^6; \\ (AS-6b)
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=6;
	);
	if(dbg!=0,
		printf("for u=%3d, used inequality %2d to obtain dBnd=%10d\n",u,ineqUsed,dBnd);
	);
	return(dBnd);
}

\\ the lower bound for d when r_0=1
\\ including the initial assumptions
\\ 25 Oct 2024
get_dBnd_r0_1(b,u)={
	my(b4,dBnd);
	
	b4=b*b*b*b;
	dBnd=(10000.0*b4/u^12)^(1/5); \\ (4.27)
	dBnd=max(dBnd,((320/3)*b^18/u^6)); \\ (4.29)
	dBnd=max(dBnd,8.74*b^(390.0/107)/u^(330.0/107)); \\ (AS-3b)
	dBnd=max(dBnd,5.95*b^(98.0/25)/u^(78.0/25)); \\ (AS-4b)
	return(dBnd);
}

\\ the lower bound for d when r_0=1
\\ including the initial assumptions
\\ 25 Oct 2024
get_dBnd_r0_1_with_a_and_d(a,b,d,u)={
	my(absNrmA,b4,dBnd);
	
	b4=b*b*b*b;
	absNrmA=d*b4-a*a;
	dBnd=(10000.0*b4/u^12)^(1/5); \\ (4.27)
	dBnd=max(dBnd,3.22*absNrmA^(3/4)*b^(3/2)/u^(3/2)); \\ (4.28) 1/60 value

	dBnd=max(dBnd,4.6*absNrmA^(45.0/152)*b^(105.0/76)/u^(165.0/76)); \\ (AS-3a)
	dBnd=max(dBnd,3.45*absNrmA^(11.0/36)*b^(3/2)/u^(13.0/6)); \\ (AS-4a)
	return(dBnd);
}
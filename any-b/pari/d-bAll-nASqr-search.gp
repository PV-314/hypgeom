\\ \r C:\MyStuff\TeXFiles\mypapers\Hypergeometric\My-Yuan-Zhang-Extension\pari\any-b\d-bAll-nASqr-search.gp
\\ was d-b2-search.gp

read("C:\\MyStuff\\TexFiles\\mypapers\\Hypergeometric\\My-Yuan-Zhang-Extension\\pari\\hypg-utils.gp");

\\ use this function
\\ output values of d (and the associated Magma commands) for all the values
\\ outstanding from the proof of the different values of r_0

\\ based on d_b2_search1_20240420() below, but with the inequalities updated
\\ d=230000, c=2941
\\ 2941
\\ 23 Sept 2024
d_searchSqr(b,uLB=1,dbg=0)={
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
				c=c+do_d_u_work(b,d,t,u,dbg);
			);
			\\if(dbg!=0 && d%2000==0,printf("d=%11d, c1=%8d, c2=%6d, total time=%8d(ms)=%s\n",d,c[1],c[2],getwalltime()-starttime,strtime(getwalltime()-starttime)));
			d=t*t-4;
			if(d>0 && d%(u*u)==0,
				d=d/u/u;
				c=c+do_d_u_work(b,d,t,u,dbg);
			);
			if(t%tMod==0,printf("b=%2d, t=%6d (u=%3d is %5.2f percent done), d=%11d, c1=%8d, c2=%6d, total time=%8d(ms)=%s\n",b,t,u,(100.0*t/tUB),floor((t*t+4)/u/u),c[1],c[2],getwalltime()-starttime,strtime(getwalltime()-starttime)));
		);
		print("done b=",b,", u=",u,": total found ",c," equations. uTime=",(getwalltime()-uStarttime),"=",strtime(getwalltime()-uStarttime),". totalTime=",(getwalltime()-starttime),"=",strtime(getwalltime()-starttime));
	);
}

\\ t was just for logging, now (6 Oct 2024) for calculating the y_k's too
\\ returns [c1,c2], where
\\ c1=the number of values, a, found with -N_a=db^4-a^2 a perfect square for b and d (for logging)
\\ c2=the number of equations to try in Magma
\\ 24 Sept 2024
do_d_u_work(b,d,t,u,dbg=0)={
	my(aLB,aUB,b4,c1,c2,dBnd,e,nrmA);

	b4=b*b*b*b;
	c1=0; \\ c for count
	c2=0; \\ c for count
	e=(t+u*sqrt(d))/2;
	dBnd=get_dBnd(b,u);
	\\if(dbg!=0 && d==1153,printf("d=%6d, t=%6d, u=%4d, dBnd=%6d, c1=%4d, c2=%4d\n",d,t,u,dBnd,c1,c2));
	if(dbg!=0 && t==2,print("for d=",d,", t=",t,", u=",u,", dBnd=",dBnd));
	if(dbg!=0 && t==18,print("for t=18, dBnd=",dBnd));
	if(d<=dBnd,
		aLB=get_aLB(b,d,u);
		aUB=sqrt(d*b4);
		if(dbg!=0 && d%100==0,printf("d=%6d, aLB=%6d, aUB=%6d\n",d,aLB,aUB));
		for(a=aLB,aUB,
			nrmA=a*a-d*b4;
			if(nrmA<0 && issquare(-nrmA),
				c1=c1+1;
				c2=c2+do_a_b_d_t_u_work(a,b,d,nrmA,t,u,dbg);
			);
		);
	);
	return([c1,c2]);
}

\\ returns 1 if further checking of the sequence associated with the arguments to function is needed
\\ returns 0 otherwise
\\ pulled out on 24 Jan 2025
do_a_b_d_t_u_work(a,b,d,nrmA,t,u,dbg=0)={
	my(bigK,c2,dBndR01,isChecked,k,yCurr,ykLB,ykUB,yM1Step1UB,yM1Step2UB,yPrev,yT);
	
	c2=0;
	isChecked=0;
	dBndR01=get_dBnd_r0_1_with_a_and_d(a,b,d,u);
	\\ from equation (4.17) (just before (C-3a)
	yM1Step1UB=0.19*(b*b*abs(nrmA))^(13.0/11)/d^(12.0/11);
	\\ from equation (4.19) (just before (C-4a)
	yM1Step2UB=(abs(nrmA)/d)^(7.0/6)*b^(8.0/3)/10.0;
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
		while(bigK==0 || k>bigK-1,
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
		ykUB=84*b*b*sqrt(abs(nrmA)^5/d);
		yPrev=b*b;
		yCurr=(b*b*(t*t+d*u*u)+2*a*t*u)/4;
		k=1;
		while(yCurr<ykUB,
			\\ recall that m_1 \geq 2 for the positively-indexed elements
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
			\\ recall that m_1 \leq K-1 for the negatively-indexed elements
			if(bigK!=0 && k<bigK && issquare(yCurr) && yCurr>ykLB,
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

\\ pulled out of function above, using the N_a-based bounds
\\ 10 Dec 2024
get_aLB(b,d,u)={
	my(a2LB,aLB,b4);
	
	b4=b*b*b*b;
	aLB=1;
	\\ from r_0=1, p/q \neq stuff, (C-3a):
	a2LB=d*b4-sqrt((d/1.36)^23*u^44/b^48);
	if(a2LB>1,
		aLB=floor(sqrt(a2LB));
	);
	\\ from r_0=1, p/q=stuff, (C-4a):
	a2LB=d*b4-d^13*u^24/b^28;
	if(a2LB>aLB*aLB,
		aLB=floor(sqrt(a2LB));
	);

	\\ from r_0>1, p/q \neq stuff, (C-5a):
	a2LB=d*b4-sqrt(sqrt((d/28)^11*u^24/b^20));
	if(a2LB>aLB*aLB,
		aLB=floor(sqrt(a2LB));
	);

	\\ from r_0>1, p/q=stuff, (C-6a):
	a2LB=d*b4-(d*d*u*u*u*u/900/b4);
	if(a2LB>aLB*aLB,
		aLB=floor(sqrt(a2LB));
	);
	return(aLB);
}

\\ adding logging to log which inequality is used to get the max
\\ 23 Sept 2024
get_dBnd(b,u,dbg=0)={
	my(b4,dBnd,dBndTemp,ineqUsed);
	
	b4=b*b*b*b;
	dBnd=(1600.0*b4/u^8)^(1/3); \\ (4.28)
	ineqUsed=1;
	dBndTemp=sqrt(10)*b^2/u^2; \\ (4.29)
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=2;
	);
	dBndTemp=1.41*(b^56/u^44)^(1/21);
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=3;
	);
	dBndTemp=b^(8/3)/u^2;
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=4;
	);
	dBndTemp=148.0*b^(36/7)/u^(24/7);
	if(dBndTemp>dBnd,
		dBnd=max(dBnd,dBndTemp);
		ineqUsed=5;
	);
	dBndTemp=210.0*b^8/u^4;
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
\\ 6 Oct 2024
get_dBnd_r0_1(b,u)={
	my(b4,dBnd);
	
	b4=b*b*b*b;
	dBnd=(1600.0*b4/u^8)^(1/3); \\ (4.27)
	dBnd=max(dBnd,sqrt(10)*b^2/u^2); \\ (4.28)
	dBnd=max(dBnd,1.41*(b^56/u^44)^(1/21)); \\ (C-3a)
	dBnd=max(dBnd,b^(8/3)/u^2); \\ (C-4a)
	return(dBnd);
}

\\ the lower bound for d when r_0=1
\\ 6 Oct 2024
get_dBnd_r0_1_with_a_and_d(a,b,d,u)={
	my(absNrmA,b4,dBnd);
	
	b4=b*b*b*b;
	absNrmA=d*b*b*b*b-a*a;
	dBnd=(1600.0*b^4/u^8)^(1/3); \\ (4.27)
	dBnd=max(dBnd,sqrt(10)*b^2/u^2); \\ (4.28)

	dBnd=max(dBnd,1.36*(absNrmA*absNrmA*b^48/u^44)^(1/23)); \\ (C-3a)
	dBnd=max(dBnd,(absNrmA*b^28/u^24)^(1/13)); \\ (C-4a)
	return(dBnd);
}

\\ 11904 equations
\\ reduced to 860 (810 once a fix was made)
\\ 20 April 2024
DONOTUSE_d_b2_search1_20240420(dbg=0)={
	my(aUB,b,c,dBnd,e,hasSmallSoln,nrmA,sc,soln1,soln2,solnM4,solnP4,t,u,x,x2,yBnd);

	b=2;
	c=0;
	u=1;
	dBnd=121.0*b^4/u^4;
	dBnd=max(dBnd,121.0*b^7/u^2);
	dBnd=max(dBnd,148.0*b^6/u^3);
	dBnd=max(dBnd,30.0*b^5/u^2);
	dBnd=max(dBnd,40.0*b^8/u^4);
	dBnd=max(dBnd,b^(28/3)/u^4);
	for(d=2,dBnd,
		if(!issquare(d),
			u=0;
			solnM4=solve_pell_minus4(d);
			solnP4=solve_pell_plus4(d);
			if(length(solnM4)>0,
				t=solnM4[1];
				u=solnM4[2];
			);
			if(length(solnM4)==0 && length(solnP4)>0,
				t=solnP4[1];
				u=solnP4[2];
			);
			if(u!=0,
				e=(t+u*sqrt(d))/2;
				dBnd=121.0*b^4/u^4;
				dBnd=max(dBnd,121.0*b^7/u^2);
				dBnd=max(dBnd,148.0*b^6/u^3);
				dBnd=max(dBnd,30.0*b^5/u^2);
				dBnd=max(dBnd,40.0*b^8/u^4);
				dBnd=max(dBnd,b^(28/3)/u^4);
				if(d%200==0,printf("d=%6d, c=%4d\n",d,c));
				if(d==1153,printf("d=%6d, u=%9.8e, dBnd=%6d, c=%4d\n",d,u,dBnd,c));
				if(d<=dBnd,
					aUB=sqrt(d*b*b*b*b);
					if(d==1153,printf("d=%6d, aUB=%6d\n",d,aUB));
					for(a=1,aUB,
						nrmA=a*a-d*b*b*b*b;
						if(nrmA<0 && issquare(-nrmA),
							\\print("d:=",d,";nrmA:=",nrmA,";s:=IntegralQuarticPoints([d,0,0,0,nrmA]);printf \"d=%o, nrmA=%o, number=%o, solns=%o\\n\",d, nrmA, #s, s;");
							soln1=a+b*b*sqrt(d);
							c=c+1;
							sc=0;
							for(y=1,100000,
								x2=nrmA+d*y*y*y*y;
								if(issquare(x2),
									sc=sc+1;
									\\printf("d=%6d, nrmA=%8d, x=%12d, y=%6d, e=%9.6f\n",d,nrmA,sqrtint(x2),y,v2);
								);
							);
							if(sc>1,
								printf("d=%6d, a=%4d, b=%2d, nrmA=%8d, soln count=%2d\n",d,a,b,nrmA,sc);
								for(y=1,1000000,
									x2=nrmA+d*y*y*y*y;
									if(issquare(x2) && y!=2,
										x=sqrtint(x2);
										soln2=x+y*y*sqrt(d);
										v2=soln2/soln1;
										v2=log(v2)/log(e);
										printf("d=%6d, a=%4d, b=%2d, nrmA=%8d, t=%4d, u=%2d, x=%12d, y=%6d, e=%9.6f\n",d,a,b,nrmA,t,u,sqrtint(x2),y,v2);
									);
								);
							);
						);
					);
				);
			);
		);
	);
	print(c);
}

DONOTUSE_old_a_b_d_t_u_work()={
				isOK=0;
				dBndR01=get_dBnd_r0_1_with_a_and_d(a,b,d,u);
				if(d<=dBndR01,
					printf("adding r0=1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d\n",d,dBndR01,a,b,t,u,k,yCurr);
					isOK=1;
				);
				if(d>dBndR01,
					ykLB=4*sqrt(abs(nrmA)/d);
					ykUB=1350*b*b*sqrt(abs(nrmA)^5/d);
					yPrev=b*b;
					yCurr=(b*b*(t*t+d*u*u)+2*a*t*u)/4;
					k=1;
					while(yCurr<ykUB,
						if(k>1 && issquare(yCurr) && yCurr>ykLB,
							printf("adding r0>1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d\n",d,dBndR01,a,b,t,u,k,yCurr);
							isOK=1;
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
						if(bigK!=0 && k<bigK && issquare(yCurr) && yCurr>ykLB,
							printf("adding r0>1, d=%8d, dBndR01=%9.6e, a=%6d, b=%3d, t=%6d, u=%3d, k=%2d, yCurr=%8d\n",d,dBndR01,a,b,t,u,k,yCurr);
							isOK=1;
						);
						yT=(t*t+d*u*u)*yCurr/2-yPrev;
						yPrev=yCurr;
						yCurr=yT;
						k=k-1;
					);
				);
				if(isOK!=0,
					print("d:=",d,";nrmA:=",nrmA,";s:=IntegralQuarticPoints([d,0,0,0,nrmA]);printf \"d=%o, nrmA=%o, number=%o, solns=%o\\n\",d, nrmA, #s, s;");
					c2=c2+1;
				);
}

\\ the following is only partially done. We need something to handle r_0=1 too
\\ this is using Lemma 4.2 not sure what the difference is between this and the above search
\\ 20 April 2024
DONOTUSE_d2_search2(dbg=0)={
	my(aUB,b,c,dBnd,e,hasSmallSoln,nrmA,sc,solnM4,solnP4,yLB,yUB,yUBAbs);

	yUBAbs=1000*1000; \\ fixed number independent of other things (hence name)
	b=2;
	c=0;
	u=1;
	dBnd=121.0*b^4/u^4;
	dBnd=max(dBnd,121.0*b^7/u^2);
	dBnd=max(dBnd,148.0*b^6/u^3);
	dBnd=max(dBnd,30.0*b^5/u^2);
	dBnd=max(dBnd,40.0*b^8/u^4);
	dBnd=max(dBnd,b^(28/3)/u^4);
	for(d=2,dBnd,
		if(!issquare(d),
			u=0;
			solnM4=solve_pell_minus4(d);
			solnP4=solve_pell_plus4(d);
			if(length(solnM4)>0,
				t=solnM4[1];
				u=solnM4[2];
			);
			if(length(solnM4)==0 && length(solnP4)>0,
				t=solnP4[1];
				u=solnP4[2];
			);
			if(u!=0,
				e=(t+u*sqrt(d))/2;
				dBnd=121.0*b^4/u^4;
				dBnd=max(dBnd,121.0*b^7/u^2);
				dBnd=max(dBnd,148.0*b^6/u^3);
				dBnd=max(dBnd,30.0*b^5/u^2);
				dBnd=max(dBnd,40.0*b^8/u^4);
				dBnd=max(dBnd,b^(28/3)/u^4);
				if(d%200==0,printf("d=%6d, dBnd=%9.6f, c=%4d\n",d,dBnd,c));
				if(d<=dBnd,
					aUB=sqrt(d*b*b*b*b);
					for(a=1,aUB,
						nrmA=a*a-d*b*b*b*b;
						if(nrmA<0 && issquare(-nrmA),
							nrmASqrt=sqrtint(-nrmA);
							\\print("d:=",d,";nrmA:=",nrmA,";s:=IntegralQuarticPoints([d,0,0,0,nrmA]);printf \"d=%o, nrmA=%o, number=%o, solns=%o\\n\",d, nrmA, #s, s;");
							soln1=a+b*b*sqrt(d);
							hasSmallSoln=0;
							yUB=1600*b*b*nrmASqrt*nrmASqrt*nrmASqrt*nrmASqrt*nrmASqrt/sqrt(d);
							yUB=sqrt(yBnd);
							yLB=4*nrmASqrt/sqrt(d); \\2*b*b*b; \\sqrt(4*b^6);
							for(y=yLB,yUB,
								x2=nrmA+d*y*y*y*y;
								if(issquare(x2) && y!=2,
									hasSmallSoln=1;
								);
							);
							if(hasSmallSoln>0,
								c=c+1;
								sc=0;
								\\print("d:=",d,";nrmA:=",nrmA,";s:=IntegralQuarticPoints([d,0,0,0,nrmA]);printf \"d=%o, nrmA=%o, number=%o, solns=%o\\n\",d, nrmA, #s, s;");
								for(y=1,yUBAbs,
									x2=nrmA+d*y*y*y*y;
									if(issquare(x2),
										sc=sc+1;
										x=sqrtint(x2);
										soln2a=x+y*y*sqrt(d);
										soln2b=-x+y*y*sqrt(d);
										v2a=soln2a/soln1;
										v2a=log(v2a)/log(e);
										v2b=soln2b/soln1;
										v2b=log(v2b)/log(e);
										\\printf("d=%6d, nrmA=%8d, x=%12d, y=%6d, exp=%12.8f, %12.8f\n",d,nrmA,sqrtint(x2),y,v2a,v2b);
									);
								);
								if(sc>2,
									printf("d=%6d, a=%4d, b=%2d, nrmA=%8d, soln count=%2d\n",d,a,b,nrmA,sc);
									for(y=1,yUBAbs,
										x2=nrmA+d*y*y*y*y;
										if(issquare(x2) && y!=b,
											x=sqrtint(x2);
											soln2a=x+y*y*sqrt(d);
											soln2b=-x+y*y*sqrt(d);
											v2a=soln2a/soln1;
											v2a=log(v2a)/log(e);
											v2b=soln2b/soln1;
											v2b=log(v2b)/log(e);
											printf("d=%6d, a=%4d, b=%2d, nrmA=%8d, t=%4d, u=%2d, x=%12d, y=%6d, exp=%12.8f, %12.8f\n",d,a,b,nrmA,t,u,sqrtint(x2),y,v2a,v2b);
										);
									);
								);
							);
						);
					);
				);
			);
		);
	);
	print(c);
}
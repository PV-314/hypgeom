\\ call the seven functions, check_b1(), check_b2(),..., check_b7()
\\ the other functions are only for use with these seven functions

check_b_d_n_u(b,d,nrmA,u,dbg=0)={
	my(nrmAOdd,t,tM2,tP2);
	
	if(nrmA>-1,
		error("ERROR: nrmA=",nrmA," is not negative");
	);
	
	\\ recall that -nrmA must be a power of 2 times an odd prime power
	\\ but we only do a partial test on this in the Java code
	nrmAOdd=abs(nrmA/gcd(nrmA,65536*65536*65536));
	if(nrmAOdd==1 || isprimepower(nrmAOdd),
		t=0;
		tP2=d*u*u+4;
		if(issquare(tP2),
			t=sqrtint(tP2);
			check_b_d_n_t_u(b,d,nrmA,t,u,dbg);
		);
		tM2=d*u*u-4;
		if(issquare(tM2),
			t=sqrtint(tM2);
			check_b_d_n_t_u(b,d,nrmA,t,u,dbg);
		);
		if(t==0,
			error("no t found for b=",b,", d=",d,", nrmA=",nrmA);
		);
	);
}

check_b_d_n_t_u(b,d,nrmA,t,u,dbg=0)={
	my(a,a2,bigK,bP,fUB,gNd4Sqr,r0Max,r03Max,r04Max,val2,y0,y1,y2,y3,yK,ykUB1,ykUB2,
	ykUB3,ykUB3Max,ykUB3MaxOld,ykUB4,ykUB4Max,ykUB4MaxOld,ykUBMax,ykUBMaxRefined,yM1,yM2,yM3);

	a2=nrmA+d*b*b*b*b;
	if(!issquare(a2),
		error("a2=",a2," not a square for b=",b,", d=",d,", nrmA=",nrmA);
	);
	a=sqrtint(a2);
	if(b==4 && d==9734404,
		printf("a=%5d, b=%2d, d=%6d, nrmA=%8d, t=%4d, u=%2d\n",a,b,d,nrmA,t,u);
	);
	
	fUB=4*b^2; \\ from (4.13)
	
	gNd4Sqr=4; \\ using lower bound from Lemma 3.5 in b(I) paper
	ykUBMax=max(16*abs(nrmA)/sqrt(d),4*b*b*abs(nrmA)/d);
	ykUB1=0.54*b^(26/11)*abs(nrmA)^(13/11)/d^(12/11); \\ (4.15)
	ykUB2=0.23*b^(8/3)*abs(nrmA)^(7/6)/d^(7/6); \\ (4.17)
	ykUB3=82*b^(4/3)*abs(nrmA)^(5/3)/d^(1/2); \\ (4.21)
	ykUB4=423*b^2*abs(nrmA)^(2)/d^(1/2); \\ (4.23)
	ykUBMax=max(ykUBMax,ykUB1);
	ykUBMax=max(ykUBMax,ykUB2);
	r0Max=0;
	ykUB3MaxOld=0;
	r03Max=0;
	ykUB4MaxOld=0;
	r04Max=0;
	for(r0=2,10,
		\\ (4.20)
		ykUB3=59.2*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr;
		ykUB3=ykUB3*(167*abs(nrmA)^(1/2)*b^4*sqrt(gNd4Sqr)/d)^(1/(2*r0-1));
		if(ykUB3>ykUBMax,
			r0Max=r0;
		);
		ykUB3MaxOld=max(ykUB3MaxOld,ykUB3);
		ykUBMax=max(ykUBMax,ykUB3);
		\\ (4.22)
		ykUB4=65.32*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr;
		ykUB4=ykUB4*(1340*abs(nrmA)*b^4/d)^(1/2/(r0-1)); \\ (4.21)
		if(ykUB4>ykUBMax,
			r0Max=r0;
		);
		ykUB4MaxOld=max(ykUB4MaxOld,ykUB4);
		ykUBMax=max(ykUBMax,ykUB4);
	);
	
	yK=0;
	y0=b*b;
	yP=vector(30);
	yP[1]=b*b*(t*t+d*u*u)+2*a*t*u;
	yP[1]=yP[1]/4;
	yP[2]=(t*t+d*u*u)*yP[1]/2-y0;
	for(i=3,length(yP),
		yP[i]=(t*t+d*u*u)*yP[i-1]/2-yP[i-2];
	);
	/*
	for(i=2,length(yP),
		if(issquare(yP[i]) && yP[i]<ykUBMax,
			yK=yP[i];
			fArray=calc_fk(a,b,d,t,u,i,yK);
			if(fArray[1]>fUB,
				printf("ERROR: yk/ykUBMaxRefined=%9.6f for a=%5d, b=%2d, d=%6d, nrmA=%8d, t=%5d, u=%2d, k=%1d, yk=%6d\n",yK/ykUBMaxRefined,a,b,d,nrmA,t,u,i,yK);
				print("fArray=",fArray,", fUB=",fUB);
				error();
			);
			ykUB3Max=0;
			r03Max=0;
			for(r0=2,10,
				\\ (4.20)
				ykUB3=59.2*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr;
				ykUB3=ykUB3*(167*abs(nrmA)^(1/2)*b^4*sqrt(gNd4Sqr)/d)^(1/(2*r0-1));
				if(ykUB3>ykUB3Max,
					r03Max=r0;
				);
				ykUB3Max=max(ykUB3Max,ykUB3);
			);

			ykUB4Max=0;
			r04Max=0;
			for(r0=2,10,
				\\ first displayed expression in Section 4.6
				ykUB4=abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr/sqrt(0.0002344);
				ykUB4=ykUB4*(fUB^2*fArray[1]^2*abs(nrmA)/0.1911/b^4/d)^(1/2/(r0-1)); \\ (4.21)
				if(ykUB4>ykUB4Max,
					r04Max=r0;
				);
				ykUB4Max=max(ykUB4Max,ykUB4);
			);
			ykUBMaxRefined=max(16*abs(nrmA)/sqrt(d),4*b*b*abs(nrmA)/d);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB1);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB2);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB3Max);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB4Max);
			
			\\if (yK<ykUBMaxRefined,
			if (yK<ykUBMax,
				\\printf("\nyk/ykUBMaxRefined=%9.6f for a=%5d, b=%2d, d=%6d, nrmA=%8d, t=%5d, u=%2d, k=%1d, yk=%6d\n",yK/ykUBMax,a,b,d,nrmA,t,u,i,yK);
				printf("\nyk/ykUBMax=%9.6f for a=%5d, b=%2d, d=%6d, nrmA=%8d, t=%5d, u=%2d, k=%1d, yk=%6d\n",yK/ykUBMaxRefined,a,b,d,nrmA,t,u,i,yK);
				printf("fArray=[%4d], r0Max=%2d, r03Max=%2d, r04Max=%2d\n",fArray,r0Max,r03Max,r04Max);
				printf("ykUBMax=%9.6e, ykUBMaxRefined=%9.6e, ykUB3MaxOld=%9.6e, ykUB3Max=%9.6e, ykUB4MaxOld=%9.6e, ykUB4Max=%9.6e\n",ykUBMax,ykUBMaxRefined,ykUB3MaxOld,ykUB3Max,ykUB4MaxOld,ykUB4Max);
				printf("a=%6d;b=%2d;d=%10d;t=%6d;u=%2d;nrmA=%7d;check_d_n(d,nrmA,dbg);\n",a,b,d,t,u,nrmA);
			);
		);
	);
	if(yP[length(yP)]<ykUBMax,
		printf("INCOMPLETE for a=%5d, b=%2d, d=%6d, nrmA=%8d, yP[length(yP)]=%6d, yP[length(yP)]/ykUBMax=%9.6f\n",a,b,d,nrmA,yP[length(yP)],yP[length(yP)]/ykUBMax);
		error("Need to increase size of yP vector");
	);
	*/
	
	bigK=0;
	yK=0;
	yM=vector(30);
	yM[1]=b*b*(t*t+d*u*u)-2*a*t*u;
	yM[1]=yM[1]/4;
	yM[2]=(t*t+d*u*u)*yM[1]/2-y0;
	for(i=3,length(yM),
		yM[i]=(t*t+d*u*u)*yM[i-1]/2-yM[i-2];
	);
	for(i=1,length(yM),
		if(yM[i]>y0 && bigK==0,
			bigK=-i;
		);
	);
	if(bigK==0,
		error("bigK=0 for a=",a,", b=",b,", d=",d,", nrmA=",nrmA);
	);
	for(i=-bigK+1,length(yM),
		if(issquare(yM[i]) && yM[i]<ykUBMax,
			yK=yM[i];
			\\print("checking i=",i,", yM[i]=",yM[i]);
			fArray=calc_fk(a,b,d,t,u,-i,yK);
			ykUB3Max=0;
			r03Max=0;
			for(r0=2,10,
				\\ (4.20)
				ykUB3=59.2*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr;
				ykUB3=ykUB3*(167*abs(nrmA)^(1/2)*b^4*sqrt(gNd4Sqr)/d)^(1/(2*r0-1));
				if(ykUB3>ykUB3Max,
					r03Max=r0;
				);
				ykUB3Max=max(ykUB3Max,ykUB3);
			);

			ykUB4Max=0;
			r04Max=0;
			for(r0=2,10,
				\\ first displayed expression in Section 4.6
				ykUB4=abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr/sqrt(0.0002344);
				ykUB4=ykUB4*(fUB^2*fArray[1]^2*abs(nrmA)/0.1911/b^4/d)^(1/2/(r0-1)); \\ (4.21)
				if(ykUB4>ykUB4Max,
					r04Max=r0;
				);
				ykUB4Max=max(ykUB4Max,ykUB4);
			);
			ykUBMaxRefined=max(16*abs(nrmA)/sqrt(d),4*b*b*abs(nrmA)/d);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB1);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB2);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB3Max);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB4Max);
			if (yK<ykUBMax,
			\\if (yK<ykUBMaxRefined,
				\\printf("\nyk/ykUBMaxRefined=%9.6f for a=%5d, b=%2d, d=%6d, nrmA=%8d, t=%5d, u=%2d, bigK=%2d, k=%1d, yk=%6d\n",yK/ykUBMaxRefined,a,b,d,nrmA,t,u,bigK,-i,yK);
				printf("\nyk/ykUBMax=%9.6f for a=%5d, b=%2d, d=%6d, nrmA=%8d, t=%5d, u=%2d, bigK=%2d, k=%1d, yk=%6d\n",yK/ykUBMax,a,b,d,nrmA,t,u,bigK,-i,yK);
				printf("fArray=[%4d], r0Max=%2d, r03Max=%2d, r04Max=%2d\n",fArray,r0Max,r03Max,r04Max);
				printf("ykUBMax=%9.6e, ykUBMaxRefined=%9.6e, ykUB3MaxOld=%9.6e, ykUB3Max=%9.6e, ykUB4MaxOld=%9.6e, ykUB4Max=%9.6e\n",ykUBMax,ykUBMaxRefined,ykUB3MaxOld,ykUB3Max,ykUB4MaxOld,ykUB4Max);
				printf("a=%6d;b=%2d;d=%10d;t=%6d;u=%2d;nrmA=%7d;check_d_n(d,nrmA,dbg);\n",a,b,d,t,u,nrmA);
			);
		);
	);
	if(yM[length(yM)]<ykUBMax,
		printf("INCOMPLETE for a=%5d, b=%2d, d=%6d, nrmA=%8d, yM[length(yM)]=%6d, yM[length(yM)]/ykUBMax=%9.6f\n",a,b,d,nrmA,yM[length(yM)],yM[length(yM)]/ykUBMax);
		error("Need to increase size of yM vector");
	);
}

\\ t1 and u1 come first power of fundamental unit
\\ returns the array [f,r,s]
calc_fk(a,b,d,t1,u1,k,yk,dbg=0)={
	my(fa,fb,myLHS,myRHS,nrmA,nrmE,nrmECurr,r1a,r1b,r1,rb,s1,s1P,sA,tCurr,tM1,tNext,uCurr,uM1,uNext,xCalc,xk,xk2,yCalc);
	
	if(dbg!=0,
		print("t1=",t1,", u1=",u1);
	);
	nrmA=a*a-d*b*b*b*b;
	sA=core(nrmA);
	if(dbg!=0,
		print("nrmA=",nrmA,", sA=",sA);
	);
	xk2=nrmA+d*yk*yk;
	if(!issquare(xk2),
		error("for a=",a,", b=",b,", d=",d,", t1=",t1,", u1=",u1,", nrmA=",nrmA,", bigK=",bigK,", k=",k,", yk=",yk,", xk2=",xk2," is not a square");
	);
	xk=sqrtint(xk2);
	
	nrmE=(t1*t1-d*u1*u1)/4;
	tM1=nrmE*t1;
	uM1=nrmE*(-u1);
	if(k>0,
		tCurr=t1;
		uCurr=u1;
		for(i=2,k,
			tNext=(d*u1*uCurr+t1*tCurr)/4;
			uNext=(u1*tCurr+t1*uCurr)/4;
			tCurr=2*tNext;
			uCurr=2*uNext;
			nrmECurr=(tCurr*tCurr-d*uCurr*uCurr)/4;
			if(abs(nrmECurr)!=1,
				error("for i=",i,", tCurr=",tCurr,", uCurr=",uCurr,", nrmECurr=",nrmECurr);
			);
		);
	);
	if(k<0,
		tCurr=tM1;
		uCurr=uM1;
		for(i=2,-k,
			tNext=(d*uM1*uCurr+tM1*tCurr)/4;
			uNext=(uM1*tCurr+tM1*uCurr)/4;
			tCurr=2*tNext;
			uCurr=2*uNext;
			nrmECurr=(tCurr*tCurr-d*uCurr*uCurr)/4;
			if(abs(nrmECurr)!=1,
				error("for i=",-i,", tCurr=",tCurr,", uCurr=",uCurr,", nrmECurr=",nrmECurr);
			);
		);
	);
	if(dbg!=0,
		print("for k=",k,", tCurr=",tCurr,", uCurr=",uCurr);
	);
	xCalc=a*(tCurr*tCurr+d*uCurr*uCurr)+2*b*b*d*tCurr*uCurr;
	xCalc=xCalc/4;
	if(abs(xCalc)!=abs(xk),
		error("for a=",a,", b=",b,", d=",d,", t1=",t1,", u1=",u1,", nrmA=",nrmA,", bigK=",bigK,", k=",k,", yk=",yk,", xk=",xk," but xCalc=",xCalc);
	);
	yCalc=b*b*(tCurr*tCurr+d*uCurr*uCurr)+2*a*tCurr*uCurr;
	yCalc=yCalc/4;
	if (yk!=yCalc,
		error("for a=",a,", b=",b,", d=",d,", t1=",t1,", u1=",u1,", nrmA=",nrmA,", bigK=",bigK,", k=",k,", yk=",yk," not equal to yCalc=",yCalc);
	);
	if(!issquare(yk),
		print("for a=",a,", b=",b,", d=",d,", t1=",t1,", u1=",u1,", nrmA=",nrmA,", bigK=",bigK,", k=",k,", yk=",yk," is not a square");
	);
	y=sqrtint(yk);
	myLHS=(xCalc+nrmE*sqrt(nrmA))/(a+sqrt(nrmA));
	myRHS=((a*uCurr+b*b*tCurr)-uCurr*sqrt(nrmA))/2/b^2;
	myRHS=myRHS^2;
	if(dbg!=0,
		print("myLHS-myRHS=",myLHS-myRHS);
	);
	
	r1a=tCurr*b*b+a*uCurr+2*b*y;
	s1=-uCurr;
	s1P=s1*sqrtint(nrmA/sA);
	if(dbg!=0,
		print("r1a=",r1a,", s1=",s1,", s1P=",s1P);
	);
	\\print((4*b*b*r1a)^2*(x+nrmE*sqrt(nrmA)));
	\\print((a+sqrt(nrmA))*(r1a+s1P*sqrt(sA))^4);
	if(dbg!=0,
		print("diff(a)=",(4*b*b*r1a)^2*(xCalc+nrmE*sqrt(nrmA))-(a+sqrt(nrmA))*(r1a+s1P*sqrt(sA))^4);
	);
	g12a=gcd(gcd(4*b*b*r1a/core(r1a),r1a*r1a),s1P^2);
	if(!issquare(g12a),
		error("g12a=",g12a," is not a square");
	);
	g1a=sqrtint(g12a);
	ra=r1a/g1a;
	sa=s1P/g1a;
	fa=4*b*b*r1a/g1a^2;
	if(dbg!=0,
		print("ra=",ra,", sa=",sa,", fa=",fa);
	);

	r1b=tCurr*b*b+a*uCurr-2*b*y;
	if(dbg!=0,
		print("r1b=",r1b,", s1=",s1,", s1P=",s1P);
	);
	\\print((4*b*b*r1a)^2*(x+nrmE*sqrt(nrmA)));
	\\print((a+sqrt(nrmA))*(r1a+s1P*sqrt(sA))^4);
	if(dbg!=0,
		print("diff(b)=",(4*b*b*r1b)^2*(xCalc+nrmE*sqrt(nrmA))-(a+sqrt(nrmA))*(r1b+s1P*sqrt(sA))^4);
	);
	g12b=gcd(gcd(4*b*b*r1b/core(r1b),r1b*r1b),s1P^2);
	if(!issquare(g12b),
		error("g12b=",g12b," is not a square");
	);
	g1b=sqrtint(g12b);
	rb=r1b/g1b;
	sb=s1P/g1b;
	fb=-4*b*b*r1b/g1b^2;
	if(dbg!=0,
		print("rb=",rb,", sb=",sb,", fb=",fb);
	);
	
	if(fa<fb,
		return([fa,ra,sa]);
	);
	return([fb,rb,sb]);
}

check_b1()={
	my(b,d,dbg,nrmA,u);

	b=1;
	dbg=1;
	u=1;
	d=8;nrmA=-7;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=8;nrmA=-4;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=13;nrmA=-9;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=12;nrmA=-11;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=32;nrmA=-16;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=480;nrmA=-224;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=2;
	d=2;nrmA=-1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=8;nrmA=-4;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=120;nrmA=-56;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=4;
	d=2;nrmA=-1;check_b_d_n_u(b,d,nrmA,u,dbg);
}

check_b2()={
	my(b,d,dbg,nrmA,u);

	b=2;
	dbg=1;
	u=1;
	d=     5;nrmA=-31;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     5;nrmA=-44;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     8;nrmA=-7;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     8;nrmA=-47;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     8;nrmA=-64;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     8;nrmA=-112;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     8;nrmA=-127;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    12;nrmA=-176;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    12;nrmA=-188;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    13;nrmA=-144;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    13;nrmA=-199;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    29;nrmA=-103;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    32;nrmA=-256;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   480;nrmA=-3584;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  1760;nrmA=-28124;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=108896;nrmA=-785852;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=352832;nrmA=-1252096;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=2;
	d=2;nrmA=-16;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=2;nrmA=-28;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=3;nrmA=-44;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=3;nrmA=-47;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=8;nrmA=-64;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=120;nrmA=-896;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=440;nrmA=-7031;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=27224;nrmA=-196463;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=4;
	d=2;nrmA=-16;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=30;nrmA=-224;check_b_d_n_u(b,d,nrmA,u,dbg);
}

check_b3(dbg=0)={
	my(b,d,dbg,nrmA,u);

	b=3;
	dbg=1;
	u=1;
	d=       5;nrmA=-116;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=-149;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=-236;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=-356;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=-404;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=-44;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-164;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-324;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=-11;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=-569;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=-729;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      20;nrmA=-1616;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      20;nrmA=-464;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      20;nrmA=-596;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=-1949;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=-233;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      32;nrmA=-1296;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      40;nrmA=-2084;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      53;nrmA=-449;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      68;nrmA=-3008;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      68;nrmA=-608;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      85;nrmA=-1109;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      85;nrmA=-5861;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      96;nrmA=-1052;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      96;nrmA=-6176;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     221;nrmA=-14876;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     221;nrmA=-5801;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     672;nrmA=-608;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     733;nrmA=-13577;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    4628;nrmA=-152084;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    4628;nrmA=-5204;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    9805;nrmA=-355961;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   12548;nrmA=-963947;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   70752;nrmA=-5116256;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  268320;nrmA=-241424;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 2166788;nrmA=-91108859;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 2365440;nrmA=-167236544;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 3786912;nrmA=-87344528;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 5026560;nrmA=-55063664;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 5143828;nrmA=-407876624;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=10240004;nrmA=-723967424;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=2;
	d=     2;nrmA=-41;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     2;nrmA=-81;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     5;nrmA=-116;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     5;nrmA=-149;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     5;nrmA=-404;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     8;nrmA=-324;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    10;nrmA=-521;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    17;nrmA=-152;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    17;nrmA=-752;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    24;nrmA=-1544;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    24;nrmA=-263;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   168;nrmA=-152;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  1157;nrmA=-1301;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  1157;nrmA=-38021;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 17688;nrmA=-1279064;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 67080;nrmA=-60356;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=591360;nrmA=-41809136;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=946728;nrmA=-21836132;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=4;
	d=    2;nrmA=-81;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    6;nrmA=-386;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   42;nrmA=-38;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 4422;nrmA=-319766;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=16770;nrmA=-15089;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=5;
	d=384;nrmA=-4208;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=10;
	d=96;nrmA=-1052;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=20;
	d=24;nrmA=-263;check_b_d_n_u(b,d,nrmA,u,dbg);
}

check_b4(dbg=0)={
	my(b,d,dbg,nrmA,u);

	b=4;
	dbg=1;
	u=1;
	d=       5;nrmA=-1084;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=-124;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=-496;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=-704;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-1024;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-112;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-1792;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-2032;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-752;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-823;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=-2816;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=-3008;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=-2304;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=-3184;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=-1648;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=-199;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=-3943;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      32;nrmA=-4096;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      60;nrmA=-2591;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      68;nrmA=-10847;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     200;nrmA=-43279;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     260;nrmA=-62716;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     480;nrmA=-57344;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     572;nrmA=-7303;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1760;nrmA=-449984;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  108896;nrmA=-12573632;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  219028;nrmA=-42828847;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  352832;nrmA=-20033536;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  777920;nrmA=-732124;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  933152;nrmA=-5836156;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 1552512;nrmA=-388645916;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=50893952;nrmA=-7748504156;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=2;
	d=     2;nrmA=-188;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     2;nrmA=-256;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     2;nrmA=-28;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     2;nrmA=-448;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     2;nrmA=-508;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     3;nrmA=-704;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     3;nrmA=-752;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     8;nrmA=-1024;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    65;nrmA=-15679;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   120;nrmA=-14336;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   440;nrmA=-112496;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 27224;nrmA=-3143408;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 88208;nrmA=-5008384;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=194480;nrmA=-183031;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=233288;nrmA=-1459039;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=388128;nrmA=-97161479;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=3;
	d=36608;nrmA=-467392;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=46368;nrmA=-11762624;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=4;
	d=2;nrmA=-256;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=30;nrmA=-3584;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=110;nrmA=-28124;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=6806;nrmA=-785852;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=22052;nrmA=-1252096;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=5;
	d=1568;nrmA=-394012;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=6;
	d=9152;nrmA=-116848;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=11592;nrmA=-2940656;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=7;
	d=800;nrmA=-173116;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=8;
	d=5513;nrmA=-313024;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=10;
	d=392;nrmA=-98503;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=12;
	d=2288;nrmA=-29212;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=2898;nrmA=-735164;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=14;
	d=200;nrmA=-43279;check_b_d_n_u(b,d,nrmA,u,dbg);
}

check_b5(dbg=0)={
	my(b,d,dbg,nrmA,u);

	b=5;
	dbg=1;
	u=1;
	d=        5;nrmA=-1444;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        5;nrmA=-2801;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        5;nrmA=-3004;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        5;nrmA=-421;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        8;nrmA=-2500;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        8;nrmA=-4744;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        8;nrmA=-4999;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        8;nrmA=-904;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       12;nrmA=-776;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       20;nrmA=-11204;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       20;nrmA=-1684;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       32;nrmA=-10000;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       32;nrmA=-18976;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       32;nrmA=-3616;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       40;nrmA=-12004;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      125;nrmA=-3049;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      192;nrmA=-12416;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      365;nrmA=-225209;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      580;nrmA=-168019;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      629;nrmA=-278881;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      629;nrmA=-310181;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     3485;nrmA=-1248829;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   278788;nrmA=-75220099;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   763872;nrmA=-73088336;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   933152;nrmA=-19252496;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  4186112;nrmA=-1296596416;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 22524512;nrmA=-12771142096;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 23155348;nrmA=-6240885424;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=121749152;nrmA=-30635568736;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=515471620;nrmA=-52020344419;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=2;
	d=       2;nrmA=-1186;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=-226;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=-625;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       3;nrmA=-194;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=-2801;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=-421;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-2500;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-4744;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=-904;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      10;nrmA=-3001;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      48;nrmA=-3104;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  190968;nrmA=-18272084;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  233288;nrmA=-4813124;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 1046528;nrmA=-324149104;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 5631128;nrmA=-3192785524;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 5788837;nrmA=-1560221356;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=30437288;nrmA=-7658892184;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=3;
	d= 666944;nrmA=-28907584;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 666944;nrmA=-310997056;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=1438400;nrmA=-590505904;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=1585920;nrmA=-93838064;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=4;
	d=      2;nrmA=-226;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      2;nrmA=-625;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     12;nrmA=-776;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      2;nrmA=-1186;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  47742;nrmA=-4568021;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  58322;nrmA=-1203281;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 261632;nrmA=-81037276;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=1407782;nrmA=-798196381;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=6;
	d=166736;nrmA=-7226896;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=166736;nrmA=-77749264;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=359600;nrmA=-147626476;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=396480;nrmA=-23459516;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=8;
	d=3;nrmA=-194;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=65408;nrmA=-20259319;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=12;
	d=41684;nrmA= -1806724;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=41684;nrmA=-19437316;check_b_d_n_u(b,d,nrmA,u,dbg);
}

check_b6(dbg=0)={
	my(b,d,dbg,nrmA,u);

	b=6;
	dbg=1;
	u=1;
	d=         5;nrmA=-1004;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         5;nrmA=-1856;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         5;nrmA=-2384;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         5;nrmA=-239;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         5;nrmA=-3776;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         5;nrmA=-5696;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         5;nrmA=-5996;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         5;nrmA=-6464;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         5;nrmA=-704;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         8;nrmA=-2624;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         8;nrmA=-5184;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        12;nrmA=-176;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        13;nrmA=-11664;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        13;nrmA=-9104;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        20;nrmA=-22199;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        20;nrmA=-25856;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        20;nrmA=-7424;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        20;nrmA=-9536;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        20;nrmA=-956;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        29;nrmA=-31184;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        29;nrmA=-3728;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        32;nrmA=-20736;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        40;nrmA=-33344;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        53;nrmA=-7184;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        68;nrmA=-48128;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        68;nrmA=-9728;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        85;nrmA=-17744;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        85;nrmA=-93776;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        96;nrmA=-16832;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        96;nrmA=-98816;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       125;nrmA=-4391;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       221;nrmA=-191;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       221;nrmA=-238016;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       221;nrmA=-92816;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       229;nrmA=-10559;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       328;nrmA=-341567;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       672;nrmA=-9728;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       733;nrmA=-217232;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      4628;nrmA=-2433344;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      4628;nrmA=-83264;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      7565;nrmA=-3013004;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      9805;nrmA=-5695376;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     12548;nrmA=-15423152;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     12548;nrmA=-3744764;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     21908;nrmA=-17784719;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     51988;nrmA=-53789852;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     70752;nrmA=-81860096;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     80660;nrmA=-65510351;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    267293;nrmA=-192254672;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    268320;nrmA=-3862784;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    944788;nrmA=-637400807;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   2166788;nrmA=-1457741744;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   2166788;nrmA=-1793161367;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   2365440;nrmA=-2675784704;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   3786912;nrmA=-1397512448;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   3936260;nrmA=-5002648991;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   4284896;nrmA=-5090889212;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   5026560;nrmA=-881018624;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   5143828;nrmA=-6526025984;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   5992708;nrmA=-7079795132;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  10240004;nrmA=-11583478784;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  21529604;nrmA=-16532196623;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  25361300;nrmA=-28241116271;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  30758112;nrmA=-442793216;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  38564096;nrmA=-46887930812;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  47775748;nrmA=-61127084864;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  52301828;nrmA=-24030661847;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  82955668;nrmA=-103445590679;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  93161108;nrmA=-103739676839;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  93161108;nrmA=-75676969439;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 100962308;nrmA=-121808085692;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 106791552;nrmA=-1537369088;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 116640004;nrmA=-115161900668;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 152571908;nrmA=-119941846847;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 200165908;nrmA=-257739260672;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 298460180;nrmA=-156987703616;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 321413188;nrmA=-199928268464;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 448084228;nrmA=-372870525884;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 542517268;nrmA=-670958192384;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=1293121604;nrmA=-194270808128;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=1298305028;nrmA=-1209700909247;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=1816464404;nrmA=-642855281984;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=4000815508;nrmA=-874018597952;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=2;
	d=        2;nrmA=-1296;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        2;nrmA=-656;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        3;nrmA=-44;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        5;nrmA=-1856;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        5;nrmA=-2384;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        5;nrmA=-239;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        5;nrmA=-6464;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        8;nrmA=-5184;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       10;nrmA=-8336;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       17;nrmA=-12032;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       17;nrmA=-2432;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       24;nrmA=-24704;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       24;nrmA=-4208;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      168;nrmA=-2432;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     1157;nrmA=-20816;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     1157;nrmA=-608336;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     3137;nrmA=-3855788;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     3137;nrmA=-936191;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    12997;nrmA=-13447463;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    17688;nrmA=-20465024;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    67080;nrmA=-965696;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   541697;nrmA=-364435436;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   591360;nrmA=-668946176;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   946728;nrmA=-349378112;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  1071224;nrmA=-1272722303;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  1256640;nrmA=-220254656;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  1285957;nrmA=-1631506496;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  1498177;nrmA=-1769948783;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  2560001;nrmA=-2895869696;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  7689528;nrmA=-110698304;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  9641024;nrmA=-11721982703;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 11943937;nrmA=-15281771216;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 25240577;nrmA=-30452021423;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 26697888;nrmA=-384342272;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 29160001;nrmA=-28790475167;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 50041477;nrmA=-64434815168;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 74615045;nrmA=-39246925904;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 80353297;nrmA=-49982067116;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=112021057;nrmA=-93217631471;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=135629317;nrmA=-167739548096;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=4;
	d=      2;nrmA=-1296;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      6;nrmA=-1052;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      6;nrmA=-6176;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     42;nrmA=-608;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   4422;nrmA=-5116256;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  16770;nrmA=-241424;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 147840;nrmA=-167236544;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 236682;nrmA=-87344528;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 314160;nrmA=-55063664;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=1922382;nrmA=-27674576;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=6674472;nrmA=-96085568;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=5;
	d=384;nrmA=-67328;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=1014452;nrmA=-824062991;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=8;
	d=36960;nrmA=-41809136;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=78540;nrmA=-13765916;check_b_d_n_u(b,d,nrmA,u,dbg);

	u=10;
	d=96;nrmA=-16832;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=16;
	d=9240;nrmA=-10452284;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=19635;nrmA=-3441479;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=20;
	d=24;nrmA=-4208;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=32;
	d=2310;nrmA=-2613071;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=40;
	d=6;nrmA=-1052;check_b_d_n_u(b,d,nrmA,u,dbg);
}

check_b7(dbg=0)={
	my(b,d,dbg,nrmA,u);

	b=7;
	dbg=1;
	u=1;
	d=          5;nrmA=-556;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=          5;nrmA=-6529;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=          8;nrmA=-11464;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=          8;nrmA=-16807;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=          8;nrmA=-19204;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=          8;nrmA=-6212;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=          8;nrmA=-712;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=          8;nrmA=-9604;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         12;nrmA=-9491;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         13;nrmA=-18892;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         13;nrmA=-26857;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         20;nrmA=-26116;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         32;nrmA=-24848;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         32;nrmA=-38416;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         32;nrmA=-45856;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         68;nrmA=-12724;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         68;nrmA=-151604;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=         96;nrmA=-156512;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        125;nrmA=-122041;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        148;nrmA=-107344;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        148;nrmA=-136324;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        148;nrmA=-318484;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        173;nrmA=-8329;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        293;nrmA=-17909;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        293;nrmA=-47393;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        480;nrmA=-537824;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        580;nrmA=-1110619;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        580;nrmA=-120196;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2405;nrmA=-4447301;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12992;nrmA=-12736;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12992;nrmA=-7535296;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      19040;nrmA=-36977104;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      34592;nrmA=-26848;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      36096;nrmA=-76604912;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      36868;nrmA=-40245364;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     138388;nrmA=-101654992;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     147460;nrmA=-351881731;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     599072;nrmA=-440064656;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     695552;nrmA=-1024047296;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     980096;nrmA=-756408896;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     980096;nrmA=-960496;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1272388;nrmA=-708473107;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   10458752;nrmA=-564094576;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   13307908;nrmA=-21080471284;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   15210004;nrmA=-20645488;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   18301280;nrmA=-37626210256;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   24443140;nrmA=-28450594819;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   25948832;nrmA=-2097690208;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   58614340;nrmA=-134108209891;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   72080096;nrmA=-162477546832;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   73925600;nrmA=-72446944;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  149572896;nrmA=-203926344992;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  428490004;nrmA=-719219088388;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  452157700;nrmA=-889085602144;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  521026272;nrmA=-576233548448;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 1644140308;nrmA=-3077562048004;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 3155293588;nrmA=-5535013374064;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 3388636948;nrmA=-8029885643524;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 3525746880;nrmA=-7631376713264;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=10434622496;nrmA=-4835663853712;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=2;
	d=        2;nrmA=-1553;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        2;nrmA=-178;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        2;nrmA=-2401;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        2;nrmA=-2866;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        2;nrmA=-4801;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        5;nrmA=-6529;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        8;nrmA=-11464;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        8;nrmA=-6212;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=        8;nrmA=-9604;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       17;nrmA=-3181;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       17;nrmA=-37901;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       24;nrmA=-39128;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       37;nrmA=-26836;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       37;nrmA=-34081;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       37;nrmA=-79621;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      120;nrmA=-134456;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      145;nrmA=-30049;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     3248;nrmA=-1883824;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     3248;nrmA=-3184;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     4760;nrmA=-9244276;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     8648;nrmA=-6712;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     9024;nrmA=-19151228;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     9217;nrmA=-10061341;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    34597;nrmA=-25413748;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   149768;nrmA=-110016164;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   173888;nrmA=-256011824;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   245024;nrmA=-189102224;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   245024;nrmA=-240124;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  2614688;nrmA=-141023644;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  3326977;nrmA=-5270117821;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  3802501;nrmA=-5161372;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  4575320;nrmA=-9406552564;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  6487208;nrmA=-524422552;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 18020024;nrmA=-40619386708;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 18481400;nrmA=-18111736;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 37393224;nrmA=-50981586248;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=107122501;nrmA=-179804772097;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=113039425;nrmA=-222271400536;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=130256568;nrmA=-144058387112;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=411035077;nrmA=-769390512001;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=788823397;nrmA=-1383753343516;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=847159237;nrmA=-2007471410881;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=3;
	d=28448;nrmA=-9952;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=7621280;nrmA=-4477399184;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=4;
	d=       2;nrmA=-1553;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=-2401;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=-2866;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       6;nrmA=-9782;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      30;nrmA=-33614;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     812;nrmA=-470956;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     812;nrmA=-796;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1190;nrmA=-2311069;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    2162;nrmA=-1678;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    2256;nrmA=-4787807;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   37442;nrmA=-27504041;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   43472;nrmA=-64002956;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   61256;nrmA=-47275556;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   61256;nrmA=-60031;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  653672;nrmA=-35255911;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 1143830;nrmA=-2351638141;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 1621802;nrmA=-131105638;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 4505006;nrmA=-10154846677;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 4620350;nrmA=-4527934;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 9348306;nrmA=-12745396562;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=32564142;nrmA=-36014596778;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=6;
	d=7112;nrmA=-2488;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=1905320;nrmA=-1119349796;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=8;
	d=203;nrmA=-199;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=203;nrmA=-117739;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=10868;nrmA=-16000739;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=15314;nrmA=-11818889;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	u=12;
	d=1778;nrmA=-622;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=476330;nrmA=-279837449;check_b_d_n_u(b,d,nrmA,u,dbg);
}
read("..\..\..\general\pari\hypg-utils.gp");

\\ call the following four functions, for b=1,2,3,4, respectively
\\ check_b1()
\\ check_b2()
\\ check_b3()
\\ check_b4()
\\ the other functions are only for use with these four functions

check_b_d_n_u(b,d,nrmA,u,dbg=0)={
	my(t,tM2,tP2);
	
	if(nrmA>-1,
		error("ERROR: nrmA=",nrmA," is not negative");
	);
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
}

check_b_d_n_t_u(b,d,nrmA,t,u,dbg=0)={
	my(a,a2,bigK,bP,gNd4Sqr,r0Max,r03Max,r04Max,val2,y0,y1,y2,y3,yK,ykUB1,ykUB2,
	ykUB4,ykUBMax,ykUBMaxRefined,yM1,yM2,yM3);
	
	a2=nrmA+d*b*b*b*b;
	if(!issquare(a2),
		error("a2=",a2," not a square for b=",b,", d=",d,", nrmA=",nrmA);
	);
	a=sqrtint(a2);
	if(b==4 && d==9734404,
		printf("a=%5d, b=%2d, d=%6d, nrmA=%8d, t=%4d, u=%2d\n",a,b,d,nrmA,t,u);
	);
	
	\\ based on Lemma 3.12 of b=1, -N_a sqr paper. ONLY holds if gcd(a,b)=1
	\\bP=nrmA/gcd(a*a,d*b*b*b*b);
	\\val2=1+min(2,valuation(bP,2)/2);
	\\gNd4Sqr=gcd(a*a,d*b*b*b*b)*2^(2*val2);
	
	gNd4Sqr=4; \\ using lower bound from Lemma 3.5 in b(I) paper
	ykUB1=10.9*b^(26/11)*abs(nrmA)^(26/11)/d^(12/11); \\ (4.14)
	ykUB2=9.1*b^(8/3)*abs(nrmA)^(5/2)/d^(7/6); \\ (4.16)
	ykUB4=598*b^2*abs(nrmA)^(3)/d; \\ (4.22)
	ykUBMax=max(ykUB1,ykUB2);
	r0Max=0;
	ykUB3MaxOld=0;
	r03Max=0;
	for(r0=2,10,
		ykUB3=59.2*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr*(167*abs(nrmA)^(5/2)*b^4*sqrt(gNd4Sqr)/d)^(1/(2*r0-1));
		if(ykUB3>ykUBMax,
			r0Max=r0;
		);
		ykUB3MaxOld=max(ykUB3MaxOld,ykUB3);
		ykUBMax=max(ykUBMax,ykUB3);
		ykUB4=65.32*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr*(1340*abs(nrmA)^3*b^4/d)^(1/2/(r0-1)); \\ (4.21)
		if(ykUB4>ykUBMax,
			r0Max=r0;
		);
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
	for(i=3,length(yP),
		if(issquare(yP[i]) && yP[i]<ykUBMax,
			yK=yP[i];
			fArray=calc_fk(a,b,d,t,u,i,yK);
			ykUB3Max=0;
			r03Max=0;
			for(r0=2,10,
				\\ykUB3=59.2*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr*(167*abs(nrmA)^(5/2)*b^4*sqrt(gNd4Sqr)/d)^(1/(2*r0-1));
				ykUB3=59.2*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr*(0.181*(16*b^4*abs(nrmA))^4*fArray[1]^8*abs(nrmA)^2*gNd4Sqr^2/b^16/d^4)^(1/4/(2*r0-1));
				if(ykUB3>ykUB3Max,
					r03Max=r0;
				);
				ykUB3Max=max(ykUB3Max,ykUB3);
			);

			ykUB4Max=0;
			r04Max=0;
			for(r0=2,10,
				ykUB4=65.32*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr*(16*b^4*abs(nrmA)*fArray[1]^2*abs(nrmA)/0.1911/b^4/d)^(1/2/(r0-1)); \\ (4.21)
				if(ykUB4>ykUB4Max,
					r04Max=r0;
				);
				ykUB4Max=max(ykUB4Max,ykUB4);
			);
			ykUBMaxRefined=max(ykUB1,ykUB2);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB3Max);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB4Max);
			
			if (yK<ykUBMaxRefined,
				printf("\nyk/ykUBMaxRefined=%9.6f for a=%5d, b=%2d, d=%6d, nrmA=%8d, t=%5d, u=%2d, k=%1d, yk=%6d, r0Max=%2d\n",yK/ykUBMaxRefined,a,b,d,nrmA,t,u,i,yK,r0Max);
				printf("ykUBMax=%9.6e, ykUBMaxRefined=%9.6e, ykUB3MaxOld=%9.6e, ykUB3Max=%9.6e, ykUB4Max=%9.6e\n",ykUBMax,ykUBMaxRefined,ykUB3MaxOld,ykUB3Max,ykUB4Max);
				printf("a=%6d;b=%2d;d=%10d;t=%6d;u=%2d;nrmA=%7d;check_d_n(d,nrmA,dbg);\n",a,b,d,t,u,nrmA);
			);
		);
	);
	if(yP[length(yP)]<ykUBMax,
		printf("INCOMPLETE for a=%5d, b=%2d, d=%6d, nrmA=%8d, yP[length(yP)]=%6d, yP[length(yP)]/ykUBMax=%9.6f\n",a,b,d,nrmA,yP[length(yP)],yP[length(yP)]/ykUBMax);
		error("Need to increase size of yP vector");
	);

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
	for(i=-bigK+2,length(yM),
		if(issquare(yM[i]) && yM[i]<ykUBMax,
			yK=yM[i];
			\\print("checking i=",i,", yM[i]=",yM[i]);
			fArray=calc_fk(a,b,d,t,u,-i,yK);
			ykUB3Max=0;
			r03Max=0;
			for(r0=2,10,
				\\ykUB3=59.2*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr*(167*abs(nrmA)^(5/2)*b^4*sqrt(gNd4Sqr)/d)^(1/(2*r0-1));
				ykUB3=59.2*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr*(0.181*(16*b^4*abs(nrmA))^4*fArray[1]^8*abs(nrmA)^2*gNd4Sqr^2/b^16/d^4)^(1/4/(2*r0-1));
				if(ykUB3>ykUB3Max,
					r03Max=r0;
				);
				ykUB3Max=max(ykUB3Max,ykUB3);
			);

			ykUB4Max=0;
			r04Max=0;
			for(r0=2,10,
				ykUB4=65.32*abs(nrmA)^(3/2)/sqrt(d)/gNd4Sqr*(16*b^4*abs(nrmA)*fArray[1]^2*abs(nrmA)/0.1911/b^4/d)^(1/2/(r0-1)); \\ (4.21)
				if(ykUB4>ykUB4Max,
					r04Max=r0;
				);
				ykUB4Max=max(ykUB4Max,ykUB4);
			);
			ykUBMaxRefined=max(ykUB1,ykUB2);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB3Max);
			ykUBMaxRefined=max(ykUBMaxRefined,ykUB4Max);
			if (yK<ykUBMaxRefined,
				printf("\nyk/ykUBMaxRefined=%9.6f for a=%5d, b=%2d, d=%6d, nrmA=%8d, t=%5d, u=%2d, bigK=%2d, k=%1d, yk=%6d, r0Max=%2d\n",yK/ykUBMaxRefined,a,b,d,nrmA,t,u,bigK,-i,yK,r0Max);
				printf("ykUBMax=%9.6e, ykUBMaxRefined=%9.6e, ykUB3MaxOld=%9.6e, ykUB3Max=%9.6e, ykUB4Max=%9.6e\n",ykUBMax,ykUBMaxRefined,ykUB3MaxOld,ykUB3Max,ykUB4Max);
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
	d=       8;nrmA=         -4;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=         -7;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=        -11;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=         -9;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     533;nrmA=       -517;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1940;nrmA=       -340;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=         -1;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
}

check_b2()={
	my(b,d,dbg,nrmA,u);
	
	b=2;
	dbg=1;
	d=       5;nrmA=        -31;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=        -44;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=        -64;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=       -112;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=       -127;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=       -156;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=       -176;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=       -188;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=       -144;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=       -199;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=       -103;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      53;nrmA=       -319;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      60;nrmA=       -924;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      60;nrmA=       -935;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     148;nrmA=      -2332;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     533;nrmA=      -8272;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1596;nrmA=      -3036;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1940;nrmA=      -5440;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    2120;nrmA=     -15695;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 1006013;nrmA=   -8462039;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=        -16;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=        -28;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       3;nrmA=        -39;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       3;nrmA=        -44;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       3;nrmA=        -47;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      15;nrmA=       -231;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      37;nrmA=       -583;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     399;nrmA=       -759;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     485;nrmA=      -1360;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
}

check_b3()={
	my(b,d,dbg,nrmA,u);
	
	b=3;
	dbg=1;
	d=       5;nrmA=        -44;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -116;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -149;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -209;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -236;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -305;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -341;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -356;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -380;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -404;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=       -324;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=       -567;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=       -612;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=       -644;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=       -531;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=       -891;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=       -477;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=       -569;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=       -729;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=      -1017;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=      -1037;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      20;nrmA=       -596;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=      -1565;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=      -1949;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      40;nrmA=      -2084;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      40;nrmA=      -3015;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      53;nrmA=       -449;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      53;nrmA=      -4193;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      68;nrmA=       -608;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      68;nrmA=      -3008;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      85;nrmA=      -1109;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      85;nrmA=      -4385;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      85;nrmA=      -5861;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      96;nrmA=      -1052;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      96;nrmA=      -5472;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      96;nrmA=      -6176;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     148;nrmA=     -11844;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     173;nrmA=      -5549;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     200;nrmA=      -8804;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     221;nrmA=      -3740;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     221;nrmA=      -5801;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     221;nrmA=     -14876;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     221;nrmA=     -17897;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     229;nrmA=     -18513;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     365;nrmA=     -14681;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     445;nrmA=     -33741;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     533;nrmA=     -41877;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     733;nrmA=     -13577;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1940;nrmA=     -27540;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    2597;nrmA=     -94076;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    7565;nrmA=     -12140;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    7573;nrmA=    -236417;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    9805;nrmA=    -355961;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   17693;nrmA=     -73577;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   18229;nrmA=    -784325;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  267293;nrmA=  -12015917;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 1517828;nrmA= -122692064;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 4941733;nrmA= -248596517;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=        -81;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=       -153;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=       -161;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -149;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      10;nrmA=       -521;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      17;nrmA=       -152;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      17;nrmA=       -752;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      24;nrmA=       -263;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      24;nrmA=      -1368;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      24;nrmA=      -1544;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      37;nrmA=      -2961;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      50;nrmA=      -2201;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     485;nrmA=      -6885;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=  379457;nrmA=  -30673016;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       6;nrmA=       -342;u= 4;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       6;nrmA=       -386;u= 4;check_b_d_n_u(b,d,nrmA,u,dbg);
}

check_b4()={
	my(b,d,dbg,nrmA,u);
	
	b=4;
	dbg=1;
	d=       5;nrmA=       -380;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -496;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -655;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -704;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=      -1084;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=      -1111;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=      -1159;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=      -1199;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=       -823;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=       -959;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=      -1024;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=      -1519;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=      -1792;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=      -1967;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       8;nrmA=      -2032;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=       -156;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=      -2496;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=      -2816;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      12;nrmA=      -3008;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=      -1807;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=      -2304;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=      -2703;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      13;nrmA=      -3184;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      20;nrmA=      -2620;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      20;nrmA=      -4796;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=      -1648;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=      -3703;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      29;nrmA=      -3943;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      32;nrmA=      -1631;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      53;nrmA=      -5104;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      53;nrmA=      -9599;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      60;nrmA=      -2591;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      60;nrmA=     -14784;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      60;nrmA=     -14960;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      68;nrmA=     -10847;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      68;nrmA=     -15007;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      85;nrmA=      -1311;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      96;nrmA=     -19535;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     125;nrmA=      -2759;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     140;nrmA=     -35516;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     148;nrmA=     -37312;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     200;nrmA=     -43279;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     229;nrmA=     -40935;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     260;nrmA=     -62716;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     533;nrmA=    -132352;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     572;nrmA=      -7303;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     904;nrmA=    -209815;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1020;nrmA=    -217020;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1373;nrmA=    -252263;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1596;nrmA=     -48576;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    1940;nrmA=     -87040;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    2120;nrmA=    -251120;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=    2213;nrmA=    -273847;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=   87612;nrmA=  -18448647;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 1006013;nrmA= -135392624;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 9734404;nrmA=-1152886588;u= 1;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	\\ u=2
	d=       2;nrmA=       -256;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=       -448;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       2;nrmA=       -508;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       3;nrmA=        -39;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       3;nrmA=       -624;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       3;nrmA=       -704;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       3;nrmA=       -752;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=       -655;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=       5;nrmA=      -1199;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      15;nrmA=      -3696;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      15;nrmA=      -3740;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      35;nrmA=      -8879;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      37;nrmA=      -9328;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=      65;nrmA=     -15679;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     255;nrmA=     -54255;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     399;nrmA=     -12144;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     485;nrmA=     -21760;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d=     530;nrmA=     -62780;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	d= 2433601;nrmA= -288221647;u= 2;check_b_d_n_u(b,d,nrmA,u,dbg);
	
	\\ u=7
	d=    1788;nrmA=    -376503;u= 7;check_b_d_n_u(b,d,nrmA,u,dbg);
}
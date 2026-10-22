read("..\..\general\pari\hypg-utils.gp");

\\ (1-use first) analytic_estimates -- for first part of lem:eq-LB lemma proof
\\ check_e -- a brute force method to check value of E for "small" a and b
\\ (2-use second) check_e_and_q_with_estimates_for_all_d -- code to use after analytic_estimates()

\\ helper functions only:
\\ check_e_and_q_estimates_for_ad -- used by simple_check_ad() to eliminate remaining (a,d)
\\ check_e_and_q_for_units -- used by check_e_and_q_estimates_for_ad()
\\ check_e_for_y -- ONLY for use with check_e()
\\ check_q_for_y -- ??
\\ check_y -- ??
\\ simple_check_ad -- ONLY for use in check_e_and_q_with_estimates_for_all_d()

analytic_estimates()={
	my(eLB,nonSqr_ELB,nonSqr_QLB,nrmALB,qLB,v1,v2);
	
	eLB=1.13;
	qLB=217; 

	nrmALB=1; \\ lower bound for |nrmA|, in fact
	v1=0.1832*calc_gnd4LB(1)/4; \\ y_k>nrmA/4. Hence 4 in denom
	v1=round_down(v1,2);
	printf("E: we need %8.6f*sqrt(d)>%8.6f\n",v1,eLB);
	nonSqr_ELB=(eLB/v1)^2;
	nonSqr_ELB=round_up(nonSqr_ELB,3);
	printf("E: we need d>%8.6f\n",nonSqr_ELB);

	v2=21.12*nrmALB/4/sqrt(nrmALB)/calc_gnd4LB(1024); \\ 4 in denom comes from y_k>b/4
	v2=round_down(v2,2);
	printf("Q: we need %8.6f*sqrt(d)>%8.6f\n",v2,qLB);
	nonSqr_QLB=(qLB/v2)^2;
	nonSqr_QLB=round_up(nonSqr_QLB,3);
	printf("Q: we need d>%8.6f\n",nonSqr_QLB);
}

check_e(dbg=0)={
	my(aLB,aUB,denomCnst,dLB,gn4,minV,nrmA,t,u,yc,yp);
	
	dLB=1; \\129;
	minV=1.2;
	denomCnst=4*exp(1.68);
	\\ for d>1200, then ok
	for(d=2,109000,
		if(!issquare(d),
			if(d%50000==0,print("d=",d));
			solnM4=solve_pell_minus4(d);
			solnP4=solve_pell_plus4(d);
			aLB=max(1,dLB-d);
			aLB=ceil(sqrt(aLB));
			aUB=floor(sqrt(d));
			for(a=aLB,aUB,
				nrmA=a*a-d;
				gn4=calc_gnd4LB(nrmA);
				if(nrmA<0 && length(solnP4)>0,
					t=solnP4[1];
					u=solnP4[2];
					\\ yPrevious and yCurrent
					yp=1;
					yc=((t+a*u)*(t+a*u)-nrmA*u*u)/4;
					minV=check_y(yc,a,d,nrmA,denomCnst,gn4,minV,dbg);

					\\ for testing
					\\a=   7, d= 104, nrmA=   -55, gn4= 2.000000, x=   163, y=    16, v=1.105261
					if(dbg!=0 && a==7 && d==104 && nrmA==-55 && yc==16,
						printf("in check_e(): (P4, k= 1) a=%5d, d=%5d, nrmA=%5d, t=%4d, u=%3d, yc=%6d, gn4=%9.6f\n",a,d,nrmA,t,u,yc,gn4);
					);
					yc=((t-a*u)*(t-a*u)-nrmA*u*u)/4;
					if(yc>1,
						minV=check_y(yc,a,d,nrmA,denomCnst,gn4,minV,dbg);
						if(dbg!=0 && a==7 && d==104 && nrmA==-55 && yc==16,
							printf("in check_e(): (P4, k=-1) a=%5d, d=%5d, nrmA=%5d, t=%4d, u=%3d, yc=%6d, gn4=%9.6f\n",a,d,nrmA,t,u,yc,gn4);
						);
					);
				);
				if(nrmA<0 && length(solnM4)>0,
					t=solnM4[1];
					u=solnM4[2];
					\\ yPrevious and yCurrent
					yp=1;
					yc=((t+a*u)*(t+a*u)-nrmA*u*u)/4;
					minV=check_y(yc,a,d,nrmA,denomCnst,gn4,minV,dbg);
					if(dbg!=0 && a==7 && d==104 && nrmA==-55 && yc==16,
						printf("in check_e(): (M4, k= 1) a=%5d, d=%5d, nrmA=%5d, t=%4d, u=%3d, yc=%6d, gn4=%9.6f\n",a,d,nrmA,t,u,yc,gn4);
					);
					yc=((t-a*u)*(t-a*u)-nrmA*u*u)/4;
					if(yc>1,
						minV=check_y(yc,a,d,nrmA,denomCnst,gn4,minV,dbg);
						if(dbg!=0 && a==7 && d==104 && nrmA==-55 && yc==16,
							printf("in check_e(): (M4, k=-1) a=%5d, d=%5d, nrmA=%5d, t=%4d, u=%3d, yc=%6d, gn4=%9.6f\n",a,d,nrmA,t,u,yc,gn4);
						);
					);
				);
				if(length(solnM4)==0 && length(solnP4)==0,
					\\print("bad (a,b)=(",a,", ",b,")");
					\\return();
				);
			);
		);
	);
}

\\ HELPER function only
\\ for use by check_e() function above
check_y(y,a,d,nrmA,denomCnst,gn4,minV,dbg=0)={
	my(v,x,x2);
	
	if(denominator(y)==1,
		x2=d*y*y+nrmA;
		if(!issquare(x2),
			print("ERROR: x2=",x2," is not a square");
			return(1/0);
		);
		if(issquare(x2),
			if(denominator(x2)!=1,print("x^2 not an integer: a=",a,", d=",d,", nrmA=",nrmA,", x2=",x2,", y=",y));
			
			x=sqrtint(x2);
			\\ the following is using equation (4.5):
			v=gn4*(2*x+2*sqrt(x*x-nrmA))/denomCnst/abs(nrmA);
			if(v<minV,
				\\minV=v;
				printf("BAD E: a=%4d, d=%4d, nrmA=%6d, gn4=%9.6f, x=%6d, y=%6d, v=%8.6f\n",a,d,nrmA,gn4,x,y,v);
				\\print("a:=",a,";b:=",b,";s:=IntegralQuarticPoints([a*a+b,0,0,0,-b]);printf \"a=%o, b=%o, number=%o, solns=%o\\n\",a, b, #s, s;");
			);
		);
	);
	return(minV);
}

\\ this is the code to use after the analytic estimates
check_e_and_q_with_estimates_for_all_d(dbg=0)={
	my(v1,v2,yLB);
	
	v1=getwalltime();
	print("starting check_e_and_q_with_estimates_for_all_d()");
	\\ upper bound on d from analytic_estimate()
	for(d=2,109000,
		if(d%10000==0,print("starting d=",d));
		if(!issquare(d),
			aUB=floor(sqrt(d));
			for(a=1,aUB,
				nrmA=a*a-d;
				if(nrmA<0,
					yLB=max(4,ceil(abs(nrmA)/4));
					simple_check_ad(a,d,yLB,dbg);
					if(a==9 && d==104,
						print("a=",a,", d=",d,", yLB=",yLB);
						simple_check_ad(a,d,yLB,1);
						\\error();
					);
				);
			);
		);
	);
	v2=getwalltime();
	print("total time=",(v2-v1));
}

\\ HELPER function only
\\ for use by check_e_and_q_with_estimates_for_b*() functions above
\\ uses actual value of gn4, but a lower bound for y to check (3.37) and (3.38) in Lemma 3.13
\\ if this initial check fails, then use the more detailed check_e_and_q_estimates_for_ad() function
\\ 16 April 2020
simple_check_ad(a,d,yLB,dbg=0)={
	my(b,gnd4,lhsE,lhsQ,minE,minQ,nrmA,v);

	b=1;
	\\ not the actual bounds in (3.37) and (3.38), but a bit larger in order to see small egs
	minE=1.5; \\13;
	minQ=500; \\700;
	nrmA=a*a-d*b*b*b*b;
	
	\\ E check first
	gnd4=calc_gnd4LB(nrmA); \\ use this to get aUB1
	lhsE=0.1832*gnd4*sqrt(d)*yLB/abs(nrmA);
	if(dbg!=0,
		printf("in simple_check_ad(): using a=%3d, d=%4d, nrmA=%6d, gnd4(LB)=%9.6f, lhsE=%9.6f, minE=%9.6f\n",a,d,nrmA,gnd4,lhsE,minE);
	);
	if(lhsE<minE,
		if(dbg!=0,
			print("in simple_check_ad(): checking small E using a=",a,", d=",d,", nrmA=",nrmA);
		);
		v=check_e_and_q_estimates_for_ad(a,d,minE,minQ,dbg);
		\\ no need already logged
		\\if(v[1]<minE,
		\\	printf("BAD E: a=%4d, b=%6d, Q=%8.6f\n",a,b,v[1]);
		\\);
	);

	\\ Q check now
	gnd4=calc_gnd_from_abd(a,b,d,dbg);
	lhsQ=21.12*sqrt(d)*yLB/gnd4;
	if(dbg!=0,
		printf("in simple_check_ad(): using a=%3d, d=%4d, nrmA=%6d, gnd4=%9.6f, lhsQ=%9.6f, minQ=%9.6f\n",a,d,nrmA,gnd4,lhsQ,minQ);
	);
	if(lhsQ<minQ,
		if(dbg!=0,
			print("in simple_check_ad(): checking small Q using a=",a,", d=",d,", nrmA=",nrmA);
		);
		v=check_e_and_q_estimates_for_ad(a,d,minE,minQ,dbg);
		\\ no need already logged
		\\if(v[2]<minQ,
		\\	printf("BAD Q: a=%4d, b=%6d, Q=%8.6f\n",a,b,v[2]);
		\\);
	);
}

\\ simple_check_ad() calls this
\\ return [minE,minQ]
check_e_and_q_estimates_for_ad(a,d,minE,minQ,dbg=0)={
	my(nrmA,solnM4,solnP4,xc,xp,yc,yp);
	
	nrmA=a*a-d;
	solnP4=solve_pell_plus4(d);
	if(length(solnP4)>0,
		t=solnP4[1];
		u=solnP4[2];
		check_e_and_q_for_units(a,d,t,u,minE,minQ,dbg);
	);
	solnM4=solve_pell_minus4(d);
	if(length(solnM4)>0,
		t=solnM4[1];
		u=solnM4[2];
		check_e_and_q_for_units(a,d,t,u,minE,minQ,dbg);
	);
	if(length(solnM4)==0 && length(solnP4)==0,
		error("no solutions found for \pm 4 Pell equation for (a,d)=(",a,", ",d,")");
	);
	return([minE,minQ]);
}

\\ HELPER function only
check_e_and_q_for_units(a,d,t,u,minE,minQ,dbg=0)={
	my(nrmA,xc,xp,xt,yc,yp,yt);
	
	nrmA=a*a-d;
	\\ xPrevious and xCurrent, yPrevious and yCurrent
	\\ checking first for positive k
	xp=a;
	yp=1;
	xc=(a*(t*t+d*u*u)+2*d*t*u)/4;
	yc=((t+a*u)*(t+a*u)-nrmA*u*u)/4;
	if(denominator(yc)==1 && yc>1, \\ && issquare(yc),
		minE=check_e_for_y(a,d,xc,yc,minE,1,dbg);
		minQ=check_q_for_y(a,d,xc,yc,minQ,1,dbg);
	);
	if(xc*xc-d*yc*yc!=nrmA,
		print("BAD! in check_e_and_q_for_units(): a=",a,", d=",d,", nrmA=",nrmA,", t=",t,", u=",u,", k=1, xc=",xc,", yc=",yc,", xc*xc-d*yc*yc=",(xc*xc-d*yc*yc));
		1/0;
	);
	for(k=2,5,
		xt=(t*t+d*u*u)*xc/2-xp;
		yt=(t*t+d*u*u)*yc/2-yp;
		xp=xc;
		xc=xt;
		yp=yc;
		yc=yt;
		if(xc*xc-d*yc*yc!=nrmA,
			print("BAD! in check_e_and_q_for_units(): a:=",a,":d:=",d,":nrmA:=",nrmA,":t:=",t,":u:=",u,":k:=",k,":xc:=",xc,":yc=",yc,":xp:=",xp,":yp:=",yp,":xc*xc-d*yc*yc=",(xc*xc-d*yc*yc));
			1/0;
		);
		if(denominator(yc)==1 && yc>1, \\ && issquare(yc),
			minE=check_e_for_y(a,d,xc,yc,minE,k,dbg);
			minQ=check_q_for_y(a,d,xc,yc,minQ,k,dbg);
		);
	);

	xp=a;
	yp=1;
	xc=(a*(t*t+d*u*u)-2*d*t*u)/4;
	yc=((t-a*u)*(t-a*u)-nrmA*u*u)/4;
	if(xc*xc-d*yc*yc!=nrmA,
		print("BAD! in check_e_and_q_for_units(): a=",a,", d=",d,", nrmA=",nrmA,", t=",t,", u=",u,", k=-1, xc=",xc,", yc=",yc,", xc*xc-d*yc*yc=",(xc*xc-d*yc*yc));
		1/0;
	);
	if(denominator(yc)==1 && yc>1, \\ && issquare(yc),
		if(dbg!=0,
			print("in check_e_and_q_for_units(): t^2-d*u^2=4, using a=",a,", d=",d,", nrmA=",nrmA,", t=",t,", u=",u);
		);
		minE=check_e_for_y(a,d,xc,yc,minE,-1,dbg);
		minQ=check_q_for_y(a,d,xc,yc,minQ,-1,dbg);
	);
	for(k=2,5,
		xt=(t*t+d*u*u)*xc/2-xp;
		yt=(t*t+d*u*u)*yc/2-yp;
		xp=xc;
		xc=xt;
		yp=yc;
		yc=yt;
		if(xc*xc-d*yc*yc!=nrmA,
			print("BAD! in check_e_and_q_for_units(): a:=",a,":d:=",d,":nrmA:=",nrmA,":t:=",t,":u:=",u,", k=",-k,", xc=",xc,", yc=",yc,", xp=",xp,", yp=",yp,", xc*xc-d*yc*yc=",(xc*xc-d*yc*yc));
			1/0;
		);
		if(denominator(yc)==1 && yc>1 && issquare(yc),
			minE=check_e_for_y(a,d,xc,yc,minE,-k,dbg);
			minQ=check_q_for_y(a,d,xc,yc,minQ,-k,dbg);
		);
	);
}

\\ HELPER function only
\\ for use by check_e_and_q_estimates_for_ab() function above
\\ if we find a value less than minV return it. Else return minV
check_e_for_y(a,d,x,y,minV,k,dbg=0)={
	my(gn4,gnd4,nrmA,v);

	nrmA=a*a-d; \\ for logging
	gn4=calc_gnd4_from_nrmACore_and_xk(nrmA,x);
	gnd4=calc_gnd_from_abd(a,1,d,dbg);

	\\ was for debugging only:
	\\if(a==6 && b==224,
	\\	print("check_e_for_y(): a=",a,", b=",b,", x=",x,", gn4=",gn4);
	\\	1/0;
	\\);
	v=0.1832*gn4*sqrt(d)*y/abs(nrmA);
	if(dbg!=0 && a==9 && d==104,
		print("in check_e_for_y(): a=",a,", d=",d,", nrmA=",nrmA,", x=",x,", y=",y,", gn4=",gn4,", gnd4=",gnd4,", v=",v,", minV=",minV);
	);
	if(v<minV,
		minV=v;
		printf("BAD E: a=%4d, nrmA=%6d, d=%7d, k=%2d, x=%7d, y=%6d, gn4=%9.6f, v=%11.6f\n",a,nrmA,d,k,x,y,gn4,v);
		\\print("a:=",a,";b:=",b,";s:=IntegralQuarticPoints([a*a+b,0,0,0,-b]);printf \"a=%o, b=%o, number=%o, solns=%o\\n\",a, b, #s, s;");
	);
	return(minV);
}

\\ HELPER function only
\\ for use by check_e_and_q_estimates_for_ab() function above
\\ if we find a value less than minV return it. Else return minV
check_q_for_y(a,d,x,y,minV,k,dbg=0)={
	my(gn4,nrmA,v);

	nrmA=a*a-d;
	gn4=calc_gnd4_from_nrmACore_and_xk(nrmA,x);
	if(dbg!=0,
		printf("in check_q_for_y(): a=%3d, d=%4d, x=%3d, y=%4d, gn4=%9.6f\n",a,d,x,y,gn4);
	);
	\\ was for debugging only:
	\\if(a==6 && b==224,
	\\	print("check_q_for_y(): a=",a,", b=",b,", x=",x,", gn4=",gn4);
	\\	1/0;
	\\);
	v=21.12*sqrt(d)*y/gn4; \\ 21.12=exp(1.68)*(1+sqrt(0.9375))*2
	if(dbg!=0,
		printf("in check_q_for_y(): a=%3d, d=%4d, x=%3d, y=%4d, gn4=%9.6f, Q=%9.6f\n",a,d,x,y,gn4,v);
	);
	if(v<minV,
		minV=v;
		printf("BAD Q: a=%4d, nrmA=%6d, d=%7d, k=%2d, x=%7d, y=%6d, gn4=%9.6f, v=%11.6f\n",a,nrmA,d,k,x,y,gn4,v);
		\\print("a:=",a,";b:=",b,";s:=IntegralQuarticPoints([a*a+b,0,0,0,-b]);printf \"a=%o, b=%o, number=%o, solns=%o\\n\",a, b, #s, s;");
	);
	return(minV);
}
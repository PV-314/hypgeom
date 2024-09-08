read("hypgeom\\general\\hypg-utils.gp");

\\ finds small solutions of x^2-(a^2+mul*p^m)*y^4=-mul*p^m
\\ usage:
\\ eqn_soln_search(mul)
\\ this will do the search. Only supports mul=1,2,4,8,16

\\ 4 Sept 2024
sqr_search(mul,dbg=0)={
	my(c0,c1,isPP,nrmA,nrmACore,pLB,pow2,solnM4,solnP4,t,u,solns,startTime,uUB,y0,yM1,yP1);

	if(mul!=1 && mul!=2 && mul!=4 && mul!=8 && mul!=16,
		print("BAD: mul=",mul,". It must be 1,2,4,8,16.");
		return();
	);
	pow2=2^100;
	uUB=10^30;
	pLB=2;
	if(mul>1,
		pLB=3;
	);
	for(a=1,10000,
	forprime(p=pLB,500000,
	for(m=1,6,
		b=mul*p^m;
		d=a*a+b;
		if(!issquare(d),
			solnM4=solve_pell_minus4(d);
			solnP4=solve_pell_plus4(d);
			if(length(solnM4)>0,
				\\printf("using M4 with u=%9.6e\n",solnM4[2]);
				t=solnM4[1];
				u=solnM4[2];
				if(u<uUB,
					c1=(t*t+u*u*d)/2; \\ trace of unit, e^2
					c0=(t*t-u*u*d)/4;
					c0=c0*c0;
					y0=1;
					yP1=((t+a*u)*(t+a*u)+b*u*u)/4;
					yM1=((t-a*u)*(t-a*u)+b*u*u)/4;

					out=make_sequences(c0,c1,yM1,y0,yP1,d,a,1,t,u,dbg);
					indices=out[1];
					solns=out[2];
					if((mul==1 && length(solns)>2) || (mul>1 && length(solns)>1),
						printf("UNIT-M1 (%1d): a=%6d, p=%6d, m=%2d, b=%8d, d=%9d, g=%3d, t=%8d, u=%4d: c0=%2d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,p,m,b,d,gcd(a^2,b),t,u,c0,c1,indices,solns);
						output_squares(a,b,c0,c1,yM1,y0,yP1,t,u);
					);
				);
			);
			if(length(solnP4)>0,
				\\printf("using P4 with u=%9.6e\n",solnP4[2]);
				t=solnP4[1];
				u=solnP4[2];
				if(u<uUB,
					c1=(t*t+u*u*d)/2; \\ trace of unit, e^2
					c0=(t*t-u*u*d)/4;
					c0=c0*c0;
					y0=1;
					yP1=((t+a*u)*(t+a*u)+b*u*u)/4;
					yM1=((t-a*u)*(t-a*u)+b*u*u)/4;
					\\if(a==4 && mul==2 && b==22,
					\\	print("for b=22: yM1=",yM1,", yP1=",yP1);
					\\);

					out=make_sequences(c0,c1,yM1,y0,yP1,d,a,1,t,u,dbg);
					indices=out[1];
					solns=out[2];
					if((mul==1 && length(solns)>2) || (mul>1 && length(solns)>1),
						printf("UNIT-P1 (%1d): a=%6d, p=%6d, m=%2d, b=%8d, d=%9d, g=%3d, t=%8d, u=%4d: c0=%2d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,p,m,b,d,gcd(a^2,b),t,u,c0,c1,indices,solns);
						output_squares(a,b,c0,c1,yM1,y0,yP1,t,u);
					);
				);
			);
		);
	);
	);
	);
}

\\ based on some of the examples found with b=16*p^m where N(e)=1
\\ 7 Sept 2024
b16pm_search(uLB,dbg=0)={
	my(a);
	
	for(u=uLB,1000000,
		if(u%1000==0,print("starting u=",u));
		a=4*u-4;
		b16pm_search_from_a(a,u,"4u-4");
		a=4*u+4;
		b16pm_search_from_a(a,u,"4u+4");
	);
}

\\ helper function for b16pm_search()
\\ 7 Sept 2024
b16pm_search_from_a(a,u,msg)={
	my(b,bUB,c0,c1,d,indices,out,solns,t,t2,y0,yM1,yP1);
	
	bUB=500000;
	for(b1=1,bUB,
		b=16*b1*b1;
		d=a*a+b;
		t2=4+d*u*u;
		if(issquare(t2),
			t=sqrtint(t2);
			yM1=((t-a*u)*(t-a*u)+b*u*u)/4;
			if(issquare(yM1),
				c1=(t*t+u*u*d)/2; \\ trace of unit, e^2
				c0=(t*t-u*u*d)/4;
				c0=c0*c0;
				y0=1;
				yP1=((t+a*u)*(t+a*u)+b*u*u)/4;
				out=make_sequences(c0,c1,yM1,y0,yP1,d,a,1,t,u,dbg);
				indices=out[1];
				solns=out[2];
				if(length(solns)>1,
					printf("%s (%1d): a=%6d, b=%8d, d=%9d, t=%8d, u=%4d: c0=%2d, c1=%6d, indices=%s, solns=%s\n",msg,length(solns),a,b,d,t,u,c0,c1,indices,solns);
					output_squares(a,b,c0,c1,yM1,y0,yP1,t,u);
				);
			);
		);
	);
}

\\ the family of examples in the paper
\\ pseudoprimes for n=2818 and 4635 too (tested to n=5000)
\\ 7 Sept 2024
b16pm_family()={
	my(a,b,b1C,b1P,biT,t,uC,uP,uT,yM1);
	
	b1P=11;
	b1C=153;
	uP=6;
	uC=88;
	for(n=2,5000,
		if(n%200==0,print("starting n=",n));
		a=4*uC-4;
		b=16*b1C*b1C;
		t=8*uC*uC+2;
		yM1=((t-a*uC)*(t-a*uC)+b*uC*uC)/4;
		if(issquare(yM1) && issquare(b),
			b1=sqrtint(b/16);
			if(isprime(b1),
				print("n=",n);
			);
		);
		if(!issquare(yM1),
			print("BAD yM1: n=",n,", u=",uC,", b=",b,"=",factor(b),", yM1=",yM1);
			1/0;
		);
		if((3*uC+1)^2-3*b1C*b1C!=-2,
			print("BAD rel: n=",n,", u=",uC,", b=",b,"=",factor(b),", yM1=",yM1);
			1/0;
		);
		b1T=14*b1C-b1P;
		b1P=b1C;
		b1C=b1T;
		uT=14*uC-uP+4;
		uP=uC;
		uC=uT;
	);
}
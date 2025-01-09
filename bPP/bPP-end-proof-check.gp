read("hypgeom\\general\\hypg-utils.gp");

\\ entry point (and check_small_d()) to functions in this file.
\\ d=a^2+b
\\ 28 Jan 2024
search_all_d(dbg=0)={
	my(dUB,m4Soln,p4Soln,startTime,t,u);

	dUB=100*1000*1000;
	startTime=getwalltime();
	output_magma_procedure();
	for(d=128,dUB,
		if(d%500000==1,print("d=",d," time taken=",(getwalltime()-startTime)));
		if(!issquare(d),
			m4Soln=solve_pell_minus4(d);
			p4Soln=solve_pell_plus4(d);
			if(length(m4Soln)>0,
				t=m4Soln[1];
				u=m4Soln[2];
				check_dtu(d,t,u,dUB,"M4",dbg);
			);
			\\ note that doing this IN ADDITION TO m4Soln when both are solvable may result in duplicates
			if(length(m4Soln)==0 && length(p4Soln)>0,
				t=p4Soln[1];
				u=p4Soln[2];
				check_dtu(d,t,u,dUB,"P4",dbg);
			);
		); \\ d sqr
	);
	print("DONE: time taken=",(getwalltime()-startTime));
}

\\ 28 Jan 2024
check_dtu(d,t,u,dUB,msg,dbg=0)={
	my(aUB,b,bLBDenom,isOK);
	
	aUB=ceil(sqrt(d));
	for(a=1,aUB,
		b=d-a*a;
		\\ excluding b=1, as Akhtari has already sorted this
		if(b>1 && b*(a*a+b)<=dUB,
			b2Pow=gcd(65536*65536*65536,b);
			bOdd=b/b2Pow;
			isOK=isprimepower(bOdd) || bOdd==1; \\ odd part is a prime power
			isOK=isOK && (b2Pow<32 || b2Pow==b);
			if(isOK,
				bLBDenom=16;
				if(b%2==0,
					bLBDenom=256;
				);
				check_abdtu(a,b,d,t,u,bLBDenom,msg,dbg);
			);
		);
	);
}

\\ 28 Jan 2024
check_abdtu(a,b,d,t,u,bLBDenom,msg,dbg=0)={
	my(c0,c1,indices,out,seqCount,solnCount,solns,u0,y0,yk,ykLB,ykUB,yM1,yP1);

	ykUB=1800*sqrt(b*b*b);
	c1=(t*t+u*u*d)/2;
	c0=(t*t-u*u*d)/4;
	c0=c0*c0;
	if(c0*c1!=0 && denominator(c0)==1 && denominator(c1)==1 && gcd(c0,c1)==1 && polisirreducible(x^2-c1*x+c0),
		y0=1;
		yP1=((t+a*u)*(t+a*u)+b*u*u)/4;
		yM1=((t-a*u)*(t-a*u)+b*u*u)/4;
		out=make_sequences(c0,c1,yM1,y0,yP1,d,a,b,t,u,dbg);
		indices=out[1];
		solns=out[2];
		ykLB=out[3];
		if(ykLB<ykUB,
			printf("ERROR: not enough terms created for d=%8d, a=%5d, b=%8d, t=%7d, u=%4d, largest term created=%9.6f, but need at least %9.6f\n",msg,d,a,b,t,u,ykLB,ykUB);
			return();
		);
		seqCount=0;
		for(i=1,length(solns),
			yk=solns[i]*solns[i];
			if(yk>1 && yk>b*b/bLBDenom && yk<ykUB,
				if(seqCount==0,
					do_magma_output(d,-b);
					printf("//%s: d:=%8d: a:=%5d: b:=%8d: t:=%7d: u:=%4d: indices=%s, solns=%s\n",msg,d,a,b,t,u,indices,solns);
					solnCount=0;
					for(i=1,100000,
						x2=(a*a+b)*i*i*i*i-b;
						if(x2>0 && issquare(x2),
							solnCount=solnCount+1;
						);
					);
					if(solnCount==3 && issquare(b),
						printf("        x^2-dy^4=-b has three solns for a=%5d, square b=%8d, d=%8d\n",a,b,d);
						for(i=1,100000,
							x2=(a*a+b)*i*i*i*i-b;
							if(x2>0 && issquare(x2),
								printf("        x=%7d: y:=%4d\n",sqrtint(x2),i);
							);
						);
					);
					if(solnCount==4 && issquare(b),
						printf("        x^2-dy^4=-b has FOUR solns for a=%5d, square b=%8d, d=%8d\n",a,b,d);
						for(i=1,100000,
							x2=(a*a+b)*i*i*i*i-b;
							if(x2>0 && issquare(x2),
								printf("        x=%7d: y:=%4d\n",sqrtint(x2),i);
							);
						);
						return(1/0);
					);
					if(solnCount==4,
						printf("        x^2-dy^4=-b has four solns for a=%5d, b=%8d, d=%8d\n",a,b,d);
						for(i=1,100000,
							x2=(a*a+b)*i*i*i*i-b;
							if(x2>0 && issquare(x2),
								printf("        x=%7d: y:=%4d\n",sqrtint(x2),i);
							);
						);
					);
					if(solnCount==5,
						printf("        x^2-dy^4=-b has FIVE solns for a=%5d, b=%8d, d=%8d\n",a,b,d);
						for(i=1,100000,
							x2=(a*a+b)*i*i*i*i-b;
							if(x2>0 && issquare(x2),
								printf("        x=%7d: y:=%4d\n",sqrtint(x2),i);
							);
						);
						return(1/0);
					);
				);
				seqCount=seqCount+1;
			);
		);
	);
}

\\ 10 Sept 2023
check_small_d()={
	my(aUB,b,b2Pow,bOdd,c,isOK);
	
	output_magma_procedure();
	c=0;
	for(d=2,127,
		aUB=ceil(sqrt(d));
		for(a=1,aUB,
			b=d-a*a;
			b2Pow=gcd(65536*65536*65536,b);
			bOdd=b/b2Pow;
			isOK=isprimepower(bOdd) || bOdd==1; \\ odd part is a prime power
			isOK=isOK && (b2Pow<32 || b2Pow==b); \\ && !issquare(b); -- should have included (reduces to 556 eqns) but didn't at the time)
			if(isOK,
				c=c+1;
				do_magma_output(d,-b);
			);
		);
	);
	print("there are ",c," small d equations to test in Magma");
}
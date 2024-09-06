read("hypgeom\\general\\hypg-utils.gp");

\\ finds small solutions of x^2-(a^2+mul*p^m)*y^4=-mul*p^m
\\ usage:
\\ eqn_soln_search(mul)
\\ this will do the search. Only supports mul=1,2,4,8,16

\\ 4 Sept 2024
eqn_soln_search(mul,dbg=0)={
	my(c0,c1,isPP,nrmA,nrmACore,pLB,pow2,solnM4,solnP4,t,u,solns,startTime,uUB,y0,yM1,yP1);

	if(mul!=1 && mul!=2 && mul!=4 && mul!=8 && mul!=16,
		print("BAD: mul=",mul,". It must be 1,2,4,8,16.");
		return();
	);
	pow2=2^100;
	pLB=2;
	if(mul>1,
		pLB=3;
	);
	for(a=1,10000,
	if(a%100==0,print("starting a=",a));
	forprime(p=pLB,1000000,
	for(m=1,6,
		b=mul*p^m;
		d=a*a+b;
		if(p==2 || (p>2 && d%8!=1),
			solnM4=solve_pell_minus4(d);
			if(length(solnM4)>0,
				solns=List([[a,1]]);
				for(y=2,10000,
					xSqr=-b+d*y*y*y*y;
					if(gcd(y,xSqr)==1 && issquare(xSqr),
						listput(solns,[sqrtint(xSqr),y]);
					);
				);
				if((mul==1 && length(solns)>3) || (mul>1 && length(solns)>2),
					print("\nRECORD!!");
				);
				if((mul==1 && length(solns)>2) || (mul==1 && p==2 && length(solns)>1) || (mul>1 && length(solns)>1),
					printf("(%1d): a=%7d, p=%5d, m=%2d, b=%8d, d=%7d, solns=%s\n",length(solns),a,p,m,b,d,solns);
				);
			);
		);
	);
	);
	);
}
read("..\..\general\pari\hypg-utils.gp");

\\ sequence of y_k's from (a+b*sqrt(d))*((t+u*sqrt(d))/2)^(2k)
\\ eSqr in function name means using epsilon^2. Hence ((t+u*sqrt(d))/2)^(2k), not ((t+u*sqrt(d))/2)^k
\\ here epsilon is a unit
\\ gcd condition: (gcd(a,b)==1 || !issquare(gcd(a,b))) is needed
\\ without allowing non-sqr gcds, we miss a=    672, b=    8281, d=      3, nrm=  -205273299, t=  4, u=  2: c0=         1, c1=    14, indices=[-4, -2, 0, 2], solns=[91, 875, 917, 12187]
\\ use \p 60 if you have uUB=10^30
conj11_search_more_gen_eSqr(dLB=2,dUB=100,useSmallA=1,dbg=0)={
	my(aLB,aSize,aUB,b,b1Size,c0,c1,isPP,nrmA,nrmACore,nrmAOdd,nrmASet,pow2,solnM4,solnP4,t,u,solns,startTime,uUB,y0,yM1,yP1);

	pow2=2^100;
	aSize=1000;
	b1Size=1000;
	startTime=getwalltime();
	uUB=1030;
	for(d=dLB,dUB,
		if(d%1==0,print("\nd=",d,", time taken=",(getwalltime()-startTime),"(ms)"));
		if(!issquare(d) && issquarefree(d),
			solnM4=solve_pell_minus4(d);
			solnP4=solve_pell_plus4(d);
			if(length(solnM4)>0 || length(solnP4)>0,
				if(length(solnM4)>0,
					printf("for d=%5d, using M4 with u=%9.6e\n",d,solnM4[2]);
				);
				if(length(solnP4)>0,
					printf("for d=%5d, using P4 with u=%9.6e\n",d,solnP4[2]);
				);
				nrmASet=Set(); \\ use this when looking for examples with "many" squares
				for(b1=1,b1Size,
				if(dbg!=0 && b1%100==0,print("d=",d,", b1=",b1,", time taken=",(getwalltime()-startTime),"(ms)"));
				b=b1*b1;
				
				\\ search around small normA
				aLB=max(1,floor(sqrt(b*b*d))-aSize/2);
				aUB=aLB+aSize;
				
				if(useSmallA!=0,
					\\ search around small a
					aLB=1;
					aUB=aSize;
				);
				
				\\ other bounds
				\\aUB=max(1200,ceil(sqrt(b*d))+300);
				\\aUB=max(2*floor(sqrt(b*b*d)),floor(sqrt(b*b*d))+b1Size);
				\\ gives nrmA positive:
				\\aLB=ceil(sqrt(b*b*d));
				if(dbg!=0 && b1%10==0,print("d=",d,", b1=",b1,", aLB=",aLB,", aUB=",aUB));
				for(a=aLB,aUB,
					nrmA=a*a-b*b*d;
					if(issquarefree(gcd(a,b)) && length(solnM4)!=0 && denominator(nrmA)==1,
						t=solnM4[1];
						u=solnM4[2];
						if(u<uUB,
							c1=(t*t+u*u*d)/2; \\ trace of unit, e^2
							c0=(t*t-u*u*d)/4;
							c0=c0*c0;
							y0=b;
							yP1=(b*(t*t+d*u*u)+2*a*t*u)/4;
							yM1=(b*(t*t+d*u*u)-2*a*t*u)/4;

							out=make_sequences(c0,c1,yM1,y0,yP1,d,a,b,t,u,dbg);
							indices=out[1];
							solns=out[2];
							\\if(d==3 && a==2*242 && b==2*484,
							\\	print("a=",a,", b=",b,", d=",d,", nrm=",nrm,", t=",t,", u=",u,", solns=",solns);
							\\	print("yM1=",yM1,", yP1=",yP1);
							\\);

							isNrmAPP=(abs(nrmA)==1 || isprimepower(abs(nrmA)));
							nrmACore=core(abs(nrmA));
							isNrmACorePP=(nrmACore==1 || isprimepower(nrmACore));
							nrmACoreOdd=core(nrmACore)/gcd(pow2,nrmACore);
							isNrmACoreOddPP=(nrmACoreOdd==1 || isprimepower(nrmACoreOdd));
							if(!issquare(abs(nrmA)) && isNrmAPP && length(solns)>3,
								if(setsearch(nrmASet,nrmA)==0,
									printf("UNIT-M1, NRM-PP (%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
									output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
									nrmASet=setunion(nrmASet,Set(nrmA));
								);
							);
							if(!issquare(abs(nrmA)) && isNrmACorePP && length(solns)>3,
								if(setsearch(nrmASet,nrmA)==0,
									printf("UNIT-M1, NRM-PPC(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
									output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
									nrmASet=setunion(nrmASet,Set(nrmA));
								);
							);
							if(!issquare(abs(nrmA)) && nrmA%2==0 && isNrmACoreOddPP && length(solns)>3,
								if(setsearch(nrmASet,nrmA)==0,
									printf("UNIT-M1, NRM-2PP(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
									output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
									nrmASet=setunion(nrmASet,Set(nrmA));
								);
							);
							if(issquare(abs(nrmA)) && length(solns)>2,
								if(setsearch(nrmASet,nrmA)==0,
									printf("UNIT-M1, NRM-SQR(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
									output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
									nrmASet=setunion(nrmASet,Set(nrmA));
								);
							);
							if(length(solns)>2,
								if(setsearch(nrmASet,nrmA)==0,
									printf("UNIT-M1, RECORD(%1d)   : a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
									output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
									nrmASet=setunion(nrmASet,Set(nrmA));
								);
							);
						);
					);
					if(issquarefree(gcd(a,b)) && length(solnP4)!=0 && denominator(nrmA)==1,
						t=solnP4[1];
						u=solnP4[2];
						if(u<uUB,
							c1=(t*t+u*u*d)/2; \\ trace of unit, e^2
							c0=(t*t-u*u*d)/4;
							c0=c0*c0;
							y0=b;
							yP1=(b*(t*t+d*u*u)+2*a*t*u)/4;
							yM1=(b*(t*t+d*u*u)-2*a*t*u)/4;
							\\if(d==3 && a==2*242 && b==2*484,
							\\	print("a=",a,", b=",b,", d=",d,", nrm=",nrm,", t=",t,", u=",u,", c0=",c0,", c1=",c1,", yM1=",yM1,", y0=",y0,", yP1=",yP1);
							\\);

							out=make_sequences(c0,c1,yM1,y0,yP1,d,a,b,t,u,dbg);
							indices=out[1];
							solns=out[2];
							\\if(d==3 && a==2*242 && b==2*484,
							\\	print("a=",a,", b=",b,", d=",d,", nrm=",nrm,", t=",t,", u=",u,", solns=",solns);
							\\);

							isNrmAPP=(abs(nrmA)==1 || isprimepower(abs(nrmA)));
							nrmACore=core(abs(nrmA));
							isNrmACorePP=(nrmACore==1 || isprimepower(nrmACore));
							nrmACoreOdd=core(nrmACore)/gcd(pow2,nrmACore);
							isNrmACoreOddPP=(nrmACoreOdd==1 || isprimepower(nrmACoreOdd));
							if(!issquare(abs(nrmA)) && isNrmAPP && length(solns)>3,
								if(setsearch(nrmASet,nrmA)==0,
									printf("UNIT-P1, NRM-PP (%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
									output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
									nrmASet=setunion(nrmASet,Set(nrmA));
								);
							);
							if(!issquare(abs(nrmA)) && isNrmACorePP && length(solns)>3,
								if(setsearch(nrmASet,nrmA)==0,
									printf("UNIT-P1, NRM-PPC(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
									output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
									nrmASet=setunion(nrmASet,Set(nrmA));
								);
							);
							if(!issquare(abs(nrmA)) && nrmA%2==0 && isNrmACoreOddPP && length(solns)>3,
								if(setsearch(nrmASet,nrmA)==0,
									printf("UNIT-P1, NRM-2PP(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
									output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
									nrmASet=setunion(nrmASet,Set(nrmA));
								);
							);
							if(issquare(abs(nrmA)) && length(solns)>2,
								if(setsearch(nrmASet,nrmA)==0,
									printf("UNIT-P1, NRM-SQR(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
									output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
									nrmASet=setunion(nrmASet,Set(nrmA));
								);
							);
							if(length(solns)>2,
								if(setsearch(nrmASet,nrmA)==0,
									printf("UNIT-P1, RECORD(%1d)   : a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
									output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
									nrmASet=setunion(nrmASet,Set(nrmA));
								);
							);
						);
					);
				);
				);
			);
		);
	);
}

\\ sequence of y_k's from (a+b*sqrt(d))*((t+u*sqrt(d))/2)^k (rather than ^(2*k))
\\ here (t+u*sqrt(d))/2 is a unit. Note alpha=a+b*sqrt(d) NOT a+b^2*sqrt(d)
conj13_search_more_gen(dLB=2,dUB=1000,useSmallA=1,dbg=0)={
	my(aLB,aSize,aUB,b,b1Size,c0,c1,d,indices,isPP,nrm,nrmSet,out,pow2,solnM4,solnP4,t,u,solns,y0,yM1,yP1);
	
	pow2=2^100;
	aSize=2*1000;
	b1Size=2*1000;
	startTime=getwalltime();
	uUB=10^30;
	forstep(d=dLB,dUB,1,
		if(d%1==0,print("\nstarting d=",d,", time taken=",(getwalltime()-startTime),"(ms)"));
		if(issquarefree(d) && !issquare(d),
			solnM4=solve_pell_minus4(d);
			solnP4=solve_pell_plus4(d);
			if((length(solnM4)>0 && solnM4[2]<uUB) || (length(solnP4)>0 && solnP4[2]<uUB),
				\\ nrmSet is not used as it is too expensive, where I was checking and doing union
				nrmASet=Set();
				for(b1=1,b1Size,
					b=b1*b1;
					\\ search around small normA
					aLB=max(1,floor(sqrt(b*b*d))-aSize/2);
					aUB=aLB+aSize;

					if(useSmallA!=0,
						\\ search around small a
						aLB=1;
						aUB=aSize;
					);

					\\ other bounds (use??)
					\\aUB=max(1200,ceil(sqrt(b*d))+300);
					\\aUB=max(2*floor(sqrt(b*b*d)),floor(sqrt(b*b*d))+b1Size);
					for(a=aLB,aUB,
						nrmA=a*a-b*b*d;
						if(issquarefree(gcd(a,b)),
							\\nrmSet=setunion(nrmSet,Set([nrm]));
							if(length(solnM4)!=0,
								t=solnM4[1];
								u=solnM4[2];
								c1=t; \\ trace of unit, e
								c0=(t*t-u*u*d)/4;
								y0=b;
								yP1=(a*u+b*t)/2;
								\\ if N_e=+1, then yM1=(b*t-a*u)/2
								\\ if N_e=-1, then yM1=(a*u-b*t)/2
								yM1=(a*u-b*t)/2; \\ if t^2-d*u^2=-4, then alpha*eps^(-1)=-alpha*epConj

								out=make_sequences(c0,c1,yM1,y0,yP1,d,a,b,t,u,dbg);
								indices=out[1];
								solns=out[2];

								isNrmAPP=(abs(nrmA)==1 || isprimepower(abs(nrmA)));
								nrmACore=core(abs(nrmA));
								isNrmACorePP=(nrmACore==1 || isprimepower(nrmACore));
								nrmACoreOdd=core(nrmACore)/gcd(pow2,nrmACore);
								isNrmACoreOddPP=(nrmACoreOdd==1 || isprimepower(nrmACoreOdd));
								if(!issquare(abs(nrmA)) && isNrmAPP && length(solns)>2,
									if(setsearch(nrmASet,nrmA)==0,
										printf("UNIT-M1, NRM-PP (%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
										output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
										nrmASet=setunion(nrmASet,Set(nrmA));
									);
								);
								if(!issquare(abs(nrmA)) && isNrmACorePP && length(solns)>3,
									if(setsearch(nrmASet,nrmA)==0,
										printf("UNIT-M1, NRM-PPC(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
										output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
										nrmASet=setunion(nrmASet,Set(nrmA));
									);
								);
								if(!issquare(abs(nrmA)) && nrmA%2==0 && isNrmACoreOddPP && length(solns)>3,
									if(setsearch(nrmASet,nrmA)==0,
										printf("UNIT-P1, NRM-2PP(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
										output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
										nrmASet=setunion(nrmASet,Set(nrmA));
									);
								);
								if(issquare(abs(nrmA)) && length(solns)>2,
									if(setsearch(nrmASet,nrmA)==0,
										printf("UNIT-M1, NRM-SQR(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
										output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
										nrmASet=setunion(nrmASet,Set(nrmA));
									);
								);
								if(length(solns)>4,
									if(setsearch(nrmASet,nrmA)==0,
										printf("UNIT-M1, RECORD(%1d)   : a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
										output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
										nrmASet=setunion(nrmASet,Set(nrmA));
									);
								);
							);
							if(length(solnP4)!=0,
								t=solnP4[1];
								u=solnP4[2];
								c1=t; \\ trace of unit, e
								c0=(t*t-u*u*d)/4;
								y0=b;
								yP1=(a*u+b*t)/2;
								yM1=(b*t-a*u)/2;

								out=make_sequences(c0,c1,yM1,y0,yP1,d,a,b,t,u,dbg);
								indices=out[1];
								solns=out[2];

								isNrmAPP=(abs(nrmA)==1 || isprimepower(abs(nrmA)));
								nrmACore=core(abs(nrmA));
								isNrmACorePP=(nrmACore==1 || isprimepower(nrmACore));
								nrmACoreOdd=core(nrmACore)/gcd(pow2,nrmACore);
								isNrmACoreOddPP=(nrmACoreOdd==1 || isprimepower(nrmACoreOdd));
								if(!issquare(abs(nrmA)) && isNrmAPP && length(solns)>2,
									if(setsearch(nrmASet,nrmA)==0,
										printf("UNIT-P1, NRM-PP (%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
										output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
										nrmASet=setunion(nrmASet,Set(nrmA));
									);
								);
								if(!issquare(abs(nrmA)) && isNrmACorePP && length(solns)>3,
									if(setsearch(nrmASet,nrmA)==0,
										printf("UNIT-P1, NRM-PPC(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
										output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
										nrmASet=setunion(nrmASet,Set(nrmA));
									);
								);
								if(!issquare(abs(nrmA)) && nrmA%2==0 && isNrmACoreOddPP && length(solns)>3,
									if(setsearch(nrmASet,nrmA)==0,
										printf("UNIT-P1, NRM-2PP(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
										output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
										nrmASet=setunion(nrmASet,Set(nrmA));
									);
								);
								if(issquare(abs(nrmA)) && length(solns)>2,
									if(setsearch(nrmASet,nrmA)==0,
										printf("UNIT-P1, NRM-SQR(%1d): a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
										output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
										nrmASet=setunion(nrmASet,Set(nrmA));
									);
								);
								if(length(solns)>4,
									if(setsearch(nrmASet,nrmA)==0,
										printf("UNIT-P1, RECORD(%1d)   : a=%7d, b=%8d, d=%7d, nrmA=%12d, t=%3d, u=%3d: c0=%10d, c1=%6d, indices=%s, solns=%s\n",length(solns),a,b,d,nrmA,t,u,c0,c1,indices,solns);
										output_squares(a,-nrmA,c0,c1,yM1,y0,yP1,t,u);
										nrmASet=setunion(nrmASet,Set(nrmA));
									);
								);
							);
						); \\ gcd(a,b) square-free check
					); \\ for a
				); \\ for b
			);
		);
		if(d%1==0,print("\nfinished d=",d,", time taken=",(getwalltime()-startTime),"(ms)=",strtime(getwalltime()-startTime)));
	);
	print("\nfinished all d, total time taken=",(getwalltime()-startTime),"(ms)=",strtime(getwalltime()-startTime));
}

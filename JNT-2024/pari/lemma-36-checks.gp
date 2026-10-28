read("..\..\general\pari\hypg-utils.gp");

\\ search to see if any are missed
check_all(dbg=0)={
	my(aUB,bigK,k,solnM4,solnP4,startTime,t,t2,yC,yP,yT);
	
	startTime=getwalltime();
	for(d=2,10000,
		aUB=floor(sqrt(d));
		for(u=1,100,
			t2=-4+d*u*u;
			\\if(d==5,print("d=",d,", t2=",t2,", u=",u));
			if(t2>0 && issquare(t2),
				t=sqrtint(t2);
				\\if(t==1,print("d=",d,", t=",t,", u=",u,", aUB=",aUB));
				for(a=1,aUB,
					yP=1;
					yM1=((t*t+d*u*u)-2*a*t*u)/4;
					yC=yM1;
					\\if(t==1,print("d=",d,", t=",t,", u=",u,", a=",a,", yM1=",yC));
					bigK=0;
					k=-1;
					if(yC>1,
						bigK=k;
					);
					while(bigK==0,
						k=k-1;
						yT=(t*t+d*u*u)*yC/2-yP;
						yP=yC;
						yC=yT;
						\\if(t==1,print("d=",d,", t=",t,", u=",u,", a=",a,", k=",k,", yC=",yC));
						if(yC>1,
							bigK=k;
						);
						if(k<-20,
							print("stop now: a=",a,", d=",d,", t=",t,", u=",u,", bigK=",bigK,", y_K=",yC);
							return();
						);
					);
					if(bigK<-1,
						if(bigK!=-2 || d!=a*a+4 || t!=a || u!=1,
							if(bigK!=-2 || d!=a*a+1 || t!=2*a || u!=2,
								print("norm -1: a=",a,", d=",d,", t=",t,", u=",u,", bigK=",bigK,", y_K=",yC,", yM1=",yM1);
							);
						);
					);
					if(bigK==-2 && d==a*a+4 && t==a && u==1 && bigK!=-2,
						error("BAD norm -1: a=",a,", d=",d,", t=",t,", u=",u,", bigK=",bigK,", y_K=",yC);
					);
					if(bigK==-2 && d==a*a+1 && t==2*a && u==2 && bigK!=-2,
						error("BAD norm -1: a=",a,", d=",d,", t=",t,", u=",u,", bigK=",bigK,", y_K=",yC);
					);
				);
			);
			t2=4+d*u*u;
			\\if(d==5,print("d=",d,", t2=",t2,", u=",u));
			if(t2>0 && issquare(t2),
				t=sqrtint(t2);
				\\if(t==1,print("nrm +1: d=",d,", t=",t,", u=",u,", aUB=",aUB));
				for(a=1,aUB,
					yP=1;
					yM1=((t*t+d*u*u)-2*a*t*u)/4;
					yC=yM1;
					bigK=0;
					k=-1;
					if(yC>1,
						bigK=k;
					);
					while(bigK==0,
						k=k-1;
						yT=(t*t+d*u*u)*yC/2-yP;
						yP=yC;
						yC=yT;
						if(yC>1,
							bigK=k;
						);
						if(k<-20,
							print("stop now: a=",a,", d=",d,", t=",t,", u=",u,", bigK=",bigK,", y_K=",yC);
							return();
						);
					);
					if(bigK<-1,
						if(bigK!=-2 || d!=a*a+4 || t!=a || u!=1,
							if(bigK!=-2 || d!=a*a+1 || t!=2*a || u!=2,
								print("norm +1: a=",a,", d=",d,", t=",t,", u=",u,", bigK=",bigK,", y_K=",yC,", yM1=",yM1);
							);
						);
					);
					if(bigK==-2 && d==a*a+4 && t==a && u==1 && bigK!=-2,
						print("BAD norm +1: a=",a,", d=",d,", t=",t,", u=",u,", bigK=",bigK,", y_K=",yC);
						return();
					);
					if(bigK==-2 && d==a*a+1 && t==2*a && u==2 && bigK!=-2,
						print("BAD norm +1: a=",a,", d=",d,", t=",t,", u=",u,", bigK=",bigK,", y_K=",yC);
						return();
					);
				);
			);
		);
	);
}
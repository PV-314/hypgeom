
check1(dbg=0)={
	my(aUB,c1,c2,c3,nrmA,t,t2a,t2b,u,y0,yLB,yM1,yM2,yP1,yP2);

	c1=0;	
	c2=0;
	c3=0;
	u=1;
	for(d=112,342,
		if(!issquare(d),
			aUB=sqrt(d);
			for(a=1,aUB,
				nrmA=a*a-d;
				if(nrmA%2==1 && nrmA!=0 && issquare(-nrmA),
					yLB=34.25*abs(nrmA)*sqrt(abs(nrmA)/d); \\ for nrmA odd only!
					c1=c1+1;
					t2a=d+4;
					if(issquare(t2a),
						c2=c2+1;
						t=sqrtint(t2a);
						if((t-a*u)*(t+a*u)==abs(nrmA)+4,
							c3=c3+1;
							y0=1;
							yM1=((t*t+d*u*u)-2*a*t*u)/4;
							yM2=(t*t+d*u*u)*yM1/2-y0;
							yP1=((t*t+d*u*u)+2*a*t*u)/4;
							yP2=(t*t+d*u*u)*yP1/2-y0;
							if(yM2<yLB || yP2<yLB,
								printf("AN EXAMPLE!" );
							);
							printf("(+4): c1=%3d, c2=%2d, c3=%2d, d=%3d, a=%3d, nrmA=%4d, t=%2d, YM1=%11.6f, YP1=%11.6f, YM2=%13.6f, YP2=%13.6f, yLB=%11.6f\n",c1,c2,c3,d,a,nrmA,t,yM1,yP1,yM2,yP2,yLB);
						);
						
					);
					t2b=d-4;
					if(issquare(t2b),
						c2=c2+1;
						t=sqrtint(t2b);
						if((t-a*u)*(t+a*u)==abs(nrmA)-4,
							c3=c3+1;
							y0=1;
							yM1=((t*t+d*u*u)-2*a*t*u)/4;
							yM2=(t*t+d*u*u)*yM1/2-y0;
							yP1=((t*t+d*u*u)+2*a*t*u)/4;
							yP2=(t*t+d*u*u)*yP1/2-y0;
							if(yM2<yLB || yP2<yLB,
								printf("AN EXAMPLE!" );
							);
							printf("(-4): c1=%3d, c2=%2d, c3=%2d, d=%3d, a=%3d, nrmA=%4d, t=%2d, YM1=%11.6f, YP1=%11.6f, YM2=%13.6f, YP2=%13.6f, yLB=%11.6f\n",c1,c2,c3,d,a,nrmA,t,yM1,yP1,yM2,yP2,yLB);
						);
					);
				);
			);
		);
	);
	print("c1=",c1,", c2=",c2,", c3=",c3);
}
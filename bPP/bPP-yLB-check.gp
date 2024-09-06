read("hypgeom\\general\\hypg-utils.gp");

\\ b a prime power (so this is for part (a) of the y lower bound lemma)
\\ 4 Sept 2023
search_bPP_all()={
	forstep(b=1,10000000,1,
		if(b==1 || isprimepower(b),
			search_bPP(b);
		);
	);
}

\\ 4 Sept 2023
search_bPP(b)={
	my(b2,cnst,d,e,m4Soln,minV,p4Soln,sqrtD,t,u,vM1,vP1,yM1,yP1);

	if(b!=1 && !isprimepower(b),
		print("b=",factor(b),", is not a prime power");
		return();
	);
	minV=0.1;
	for(a=1,5000,
		\\if(a%1000==0,print("b=",b,", a=",a));
		d=a*a+b;
		m4Soln=solve_pell_minus4(d);
		p4Soln=solve_pell_plus4(d);
		if(length(m4Soln)>0 && m4Soln[2]<10000,
			t=m4Soln[1];
			u=m4Soln[2];
			
			yM1=((t-a*u)*(t-a*u)+b*u*u)/4;
			if(yM1>1 && issquare(yM1),
				doProofCaseCheck(-a,b,d,t,u,sqrtint(yM1));
				vM1=yM1/b/b;
				if(vM1<minV,
					minV=vM1;
					printf("SMALL M4: a=%6d, b=%4d, d=%9d, t=%6d, u=%6d, yM1=%6d, v=%9.5f, 1/v=%9.5f\n",a,b,d,t,u,yM1,minV,1/minV);
				);
			);
			yP1=((t+a*u)*(t+a*u)+b*u*u)/4;
			if(yP1>1 && issquare(yP1),
				doProofCaseCheck(a,b,d,t,u,sqrtint(yP1));
				vP1=yP1/b/b;
				if(vP1<minV,
					minV=vP1;
					printf("SMALL M4: a=%6d, b=%4d, d=%9d, t=%6d, u=%6d, yP1=%6d, v=%9.5f, 1/v=%9.5f\n",a,b,d,t,u,yP1,minV,1/minV);
				);
			);
		);
		if(length(p4Soln)>0 && p4Soln[2]<10000,
			t=p4Soln[1];
			u=p4Soln[2];
			sqrtD=sqrt(d);
			e=(t+u*sqrtD)/2;
			
			yM1=((t-a*u)*(t-a*u)+b*u*u)/4;
			if(yM1>1 && issquare(yM1),
				doProofCaseCheck(-a,b,d,t,u,sqrtint(yM1));
				vM1=yM1/b/b;
				if(vM1<minV,
					minV=vM1;
					printf("SMALL P4: a=%6d, b=%4d, d=%9d, t=%6d, u=%6d, yM1=%6d, v=%9.5f, 1/v=%9.5f\n",a,b,d,t,u,yM1,minV,1/minV);
				);
			);
			yP1=((t+a*u)*(t+a*u)+b*u*u)/4;
			if(yP1>1 && issquare(yP1),
				doProofCaseCheck(a,b,d,t,u,sqrtint(yP1));
				vP1=yP1/b/b;
				if(vP1<minV,
					minV=vP1;
					printf("SMALL P4: a=%6d, b=%4d, d=%9d, t=%6d, u=%6d, yP1=%6d, v=%9.5f, 1/v=%9.5f\n",a,b,d,t,u,yP1,minV,1/minV);
				);
			);
		);
	);
}

\\ remember that y=sqrt(y_k)
\\ 20 Dec 2023
doProofCaseCheck(a,b,d,t,u,y,dbg=0)={
	my(bDivs,b1,b2,g1,g2,is23Checked,is24Checked,is25Checked,is26Checked,isChecked,r,s,yv1,yv2);
	
	g1=gcd((t+a*u)*(t+a*u),b*u*u);
	if(g1!=1 && g1!=4,
		printf("BAD g1=%3d: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: 4*nrmE:=%6: y:=%6d: k=%2d\n",g1,a,b,d,t,u,(t*t-d*u*u)/4,y,a/abs(a));
		return();
	);
	if(g1==1 && b%2==0,
		printf("BAD g1=1, but b even: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: 4*nrmE:=%6: y:=%6d: k=%2d\n",g1,a,b,d,t,u,(t*t-d*u*u)/4,y,a/abs(a));
		return();
	);
	isChecked=0;
	yv1=2*y-(t+a*u);
	yv2=2*y+(t+a*u);
	g2=gcd(yv1,yv2);
	bDivs=divisors(b);
	if(g1==1 && gcd(yv1,yv2)==1,
		if(b%2==0,
			printf("BAD b even for eqn (2.3): g1:=%4d: a:=%6d: b:=%5d: d:=%9d: t:=%8d: u:=%6d: nrmE:=%3d: y:=%6d: k:=%2d: g2:=%3d:\n",g1,a,b,d,t,u,(t*t-d*u*u)/4,y,a/abs(a),g2);
			return();
		);
		for(i=1,length(bDivs),
			b1=bDivs[i];
			b2=b/b1;
			if(yv1%b1==0 && issquare(yv1/b1) && yv2%b2==0 && issquare(yv2/b2),
				r=sqrtint(yv1/b1);
				s=sqrtint(yv2/b2);
				if((y*y)/(b*b/16)<1.5,
					printf("SMALL y for eqn (2.3) : a:=%6d: b:=%5d: d:=%9d: t:=%8d: u:=%6d: nrmE:=%3d: y:=%6d: ykb2Ratio:=%9.6f: k:=%2d: b1:=%4d: r:=%4d: b2:=%5d: s:=%4d: g1:=%2d: g2:=%2d:\n",a,b,d,t,u,(t*t-d*u*u)/4,y,y*y/b^2,a/abs(a),b1,r,b2,s,g1,g2);
				);
				isChecked=1;
			);
		);
	);
	if(g1==1 && gcd(yv1,yv2)!=1,
		printf("BAD g1=%4d but gcd(yv1,yv2)=%2d: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: nrmE:=%3d: y:=%6d: k=%2d\n",g1,gcd(yv1,yv2),a,b,d,t,u,(t*t-d*u*u)/4,y,a/abs(a));
		return();
	);
	if(g1==4,
		g22=gcd(1024*1024,g2);
		if(g2!=g22,
			printf("BAD(1) g2=%6d, v_2(g2)=%3d for g1=%4d: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: nrmE:=%3d: y:=%6d: k=%2d\n",g2,get_val(g2,2),g1,a,b,d,t,u,(t*t-d*u*u)/4,y,a/abs(a));
			return();
		);
		if(g2!=2 && g2!=4,
			printf("BAD(2) g2=%6d, v_2(g2)=%3d for g1=%4d: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: nrmE:=%3d: y:=%6d: k=%2d\n",g2,get_val(g2,2),g1,a,b,d,t,u,(t*t-d*u*u)/4,y,a/abs(a));
			return();
		);
		
		if(g2==4,
			is24Checked=0;
			for(i=1,length(bDivs),
				b1=bDivs[i];
				b2=b/b1;
				if(yv1%b1==0 && issquare(yv1/b1) && yv2%b2==0 && issquare(yv2/b2),
					r=sqrtint(yv1/b1);
					s=sqrtint(yv2/b2);
					
					if((gcd(r*r,s*s)==4 && gcd(b1,b2)==1) || (gcd(r*r,s*s)==1 && 4%gcd(b1,b2)==0),
						isChecked=1;
						is24Checked=1;
						if(gcd(r*r,s*s)==4 && gcd(b1,b2)==1 && (y*y)/(b*b)<2,
							printf("SMALL y for eqn (2.4)a: a:=%6d: b:=%5d: d:=%9d: t:=%8d: u:=%6d: nrmE:=%3d: y:=%6d: ykb2Ratio:=%9.6f: k:=%2d: b1:=%4d: r:=%4d: b2:=%5d: s:=%4d: g1:=%2d: g2:=%2d:\n",a,b,d,t,u,(t*t-d*u*u)/4,y,y*y/b^2,a/abs(a),b1,r,b2,s,g1,g2);
						);
						if(gcd(r*r,s*s)==1 && gcd(b1,b2)==1 && (y*y)/(b*b/16)<2,
							printf("SMALL y for eqn (2.4)b: a:=%6d: b:=%5d: d:=%9d: t:=%8d: u:=%6d: nrmE:=%3d: y:=%6d: ykb2Ratio:=%9.6f: k:=%2d: b1:=%4d: r:=%4d: b2:=%5d: s:=%4d: g1:=%2d: g2:=%2d:\n",a,b,d,t,u,(t*t-d*u*u)/4,y,y*y/b^2,a/abs(a),b1,r,b2,s,g1,g2);
						);
						if(gcd(r*r,s*s)==1 && gcd(b1,b2)==2 && (y*y)/(b*b/64)<4,
							printf("SMALL y for eqn (2.4)c: a:=%6d: b:=%5d: d:=%9d: t:=%8d: u:=%6d: nrmE:=%3d: y:=%6d: ykb2Ratio:=%9.6f: k:=%2d: b1:=%4d: r:=%4d: b2:=%5d: s:=%4d: g1:=%2d: g2:=%2d:\n",a,b,d,t,u,(t*t-d*u*u)/4,y,y*y/b^2,a/abs(a),b1,r,b2,s,g1,g2);
						);
						if(gcd(r*r,s*s)==1 && gcd(b1,b2)==4 && (y*y)/(b*b/256)<5,
							printf("SMALL y for eqn (2.4)d: a:=%6d: b:=%5d: d:=%9d: t:=%8d: u:=%6d: nrmE:=%3d: y:=%6d: ykb2Ratio:=%9.6f: k:=%2d: b1:=%4d: r:=%4d: b2:=%5d: s:=%4d: g1:=%2d: g2:=%2d:\n",a,b,d,t,u,(t*t-d*u*u)/4,y,y*y/b^2,a/abs(a),b1,r,b2,s,g1,g2);
						);
					);
					if(!(gcd(r*r,s*s)==4 && gcd(b1,b2)==1) && !(gcd(r*r,s*s)==1 && gcd(b1,b2)==4) && !(gcd(r*r,s*s)==1 && gcd(b1,b2)==2) && !(gcd(r*r,s*s)==1 && gcd(b1,b2)==1),
						printf("BAD eq'n (2.4): g2=%3d for g1=4: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: y:=%6d: k:=%2d: r=%4d, s=%4d, b1=%4d, b2=%4d, gcd(r*r,s*s)=%2d, gcd(b1,b2)=%2d\n",g2,a,b,d,t,u,y,a/abs(a),r,s,b1,b2,gcd(r*r,s*s),gcd(b1,b2));
					);
				);
			);
			if(is24Checked==0,
				printf("BAD eq'n (2.4) unchecked: g2=%3d for g1=%2d: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: y:=%6d: k=%2d\n",g2,g1,a,b,d,t,u,y,a/abs(a));
				return();
			);
		);

		\\ this case does occur:
		\\ eq'n (2.5): g2=  2 for g1=4: a:=     2: b:=  13: d:=       17: t:=     8: u:=     2: y:=     7: k= 1
		\\ eq'n (2.5): g2=  2 for g1=4: a:=    16: b:=  13: d:=      269: t:=   164: u:=    10: y:=   163: k= 1
		if(g2==2 && b%2==1,
			\\printf("eq'n (24): g2=%3d for g1=4: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: y:=%6d: k=%2d\n",g2,a,b,d,t,u,y,a/abs(a));
			is25Checked=0;
			bDivs=divisors(b);
			for(i=1,length(bDivs),
				b1=bDivs[i];
				b2=b/b1;
				if(yv1%(2*b1)==0 && issquare(yv1/(2*b1)) && yv2%(2*b2)==0 && issquare(yv2/(2*b2)),
					r=sqrtint(yv1/(2*b1));
					s=sqrtint(yv2/(2*b2));
					if(gcd(b1*r*r,b2*s*s)==1,
						isChecked=1;
						is25Checked=1;
						if((y*y)/(b*b/4)<1.004,
							printf("SMALL y for eqn (2.5) : a:=%6d: b:=%5d: d:=%9d: t:=%8d: u:=%6d: nrmE:=%3d: y:=%6d: ykb2Ratio:=%9.6f: k:=%2d: b1:=%4d: r:=%4d: b2:=%5d: s:=%4d: g1:=%2d: g2:=%2d:\n",a,b,d,t,u,(t*t-d*u*u)/4,y,y*y/b^2,a/abs(a),b1,r,b2,s,g1,g2);
						);
					);
					if(gcd(b1*r*r,b2*s*s)!=1,
						printf("BAD eq'n (2.5): g2=%3d for g1=4: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: y:=%6d: k:=%2d: gcd(b1*r*r,b2*s*s)=%2d\n",g2,a,b,d,t,u,y,a/abs(a),gcd(b1*r*r,b2*s*s));
					);
				);
			);
			if(is25Checked==0,
				printf("BAD eq'n (2.5) unchecked: g2=%3d for g1=4: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: y:=%6d: k=%2d\n",g2,a,b,d,t,u,y,a/abs(a));
			);
		);

		if(g2==2 && b%2==0,
			if(dbg!=0,
				printf("eq'n (2.6): g2=%3d for g1=%2d: a:=%6d: b:=%5d: bMod8:=%2d: d:=%9d: t:=%6d: u:=%6d: y:=%6d: y^2/b^2:=%9.6f: b^2/y^2:=%9.6f: k:=%2d:\n",g2,g1,a,b,b%8,d,t,u,y,1.0*y*y/b/b,1.0*b*b/y/y,a/abs(a));
			);
			is26Checked=0;
			bDivs=divisors(b);
			for(i=1,length(bDivs),
				b1=bDivs[i];
				b2=b/b1;
				if(yv1%b1==0 && issquare(yv1/b1) && yv2%b2==0 && issquare(yv2/b2),
					r=sqrtint(yv1/b1);
					s=sqrtint(yv2/b2);
					if(gcd(b1*r*r,b2*s*s)==2 && gcd(b1,b2)==2,
						isChecked=1;
						is26Checked=1;
						if((y*y)/(b*b/64)<4,
							printf("SMALL y for eqn (2.6) : a:=%6d: b:=%5d: d:=%9d: t:=%8d: u:=%6d: nrmE:=%3d: y:=%6d: ykb2Ratio:=%9.6f: k:=%2d: b1:=%4d: r:=%4d: b2:=%5d: s:=%4d: g1:=%2d: g2:=%2d:\n",a,b,d,t,u,(t*t-d*u*u)/4,y,y*y/b^2,a/abs(a),b1,r,b2,s,g1,g2);
						);
					);
				);
			);
			if(is26Checked==0,
				printf("BAD eq'n (2.6) unchecked: g2=%3d for g1=%2d: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: y:=%6d: k=%2d\n",g2,g1,a,b,d,t,u,y,a/abs(a));
			);
		);
		
		if(isChecked==0,
			printf("BAD unchecked: g2=%3d for g1=%2d: a:=%6d: b:=%5d: d:=%9d: t:=%6d: u:=%6d: y:=%6d: k=%2d\n",g2,g1,a,b,d,t,u,y,a/abs(a));
		);
	);
}

\\ for b=4*p^m
\\ 4 Sept 2023
search_b2_all()={
	for(b=2,10000,
		b2=gcd(65536*65536*65536*65536,b);
		if(b2==4 && (b/b2==1 || isprimepower(b/b2)),
			search_b2(b);
		);
	);
}

\\ 4 Sept 2023
search_b2(b)={
	my(b2,cnst,d,t,u,yM1,yP1);

	b2=gcd(65536*65536*65536*65536,b);
	if(b/b2!=1 && !isprimepower(b/b2),
		print("b=",factor(b),", is not of the form 2^ell*p^m");
		return();
	);
	minV=0.1;
	for(d=1,3000000,
		a2=d-b;
		if(issquare(a2),
			a=sqrtint(a2);
			uUB=sqrt(d)/2;
			for(u=1,uUB,
				v=d*u*u-4;
				if(!issquare(d) && issquare(v),
					t=sqrtint(v);
					yM1=((t-a*u)*(t-a*u)+b*u*u)/4;
					yP1=((t+a*u)*(t+a*u)+b*u*u)/4;
					if(yM1>1 && issquare(yM1),
						vM1=yM1/b/b;
						if(vM1<minV,
							minV=vM1;
							printf("M4: a=%6d, b=%4d, d=%9d, t=%6d, u=%6d, yM1=%6d, v=%9.5f, 1/v=%9.5f\n",a,b,d,t,u,yM1,minV,1/minV);
						);
					);
					if(yP1>1 && issquare(yP1),
						vP1=yP1/b/b;
						if(vP1<minV,
							minV=vP1;
							printf("M4: a=%6d, b=%4d, d=%9d, t=%6d, u=%6d, yP1=%6d, v=%9.5f, 1/v=%9.5f\n",a,b,d,t,u,yP1,minV,1/minV);
						);
					);
				);
				v=d*u*u+4;
				if(!issquare(d) && issquare(v),
					t=sqrtint(v);
					yM1=((t-a*u)*(t-a*u)+b*u*u)/4;
					yP1=((t+a*u)*(t+a*u)+b*u*u)/4;
					if(yM1>1 && issquare(yM1),
						vM1=yM1/b/b;
						if(vM1<minV,
							minV=vM1;
							printf("P4: a=%6d, b=%4d, d=%9d, t=%6d, u=%6d, yM1=%6d, v=%9.5f, 1/v=%9.5f\n",a,b,d,t,u,yM1,minV,1/minV);
						);
					);
					if(yP1>1 && issquare(yP1),
						vP1=yP1/b/b;
						if(vP1<minV,
							minV=vP1;
							printf("P4: a=%6d, b=%4d, d=%9d, t=%6d, u=%6d, yP1=%6d, v=%9.5f, 1/v=%9.5f\n",a,b,d,t,u,yP1,minV,1/minV);
						);
					);
				);
			);
		);
	);
}

\\ initial search for the small y_k when b is a prime power, where the solutions are like in these examples:
\\ this function is based on these examples:
\\ SMALL y for eqn (2.3) : a:=   685: b:= 71647: d:=   540872: t:=   18386: u:=    25: nrmE:= -1: y:= 18068: ykb2Ratio:= 0.063595: k:= 1: b1:=   1: r:=  25: b2:=71647: s:=   1: g1:= 1: g2:= 1:
\\ SMALL y for eqn (2.3) : a:=   353: b:= 19207: d:=   143816: t:=    4930: u:=    13: nrmE:= -1: y:=  4844: ykb2Ratio:= 0.063605: k:= 1: b1:=   1: r:=  13: b2:=19207: s:=   1: g1:= 1: g2:= 1:
\\ i.e.,
\\ 2y-(t+a*u)=b1*r*r, with b1=1, r=u
\\ and 2*y+(t+a*u)=b2*s*s, with b2=b, s=1
\\ restart:tv:=(b-2*a*u-u*u)/2:expand(tv^2-(a*a+b)*u^2);factor(4*%);
\\ 28 Aug 2024
search_parta_1()={
	my(t,v,yk);
	
	for(u=1,300,
		u2=u*u;
		u3=u2*u;
		u4=u3*u;
		if(u%2==1,print("starting u=",u));
		for(a=1,1500,
		for(b=1,100000,
			v=b*b-4*b*a*u-6*b*u2+4*a*u3+u4;
			if(abs(v)==16,
				t=(b-2*a*u-u2)/2;
				if(t>0 && denominator(t)==1,
					yk=(t+a*u)*(t+a*u)+b*u2;
					if(yk%4==0 && issquare(yk),
						yk=yk/4;
						printf("a=%4d, b=%6d, t=%6d, u=%3d, y_k=%9d, y_k/b^2=%9.6f\n",a,b,t,u,yk,yk/b/b);
					);
				);
			);
		);
		);
	);
}
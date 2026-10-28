read("..\..\..\general\pari\quartic-solver.gp");

\\ call the following three functions, for b=5,13,17, respectively
\\ check_b5()
\\ check_b13()
\\ check_b17()
\\ the other functions are only for use with these four functions

check_d_n(d,nrmA,dbg=0)={
	my(allSolns,bfSolns,cSoln,startTime);
	
	startTime=getwalltime();
	print("\nd=",d,", nrmA=",nrmA,": ",factor(nrmA));
	if(issquare(-nrmA),
		soln=quartic_thue_solve(d,nrmA,dbg);
		allSolns=Set();
		for(i=1,length(soln),
			cSoln=soln[i];
			if(cSoln[1]>0 && cSoln[2]>0,
				allSolns=setunion(allSolns,[cSoln]);
			);
		);
		bfSolns=qt_test_brute(d,nrmA,dbg);
		print("Number of solutions=",length(allSolns),", allSolns=",allSolns,", time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
		if(length(allSolns)!=length(bfSolns),
			print("CHECK: length(allSolns)=",length(allSolns),", length(bfSolns)=",length(bfSolns));
			print("allSolns=",allSolns);
			print("bfSolns=",bfSolns);
			return();
		);
		for(i=1,length(allSolns),
			ind=setsearch(bfSolns,allSolns[i]);
			if(ind==0,
				print("BAD: could not find allSolns[i]=",allSolns[i]," in bfSolns");
			);
		);
		if(length(allSolns)>3,
			print("BIG!!");
			return();
		);
	);
}

qt_test_brute(d,n,dbg=0)={
	my(solns,x,x2,yUB);

	solns=Set();
	yUB=10*1000*1000;
	for(y=1,yUB,
		x2=d*y*y*y*y+n;
		if (x2>0 && issquare(x2),
			x=sqrtint(x2);
			solns=setunion(solns,[[x,y]]);
		);
	);
	return(solns);
};

check_b5()={
	my(d,dbg,nrmA,startTime);

	dbg=1;
	startTime=getwalltime();
	\\ u=1
	d=5;nrmA=-1444;check_d_n(d,nrmA,dbg);
	d=8;nrmA=-2500;check_d_n(d,nrmA,dbg);
	d=13;nrmA=-5625;check_d_n(d,nrmA,dbg);
	d=32;nrmA=-10000;check_d_n(d,nrmA,dbg);
	d=533;nrmA=-148225;check_d_n(d,nrmA,dbg);
	
	\\ u=2
	d=2;nrmA=-625;check_d_n(d,nrmA,dbg);
	d=8;nrmA=-2500;check_d_n(d,nrmA,dbg);
	
	\\ u=4
	d=2;nrmA=-625;check_d_n(d,nrmA,dbg);
	print("total b=5 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b13()={
	my(d,dbg,nrmA,startTime);
	
	dbg=1;
	startTime=getwalltime();
	\\ u=1
	d=8;nrmA=-114244;check_d_n(d,nrmA,dbg);
	d=13;nrmA=-257049;check_d_n(d,nrmA,dbg);
	d=32;nrmA=-456976;check_d_n(d,nrmA,dbg);

	\\ u=2
	d=2;nrmA=-28561;check_d_n(d,nrmA,dbg);
	d=8;nrmA=-114244;check_d_n(d,nrmA,dbg);
	
	\\ u=4
	d=2;nrmA=-28561;check_d_n(d,nrmA,dbg);
	print("total b=13 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b17(dbg=0)={
	my(d,dbg,nrmA,startTime);
	
	dbg=1;
	startTime=getwalltime();
	\\ u=1
	d=8;nrmA=-334084;check_d_n(d,nrmA,dbg);
	d=8;nrmA=-56644;check_d_n(d,nrmA,dbg);
	d=13;nrmA=-751689;check_d_n(d,nrmA,dbg);
	d=32;nrmA=-1336336;check_d_n(d,nrmA,dbg);
	d=580;nrmA=-3041536;check_d_n(d,nrmA,dbg);

	\\ u=2
	d=2;nrmA=-83521;check_d_n(d,nrmA,dbg);
	d=2;nrmA=-14161;check_d_n(d,nrmA,dbg);
	\\d=8;nrmA=-334084;check_d_n(d,nrmA,dbg);
	d=145;nrmA=-760384;check_d_n(d,nrmA,dbg);
	
	\\ u=4
	\\d=2;nrmA=-83521;check_d_n(d,nrmA,dbg);
	print("total b=17 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

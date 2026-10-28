read("..\..\..\general\pari\quartic-solver.gp");

\\ call the following four functions, for b=1,2,3,4, respectively
\\ check_b1()
\\ check_b2()
\\ check_b3()
\\ check_b4()
\\ the other functions are only for use with these four functions

check_d_n(d,nrmA,dbg=0)={
	my(allSolns,bfSolns,cSoln,startTime);
	
	startTime=getwalltime();
	print("\nd=",d,", nrmA=",nrmA,": ",factor(nrmA));
	nrmAOdd=-nrmA/gcd(nrmA,65536*65536*65536);
	if(!isprimepower(nrmAOdd) && !issquare(-nrmA) && nrmAOdd!=1,
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

\\ just for comparison
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

\\ the variables a,b,t,u are only here so the source sequences can be identified
check_b1()={
	my(a,b,d,dbg,nrmA,startTime,u);

	dbg=1;
	startTime=getwalltime();
	a=     1;b= 1;d=         8;t=     2;u= 1;nrmA=     -7;check_d_n(d,nrmA,dbg);
	a=     1;b= 1;d=        12;t=     4;u= 1;nrmA=    -11;check_d_n(d,nrmA,dbg);
	a=     2;b= 1;d=         8;t=     2;u= 1;nrmA=     -4;check_d_n(d,nrmA,dbg);
	a=     2;b= 1;d=        13;t=     3;u= 1;nrmA=     -9;check_d_n(d,nrmA,dbg);
	print("total b=1 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b2()={
	my(a,b,d,dbg,nrmA,startTime,u);
	
	dbg=1;
	startTime=getwalltime();
	\\ u=1
	a=     1;b= 2;d=         8;t=     2;u= 1;nrmA=   -127;check_d_n(d,nrmA,dbg);
	a=     2;b= 2;d=        12;t=     4;u= 1;nrmA=   -188;check_d_n(d,nrmA,dbg);
	a=     3;b= 2;d=        13;t=     3;u= 1;nrmA=   -199;check_d_n(d,nrmA,dbg);
	a=     4;b= 2;d=         8;t=     2;u= 1;nrmA=   -112;check_d_n(d,nrmA,dbg);
	a=     4;b= 2;d=        12;t=     4;u= 1;nrmA=   -176;check_d_n(d,nrmA,dbg);
	a=     5;b= 2;d=        60;t=     8;u= 1;nrmA=   -935;check_d_n(d,nrmA,dbg);
	a=     6;b= 2;d=         5;t=     1;u= 1;nrmA=    -44;check_d_n(d,nrmA,dbg);
	a=     6;b= 2;d=        12;t=     4;u= 1;nrmA=   -156;check_d_n(d,nrmA,dbg);
	a=     6;b= 2;d=        60;t=     8;u= 1;nrmA=   -924;check_d_n(d,nrmA,dbg);
	a=     6;b= 2;d=       148;t=    12;u= 1;nrmA=  -2332;check_d_n(d,nrmA,dbg);
	a=     7;b= 2;d=         5;t=     1;u= 1;nrmA=    -31;check_d_n(d,nrmA,dbg);
	a=     8;b= 2;d=         8;t=     2;u= 1;nrmA=    -64;check_d_n(d,nrmA,dbg);
	a=     8;b= 2;d=        13;t=     3;u= 1;nrmA=   -144;check_d_n(d,nrmA,dbg);
	a=    16;b= 2;d=       533;t=    23;u= 1;nrmA=  -8272;check_d_n(d,nrmA,dbg);
	a=    19;b= 2;d=        29;t=     5;u= 1;nrmA=   -103;check_d_n(d,nrmA,dbg);
	a=    23;b= 2;d=        53;t=     7;u= 1;nrmA=   -319;check_d_n(d,nrmA,dbg);
	a=   135;b= 2;d=      2120;t=    46;u= 1;nrmA= -15695;check_d_n(d,nrmA,dbg);

	\\ u=2
	a=     1;b= 2;d=         3;t=     4;u= 2;nrmA=    -47;check_d_n(d,nrmA,dbg);
	a=     2;b= 2;d=         2;t=     2;u= 2;nrmA=    -28;check_d_n(d,nrmA,dbg);
	a=     2;b= 2;d=         3;t=     4;u= 2;nrmA=    -44;check_d_n(d,nrmA,dbg);
	a=     3;b= 2;d=         3;t=     4;u= 2;nrmA=    -39;check_d_n(d,nrmA,dbg);
	a=     3;b= 2;d=        15;t=     8;u= 2;nrmA=   -231;check_d_n(d,nrmA,dbg);
	a=     3;b= 2;d=        37;t=    12;u= 2;nrmA=   -583;check_d_n(d,nrmA,dbg);
	a=     4;b= 2;d=         2;t=     2;u= 2;nrmA=    -16;check_d_n(d,nrmA,dbg);
	print("total b=2 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b3(dbg=0)={
	my(a,b,d,dbg,nrmA,startTime,u);
	
	dbg=1;
	startTime=getwalltime();
	\\ u=1
	a=     1;b= 3;d=         5;t=     1;u= 1;nrmA=   -404;check_d_n(d,nrmA,dbg);
	a=     1;b= 3;d=         5;t=     3;u= 1;nrmA=   -404;check_d_n(d,nrmA,dbg);
	a=     2;b= 3;d=         8;t=     2;u= 1;nrmA=   -644;check_d_n(d,nrmA,dbg);
	a=     2;b= 3;d=       221;t=    15;u= 1;nrmA= -17897;check_d_n(d,nrmA,dbg);
	a=     4;b= 3;d=        13;t=     3;u= 1;nrmA=  -1037;check_d_n(d,nrmA,dbg);
	a=     5;b= 3;d=         5;t=     1;u= 1;nrmA=   -380;check_d_n(d,nrmA,dbg);
	a=     5;b= 3;d=         5;t=     3;u= 1;nrmA=   -380;check_d_n(d,nrmA,dbg);
	a=     6;b= 3;d=         8;t=     2;u= 1;nrmA=   -612;check_d_n(d,nrmA,dbg);
	a=     6;b= 3;d=        13;t=     3;u= 1;nrmA=  -1017;check_d_n(d,nrmA,dbg);
	a=     6;b= 3;d=       229;t=    15;u= 1;nrmA= -18513;check_d_n(d,nrmA,dbg);
	a=     7;b= 3;d=         5;t=     1;u= 1;nrmA=   -356;check_d_n(d,nrmA,dbg);
	a=     8;b= 3;d=         5;t=     1;u= 1;nrmA=   -341;check_d_n(d,nrmA,dbg);
	a=     8;b= 3;d=         5;t=     3;u= 1;nrmA=   -341;check_d_n(d,nrmA,dbg);
	a=     9;b= 3;d=         8;t=     2;u= 1;nrmA=   -567;check_d_n(d,nrmA,dbg);
	a=     9;b= 3;d=        12;t=     4;u= 1;nrmA=   -891;check_d_n(d,nrmA,dbg);
	a=    10;b= 3;d=         5;t=     1;u= 1;nrmA=   -305;check_d_n(d,nrmA,dbg);
	a=    10;b= 3;d=         5;t=     3;u= 1;nrmA=   -305;check_d_n(d,nrmA,dbg);
	a=    10;b= 3;d=        53;t=     7;u= 1;nrmA=  -4193;check_d_n(d,nrmA,dbg);
	a=    12;b= 3;d=       148;t=    12;u= 1;nrmA= -11844;check_d_n(d,nrmA,dbg);
	a=    13;b= 3;d=         5;t=     1;u= 1;nrmA=   -236;check_d_n(d,nrmA,dbg);
	a=    14;b= 3;d=         5;t=     1;u= 1;nrmA=   -209;check_d_n(d,nrmA,dbg);
	a=    14;b= 3;d=         5;t=     3;u= 1;nrmA=   -209;check_d_n(d,nrmA,dbg);
	a=    15;b= 3;d=        40;t=     6;u= 1;nrmA=  -3015;check_d_n(d,nrmA,dbg);
	a=    16;b= 3;d=         5;t=     1;u= 1;nrmA=   -149;check_d_n(d,nrmA,dbg);
	a=    16;b= 3;d=         5;t=     3;u= 1;nrmA=   -149;check_d_n(d,nrmA,dbg);
	a=    17;b= 3;d=         5;t=     1;u= 1;nrmA=   -116;check_d_n(d,nrmA,dbg);
	a=    18;b= 3;d=         8;t=     2;u= 1;nrmA=   -324;check_d_n(d,nrmA,dbg);
	a=    18;b= 3;d=        13;t=     3;u= 1;nrmA=   -729;check_d_n(d,nrmA,dbg);
	a=    19;b= 3;d=         5;t=     1;u= 1;nrmA=    -44;check_d_n(d,nrmA,dbg);
	a=    20;b= 3;d=        29;t=     5;u= 1;nrmA=  -1949;check_d_n(d,nrmA,dbg);
	a=    21;b= 3;d=        12;t=     4;u= 1;nrmA=   -531;check_d_n(d,nrmA,dbg);
	a=    22;b= 3;d=        13;t=     3;u= 1;nrmA=   -569;check_d_n(d,nrmA,dbg);
	a=    24;b= 3;d=        13;t=     3;u= 1;nrmA=   -477;check_d_n(d,nrmA,dbg);
	a=    28;b= 3;d=        29;t=     5;u= 1;nrmA=  -1565;check_d_n(d,nrmA,dbg);
	a=    32;b= 3;d=        20;t=     4;u= 1;nrmA=   -596;check_d_n(d,nrmA,dbg);
	a=    32;b= 3;d=        85;t=     9;u= 1;nrmA=  -5861;check_d_n(d,nrmA,dbg);
	a=    34;b= 3;d=        40;t=     6;u= 1;nrmA=  -2084;check_d_n(d,nrmA,dbg);
	a=    36;b= 3;d=       533;t=    23;u= 1;nrmA= -41877;check_d_n(d,nrmA,dbg);
	a=    40;b= 3;d=        96;t=    10;u= 1;nrmA=  -6176;check_d_n(d,nrmA,dbg);
	a=    48;b= 3;d=        96;t=    10;u= 1;nrmA=  -5472;check_d_n(d,nrmA,dbg);
	a=    48;b= 3;d=       445;t=    21;u= 1;nrmA= -33741;check_d_n(d,nrmA,dbg);
	a=    50;b= 3;d=        68;t=     8;u= 1;nrmA=  -3008;check_d_n(d,nrmA,dbg);
	a=    50;b= 3;d=        85;t=     9;u= 1;nrmA=  -4385;check_d_n(d,nrmA,dbg);
	a=    55;b= 3;d=       221;t=    15;u= 1;nrmA= -14876;check_d_n(d,nrmA,dbg);
	a=    62;b= 3;d=        53;t=     7;u= 1;nrmA=   -449;check_d_n(d,nrmA,dbg);
	a=    70;b= 3;d=        68;t=     8;u= 1;nrmA=   -608;check_d_n(d,nrmA,dbg);
	a=    76;b= 3;d=        85;t=     9;u= 1;nrmA=  -1109;check_d_n(d,nrmA,dbg);
	a=    82;b= 3;d=        96;t=    10;u= 1;nrmA=  -1052;check_d_n(d,nrmA,dbg);
	a=    86;b= 3;d=       200;t=    14;u= 1;nrmA=  -8804;check_d_n(d,nrmA,dbg);
	a=    92;b= 3;d=       173;t=    13;u= 1;nrmA=  -5549;check_d_n(d,nrmA,dbg);
	a=   110;b= 3;d=       221;t=    15;u= 1;nrmA=  -5801;check_d_n(d,nrmA,dbg);
	a=   119;b= 3;d=       221;t=    15;u= 1;nrmA=  -3740;check_d_n(d,nrmA,dbg);
	a=   122;b= 3;d=       365;t=    19;u= 1;nrmA= -14681;check_d_n(d,nrmA,dbg);
	a=   214;b= 3;d=       733;t=    27;u= 1;nrmA= -13577;check_d_n(d,nrmA,dbg);
	a=   341;b= 3;d=      2597;t=    51;u= 1;nrmA= -94076;check_d_n(d,nrmA,dbg);
	a=   360;b= 3;d=      1940;t=    44;u= 1;nrmA= -27540;check_d_n(d,nrmA,dbg);
	a=   614;b= 3;d=      7573;t=    87;u= 1;nrmA=-236417;check_d_n(d,nrmA,dbg);
	a=   662;b= 3;d=      9805;t=    99;u= 1;nrmA=-355961;check_d_n(d,nrmA,dbg);
	a=   832;b= 3;d=     18229;t=   135;u= 1;nrmA=-784325;check_d_n(d,nrmA,dbg);
	a=  1166;b= 3;d=     17693;t=   133;u= 1;nrmA= -73577;check_d_n(d,nrmA,dbg);
	a= 12316;b= 3;d=   4941733;t=  2223;u= 1;nrmA=-248596517;check_d_n(d,nrmA,dbg);

	\\ u=2
	a=     1;b= 3;d=         2;t=     2;u= 2;nrmA=   -161;check_d_n(d,nrmA,dbg);
	a=     3;b= 3;d=         2;t=     2;u= 2;nrmA=   -153;check_d_n(d,nrmA,dbg);
	a=     6;b= 3;d=        37;t=    12;u= 2;nrmA=  -2961;check_d_n(d,nrmA,dbg);
	a=     9;b= 3;d=         2;t=     2;u= 2;nrmA=    -81;check_d_n(d,nrmA,dbg);
	a=    16;b= 3;d=         5;t=     4;u= 2;nrmA=   -149;check_d_n(d,nrmA,dbg);
	a=    17;b= 3;d=        10;t=     6;u= 2;nrmA=   -521;check_d_n(d,nrmA,dbg);
	a=    20;b= 3;d=        24;t=    10;u= 2;nrmA=  -1544;check_d_n(d,nrmA,dbg);
	a=    24;b= 3;d=        24;t=    10;u= 2;nrmA=  -1368;check_d_n(d,nrmA,dbg);
	a=    25;b= 3;d=        17;t=     8;u= 2;nrmA=   -752;check_d_n(d,nrmA,dbg);
	a=    35;b= 3;d=        17;t=     8;u= 2;nrmA=   -152;check_d_n(d,nrmA,dbg);
	a=    41;b= 3;d=        24;t=    10;u= 2;nrmA=   -263;check_d_n(d,nrmA,dbg);
	a=    43;b= 3;d=        50;t=    14;u= 2;nrmA=  -2201;check_d_n(d,nrmA,dbg);

	\\ u=4
	a=    10;b= 3;d=         6;t=    10;u= 4;nrmA=   -386;check_d_n(d,nrmA,dbg);
	a=    12;b= 3;d=         6;t=    10;u= 4;nrmA=   -342;check_d_n(d,nrmA,dbg);
	print("total b=3 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b4(dbg=0)={
	my(a,b,d,dbg,nrmA,startTime,u);
	
	dbg=1;
	startTime=getwalltime();
	\\ u=1
	a=     4;b= 4;d=         8;t=     2;u= 1;nrmA=  -2032;check_d_n(d,nrmA,dbg);
	a=     8;b= 4;d=        12;t=     4;u= 1;nrmA=  -3008;check_d_n(d,nrmA,dbg);
	a=     9;b= 4;d=         5;t=     1;u= 1;nrmA=  -1199;check_d_n(d,nrmA,dbg);
	a=     9;b= 4;d=         8;t=     2;u= 1;nrmA=  -1967;check_d_n(d,nrmA,dbg);
	a=    11;b= 4;d=         5;t=     1;u= 1;nrmA=  -1159;check_d_n(d,nrmA,dbg);
	a=    12;b= 4;d=        13;t=     3;u= 1;nrmA=  -3184;check_d_n(d,nrmA,dbg);
	a=    13;b= 4;d=         5;t=     1;u= 1;nrmA=  -1111;check_d_n(d,nrmA,dbg);
	a=    14;b= 4;d=         5;t=     1;u= 1;nrmA=  -1084;check_d_n(d,nrmA,dbg);
	a=    16;b= 4;d=         8;t=     2;u= 1;nrmA=  -1792;check_d_n(d,nrmA,dbg);
	a=    16;b= 4;d=        12;t=     4;u= 1;nrmA=  -2816;check_d_n(d,nrmA,dbg);
	a=    18;b= 4;d=        20;t=     4;u= 1;nrmA=  -4796;check_d_n(d,nrmA,dbg);
	a=    18;b= 4;d=       140;t=    12;u= 1;nrmA= -35516;check_d_n(d,nrmA,dbg);
	a=    20;b= 4;d=        60;t=     8;u= 1;nrmA= -14960;check_d_n(d,nrmA,dbg);
	a=    23;b= 4;d=         8;t=     2;u= 1;nrmA=  -1519;check_d_n(d,nrmA,dbg);
	a=    24;b= 4;d=         5;t=     1;u= 1;nrmA=   -704;check_d_n(d,nrmA,dbg);
	a=    24;b= 4;d=        12;t=     4;u= 1;nrmA=  -2496;check_d_n(d,nrmA,dbg);
	a=    24;b= 4;d=        60;t=     8;u= 1;nrmA= -14784;check_d_n(d,nrmA,dbg);
	a=    24;b= 4;d=       148;t=    12;u= 1;nrmA= -37312;check_d_n(d,nrmA,dbg);
	a=    25;b= 4;d=         5;t=     1;u= 1;nrmA=   -655;check_d_n(d,nrmA,dbg);
	a=    25;b= 4;d=        13;t=     3;u= 1;nrmA=  -2703;check_d_n(d,nrmA,dbg);
	a=    28;b= 4;d=         5;t=     1;u= 1;nrmA=   -496;check_d_n(d,nrmA,dbg);
	a=    30;b= 4;d=         5;t=     1;u= 1;nrmA=   -380;check_d_n(d,nrmA,dbg);
	a=    32;b= 4;d=         8;t=     2;u= 1;nrmA=  -1024;check_d_n(d,nrmA,dbg);
	a=    32;b= 4;d=        13;t=     3;u= 1;nrmA=  -2304;check_d_n(d,nrmA,dbg);
	a=    33;b= 4;d=         8;t=     2;u= 1;nrmA=   -959;check_d_n(d,nrmA,dbg);
	a=    35;b= 4;d=         8;t=     2;u= 1;nrmA=   -823;check_d_n(d,nrmA,dbg);
	a=    39;b= 4;d=        13;t=     3;u= 1;nrmA=  -1807;check_d_n(d,nrmA,dbg);
	a=    49;b= 4;d=        68;t=     8;u= 1;nrmA= -15007;check_d_n(d,nrmA,dbg);
	a=    50;b= 4;d=        20;t=     4;u= 1;nrmA=  -2620;check_d_n(d,nrmA,dbg);
	a=    54;b= 4;d=        12;t=     4;u= 1;nrmA=   -156;check_d_n(d,nrmA,dbg);
	a=    59;b= 4;d=        29;t=     5;u= 1;nrmA=  -3943;check_d_n(d,nrmA,dbg);
	a=    61;b= 4;d=        29;t=     5;u= 1;nrmA=  -3703;check_d_n(d,nrmA,dbg);
	a=    62;b= 4;d=       260;t=    16;u= 1;nrmA= -62716;check_d_n(d,nrmA,dbg);
	a=    63;b= 4;d=        53;t=     7;u= 1;nrmA=  -9599;check_d_n(d,nrmA,dbg);
	a=    64;b= 4;d=       533;t=    23;u= 1;nrmA=-132352;check_d_n(d,nrmA,dbg);
	a=    71;b= 4;d=        96;t=    10;u= 1;nrmA= -19535;check_d_n(d,nrmA,dbg);
	a=    76;b= 4;d=        29;t=     5;u= 1;nrmA=  -1648;check_d_n(d,nrmA,dbg);
	a=    81;b= 4;d=        32;t=     6;u= 1;nrmA=  -1631;check_d_n(d,nrmA,dbg);
	a=    81;b= 4;d=        68;t=     8;u= 1;nrmA= -10847;check_d_n(d,nrmA,dbg);
	a=    89;b= 4;d=       200;t=    14;u= 1;nrmA= -43279;check_d_n(d,nrmA,dbg);
	a=    92;b= 4;d=        53;t=     7;u= 1;nrmA=  -5104;check_d_n(d,nrmA,dbg);
	a=   113;b= 4;d=        60;t=     8;u= 1;nrmA=  -2591;check_d_n(d,nrmA,dbg);
	a=   133;b= 4;d=       229;t=    15;u= 1;nrmA= -40935;check_d_n(d,nrmA,dbg);
	a=   143;b= 4;d=        85;t=     9;u= 1;nrmA=  -1311;check_d_n(d,nrmA,dbg);
	a=   147;b= 4;d=       904;t=    30;u= 1;nrmA=-209815;check_d_n(d,nrmA,dbg);
	a=   171;b= 4;d=       125;t=    11;u= 1;nrmA=  -2759;check_d_n(d,nrmA,dbg);
	a=   210;b= 4;d=      1020;t=    32;u= 1;nrmA=-217020;check_d_n(d,nrmA,dbg);
	a=   315;b= 4;d=      1373;t=    37;u= 1;nrmA=-252263;check_d_n(d,nrmA,dbg);
	a=   540;b= 4;d=      2120;t=    46;u= 1;nrmA=-251120;check_d_n(d,nrmA,dbg);
	a=   541;b= 4;d=      2213;t=    47;u= 1;nrmA=-273847;check_d_n(d,nrmA,dbg);
	a=   600;b= 4;d=      1596;t=    40;u= 1;nrmA= -48576;check_d_n(d,nrmA,dbg);
	a=   640;b= 4;d=      1940;t=    44;u= 1;nrmA= -87040;check_d_n(d,nrmA,dbg);
	a=  1995;b= 4;d=     87612;t=   296;u= 1;nrmA=-18448647;check_d_n(d,nrmA,dbg);

	\\ u=2
	a=     2;b= 4;d=         2;t=     2;u= 2;nrmA=   -508;check_d_n(d,nrmA,dbg);
	a=     4;b= 4;d=         3;t=     4;u= 2;nrmA=   -752;check_d_n(d,nrmA,dbg);
	a=     8;b= 4;d=         2;t=     2;u= 2;nrmA=   -448;check_d_n(d,nrmA,dbg);
	a=     8;b= 4;d=         3;t=     4;u= 2;nrmA=   -704;check_d_n(d,nrmA,dbg);
	a=     9;b= 4;d=         5;t=     4;u= 2;nrmA=  -1199;check_d_n(d,nrmA,dbg);
	a=     9;b= 4;d=        35;t=    12;u= 2;nrmA=  -8879;check_d_n(d,nrmA,dbg);
	a=    10;b= 4;d=        15;t=     8;u= 2;nrmA=  -3740;check_d_n(d,nrmA,dbg);
	a=    12;b= 4;d=         3;t=     4;u= 2;nrmA=   -624;check_d_n(d,nrmA,dbg);
	a=    12;b= 4;d=        15;t=     8;u= 2;nrmA=  -3696;check_d_n(d,nrmA,dbg);
	a=    12;b= 4;d=        37;t=    12;u= 2;nrmA=  -9328;check_d_n(d,nrmA,dbg);
	a=    16;b= 4;d=         2;t=     2;u= 2;nrmA=   -256;check_d_n(d,nrmA,dbg);
	a=    25;b= 4;d=         5;t=     4;u= 2;nrmA=   -655;check_d_n(d,nrmA,dbg);
	a=    27;b= 4;d=         3;t=     4;u= 2;nrmA=    -39;check_d_n(d,nrmA,dbg);
	a=    31;b= 4;d=        65;t=    16;u= 2;nrmA= -15679;check_d_n(d,nrmA,dbg);
	a=   105;b= 4;d=       255;t=    32;u= 2;nrmA= -54255;check_d_n(d,nrmA,dbg);
	a=   270;b= 4;d=       530;t=    46;u= 2;nrmA= -62780;check_d_n(d,nrmA,dbg);
	a=   300;b= 4;d=       399;t=    40;u= 2;nrmA= -12144;check_d_n(d,nrmA,dbg);
	a=   320;b= 4;d=       485;t=    44;u= 2;nrmA= -21760;check_d_n(d,nrmA,dbg);

	\\ u=7
	a=   285;b= 4;d=      1788;t=   296;u= 7;nrmA=-376503;check_d_n(d,nrmA,dbg);
	print("total b=4 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

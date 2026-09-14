F := GF(2);
n := 10;
m := 6;
o := 4;
pL := 2;

function TruncatedCoeffBounded(n, pL, d)
	if d lt 0 then
		return 0;
	end if;
	if n eq 0 then
		return d eq 0 select 1 else 0;
	end if;

	maxj := Minimum(n, d div pL);
	ans := 0;
	for j in [0..maxj] do
		t := d - j*pL;
		ans +:= ((j mod 2) eq 0 select 1 else -1) * Binomial(n, j) * Binomial(n + t - 1, t);
	end for;
	return ans;
end function;

function PolyMulTrunc(A, B, maxDeg)
	C := [0 : i in [0..maxDeg]];
	da := #A - 1;
	db := #B - 1;
	for i in [0..Minimum(da, maxDeg)] do
		if A[i+1] eq 0 then
			continue;
		end if;
		limj := Minimum(db, maxDeg - i);
		for j in [0..limj] do
			if B[j+1] ne 0 then
				C[i+j+1] +:= A[i+1] * B[j+1];
			end if;
		end for;
	end for;
	return C;
end function;

function SeriesInverse(B, maxDeg)
	if not (#B ge 1 and B[1] eq 1) then
		error "SeriesInverse requires constant term 1";
	end if;

	C := [0 : i in [0..maxDeg]];
	C[1] := 1;
	degB := #B - 1;
	for d in [1..maxDeg] do
		s := 0;
		lim := Minimum(d, degB);
		for i in [1..lim] do
			if B[i+1] ne 0 then
				s +:= B[i+1] * C[d-i+1];
			end if;
		end for;
		C[d+1] := -s;
	end for;
	return C;
end function;

function BuildA(n, pL, maxDeg)
	A := [0 : i in [0..maxDeg]];
	for d in [0..maxDeg] do
		A[d+1] := TruncatedCoeffBounded(n, pL, d);
	end for;
	return A;
end function;

function BuildB(m, pL, maxDeg)
	B := [0 : i in [0..maxDeg]];
	B[1] := 1;
	for d in [1..maxDeg] do
		if (d mod 2) eq 0 then
			t := d div 2;
			B[d+1] := TruncatedCoeffBounded(m, pL, t);
		end if;
	end for;
	return B;
end function;

function BuildT1(n, m, pL, maxDeg)
	A := BuildA(n, pL, maxDeg);
	B := BuildB(m, pL, maxDeg);
	Binv := SeriesInverse(B, maxDeg);
	C := PolyMulTrunc(A, Binv, maxDeg);

	Cplus := [0 : i in [0..maxDeg]];
	active := true;
	for d in [0..maxDeg] do
		if active and C[d+1] ge 0 then
			Cplus[d+1] := C[d+1];
		else
			active := false;
			Cplus[d+1] := 0;
		end if;
	end for;
	return Cplus;
end function;

function SquarefreeExponentVectors(n, d)
	if n eq 1 then
		if d eq 0 then
			return [[0]];
		elif d eq 1 then
			return [[1]];
		else
			return [];
		end if;
	end if;

	res := [];
	if d ge 0 then
		tails0 := SquarefreeExponentVectors(n - 1, d);
		for t in tails0 do
			Append(~res, [0] cat t);
		end for;
	end if;
	if d ge 1 then
		tails1 := SquarefreeExponentVectors(n - 1, d - 1);
		for t in tails1 do
			Append(~res, [1] cat t);
		end for;
	end if;
	return res;
end function;

function ExpKey(v)
	return Sprint(v);
end function;

function BuildDegreeBasisData(n, d)
	basis := SquarefreeExponentVectors(n, d);
	idx := AssociativeArray();
	for i in [1..#basis] do
		idx[ExpKey(basis[i])] := i;
	end for;
	return basis, idx;
end function;

function BuildMacaulayMatrixDegree2(F, n, d, quadTermsList)
	basisD, idxD := BuildDegreeBasisData(n, d);
	Nd := #basisD;
	if Nd eq 0 then
		return Matrix(F, 0, 0, []), 0;
	end if;

	if d lt 2 then
		return Matrix(F, 0, Nd, []), Nd;
	end if;

	basisDm2, _ := BuildDegreeBasisData(n, d - 2);
	if #basisDm2 eq 0 then
		return Matrix(F, 0, Nd, []), Nd;
	end if;

	rows := [];
	for terms in quadTermsList do
		for u in basisDm2 do
			row := [F!0 : i in [1..Nd]];
			for t in terms do
				i := t[1];
				j := t[2];
				c := t[3];

				w := [u[k] : k in [1..n]];
				w[i] +:= 1;
				w[j] +:= 1;

				if w[i] ge 2 or w[j] ge 2 then
					continue;
				end if;

				key := ExpKey(w);
				if IsDefined(idxD, key) then
					row[idxD[key]] +:= c;
				end if;
			end for;
			Append(~rows, row);
		end for;
	end for;

	if #rows eq 0 then
		return Matrix(F, 0, Nd, []), Nd;
	end if;

	M := Matrix(F, #rows, Nd, &cat rows);
	return M, Nd;
end function;

// Quadratic terms are listed as <i, j, coefficient> with i <= j.
quadTermsList := [
	[
		<1,1,F!1>,<1,4,F!1>,<1,5,F!1>,<1,7,F!1>,<1,9,F!1>,<2,2,F!1>,<2,3,F!1>,<2,6,F!1>,<2,7,F!1>,<2,9,F!1>,<2,10,F!1>,
		<3,3,F!1>,<3,4,F!1>,<3,5,F!1>,<3,6,F!1>,<3,8,F!1>,<3,9,F!1>,<4,5,F!1>,<4,8,F!1>,<4,9,F!1>,<5,5,F!1>,<5,6,F!1>,<5,7,F!1>,
		<5,8,F!1>,<6,6,F!1>,<6,8,F!1>,<6,9,F!1>
	],
	[
		<1,1,F!1>,<1,4,F!1>,<1,7,F!1>,<1,9,F!1>,<2,3,F!1>,<2,4,F!1>,<2,5,F!1>,<2,7,F!1>,<2,10,F!1>,<3,3,F!1>,<3,5,F!1>,
		<3,8,F!1>,<3,9,F!1>,<4,5,F!1>,<4,7,F!1>,<5,6,F!1>,<5,7,F!1>,<6,8,F!1>,<6,9,F!1>
	],
	[
		<1,1,F!1>,<1,4,F!1>,<1,5,F!1>,<1,8,F!1>,<1,9,F!1>,<2,2,F!1>,<2,4,F!1>,<2,7,F!1>,<2,10,F!1>,<3,6,F!1>,<3,7,F!1>,
		<3,9,F!1>,<4,4,F!1>,<4,7,F!1>,<5,6,F!1>,<5,8,F!1>,<6,6,F!1>
	],
	[
		<1,2,F!1>,<1,5,F!1>,<1,8,F!1>,<1,9,F!1>,<1,10,F!1>,<2,2,F!1>,<2,5,F!1>,<2,6,F!1>,<2,8,F!1>,<2,10,F!1>,<3,4,F!1>,
		<3,7,F!1>,<3,9,F!1>,<3,10,F!1>,<4,5,F!1>,<4,7,F!1>,<4,8,F!1>,<5,5,F!1>,<5,6,F!1>,<5,7,F!1>,<5,9,F!1>,<6,7,F!1>
	],
	[
		<1,1,F!1>,<1,3,F!1>,<1,6,F!1>,<1,10,F!1>,<2,4,F!1>,<2,5,F!1>,<2,9,F!1>,<3,7,F!1>,<3,8,F!1>,<3,10,F!1>,<4,6,F!1>,
		<4,9,F!1>,<5,6,F!1>,<5,8,F!1>
	],
	[
		<1,2,F!1>,<1,3,F!1>,<1,4,F!1>,<1,7,F!1>,<1,8,F!1>,<1,9,F!1>,<1,10,F!1>,<2,4,F!1>,<2,5,F!1>,<2,6,F!1>,<2,10,F!1>,
		<3,3,F!1>,<3,6,F!1>,<3,9,F!1>,<3,10,F!1>,<4,5,F!1>,<4,6,F!1>,<4,7,F!1>,<4,8,F!1>,<4,10,F!1>,<5,6,F!1>,<5,7,F!1>,
		<5,8,F!1>,<5,9,F!1>,<6,9,F!1>,<6,10,F!1>
	]
];

printf "UOV(v=6, o=4, m=6, q=2), n=10 in A_2 = F_2[x]/<x_i^2>.\n";
T1 := BuildT1(n, m, pL, 5);
To := BuildA(o, pL, 5);
printf "d\trows\tcols\trank\tright_kernel_dim\tT1\tTo\n";
for d in [0..5] do
	M, Nd := BuildMacaulayMatrixDegree2(F, n, d, quadTermsList);
	rk := Rank(M);
	kr := Nd - rk;
	assert kr eq Dimension(Kernel(Transpose(M)));
	printf "%o\t%o\t%o\t%o\t%o\t%o\t%o\n", d, NumberOfRows(M), NumberOfColumns(M), rk, kr, T1[d+1], To[d+1];
end for;

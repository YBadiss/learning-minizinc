include "alldifferent_except_0.mzn";
include "exactly.mzn";

int: n; % number of court members
set of int: COURT = 1..n;
set of int: COURT0 = 0..n;
int: emperor = 1;
array[COURT] of int: rank;
array[COURT] of int: ability;

int: m; % number of horses
set of int: HORSE = 1..m;
set of int: HORSE0 = 0..m;
array[HORSE] of int: beauty;
array[HORSE] of int: speed;

array[COURT,HORSE] of int: enjoy;

array[HORSE0] of var COURT0: rider0;
array[COURT0] of var HORSE0: horse0;

constraint forall(i in COURT)(horse0[i] != 0 -> rider0[horse0[i]] = i);
constraint forall(i in HORSE)(rider0[i] != 0 -> horse0[rider0[i]] = i);
constraint alldifferent_except_0(rider0);
constraint alldifferent_except_0(horse0);

array[HORSE] of var COURT0: rider = [rider0[i] | i in HORSE];
array[COURT] of var HORSE0: horse = [horse0[i] | i in COURT];

array[COURT] of var int: happiness;
constraint forall(i in COURT)(horse0[i] == 0 -> happiness[i] = 0);
constraint forall(i in COURT)(horse0[i] != 0 -> happiness[i] = enjoy[i, horse0[i]]);
constraint forall(i in COURT)(happiness[i] >= 0);
constraint forall(i in COURT)(i != emperor -> happiness[emperor] > happiness[i]);

constraint forall(i, j in COURT)(rank[i] > rank[j] ->
                                                  beauty[horse0[i]] >= beauty[horse0[j]] \/ horse0[j] = 0);

% the emperor enjoys it the most
constraint happiness[emperor] = max(happiness);

array[HORSE,HORSE] of var bool: badConstraints;
constraint forall(i, j in HORSE)(badConstraints[i, j] = (speed[i] > speed[j] /\
                                                                                 ability[rider[i]] < ability[rider[j]] /\
                                                                                 rider[i] != 0));
var int: obj = sum(happiness) - (sum(i, j in HORSE)(bool2int(badConstraints[i, j])) * 100);

constraint exactly(max(n - m, 0), horse, 0);

solve maximize obj;
output ["horse = \(horse);\nobj = \(obj);\n"]; % ++ [if fix(badConstraints[i,j]) then "(\(i), \(j))" else "" endif | i, j in HORSE];
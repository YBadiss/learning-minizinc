int: n; % number of court members
set of int: COURT = 1..n;
int: emperor = 1;
array[COURT] of int: rank;
array[COURT] of int: ability;

int: m; % number of horses
set of int: HORSE = 1..m;
array[HORSE] of int: beauty;
array[HORSE] of int: speed;

array[COURT,HORSE] of int: enjoy;

int: the_min = min(m, n);

array[HORSE] of var COURT: rider;
array[COURT] of var HORSE: horse;

include "inverse.mzn";
constraint inverse(rider, horse);

array[COURT] of var int: happiness;
constraint forall(i in COURT)(happiness[i] = enjoy[i, horse[i]]);
constraint forall(i in COURT)(happiness[i] > 0);

constraint forall(i, j in COURT)(rank[i] > rank[j] -> beauty[horse[i]] >= beauty[horse[j]]);

% the emperor enjoys it the most
constraint happiness[emperor] = max(happiness);

array[HORSE,HORSE] of var bool: badConstraints;
constraint forall(i, j in HORSE)(badConstraints[i, j] = (speed[i] > speed[j] /\ ability[rider[i]] < ability[rider[j]]));
var int: obj = sum(happiness) - (sum(i in 1..m, j in i+1..m)(bool2int(badConstraints[i, j])) * 100);

solve maximize obj;
output ["horse = \(horse);\nobj = \(obj);"];
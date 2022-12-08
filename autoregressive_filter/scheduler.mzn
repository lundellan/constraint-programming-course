include "globals.mzn";
include "assignment4_1_3.dzn";

% Global variables
int : del_add; % Number of cycles to complete addition
int : del_mul; % Number of cycles to complete multiplication
int : number_add; % Number of additioners
int : number_mul; % Number of multipliers
int : n; % Number of operations
set of int : last;
set of int : add;
set of int : mul;
array[1..n] of set of int : dependencies;

int: maxCycles = n * del_mul;

% Maxamiala antalet möjliga cykler
array[1..n] of var 0..maxCycles : s;

% Totala kostnaden för alla operationer
array[1..n] of var 1..del_mul : total = [if i in mul then del_mul else del_add endif | i in 1..n];

% Antalet additions och multiplikations operationer
int: no_adds = length(set2array(add));
int: no_muls = length(set2array(mul));


% Kollar så att den totala tiden för en gren plus nuvarande exekvering är mindre än dependency tiden
constraint
  forall(i in 1..n)(
  	  forall(dep in dependencies[i]) (
  		   total[i] + s[i] <= s[dep]
    )
  );
  
% Starttider som kan varieras 
array[1..no_adds] of var 0..maxCycles: start_adds = [s[i] | i in 1..n where i in add];
array[1..no_muls] of var 0..maxCycles: start_muls = [s[i] | i in 1..n where i in mul];

% Durations
array[1..no_adds] of var 0..del_add: duration_adds = [del_add | i in 1..no_adds];
array[1..no_muls] of var 0..del_mul: duration_muls = [del_mul | i in 1..no_muls];

% Behövs enbart en additioner och multiplier alltid
array[1..no_adds] of var 0..1: needed_add = [1 | i in 1..no_adds];
array[1..no_muls] of var 0..1: needed_mul = [1 | i in 1..no_muls];

var int: cost = max([s[l] + total[l] | l in last]);

% Starttiderna, durations, antalet ALUer som behövs, antalet tillgängliga ALUer totalt
constraint cumulative(start_adds, duration_adds, needed_add, number_add);
constraint cumulative(start_muls, duration_muls, needed_mul, number_mul);

solve minimize cost;

output([
  show(start_adds),
  show(start_muls),
  show(cost)
]);
include "urban_7.dzn";
include "globals.mzn";

int: n;
int: n_commercial;
int: n_residential;
array[1..n+1] of int: point_distribution;

% Position 0 innebär commercial, 1 residential (lex2 används för att undvika symmetrier)
array[1..n, 1..n] of var 0..1: placements; 
constraint lex2(placements);

% Antalet residentials i raderna
array[1..n] of var int: sum_rows; 
constraint forall(i in 1..n)(sum_rows[i] = sum(j in 1..n)(placements[i,j]));

% Antalet residentials i kolumnerna
array[1..n] of var int: sum_cols; 
constraint forall(i in 1..n)(sum_cols[i] = sum(j in 1..n)(placements[j,i]));

% Kontrollerar att totala antalet residential stämmer
constraint n_residential = sum(i in 1..n)(sum_rows[i]);

% Antalet poäng i raderna
array[1..n] of var int: points_rows; 
constraint forall(i in 1..n)(points_rows[i] = point_distribution[sum_rows[i]+1]);

% Antalet poäng i kolumnerna
array[1..n] of var int: points_cols; 
constraint forall(i in 1..n)(points_cols[i] = point_distribution[sum_cols[i]+1]);

% Slutpoängen för layouten
var int: total_points;
constraint total_points = sum(i in 1..n)(points_rows[i])+sum(i in 1..n)(points_cols[i]);

solve maximize total_points;

output["points = ", show(total_points), "\n", "solution = ", "\n"] ++ 
      [show_int(1,placements[i,j]) ++ " " ++ if j mod n == 0 then "\n" else "" endif | i,j in 1..n];
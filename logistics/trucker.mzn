include "globals.mzn";
include "assignment2_data3.dzn";

int: graph_size;
int: start;
int: n_dests;
array[1..n_dests] of int: dests;
int: n_edges;
array[1..n_edges] of int: cities_1;
array[1..n_edges] of int: cities_2;
array[1..n_edges] of int: costs;

array[1..n_edges, 1..2] of int: arcs;
array[1..graph_size] of int: balances;
array[1..n_edges] of var 0..1: flows;
var int: total_cost;

arcs = array2d(1..n_edges, 
               1..2, 
               [ if j == 1 then cities_1[i] else cities_2[i] endif | i in 1..n_edges, j in 1..2 ]);
                                  
balances = array1d(1..graph_size,
                   [ if i == start then n_dests elseif exists(j in 1..n_dests)(dests[j] == i) then -1 else 0 endif | i in 1..graph_size ]);  
                   
total_cost = sum(i in 1..n_edges)(abs(flows[i] * costs[i]));

constraint network_flow(arcs, balances, flows);
solve minimize total_cost;

output[ show(arcs), show(balances), show(flows), show(total_cost)];
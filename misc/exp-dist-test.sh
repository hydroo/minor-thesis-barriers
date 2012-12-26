#!/bin/sh
gnuplot << EOF

set term post eps
set output "exp-dist-test.eps"

set xrange [0:300]
set yrange [0:1]

plot 1-2.718281828459045**(-x*$1) title "1-e**(-x * $1)"

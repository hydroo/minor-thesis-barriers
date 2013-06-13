set terminal pdf color
set style data linespoints

set xtics (2,4,8,16,32,48,64)

set xlabel "Threads"
set ylabel "Cycles"

set title "Atlas: Absolute Cycles per Barrier"
set output "observations.plot.absolute.pdf"

plot "observations.plot.data" using 1:2 title "Add-Fetch", \
     "observations.plot.data" using 1:3 title "Ronny"

set title "Cycles per Thread per Barrier"
set output "observations.plot.per-thread.pdf"

plot "observations.plot.data" using 1:4 title "Add-Fetch", \
     "observations.plot.data" using 1:5 title "Ronny"

set timestamp

set term x11 0
plot "LRandom.data" using 1:5 title "MLF memory" with lines, \
     "LRandom.data" using 1:3 title "MAlonzo Memory" with lines


set term x11 1
plot "LRandom.data" using 1:4 title "MLF CPU" with lines, \
     "LRandom.data" using 1:2 title "MAlonzo CPU" with lines

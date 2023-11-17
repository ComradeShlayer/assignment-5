%%%%% Do NOT copy this file into philosophers.pl
%%%%% Feel free to make new initial states for testing/debugging purposes
%%%%% However, we suggest to do so, you should create a new file and load it 
%%%%% instead of this one in philosophers.pl
%%%%% DO NOT SUBMIT THIS FILE

philosopher(p1).	philosopher(p2).	philosopher(p3).
left(p1,p2).	left(p2,p3).	left(p3,p1).
right(p1,p3).	right(p3,p2).	right(p2,p1).
fork(f1).	fork(f2).	fork(f3).
/*
                p2
               /  \
              f1  f2
             /     \
           p1--f3--p3
*/           
between(p1,f1,p2).	between(p2,f2,p3).	between(p3,f3,p1).
between(p2,f1,p1).	between(p3,f2,p2).	between(p1,f3,p3).

thinking(p1, []).	thinking(p2, []).	thinking(p3, []).
available(f1, []).	available(f2, []).	available(f3, []).



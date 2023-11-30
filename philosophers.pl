% Enter the names of your group members below.
% If you only have 2 group members, leave the last space blank
%
%%%%%
%%%%% NAME: Sean Adlam  500787559
%%%%% NAME: Max Shlayer 501017377
%%%%% NAME: Razz Yau    501048542
%
% Add the required rules in the corresponding sections. 
% If you put the rules in the wrong sections, you will lose marks.
%
% You may add additional comments as you choose but DO NOT MODIFY the comment lines below
%

%%%%% SECTION: dynamic_philosophers
%%%%% These lines allow you to write statements for a predicate that are not consecutive in your program
%%%%% Doing so enabkes the specification of an initial state in another file
%%%%% DO NOT MODIFY THE CODE IN THIS SECTION
:- dynamic thinking/2.
:- dynamic waiting/2.
:- dynamic eating/2.
:- dynamic available/2. 
:- dynamic has/3.


%%%%% SECTION: planner_philosophers
%%%%% This line loads the generic planner code from the file "planner.pl"
%%%%% Just ensure that that the planner.pl file is in the same directory as this one
%%%%% DO NOT EDIT THIS SECTION
:- [planner].


%%%%% SECTION: init_philosophers
%%%%% Loads the initial state from the file philosophersInit.pl
%%%%% HINT: You can create other files with other initial states to more easily test individual actions
%%%%%       To do so, just replace the line below with one loading in the file with your initial state
:- [philosophersInit].


%%%%% SECTION: goal_states_philosophers
%%%%% Below we define different goal states, each with a different ID
%%%%% HINT: It may be useful to define "easier" goals when starting your program or when debugging
%%%%%       You can do so by adding more goal states below
goal_state(1, S) :- eating(p1, S).
goal_state(2, S) :- happy(p1, S).
goal_state(3, S) :- happy(p1, S), waiting(p2, S).
goal_state(4, S) :- happy(p1, S), happy(p2, S).
goal_state(5, S) :- happy(p1, S), happy(p2, S), happy(p3,S).



%%%%% SECTION: precondition_axioms_philosophers
%%%%% Write precondition axioms for all actions in your domain. Recall that to avoid
%%%%% potential problems with negation in Prolog, you should not start bodies of your
%%%%% rules with negated predicates. Make sure that all variables in a predicate 
%%%%% are instantiated by constants before you apply negation to the predicate that 
%%%%% mentions these variables.

%Can attempt to pickUp if
%1. there is a philosopher
%2. there is a fork
%3. the fork is available
%4. the fork is between two philosophers
poss(pickUp(P, F), S) :- philosopher(P), fork(F), available(F, S), left(P, L), between(P, F, L), not has(P, F, S).
poss(pickUp(P, F), S) :- philosopher(P), fork(F), available(F, S), right(P, R), between(P, F, R), not has(P, F, S).

%Can attempt to putDown if
%1. there is a philosopher
%2. there is a fork
%3. the philosopher has the fork in this scenario
poss(putDown(P, F), S) :- philosopher(P), fork(F), has(P, F, S).

%Can attempt to trytoEat if
%1. there is a philosopher
%2. the philosopher has Fork1
%3. the philosopher has Fork2
%4. Fork1 is not Fork2
poss(tryToEat(P), S) :- philosopher(P), has(P, Fork1, S), has(P, Fork2, S), not Fork1 = Fork2.


%%%%% SECTION: successor_state_axioms_philosophers 
%%%%% Write successor-state axioms that characterize how the truth value of all 
%%%%% fluents change from the current situation S to the next situation [A | S]. 
%%%%% You will need two types of rules for each fluent: 
%%%%% 	(a) rules that characterize when a fluent becomes true in the next situation 
%%%%%	as a result of the last action, and
%%%%%	(b) rules that characterize when a fluent remains true in the next situation,
%%%%%	unless the most recent action changes it to false.
%%%%% When you write successor state axioms, you can sometimes start bodies of rules 
%%%%% with negation of a predicate, e.g., with negation of equality. This can help 
%%%%% to make them a bit more efficient.
%%%%%
%%%%% Write your successor state rules here: you have to write brief comments %


%a fork is available if it was put down and was not just picked up
%available(F, S)
available(F, [A | S]) :- A = putDown(P, F), has(P, F, S).
available(F, [A | S]) :- not A = pickUp(P, F), available(F, S).

%a philosopher has a fork if they pick it up when it is available or they have it and dont put it down
%has(P, F, S)
has(P, F, [A | S]) :- A = pickUp(P, F), available(F, S).
has(P, F, [A | S]) :- not A = putDown(P, F), has(P, F, S).

%a philosopher is thinking if they have one fork and put it down or they are already thinking and dont pick up a fork (by dropping the first one)
%thinking(P, S)
thinking(P, [A | S]) :- A = putDown(P, F), has(P, F, S).
thinking(P, [A | S]) :- not A = pickUp(P, F), thinking(P, S).

%a philosopher is eating if they last tryToEat succcessfully or if they were eating and dont put a fork down
%eating(P, S)
eating(P, [A | S]) :- A = tryToEat(P), waiting(P, S).
eating(P, [A | S]) :- not A = putDown(P, S), eating(P, S).

%a philosopher is waiting if a lot of things...
%waiting(P, S)
waiting(P, [_A | S]) :- not thinking(P, S), not eating(P, S).
waiting(P, [A | S]) :- A = pickUp(P, F), thinking(P, S).
waiting(P, [A | S]) :- A = putDown(P, F), eating(P, S).
waiting(P, [A | S]) :- not A = tryToEat(P), waiting(P, S).
waiting(P, [A | S]) :- not A = putDown(P, F), waiting(P, S), has(P, F, S).


%a philosopher is happy if they put down a fork after eating or was happy at a point before
%happy(P, S)
happy(P, [A | S]) :- A = putDown(P, _F), eating(P, S).
happy(P, [_A | S]) :- happy(P, S).

%%%%% SECTION: declarative_heuristics_philosophers
%%%%% The predicate useless(A,ListOfPastActions) is true if an action A is useless
%%%%% given the list of previously performed actions. The predicate useless(A,ListOfPastActions)
%%%%% helps to solve the planning problem by providing declarative heuristics to 
%%%%% the planner. If this predicate is correctly defined using a few rules, then it 
%%%%% helps to speed-up the search that your program is doing to find a list of actions
%%%%% that solves a planning problem. Write as many rules that define this predicate
%%%%% as you can: think about useless repetitions you would like to avoid, and about 
%%%%% order of execution (i.e., use common sense properties of the application domain). 
%%%%% Your rules have to be general enough to be applicable to any problem in your domain,
%%%%% in other words, they have to help in solving a planning problem for any instance
%%%%% (i.e., any initial and goal states).
%%%%%	
%%%%% write your rules implementing the predicate  useless(Action,History) here. %
useless(pickUp(P,F), [putDown(P,F) | _T]). % do not pick up a fork that was just put down.
useless(putDown(P,F), [pickUp(P,F) | _T]). % do not put down a fork that was just picked up.
useless(pickUp(P1, F), History) :- member(pickUp(P2, F), History), not member(putDown(P2, F), History). % do not attempt to pick up a fork that has already been picked up by another philosopher before they put that fork down.

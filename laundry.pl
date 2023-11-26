% Enter the names of your group members below.
% If you only have 2 group members, leave the last space blank
%
%%%%%
%%%%% NAME: 
%%%%% NAME:
%%%%% NAME:
%
% Add the required rules in the corresponding sections. 
% If you put the rules in the wrong sections, you will lose marks.
%
% You may add additional comments as you choose but DO NOT MODIFY the comment lines below
%

%%%%% SECTION: dynamic_laundry
%%%%% These lines allow you to write statements for a predicate that are not consecutive in your program
%%%%% Doing so enabkes the specification of an initial state in another file
%%%%% DO NOT MODIFY THE CODE IN THIS SECTION
:- dynamic clean/2.
:- dynamic wet/2.
:- dynamic folded/2.
:- dynamic holding/2.
:- dynamic hasSoap/2.
:- dynamic hasSoftener/2.
:- dynamic hasLint/2.
:- dynamic in/3.
:- dynamic container/1.


%%%%% SECTION: planner_laundry
%%%%% This line loads the generic planner code from the file "planner.pl"
%%%%% Just ensure that that the planner.pl file is in the same directory as this one
%%%%% DO NOT EDIT THIS SECTION
:- [planner].


%%%%% SECTION: init_laundry
%%%%% Loads the initial state from the file laundryInit.pl
%%%%% HINT: You can create other files with other initial states to more easily test individual actions
%%%%%       To do so, just replace the line below with one loading in the file with your initial state
:- [laundryInit].


%%%%% SECTION: goal_states_laundry
%%%%% Below we define different goal states, each with a different ID
%%%%% HINT: It may be useful to define "easier" goals when starting your program or when debugging
%%%%%       You can do so by adding more goal states below
goal_state(1, S) :- clean(cl1,S).
goal_state(2, S) :- clean(cl1,S), not wet(cl1,S).
goal_state(3, S) :- clean(cl1,S), not wet(cl1,S), folded(cl1,S), in(cl1,dresser,S).


%%%%% Your program is not required to produce plans for the following long
%%%%% goal state that is optional. But if you want to try it, then
%%%%% try to solve this more difficult planning problem.
goal_state(100, S) :- clean(cl1,S), clean(cl2,S), not wet(cl1,S), not wet(cl2,S),
        folded(cl1,S), folded(cl2,S), in(cl1,dresser,S), in(cl2,dresser,S).



%%%%% SECTION: precondition_axioms_laundry
%%%%% Write precondition axioms for all actions in your domain. Recall that to avoid
%%%%% potential problems with negation in Prolog, you should not start bodies of your
%%%%% rules with negated predicates. Make sure that all variables in a predicate 
%%%%% are instantiated by constants before you apply negation to the predicate that 
%%%%% mentions these variables. 

% The following defines different types of objects as containers
% You do not need to edit it
container(X) :- washer(X).
container(X) :- dryer(X).
container(X) :- cupboard(X).
container(X) :- hamper(X).
container(dresser).

% Put the rest of your precondition axioms below
poss(fetch(O, C), S) :- not (holding(_, S)).
poss(putAway(O, C), S) :- container(C), holding(O, S).
poss(addSoap(P, W), S) :- washer(W), soap(P), holding(P, S), not hasSoap(W, S).
poss(addSoftener(T, W), S) :- washer(W), softener(T), holding(T, S), not hasSoftener(W, S).
poss(removeLint(D), S) :- dryer(D), not (holding(_, S)), hasLint(D, S).
poss(washClothes(C, W), S) :- washer(W), in(C, W, S), not clean(C, S), hasSoap(W, S), hasSoftener(W, S).
poss(dryClothes(C, D), S) :- dryer(D), clothes(C), in(C, D, S), wet(C, S), not hasLint(D, S).
poss(fold(C), S) :- clothes(C), clean(C, S), not (folded(C, S), holding(_, S), wet(C, S)). 
poss(wear(C), S) :- clothes(C), folded(C, S).
poss(move(C, F, T), S) :- clothes(C), container(T), container(F), in(C, F, S), not (T = F, holding(_, S), in(_, T, S)). 

%%%%% SECTION: successor_state_axioms_laundry 
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

%in requires two of (a) and (b) since there are two actions that can move an object into a container
%for move action, we only need to check one of the locations each time since we either care where it was or where it went 
in(O, C, [move(O, _, C)|S]).
in(O, C, [putAway(O, C)|S]).
in(O, C, [A|S]) :- not A = move(O, C, _), in(O, C, S).
in(O, C, [A|S]) :- not A = fetch(O, C), in(O, C, S).
%three cases to no longer be holding, depends on what you are holding, since certain things can be added to washers and certain things cannot
holding(O, [fetch(O, _)|S]).
holding(O, [A|S]) :- not A = putAway(O, _), holding(O, S).
holding(O, [A|S]) :- soap(O), not A = addSoap(O, _), holding(O, S).
holding(O, [A|S]) :- softener(O), not A = addSoftener(O, _), holding(O, S).
%these next six are classic cases, there is one action that causes them to be true and one action causes them to be false 
hasSoap(W, [addSoap(P, W)|S]).
hasSoap(W, [A|S]) :- not A = washClothes(_, W), hasSoap(W, S).
hasSoftener(W, [addSoftener(P, W)|S]).
hasSoftener(W, [A|S]) :- not A = washClothes(_, W), hasSoftener(W, S).
hasLint(D, [dryClothes(_, D)|S]).
hasLint(D, [A|S]) :- not A = removeLint(D), hasLint(D, S).
clean(C, [washClothes(C, _)|S]).
clean(C, [A|S]) :- not A = wear(C), clean(C, S). 
wet(C, [washClothes(C, _)|S]).
wet(C, [A|S]) :- not A = dryClothes(C, _), wet(C, S).
folded(C, [fold(C)|S]).
folded(C, [A|S]) :- not A = wear(C), folded(C, S).

%%%%% SECTION: declarative_heuristics_laundry
%%%%% The predicate useless(A,ListOfPastActions) is true if an action A is useless
%%%%% given the list of previously performed actions. The predicate useless(A,ListOfPastActions)
%%%%% helps solve the planning problem by providing declarative heuristics to 
%%%%% the planner. If this predicate is correctly defined using a few rules, then it 
%%%%% helps speed-up the search that your program is doing to find a list of actions
%%%%% that solves a planning problem. Write as many rules that define this predicate
%%%%% as you can: think about useless repetitions you would like to avoid, and about 
%%%%% order of execution (i.e., use common sense properties of the application domain). 
%%%%% Your rules have to be general enough to be applicable to any problem in your domain,
%%%%% in other words, they have to help in solving a planning problem for any instance
%%%%% (i.e., any initial and goal states).
%%%%%	
%%%%% write your rules implementing the predicate  useless(Action,History) here. %

useless(fetch(O, _), History) :- member(fetch(O, _), History).
useless(putAway(O, _), History) :- member(putAway(O, _), History).
useless(addSoap(P, W), History) :- member(addSoap(P, W), History).
useless(addSoftener(T, W), History) :- member(addSoftener(T, W), History).
useless(removeLint(D), History) :- member(removeLint(D), History).
useless(washClothes(C, W), History) :- member(washClothes(C, W), History).
useless(dryClothes(C, D), History) :- member(dryClothes(C, D), History).
useless(fold(C), History) :- member(fold(C), History).
useless(wear(C), History) :- member(wear(C), History).
useless(move(O, F, T), History) :- member(move(O, F, T), History).

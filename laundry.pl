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
goal_state(4, S) :- wet(cl1,S).
goal_state(5, S) :- in(cl1,washer,S).

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
poss(fetch(O, C), S) :- not (holding(_, S)), container(C), in(O, C, S).
poss(putAway(O, C), S) :- container(C), holding(O, S).
poss(addSoap(P, W), S) :- washer(W), not hasSoap(W, S), soap(P), holding(P, S).
poss(addSoftener(T, W), S) :- washer(W), softener(T), holding(T, S), not hasSoftener(W, S).
poss(removeLint(D), S) :- not (holding(_, S)), dryer(D), hasLint(D, S).
poss(washClothes(C, W), S) :- clothes(C), washer(W), in(C, W, S), not clean(C, S), hasSoap(W, S), hasSoftener(W, S).
poss(dryClothes(C, D), S) :- dryer(D), clothes(C), in(C, D, S), wet(C, S), not hasLint(D, S).
poss(fold(C), S) :- clothes(C), clean(C, S), not folded(C, S), not holding(_, S), not wet(C, S). 
poss(wear(C), S) :- clothes(C), folded(C, S).
poss(move(C, F, T), S) :- not holding(_, S), container(T), not in(_, T, S), container(F), not T = F, clothes(C), in(C, F, S). 

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

%in requires two of (a) and (b) since there are two actions that can move an object into a container, for (b) we combine the nots
%for move action, we only need to check one of the locations each time since we either care where it was or where it went 
in(O, C, [A|_S]):- A = move(O, _, C).
in(O, C, [A|_S]):- A = putAway(O, C).
in(O, C, [A|S]) :- not A = move(O, C, _), not A = fetch(O, C), in(O, C, S).
%three cases to no longer be holding, depends on what you are holding, since certain things can be added to washers and certain things cannot
holding(O, [A|_S]):- A = fetch(O, _).
holding(O, [A|S]) :- not A = putAway(O, _), not A = addSoap(O, _), not A = addSoftener(O, _), holding(O, S).
%these next six are classic cases, there is one action that causes them to be true and one action causes them to be false 
hasSoap(W, [A|_S]):- A = addSoap(_, W).
hasSoap(W, [A|S]) :- not A = washClothes(_, W), hasSoap(W, S).
hasSoftener(W, [A|_S]):- A = addSoftener(_, W).
hasSoftener(W, [A|S]) :- not A = washClothes(_, W), hasSoftener(W, S).
hasLint(D, [A|_S]):- A = dryClothes(_, D).
hasLint(D, [A|S]) :- not A = removeLint(D), hasLint(D, S).
clean(C, [A|_S]):- A = washClothes(C, _).
clean(C, [A|S]) :- not A = wear(C), clean(C, S). 
wet(C, [A|_S]):- A = washClothes(C, _).
wet(C, [A|S]) :- not A = dryClothes(C, _), wet(C, S).
folded(C, [A|_S]):- A = fold(C).
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

useless(washClothes(C,W), History) :- member(dryClothes(C,W), History). % do not wash if the clothes are already dry
useless(washClothes(C, _W), History) :- member(fold(C), History). % do not wash if the clothes are already folded
useless(dryClothes(C, _W), History) :- member(fold(C), History). % do not dry if the clothes are already folded

useless(putAway(O,C), [fetch(O,C) | _T]). % do not put away something you just fetched
useless(fetch(O,C), [putAway(O,C) | _T]). % do not fetch something you just put away

useless(move(_,_,_), [move(_,_,_) | _T]). % sequential move actions are redundant
useless(fetch(_,_), [fetch(_,_) | _T]). % sequential fetch actions are redundant
useless(putAway(_,_), [putAway(_,_) | _T]). % sequential putAway actions are redundant
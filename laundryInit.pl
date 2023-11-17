%%%%% Do NOT copy this file into laundry.pl
%%%%% Feel free to make new initial states for testing/debugging purposes
%%%%% However, we suggest to do so, you should create a new file and load it 
%%%%% instead of this one in laundry.pl
%%%%% DO NOT SUBMIT THIS FILE

washer(w1).     dryer(d1).

clothes(cl1).   clothes(cl2). hamper(h1).     hamper(h2).

soap(p1).       soap(p2).       cupboard(cbd1). cupboard(cbd2).

softener(sft1). softener(sft2). 

in(cl1,h1,[]).  in(cl2,h2,[]).

in(p1,cbd1,[]). in(p2,cbd2,[]). 

in(sft1,cbd1,[]).       in(sft2,cbd2,[]).


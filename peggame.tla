------------------------------ MODULE peggame ------------------------------
EXTENDS TLC, Sequences, Integers

VARIABLES nn
CONSTANTS a,b,c,d,e

Init == /\ a = <<FALSE>>
        /\ b = <<TRUE,TRUE>>
        /\ c = <<TRUE,TRUE,TRUE>>
        /\ d = <<TRUE,TRUE,TRUE,TRUE>>
        /\ e = <<TRUE,TRUE,TRUE,TRUE,TRUE>>
        /\ nn = << a,b,c,d,e >>

Up(x,y) == nn' = [ sa \in nn |->
                   [ sb \in nn[sa] |->
                     IF sa = 2 /\ sb = 1
                     THEN
                        /\  nn[1][1] = FALSE 
                        /\  nn[2][1] = TRUE
                        /\  nn[3][1] = TRUE
                     ELSE
                       nn[sa,sb]
                   ]
                 ]
           
NextFor(x,y) == Up(x,y)

Next == NextFor(2,1)

=============================================================================
\* Modification History
\* Last modified Sun Mar 10 03:28:31 EDT 2019 by jay
\* Created Sun Mar 10 00:12:41 EST 2019 by jay

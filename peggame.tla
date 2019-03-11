------------------------------ MODULE peggame ------------------------------
EXTENDS TLC, Sequences, Integers

VARIABLES state
CONSTANTS a,b,c,d,e

\* Spots
\*   The set of <<x,y>> tuples where (x \in 1..5), (y \in 1..5), and (x+y<=6)  
Spots == { <<x,y>> \in {1..5}\X{1..5} : x+y<=6 }  


\* Init
\*   state = The set of Spots except (3,1) 
Init == /\ state = Spots \ <<3,1>>

\* Init
\*   state = A function f(x,y) returning FALSE for the (3,1) spot but TRUE for all other Spots
Init == /\ state = [ <<x,y>> \in Spots |-> ~(x=3 /\ y=1) ]

\* NextUpStates
\*   state' = A function f(x,y) returning true if 
\*            - The tuple <<x,y>> is in the current state, but not in the next state
\*            - The tuple <<x+1,y>> is in the current state, but not in the next state
\*            - The tuple <<x+2,y>> is not in the current state, but is in the next state
NextUpStates == \A <<x,y>> \in Spots :  TRUE

\* the set of states similar to the current state,
\* except where  

nn' = [ sa \in nn |->
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
                 
Next == Up

=============================================================================
\* Modification History
\* Last modified Sun Mar 10 22:57:07 EDT 2019 by jay
\* Created Sun Mar 10 00:12:41 EST 2019 by jay

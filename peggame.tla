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

\* CanJumpUp(x,y)
\*         A function f(x,y) returning true if:
\*            - The tuple <<x,y>>   is in Spots, is in the current state
\*            - The tuple <<x+1,y>> is in Spots, is in the current state
\*            - The tuple <<x+2,y>> is in Spots, is not in the current state
CanJumpUp(s,x,y) == <<x,y>> \in Spots /\ <<x,y>> \in s /\ <<x,y>> \notin state'

\* JumpUp(s,x,y)
\*   The given state, except...
\*            - Minus <<x,y>> 
\*            - Minus <<x+1,y>>
\*            - Plus <<x+2,y>>
JumpUp(s,x2,y2) == (((s \ <<x2,y2>>) \ <<x2+1,y2>>) \cup <<x2+2,y2>>)   

\* the set of states similar to the current state,
\* except where  

\* nn' = [ sa \in nn |->
\*                    [ sb \in nn[sa] |->
\*                      IF sa = 2 /\ sb = 1
\*                      THEN
\*                         /\  nn[1][1] = FALSE 
\*                         /\  nn[2][1] = TRUE
\*                         /\  nn[3][1] = TRUE
\*                      ELSE
\*                        nn[sa,sb]
\*                    ]
\*                  ]

\* Next
\*   The next state(s) are those which are the JumpUp(..) of the current state
Next ==  \E x \in Spots, y \in Spots : CanJumpUp(state,x,y) /\ state' = JumpUp(state,x,y) 

=============================================================================
\* Modification History
\* Last modified Sun Mar 10 23:45:06 EDT 2019 by jay
\* Created Sun Mar 10 00:12:41 EST 2019 by jay

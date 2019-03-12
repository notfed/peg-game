------------------------------ MODULE peggame ------------------------------
EXTENDS TLC, Integers

VARIABLES state

\* Spots
\*   The set of <<x,y>> \in <<1..5,1..5>> where (x+y<=6)  
Spots == { <<x,y>> \in {1,2,3,4,5}\X{1,2,3,4,5} : x+y<=6 }  


\* Init
\*   state = The set of Spots except (3,1)
Init == /\ state = Spots \ { <<5,1>> }

\* RotateR(s) - Rotates the board to the right by 360/3 degrees.
\* RotateRSpot(spot) == <<spot[2], 7-spot[1]-spot[2]>>
RotateR(s) ==  { <<x,y>> \in Spots :  <<y, 7-x-y>> \in s }  

\* RotateR(s) - Rotates the board to the left by 360/3 degrees.
\* RotateLSpot(spot) == <<7-spot[1]-spot[2], spot[1]>>
RotateL(s) ==  { <<x,y>> \in Spots :  <<7-x-y, x>> \in s }

\* CanJumpUp(x,y)
\*         A function f(x,y) returning true if:
\*            - The tuple <<x,y>>   is in Spots, is in the current state
\*            - The tuple <<x+1,y>> is in Spots, is in the current state
\*            - The tuple <<x+2,y>> is in Spots, is not in the current state
CanJumpUp(s,x,y) == /\ <<x,y>> \in s
                    /\ <<x+1,y>> \in s
                    /\ <<x+2,y>> \in Spots /\ <<x+2,y>> \notin s

\* JumpUp(s,x,y)
\*   The given state, except...
\*            - Minus <<x,y>> 
\*            - Minus <<x+1,y>>
\*            - Plus <<x+2,y>>
JumpUp(s,x2,y2) == (((s \ {<<x2,y2>>}) \ {<<x2+1,y2>>}) \cup {<<x2+2,y2>>})   

\* Next
\*   The next state(s) are those which are the JumpUp(..) of the current state
Next == \E <<x,y>> \in Spots : CanJumpUp(state,x,y) /\ state' = JumpUp(state,x,y) 

=============================================================================
\* Modification History
\* Last modified Mon Mar 11 22:46:30 EDT 2019 by jay
\* Created Sun Mar 10 00:12:41 EST 2019 by jay

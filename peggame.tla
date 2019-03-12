------------------------------ MODULE peggame ------------------------------
EXTENDS TLC, Integers

VARIABLES state

\* Spots
\*   The set of <<x,y>> \in <<1..5,1..5>> where (x+y<=6)  
Spots == { <<x,y>> \in {1,2,3,4,5}\X{1,2,3,4,5} : x+y<=6 }  


\* Init
\*   state = The set of Spots except (3,1)
Init == /\ state = Spots \ { <<4,1>> }

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
CanJumpUpRight(s,x,y) == /\ <<x,y>> \in s
                         /\ <<x+1,y>> \in s
                         /\ <<x+2,y>> \in (Spots \ s)
                    
CanJumpDownLeft(s,x,y) == /\ <<x,y>> \in s
                          /\ <<x-1,y>> \in s
                          /\ <<x-2,y>> \in (Spots \ s)

CanJumpUpLeft(s,x,y) == /\ <<x,y>> \in s
                        /\ <<x+1,y-1>> \in s
                        /\ <<x+2,y-2>> \in (Spots \ s)
                    
CanJumpDownRight(s,x,y) == /\ <<x,y>> \in s
                           /\ <<x-1,y+1>> \in s
                           /\ <<x-2,y+2>> \in (Spots \ s)

CanJumpRight(s,x,y) == /\ <<x,y>> \in s
                       /\ <<x,y+1>> \in s
                       /\ <<x,y+2>> \in (Spots \ s)
                       
CanJumpLeft(s,x,y) == /\ <<x,y>> \in s
                       /\ <<x,y-1>> \in s
                       /\ <<x,y-2>> \in (Spots \ s)
\* JumpUp(s,x,y)
\*   The given state, except...
\*            - Minus <<x,y>> 
\*            - Minus <<x+1,y>>
\*            - Plus <<x+2,y>>
JumpUpRight(s,x,y)  == (((s \ {<<x,y>>}) \ {<<x+1,y>>}) \cup {<<x+2,y>>})   
JumpDownLeft(s,x,y) == (((s \ {<<x,y>>}) \ {<<x-1,y>>}) \cup {<<x+2,y>>})

JumpUpLeft(s,x,y)    == (((s \ {<<x,y>>}) \ {<<x+1,y-1>>}) \cup {<<x+2,y-2>>})
JumpDownRight(s,x,y) == (((s \ {<<x,y>>}) \ {<<x-1,y-1>>}) \cup {<<x+2,y+2>>})  

JumpRight(s,x,y) == (((s \ {<<x,y>>}) \ {<<x,y+1>>}) \cup {<<x,y+2>>})   
JumpLeft(s,x,y)  == (((s \ {<<x,y>>}) \ {<<x,y-1>>}) \cup {<<x,y-2>>})

\* Next
\*   The next state(s) are those which are the JumpUp(..) of the current state
Next == \/ (\E <<x,y>> \in Spots : CanJumpUpRight(state,x,y)   /\ state' = JumpUpRight(state,x,y))
        \/ (\E <<x,y>> \in Spots : CanJumpDownLeft(state,x,y)  /\ state' = JumpDownLeft(state,x,y))
        \/ (\E <<x,y>> \in Spots : CanJumpUpLeft(state,x,y)    /\ state' = JumpUpLeft(state,x,y))
        \/ (\E <<x,y>> \in Spots : CanJumpDownRight(state,x,y) /\ state' = JumpDownRight(state,x,y))
        \/ (\E <<x,y>> \in Spots : CanJumpRight(state,x,y)     /\ state' = JumpRight(state,x,y))
        \/ (\E <<x,y>> \in Spots : CanJumpLeft(state,x,y)      /\ state' = JumpLeft(state,x,y))

=============================================================================
\* Modification History
\* Last modified Mon Mar 11 23:35:43 EDT 2019 by jay
\* Created Sun Mar 10 00:12:41 EST 2019 by jay

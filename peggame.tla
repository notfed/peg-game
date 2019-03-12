------------------------------ MODULE peggame ------------------------------
EXTENDS TLC, Integers, FiniteSets

VARIABLES state

\* Spots
\*   The set of <<x,y>> \in <<1..5,1..5>> where (x+y<=6)  
Spots == { <<x,y>> \in {1,2,3,4,5}\X{1,2,3,4,5} : x+y<=6 }  


\* Init
\*   state = The set of Spots except (5,1)
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
CanJumpUpRight(x,y) == /\ <<x,y>> \in state
                         /\ <<x+1,y>> \in state
                         /\ <<x+2,y>> \in (Spots \ state)
                    
CanJumpDownLeft(x,y) == /\ <<x,y>> \in state
                          /\ <<x-1,y>> \in state
                          /\ <<x-2,y>> \in (Spots \ state)

CanJumpUpLeft(x,y) == /\ <<x,y>> \in state
                        /\ <<x+1,y-1>> \in state
                        /\ <<x+2,y-2>> \in (Spots \ state)
                    
CanJumpDownRight(x,y) == /\ <<x,y>> \in state
                           /\ <<x-1,y+1>> \in state
                           /\ <<x-2,y+2>> \in (Spots \ state)

CanJumpRight(x,y) == /\ <<x,y>> \in state
                       /\ <<x,y+1>> \in state
                       /\ <<x,y+2>> \in (Spots \ state)
                       
CanJumpLeft(x,y) == /\ <<x,y>> \in state
                       /\ <<x,y-1>> \in state
                       /\ <<x,y-2>> \in (Spots \ state)
\* JumpUp(x,y)
\*   The current state, except...
\*            - Minus <<x,y>> 
\*            - Minus <<x+1,y>>
\*            - Plus <<x+2,y>>
JumpUpRight(x,y)  == (((state \ {<<x,y>>}) \ {<<x+1,y>>}) \cup {<<x+2,y>>})   
JumpDownLeft(x,y) == (((state \ {<<x,y>>}) \ {<<x-1,y>>}) \cup {<<x-2,y>>})

JumpUpLeft(x,y)    == (((state \ {<<x,y>>}) \ {<<x+1,y-1>>}) \cup {<<x+2,y-2>>})
JumpDownRight(x,y) == (((state \ {<<x,y>>}) \ {<<x-1,y+1>>}) \cup {<<x-2,y+2>>})  

JumpRight(x,y) == (((state \ {<<x,y>>}) \ {<<x,y+1>>}) \cup {<<x,y+2>>})   
JumpLeft(x,y)  == (((state \ {<<x,y>>}) \ {<<x,y-1>>}) \cup {<<x,y-2>>})

\* Win returns TRUE if there is one peg left
Win == Cardinality(state) = 1

\* Next
\*   The next state(s) are those which are the JumpUp(..) of the current state
Next == \/ (\E <<x,y>> \in Spots : CanJumpUpRight(x,y)   /\ state' = JumpUpRight(x,y))
        \/ (\E <<x,y>> \in Spots : CanJumpDownLeft(x,y)  /\ state' = JumpDownLeft(x,y))
        \/ (\E <<x,y>> \in Spots : CanJumpUpLeft(x,y)    /\ state' = JumpUpLeft(x,y))
        \/ (\E <<x,y>> \in Spots : CanJumpDownRight(x,y) /\ state' = JumpDownRight(x,y))
        \/ (\E <<x,y>> \in Spots : CanJumpRight(x,y)     /\ state' = JumpRight(x,y))
        \/ (\E <<x,y>> \in Spots : CanJumpLeft(x,y)      /\ state' = JumpLeft(x,y))

=============================================================================
\* Modification History
\* Last modified Tue Mar 12 00:02:48 EDT 2019 by jay
\* Created Sun Mar 10 00:12:41 EST 2019 by jay

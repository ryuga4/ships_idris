module Main

import Data.Fin
import Data.Vect
import Prelude.Cast



%default total

main : IO ()
main = putStrLn "hello Ships!"


data CellState = Unknown
               | ShipFound
               | HitAndSink
               | NoShip


record Board (n : Nat) (m : Nat) where
  constructor MkBoard
  board : Vect n (Vect m CellState)
  notZeroN : GT n Z
  notZeroM : GT m Z


getCellState : Board n m -> Fin n -> Fin m -> CellState
getCellState b x y = index y (index x (board b))

data Orientation = Vertical | Horizontal


(-) : (a : Nat) -> (b : Fin a) -> Nat
(S a) - FZ = S a
(S a) - (FS b) = a - b

data Ship : (n : Nat) -> (m : Nat) -> Type where
 VerticalShip : {auto prfN : GT n Z}
             -> {auto prfM : GT m Z}
             -> (x : Fin n, y : Fin m)
             -> (l : Nat)
             -> {auto prfL : GT l Z}
             -> {auto prf : LTE (cast y + l) m}
             -> Ship n m
 HorizontalShip : {auto prfN : GT n Z}
               -> {auto prfM : GT m Z}
               -> (x : Fin n, y : Fin m)
               -> (l : Nat)
               -> {auto prfL : GT l Z}
               -> {auto prf : LTE (cast x + l) n}
               -> Ship n m


length : Ship n m -> Nat
length (VerticalShip _ _ l) = l
length (HorizontalShip _ _ l) = l


exampleShip : Ship 10 10
exampleShip = HorizontalShip 6 0 3
exampleBoard : Board 4 4
exampleBoard = MkBoard
  [ [Unknown, Unknown, Unknown, Unknown]
  , [Unknown, Unknown, Unknown, Unknown]
  , [Unknown, Unknown, Unknown, Unknown]
  , [Unknown, Unknown, Unknown, Unknown]
  ] (LTESucc LTEZero) (LTESucc LTEZero)

shipX : Ship n m -> Fin n
shipX (HorizontalShip x _ _) = x
shipX (VerticalShip x _ _) = x


shipY : Ship n m -> Fin m
shipY (HorizontalShip _ y _) = y
shipY (VerticalShip _ y _) = y


natToFin : (n : Nat) -> Fin (S n)
natToFin Z = FZ
natToFin (S k) = FS (natToFin k)


natToFinLTE : (n : Nat) -> {auto prf : LT n m} -> Fin m
natToFinLTE {prf = (LTESucc x)} Z = FZ
natToFinLTE {prf = (LTESucc x)} (S k) = FS (natToFinLTE k)



weakenFinFull : {auto prf : LTE n m} -> (a : Fin n) -> (b : Fin m ** finToNat a = finToNat b)
weakenFinFull {prf = LTESucc p} FZ = (FZ ** Refl)
weakenFinFull {prf = LTESucc p} (FS f) with (weakenFinFull f {prf = p})
  weakenFinFull {prf = LTESucc p} (FS f) | (x ** pf) = (FS x ** rewrite pf in Refl)


weakenFin : {prf : LTE n m} -> Fin n -> Fin m
weakenFin {prf} x with (weakenFinFull x {prf = prf})
  weakenFin x | (y ** _) = y


shipCells : (s : Ship n m) -> List (Fin n, Fin m)
shipCells {m = S m} (VerticalShip x y (S l) {prf}) = map (\i => (x,i)) [y .. natToFinLTE (cast y + l) {prf = rewrite (plusSuccRightSucc (cast y) l) in prf}]
shipCells {n = S n} (HorizontalShip x y (S l) {prf}) = map (\i => (i,y)) [x .. natToFinLTE (cast x + l) {prf = rewrite (plusSuccRightSucc (cast x) l) in prf}]

shipCellValues : (cells : Vect l (Fin a, Fin b))
              -> (board : Board n m)
              -> {prfX : LTE a n}
              -> {prfY : LTE b m}
              -> Vect l CellState
shipCellValues {prfX} {prfY} cells board =
  map (\(x,y) => getCellState board
                              (weakenFin {prf = prfX} x)
                              (weakenFin {prf = prfY} y)) cells



(Cast a a2, Cast b b2) => Cast (a,b) (a2,b2) where
 cast (a,b) = (cast a, cast b)


finToLTE : (a : Fin n)
        -> LT (cast a) n
finToLTE FZ = LTESucc LTEZero
finToLTE (FS x) = LTESucc (finToLTE x)


lteSwapZero : (a,c : Nat)
           -> LTE a (c - 0)
           -> LTE (a + 0) c
lteSwapZero Z c x = LTEZero
lteSwapZero (S k) (S j) (LTESucc x) = LTESucc (lteSwapZero k j (rewrite (minusZeroRight j) in x))




minusSucc : (a,b : Nat)
          -> {auto prf : LTE b a}
          -> {auto prf2 : LTE b (S a)}
          -> S a - b = S (a - b)
minusSucc Z Z = Refl
minusSucc (S k) Z = Refl
minusSucc (S a) (S b) {prf=LTESucc prf} {prf2=LTESucc prf2} = minusSucc a b 






ltePlus : (a,b : Nat)
       -> (c : Nat)
       -> LTE a b
       -> LTE (a+c) (b+c)
ltePlus Z     b     Z     x           = LTEZero
ltePlus (S k) (S b) c     (LTESucc x) = LTESucc (ltePlus k b c x)
ltePlus Z     j     (S k) LTEZero = rewrite sym (plusSuccRightSucc j k) in LTESucc (ltePlus Z j k LTEZero)






plusSuccSucc : {a,b : Nat}
            -> a = b
            -> S a = S b 
plusSuccSucc {a = Z} {b = Z} prf = Refl
plusSuccSucc {a = (S j)} {b = (S j)} Refl = Refl
plusSuccSucc {a = Z} {b = S b} Refl impossible
plusSuccSucc {a = S a} {b = Z} Refl impossible


swapMinus : (a,b,c : Nat)
         -> {auto prf : LTE b a}
         -> {auto prf2 : LTE b c}
         -> (a-b) + c = a + (c - b)
swapMinus Z Z Z = Refl
swapMinus Z Z (S k) = Refl
swapMinus Z (S k) Z = Refl
swapMinus (S k) Z Z = Refl
swapMinus (S k) Z (S j) = Refl
swapMinus (S k) (S j) (S i) {prf = LTESucc prf} {prf2 = LTESucc prf2} with (swapMinus k j i)
  swapMinus (S k) (S j) (S i) {prf = LTESucc prf} | with_pat = rewrite sym (plusSuccRightSucc (k - j) i) in plusSuccSucc with_pat



lteSelfSucc : (a : Nat)
           -> LTE a (S a)
lteSelfSucc Z = LTEZero
lteSelfSucc (S k) = LTESucc (lteSelfSucc k)



plusOneNSuccN : (n : Nat)
             -> 1 + n = S n
plusOneNSuccN n = Refl



plusRightMinusCancel : (a,b : Nat)
                    -> {auto prf : LTE b a}
                    -> a - b + b = a
plusRightMinusCancel Z Z = Refl
plusRightMinusCancel (S k) Z = rewrite sym (plusZeroRightNeutral k) in Refl
plusRightMinusCancel (S k) (S j) {prf = LTESucc prf} with (plusRightMinusCancel k j)-- {prf = lteSuccRight prf})
  plusRightMinusCancel (S k) (S j) {prf = LTESucc prf} | with_pat = rewrite swapMinus k j (S j) {prf2 = lteSelfSucc j} in 
                                                                    rewrite sym (minusOneSuccN j) in 
                                                                    rewrite plusCommutative k (S Z) in Refl




lteSwapMinus : (a,b,c : Nat)
            -> {prf : LTE b c}
            -> LTE a (c - b)
            -> LTE (a + b) c
lteSwapMinus Z b c x {prf} = prf
lteSwapMinus (S a) b (S c) x = rewrite sym (plusRightMinusCancel (S c) b) in ltePlus (S a) (S c - b) b x



lteMinus : (n,m : Nat)
        -> {auto prf : LTE m n}
        -> (LTE (n-m) n)
        
lteMinus Z Z = LTEZero
lteMinus (S k) Z = LTESucc lteRefl
lteMinus (S k) (S j) {prf = LTESucc prf} with (lteMinus k j)
  lteMinus (S k) (S j) | with_pat = lteSuccRight with_pat



verticalShipsOfLength : (board : Board n m)
             -> (length : Nat)
             -> {auto notZeroLengthPrf : GT length Z}
             -> {auto lteLengthM : LTE length m}
             -> List (Ship n m)
verticalShipsOfLength {n = Z} (MkBoard board notZeroN notZeroM) _ impossible
verticalShipsOfLength {m = Z} (MkBoard board notZeroN notZeroM) _ impossible
verticalShipsOfLength {lteLengthM} {n = S n} {m = S m} board length = do
    a <- toList (range {len = S n})
    b <- toList (range {len = (S m) - length})
    pure $ shipAtPosition a b
  where
  shipAtPosition : Fin (S n)
                -> Fin (S m - length)
                -> Ship (S n) (S m)
  shipAtPosition x y with (weakenFinFull y {m = S m} {prf = lteMinus (S m) length})
    shipAtPosition x y | (weakenY ** pf) = (VerticalShip x weakenY length
                                                         {prf = rewrite sym pf in
                                                                lteSwapMinus {prf = lteLengthM} (finToNat y) length (S m) (lteSuccLeft (finToLTE y))})





allPossibleShips : (board : Board n m)
                -> (shipLengths : List (x : Nat ** (GT x Z , LTE x m)))
                -> List (Ship n m)
allPossibleShips board shipLengths = join $ map (\(i ** (notZeroLengthPrf, lteLengthM)) => verticalShipsOfLength board i) shipLengths



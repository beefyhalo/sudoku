module sudoku

import data.Vect
import Grid

%default total
%access public export

data NoDupsButEmpty : Vect n (Value m) -> Type where
  EmptyList : NoDupsButEmpty []
  ThisEmpty : (prf: NoDupsButEmpty xs) -> NoDupsButEmpty (Empty :: xs)
  ThisNoDup : (prf: Not (Elem x xs)) -> (induction: NoDupsButEmpty xs) -> NoDupsButEmpty (x :: xs)

data ValidRows : Vect n (Vect m a) -> Type where
  ValidEmpty : ValidRows []
  ValidRow : (prf : NoDupsButEmpty x) -> (induction : ValidRows xs) -> ValidRows (x :: xs)

data ValidCols : Vect n (Vect m a) -> Type where
  ColsValid : (prf : ValidRows (cols g)) -> ValidCols g

data ValidBoxes : Vect (n*n) (Vect (n*n) a) -> Type where
  BoxsValid : (prf : ValidRows (boxes g)) -> ValidBoxes g

data Valid : Grid n -> Type where
  IsValid : (rows : ValidRows g) -> (cols : ValidCols g) -> (boxes : ValidBoxes g) -> Valid (MkGrid g)

rowsHaveDupes : (prf : NoDupsButEmpty x -> Void) -> ValidRows (x :: xs) -> Void
rowsHaveDupes contra (ValidRow prf x) = contra prf

tailIsBad : (contra: (ValidRows xs) -> Void) -> ValidRows (x :: xs) -> Void
tailIsBad contra (ValidRow prf x) = contra x

tailHasDups : (contra : NoDupsButEmpty xs -> Void) -> NoDupsButEmpty (x :: xs) -> Void
tailHasDups contra (ThisEmpty prf) = contra prf
tailHasDups contra (ThisNoDup prf induction) = contra induction

hasDup : (isElem : Elem (Filled x) xs) -> NoDupsButEmpty ((Filled x) :: xs) -> Void
hasDup isElem (ThisNoDup prf induction) = prf isElem

decNoDupsButEmpty : (x : Vect n (Value m)) -> Dec (NoDupsButEmpty x)
decNoDupsButEmpty [] = Yes EmptyList
decNoDupsButEmpty (x :: xs) with (decNoDupsButEmpty xs)
  | Yes prf = case x of 
    Empty    => Yes (ThisEmpty prf)
    Filled x => case (isElem (Filled x) xs) of
      Yes prf   => No (hasDup prf)
      No contra => Yes (ThisNoDup contra prf)
  | No contra = No (tailHasDups contra)

decValidRows : (g : Vect n (Vect m (Value k))) -> Dec (ValidRows g)
decValidRows [] = Yes ValidEmpty
decValidRows (x :: xs) with (decNoDupsButEmpty x)
  | No contra    = No (rowsHaveDupes contra)
  | Yes nodupesX with (decValidRows xs)
    | Yes prf   = Yes (ValidRow nodupesX prf)
    | No contra = No (tailIsBad contra)

rowsInvalid : (contra : ValidRows g -> Void) -> Valid (MkGrid g) -> Void
rowsInvalid contra (IsValid rows cols boxes) = contra rows

colsInvalid : (contra : ValidRows (cols g) -> Void) -> Valid (MkGrid g) -> Void
colsInvalid contra (IsValid rows (ColsValid cols) boxes) = contra cols

boxesInvalid : (contra : ValidRows (boxes g) -> Void) -> Valid (MkGrid g) -> Void
boxesInvalid contra (IsValid rows cols (BoxsValid boxes)) = contra boxes

decValid : (g : Grid n) -> Dec (Valid g)
decValid (MkGrid g) with (decValidRows g)
  | No contra = No (rowsInvalid contra)
  | Yes validRows with (decValidRows (cols g))
    | No contra  = No (colsInvalid contra)
    | Yes validCols with (decValidRows (boxes g))
      | No contra      = No (boxesInvalid contra)
      | Yes validBoxes = Yes (IsValid validRows (ColsValid validCols) (BoxsValid validBoxes))
  

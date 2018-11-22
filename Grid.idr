module sudoku

import data.Vect

%default total
%access public export

data Value : (n : Nat) -> Type where
  Empty  : Value n
  Filled : (x : Fin n) -> Value n

Uninhabited (Empty = Filled _) where
  uninhabited Refl impossible

Uninhabited (Filled _ = Empty) where
  uninhabited Refl impossible

negCong : (contra : (x = y) -> Void) -> (Filled x = Filled y) -> Void
negCong contra Refl = contra Refl

DecEq (Value n) where
  decEq Empty Empty = Yes Refl
  decEq Empty (Filled x) = No uninhabited
  decEq (Filled x) Empty = No uninhabited
  decEq (Filled x) (Filled y) with (decEq x y)
    | Yes prf = Yes (cong prf)
    | No contra = No (negCong contra)

data Grid : (n : Nat) -> Type where
  MkGrid : Vect (n*n) (Vect (n*n) (Value (n*n))) -> Grid (n*n)

cols : Vect n (Vect m a) -> Vect m (Vect n a)
cols = transpose

splitUp : Vect (m*n) a -> Vect m (Vect n a)
splitUp xs {m=Z} = []
splitUp xs {n} {m=S k} = take n xs :: splitUp (drop n xs)

boxes : Vect (n*n) (Vect (n*n) a) -> Vect (n*n) (Vect (n*n) a)
boxes xs = map Vect.concat . Vect.concat --Combine back into n*n
          . map cols                     --Cols the boxes and rows
          . splitUp . map splitUp $ xs   --Split into m*m*m*m

module sudoku

import data.Vect
import Grid
import Valid
import Solved

%default total
%access public export

filterValid : List (Grid n) -> List (g : (Grid n) ** Valid g)
filterValid [] = []
filterValid (g :: xs) with (decValid g)
  | Yes prf = (g ** prf) :: filterValid xs
  | No _    = filterValid xs

filterSolved : (List (g : Grid n ** Valid g)) -> List (g : Grid n ** solved : Valid g ** Solved g)
filterSolved [] = []
filterSolved ((g ** valid) :: xs) with (decSolved g)
  | Yes prf = (g ** valid ** prf) :: filterSolved xs
  | No _    = filterSolved xs


setOfFin : List (Fin n)
setOfFin {n} = setOfFin' n
  where setOfFin' : (acc : Nat) -> List (Fin n)
        setOfFin' Z = []
        setOfFin' (S k) = case (natToFin k n) of
                               Just fin => fin :: setOfFin' k
                               Nothing => []
                               
choices : Value n -> List (Value n)
choices Empty {n}  = map Filled setOfFin
choices (Filled x) = [Filled x]

pruneRow : Vect (n*n) (List (Value (n*n))) -> Vect (n*n) (List (Value (n*n)))
pruneRow xss = [minus xs singles | xs <- xss] 
  where singles = concat . filter (\xs => length xs == 1) . toList $ xss
        minus : Eq a => (options : List a) -> (s : List a) -> List a
        minus []  _ = []
        minus [x] _ = [x]
        minus xs s  = [x | x <- xs, not (elem x s)]

prune : Vect (n*n) (Vect (n*n) (List (Value (n*n)))) -> Vect (n*n) (Vect (n*n) (List (Value (n*n))))
prune = pruneBy boxes . pruneBy cols . pruneBy id
  where pruneBy : (f : {a : Type} -> {m : Nat} -> Vect (m*m) (Vect (m*m) a) -> Vect (m*m) (Vect (m*m) a))
          -> Vect (n*n) (Vect (n*n) (List (Value (n*n)))) -> Vect (n*n) (Vect (n*n) (List (Value (n*n))))
        pruneBy f = f . map pruneRow . f

iterPrune : Vect (n*n) (Vect (n*n) (List (Value (n*n)))) -> Vect (n*n) (Vect (n*n) (List (Value (n*n))))
iterPrune {n} = fix n prune
  where fix : Eq a => (maxIter : Nat) -> (a -> a) -> a -> a
        fix Z _ x = x
        fix (S n) f x = let x' = f x in
          if x == x' then x else fix n f x'

allChoices : Grid n -> List (Grid n)
allChoices (MkGrid xs) = map MkGrid $ traverse (traverse choices) xs

allChoicesPruned : Grid n -> List (Grid n)
allChoicesPruned (MkGrid xs) = map MkGrid $ traverse sequence . iterPrune $ map (map choices) xs

solveSudoku : (g : Grid n) -> List (g' : (Grid n) ** solved : Valid g' ** Solved g')
solveSudoku = filterSolved . filterValid . allChoices

solveSudokuFast : (g : Grid n) -> List (g' : (Grid n) ** solved : Valid g' ** Solved g')
solveSudokuFast = filterSolved . filterValid . allChoicesPruned
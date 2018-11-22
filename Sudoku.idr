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

allChoices : Grid n -> List (Grid n)
allChoices (MkGrid xs) = map MkGrid $ traverse (traverse choices) xs

solveSudoku : (g : Grid n) -> List (g' : (Grid n) ** solved : Valid g' ** Solved g')
solveSudoku = filterSolved . filterValid . allChoices
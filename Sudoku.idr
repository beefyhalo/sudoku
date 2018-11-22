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
                               
guess : Value n -> List (Value n)
guess Empty {n}  = map Filled setOfFin
guess (Filled x) = [Filled x]


allGuesses : Grid n -> List (Grid n)
allGuesses x = ?allGuesses_rhs


generateCases : Grid n -> (List (g' : Grid n ** Valid g'))
generateCases (MkGrid xs) = filterValid ?generateCases_rhs_1

solveSudoku : (g : Grid n) -> List (g' : (Grid n) ** solved : Valid g' ** Solved g')
solveSudoku = filterSolved . generateCases
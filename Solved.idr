module sudoku

import data.Vect
import Grid
import Valid

%default total
%access public export

data RowIsFilled : Vect n (Value m) -> Type where
  EmptyRow : RowIsFilled []
  FilledRow : (induction: RowIsFilled xs) -> RowIsFilled ((Filled x) :: xs)

data RowsAreFilled : Vect n (Vect m a) -> Type where
  EmptyRows : RowsAreFilled []
  FilledRows : (prf : RowIsFilled x) -> (induction : RowsAreFilled xs) -> RowsAreFilled (x :: xs)

data Solved :  (g : Grid n) -> Type where
  SolvedGrid : (valid : Valid (MkGrid xs)) -> (prf : RowsAreFilled xs) -> Solved (MkGrid xs)
  
Uninhabited (RowIsFilled (Empty :: xs)) where
  uninhabited _ impossible

badRowCons : (contra : RowIsFilled xs -> Void) -> RowIsFilled (x :: xs) -> Void
badRowCons contra (FilledRow induction) = contra induction

decRowIsFilled : (v : Vect n (Value m)) -> Dec (RowIsFilled v)
decRowIsFilled [] = Yes EmptyRow
decRowIsFilled (Empty :: xs) = No uninhabited
decRowIsFilled ((Filled x) :: xs) with (decRowIsFilled xs)
  | Yes prf = Yes (FilledRow prf)
  | No contra = No (badRowCons contra)
  
badRows : (contra : RowIsFilled x -> Void) -> RowsAreFilled (x :: xs) -> Void
badRows contra (FilledRows prf induction) = contra prf

badRowsCons : (contra : RowsAreFilled xs -> Void) -> RowsAreFilled (x :: xs) -> Void
badRowsCons contra (FilledRows prf induction) = contra induction

decRowsAreFilled : (xs : Vect n (Vect m (Value k))) -> Dec (RowsAreFilled xs)
decRowsAreFilled [] = Yes EmptyRows
decRowsAreFilled (x :: xs) with (decRowsAreFilled xs)
  | No contra = No (badRowsCons contra)
  | Yes induction with (decRowIsFilled x)
    | No contra = No (badRows contra)
    | Yes prf   = Yes (FilledRows prf induction)

rowsArentFilled : (contra : RowsAreFilled xs -> Void) -> Solved (MkGrid xs) -> Void
rowsArentFilled contra (SolvedGrid valid prf) = contra prf

decSolved : (g : Grid n) -> {auto valid : Valid g} -> Dec (Solved g)
decSolved (MkGrid xs) {valid} with (decRowsAreFilled xs)
  | No contra = No (rowsArentFilled contra)
  | Yes prf   = Yes (SolvedGrid valid prf)

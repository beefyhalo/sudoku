module sudoku

import data.Vect
import Grid
import Valid

%default total
%access public export

data RowIsFilled : Vect n a -> Type where
  EmptyRow : RowIsFilled []
  FilledRow : (prf: Not (Elem x xs)) -> (induction: RowIsFilled xs) -> RowIsFilled (x :: xs)

data RowsAreFilled : Vect n (Vect m a) -> Type where
  EmptyRows : RowsAreFilled []
  FilledRows : (prf : RowIsFilled x) -> (induction : RowsAreFilled xs) -> RowsAreFilled (x :: xs)

data Solved :  (g : Grid n) -> Type where
  SolvedGrid : (valid : Valid (MkGrid xs)) -> (prf : RowsAreFilled xs) -> Solved (MkGrid xs)
  
badRow : (contra : Elem x xs) -> RowIsFilled (x :: xs) -> Void
badRow contra (FilledRow prf induction) = prf contra

badRowCons : (contra : RowIsFilled xs -> Void) -> RowIsFilled (x :: xs) -> Void
badRowCons contra (FilledRow prf induction) = contra induction

decRowIsFilled : DecEq a => (v : Vect n a) -> Dec (RowIsFilled v)
decRowIsFilled [] = Yes EmptyRow
decRowIsFilled (x :: xs) with (decRowIsFilled xs)
  | No contra = No (badRowCons contra) 
  | Yes induction with (isElem x xs)
    | Yes prf   = No (badRow prf)
    | No contra = Yes (FilledRow contra induction)
  
badRows : (contra : RowIsFilled x -> Void) -> RowsAreFilled (x :: xs) -> Void
badRows contra (FilledRows prf induction) = contra prf

badRowsCons : (contra : RowsAreFilled xs -> Void) -> RowsAreFilled (x :: xs) -> Void
badRowsCons contra (FilledRows prf induction) = contra induction

decRowsAreFilled : DecEq a => (xs : Vect n (Vect m a)) -> Dec (RowsAreFilled xs)
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

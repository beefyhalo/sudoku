module sudoku

import data.Vect
import Grid
import Valid
import Solved
import Sudoku

%default total
%access public export

solved : Grid 4
solved = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                      [[Filled 0, Filled 1, Filled 2, Filled 3],
                      [Filled 2, Filled 3, Filled 0, Filled 1],
                      [Filled 1, Filled 2, Filled 3, Filled 0],
                      [Filled 3, Filled 0, Filled 1, Filled 2]]

singleEmpty : Grid 4
singleEmpty = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Filled 2, Filled 3],
                          [Filled 2, Filled 3, Filled 0, Filled 1],
                          [Filled 1, Filled 2, Filled 3, Filled 0],
                          [Filled 3, Filled 0, Filled 1, Filled 2]]

singleEmpty2 : Grid 4
singleEmpty2 = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Filled 0, Filled 1, Filled 2, Filled 3],
                          [Filled 2, Filled 3, Filled 0, Filled 1],
                          [Filled 1, Empty, Filled 3, Filled 0],
                          [Filled 3, Filled 0, Filled 1, Filled 2]]


fewEmpty : Grid 4
fewEmpty = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Filled 0, Filled 1, Filled 2, Filled 3],
                          [Filled 2, Filled 3, Filled 0, Empty],
                          [Filled 1, Empty, Filled 3, Filled 0],
                          [Empty, Filled 0, Filled 1, Filled 2]]

someEmpty : Grid 4
someEmpty = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Filled 0, Filled 1, Filled 2, Filled 3],
                          [Filled 2, Empty, Filled 0, Empty],
                          [Filled 1, Empty, Empty, Empty],
                          [Empty, Filled 0, Filled 1, Filled 2]]
                        
almostSolved : Grid 4
almostSolved = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Empty, Filled 3],
                          [Empty, Empty, Empty, Empty],
                          [Filled 1, Empty, Empty, Empty],
                          [Empty, Filled 0, Filled 1, Filled 2]]
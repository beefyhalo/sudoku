module sudoku

import data.Vect
import Grid
import Valid
import Solved
import Sudoku

%default total
%access public export

almostSolved : Grid 4
almostSolved = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Empty, Filled 3],
                          [Empty, Empty, Empty, Empty],
                          [Filled 1, Empty, Empty, Empty],
                          [Empty, Filled 0, Filled 1, Filled 2]]
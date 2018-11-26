module sudoku

import data.Vect
import Grid
import Valid
import Solved
import Sudoku

%default total
%access public export

solved : Grid 4
solved = MkGrid {n=2} [[Filled 0, Filled 1, Filled 2, Filled 3],
                       [Filled 2, Filled 3, Filled 0, Filled 1],
                       [Filled 1, Filled 2, Filled 3, Filled 0],
                       [Filled 3, Filled 0, Filled 1, Filled 2]]

singleEmpty : Grid 4
singleEmpty = MkGrid {n=2} [[Empty, Filled 1, Filled 2, Filled 3],
                            [Filled 2, Filled 3, Filled 0, Filled 1],
                            [Filled 1, Filled 2, Filled 3, Filled 0],
                            [Filled 3, Filled 0, Filled 1, Filled 2]]

singleEmpty2 : Grid 4
singleEmpty2 = MkGrid {n=2} [[Filled 0, Filled 1, Filled 2, Filled 3],
                             [Filled 2, Filled 3, Filled 0, Filled 1],
                             [Filled 1, Empty, Filled 3, Filled 0],
                             [Filled 3, Filled 0, Filled 1, Filled 2]]


threeEmpty : Grid 4
threeEmpty = MkGrid {n=2} [[Filled 0, Filled 1, Filled 2, Filled 3],
                           [Filled 2, Filled 3, Filled 0, Empty],
                           [Filled 1, Empty, Filled 3, Filled 0],
                           [Empty, Filled 0, Filled 1, Filled 2]]

fourEmpty : Grid 4
fourEmpty = MkGrid {n=2} [[Empty, Filled 1, Filled 2, Filled 3],
                          [Filled 2, Empty, Empty, Filled 1],
                          [Filled 1, Filled 2, Empty, Filled 0],
                          [Filled 3, Filled 0, Filled 1, Filled 2]]

fiveEmpty : Grid 4
fiveEmpty = MkGrid {n=2} [[Filled 0, Empty, Empty, Filled 3],
                          [Filled 2, Filled 3, Filled 0, Empty],
                          [Filled 1, Filled 2, Empty, Filled 0],
                          [Empty, Filled 0, Filled 1, Filled 2]]

sixEmpty : Grid 4
sixEmpty = MkGrid {n=2}
                         [[Filled 0, Filled 1, Filled 2, Filled 3],
                          [Filled 2, Empty, Filled 0, Empty],
                          [Filled 1, Empty, Empty, Empty],
                          [Empty, Filled 0, Filled 1, Filled 2]]
                        
almostSolved : Grid 4
almostSolved = MkGrid {n=2}
                         [[Empty, Filled 1, Empty, Filled 3],
                          [Empty, Empty, Empty, Empty],
                          [Filled 1, Empty, Empty, Empty],
                          [Empty, Filled 0, Filled 1, Filled 2]]


fullsize_easy : Grid 9
fullsize_easy = MkGrid {n=3} [[Empty, Filled 5, Filled 3, Empty, Filled 4, Empty, Filled 2, Filled 8, Empty],
                              [Empty, Filled 1, Empty, Empty, Empty, Empty, Filled 4, Empty, Filled 6],
                              [Empty, Empty, Filled 8, Filled 0, Empty, Empty, Empty, Empty, Filled 7],
                              [Empty, Filled 8, Filled 5, Filled 4, Filled 7, Filled 0, Empty, Empty, Filled 2],
                              [Filled 1, Empty, Empty, Empty, Empty, Empty, Empty, Empty, Filled 3],
                              [Filled 2, Empty, Empty, Filled 3, Filled 6, Filled 1, Filled 8, Filled 7, Empty],
                              [Filled 8, Empty, Empty, Empty, Empty, Filled 4, Filled 5, Empty, Empty],
                              [Filled 5, Empty, Filled 6, Empty, Empty, Empty, Empty, Filled 3, Empty],
                              [Empty, Filled 3, Filled 0, Empty, Filled 2, Empty, Filled 1, Filled 6, Empty]]

fullsize_medium : Grid 9
fullsize_medium = MkGrid {n=3} [[Empty, Filled 4, Empty, Filled 3, Empty, Empty, Filled 1, Empty, Empty],
                                [Empty, Filled 7, Filled 6, Empty, Empty, Empty, Empty, Filled 2, Filled 0],
                                [Empty, Empty, Filled 8, Empty, Filled 0, Empty, Empty, Empty, Empty],
                                [Empty, Filled 5, Empty, Filled 7, Filled 4, Filled 0, Empty, Empty, Empty],
                                [Filled 7, Empty, Empty, Empty, Filled 3, Empty, Empty, Empty, Filled 2],
                                [Empty, Empty, Empty, Filled 6, Filled 2, Filled 1, Empty, Filled 7, Empty],
                                [Empty, Empty, Empty, Empty, Filled 1, Empty, Filled 4, Empty, Empty],
                                [Filled 6, Filled 0, Empty, Empty, Empty, Empty, Filled 7, Filled 3, Empty],
                                [Empty, Empty, Filled 5, Empty, Empty, Filled 7, Empty, Filled 0, Empty]]
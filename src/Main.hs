module Main where

import AlgorithmW (e0, e1, e2, e3, e4, e5, test) 



main :: IO ()
main = mapM_ test [e0, e1, e2, e3, e4, e5]

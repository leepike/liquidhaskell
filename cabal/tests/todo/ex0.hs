module Ex where

-- Testing "existential-types"

{-@ foldN :: forall a <p :: x0:Int -> x1:a -> Bool>. 
                (i:Int -> a<p i> -> exists [j : Int = i + 1]. a<p j>) 
              -> n:{v: Int | v >= 0}
              -> (exists [z : Int = 0]. a <p z>) 
              -> a <p n>
  @-}
foldN :: (Int -> a -> a) -> Int -> a -> a
foldN f n = go 0 
  where go i x | i < n     = go (i+1) (f i x)
               | otherwise = x

{-@ count :: m: {v: Int | v > 0 } -> {v: Int | v = m} @-}
count :: Int -> Int
count = foldN (\_ n -> n + 1) 
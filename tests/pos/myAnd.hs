module And where


{-@ myAnd1 :: forall <p :: Bool -> Prop>. Bool<p> -> Bool<p> -> Bool<p> @-}
myAnd1 :: Bool -> Bool -> Bool
myAnd1 _ = undefined

{-@ myAnd :: forall <p :: x:Bool -> Prop>. Bool<p> -> [Bool<p>] -> Bool<p> @-}
myAnd :: Bool -> [Bool] -> Bool
myAnd = foldl myAnd1
-- foldl :: (a -> b -> a) -> a -> [b] -> a

s = myAnd True [True, False, True]


{-@ f :: {x:Bool | Prop(x)} @-}
f = myAnd True [True, True, True]

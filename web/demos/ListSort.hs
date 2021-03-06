-- ---
-- layout: post
-- title: "Verifing Sorting Algorithms With Recursive Refinements"
-- date: 2013-01-25 16:12
-- comments: true
-- external-url:
-- categories: abstract-refinements
-- author: Niki Vazou
-- published: false
-- ---

-- Let see how we can use **abstract refinements* to verify that
-- the result of a list sorting function is actually a sorted list.


module ListSort (insertSort, mergeSort, quickSort) where


-- First, lets describe a sorted list:

-- \begin{code}The list type is refined with an abstract refinement, yielding the refined type:
-- data [a] <p :: elt:a -> a -> Bool> where
--   | []  :: [a] <p>
--   | (:) :: h:a -> [a<p h>]<p> -> [a]<p>
-- \end{code}

-- The definition states that a value of type `[a]<p>` is either empty (`[]`)
-- or constructed from a pair of a head `h::a` and a tail of a list of a values
-- each of which satisfies the refinement (`p h`).
-- Furthermore, the abstract refinement `p` holds recursively within the
-- tail, ensuring that the relationship `p` holds between all pairs of list elements.


-- \begin{code}A sorted list is defined by instantiating the abstract refinement `p` with
-- \elt v -> v >= elt
-- \end{code}

-- So, we define the type-synonym `SList a`


{-@ type SList a = [a]<{\elt v -> (v >= elt)}> @-}


-- We aim to verify that the result of each sorting function is of type `SList a`

-- Insert Sort
-- -----------

-- Lets write a function `insert` that inserts an element into the correct position of a sorted list:


insert y []                   = [y]
insert y (x : xs) | y <= x    = y : x : xs
                  | otherwise = x : insert y xs


-- Its type states that if you give `insert` an element and a sorted list,
-- it returns a sorted list.

-- To write `insertSort`,
-- we can recursively apply this `insert` to the elements of the list:


{-@ insertSort :: (Ord a) => xs:[a] -> SList a @-}
insertSort            :: (Ord a) => [a] -> [a]
insertSort []         = []
insertSort (x:xs)     = insert x (insertSort xs)


-- And the system can prove that the result of `insertSort` is a sorted list.

-- Merge Sort
-- ----------

-- We first write a `merge` function:


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
  | x <= y
  = x:(merge xs (y:ys))
  | otherwise
  = y:(merge (x:xs) ys)


-- The system can prove that if both arguments of `merge` are sorted lists,
-- then its result is also a sorted list.

-- Next, we write a `split` function that splits any list in two sublists:

split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs         = (xs, [])


-- Finally, using the above functions we write `mergeSort`:


{-@ mergeSort :: (Ord a) => xs:[a] -> SList a @-}
mergeSort :: Ord a => [a] -> [a]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort xs1) (mergeSort xs2) where (xs1, xs2) = split xs


-- The system can prove that the result of `mergeSort` is a sorted list.
-- For the first two cases empty lists or lists with one element can easily proved
-- to be sorted. For the last case, if we assume that `mergeSort`'s result is a
-- sorted list, then `merge` is applied to two sorted lists, thus its result will
-- be also a sorted list.

-- Quick Sort
-- ----------

-- \begin{code}We would like to define `quickSort` as follows:
-- quickSort' []     = []
-- quickSort' (x:xs) = append' lts gts
--   where lts = quickSort' [y | y <- xs, y < x]
--         gts = quickSort' [z | z <- xs, z >= x]

-- append' []     ys  = ys
-- append' (x:xs) ys  = x : append' xs ys
-- \end{code}


-- In order for `quicksort` to return a sorted list,
-- append should return a sorted list.
-- Thus, we would like to be able to express the fact that `append`
-- is called with two sorted lists and each element of the first list
-- is less than each element of the second.
-- To do so, we provide `append` one more argument or a "ghost" variable, say `k`, of type `a`
-- and give it the type


{-@ append :: k:a -> l:SList {v:a | v<k} -> ge:SList {v:a | v>=k} -> SList a @-}


-- So, `append` is defined as:


append :: a -> [a] -> [a] -> [a]
append k []     ys  = ys
append k (x:xs) ys  = x : append k xs ys


-- And finally we can define `quicksort`:


{-@ quickSort :: (Ord a) => [a] -> SList a @-}
quickSort []     = []
quickSort (x:xs) = append x lts gts
  where lts = quickSort [y | y <- xs, y < x]
        gts = quickSort [z | z <- xs, z >= x]



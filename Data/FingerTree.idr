module FingerTree 

infixr 5 ><
infixr 5 <|, :<
infixl 5 |>, :>

data Affix a = One a | Two a a | Three a a a | Four a a a a  
data Node v a = Branch3 v a a a | Branch2 v a a 

data FingerTree v a 
  = Empty 
  | Single a
  | Deep 
    v                          -- annotation
    (Affix a)                  -- prefix
    (FingerTree v (Node v a))  -- deeper
    (Affix a)                  -- suffix

||| can data type and it's constructor have the same name? View instead of ViewEl
data View v a = Nil | ViewEl a (FingerTree v a)

||| There is no `deriving` mechanism in idris, let's write Show instances for all tree elements

Show a => Show (Affix a) where
  show (One x) = "One " ++ (show x)
  show (Two x y) = "Two " ++ (show x) ++ " " ++ (show y)
  show (Three x y z) = "Three " ++ (show x) ++ " " ++ (show y) ++ " " ++ (show z)
  show (Four x y z w) = "Four " ++ (show x) ++ " " ++ (show y) ++ " " ++ (show z) ++ " " ++ (show w)
  
(Show a, Show v) => Show (Node v a) where
  show (Branch3 p x y z) = " (Branch3 branch-annot: " ++ (show p) ++ " " ++ (show x) ++ " " ++ (show y) ++ " " ++ (show z) ++ ") "
  show (Branch2 p x y) = " (Branch2 branch-annot: " ++ (show p) ++ " " ++ (show x) ++ " " ++ (show y) ++ ") "
  
(Show a, Show v) => Show (FingerTree v a) where
  show Empty                         = "Empty"
  show (Single x)                    = "Single " ++ show x    
  show (Deep v prefix deeper suffix) = "Deep { annotation = " ++ (show v) ++ ", prefix = " ++ show prefix ++ ", deeper = " ++ show deeper ++ ", suffix = "  ++ show suffix ++ "}" 
            
(Show v, Show a) => Show (View v a) where
  show Nil = "Nil"
  show (ViewEl x tree) = "ViewEl " ++ show x ++ " rest_tree: " ++ show tree

||| Annotations are monoidal: type v is a member of monoid interface ( typeclass in haskell )

interface Monoid v =>  Measured v a where
  measure : a -> v  

||| foldr : (a -> b -> b) -> b -> FingerTree v a -> b
Foldable (Node v) where
 foldr f acc (Branch2 _ x y) = f x (f y acc)
 foldr f acc (Branch3 _ x y z) = f z $ f y (f z acc)
 
branch2        :  (Measured v a) => a -> a -> Node v a
branch2 a b    =   Branch2 (measure a <+> measure b) a b

branch3        :  (Measured v a) => a -> a -> a -> Node v a
branch3 a b c  =   Branch3 (measure a <+> measure b <+> measure c) a b c
 
Foldable Affix where
 foldr f acc (One x) = f x acc
 foldr f acc (Two x y) = f x (f y acc)
 foldr f acc (Three x y z) = f z $ f y (f z acc)
 foldr f acc (Four x y z w) = f x $ f y (f z (f w acc))

||| QUESTION: possible optimization. do we have interface IsList in Idris? 
||| to make (Affix a) and (Node a) it's instances? 
||| to use toList and fromList instead of toListAffix and toListNode?

toListAffix : Affix a -> List a
toListAffix (One x)        = [x]
toListAffix (Two x y)      = [x,y]
toListAffix (Three x y z)  = [x,y,z]
toListAffix (Four x y z w) = [x,y,z,w]

fromListAffix : List a -> Affix a
fromListAffix [x] = One x
fromListAffix [x,y] = Two x y
fromListAffix [x,y,z] = Three x y z
fromListAffix [x,y,z,w] = Four x y z w
||| fromListAffix _ = Error "Affix must be one to four elements"


toListNode : Node v a -> List a
toListNode (Branch3 _ a b c) = [a,b,c]
toListNode (Branch2 _ a b)   = [a,b]

fromListNode : Measured v a => List a -> Node v a
fromListNode [x,y] = Branch2 m x y where 
                                     m = measure x <+> measure y
fromListNode [x,y,z] = Branch3 m x y z where 
                                     m = (measure x <+> measure y) <+> measure z
|||fromList _ = Error "Node must contain 2 or three elements"                                                          

affixPrepend : a -> Affix a -> Affix a
affixPrepend x aff = fromListAffix $ x :: (toListAffix aff)

affixAppend : a -> Affix a -> Affix a               
affixAppend x aff = fromListAffix $ (toListAffix aff) ++ [x]
 
annotation : (Measured v a) => FingerTree v a -> v
annotation Empty          = neutral
annotation (Single x)     = measure x
annotation (Deep v _ _ _) =  v

||| Measurements. Making data type (FingerTree v a) an instance of interface Measured
Measured v a => Measured v (FingerTree v a) where    
 measure Empty      = neutral
 measure (Single x) = measure x
 measure tree       = annotation tree
 
Measured v a => Measured v (Affix a) where
 measure = mconcat . map measure . toListAffix where
                                                mconcat : List v -> v
                                                mconcat = foldr (<+>) neutral

Measured v a => Measured v (Node v a) where
 measure (Branch2 v _ _)   = v
 measure (Branch3 v _ _ _) = v

||| Convert an affix into an entire tree, doing rebalancing if nesassary
affixToTree : Measured v a => Affix a -> FingerTree v a
affixToTree affix = case (toListAffix affix) of
 [x]       => Single x
 [x,y]     => Deep (measure affix) (One x) Empty (One y)
 [x,y,z]   => Deep (measure affix) (One x) Empty (Two y z)
 [x,y,z,w] => Deep (measure affix) (Two x y) Empty (Two z w)


Foldable (FingerTree v) where
 foldr f acc Empty                          = acc
 foldr f acc (Single x)                     = f x acc
 foldr f acc (Deep _ pref deep suff) = foldr f foldedDeeper pref
                                                where
                                                   foldedDeeper = foldr f foldedSuffix deep
                                                   where 
                                                     foldedSuffix = foldr f acc suff


||| Analyze the right end of sequence
viewr : (Measured v a) => FingerTree v a -> View v a
viewr Empty = Nil
viewr (Single x) = ViewEl x Empty
viewr (Deep _ prefix deeper (One x)) = ViewEl x $
 case viewr deeper of 
  ViewEl node rest' => 
   let suff  = fromListAffix $ toListNode node
       annot = (measure prefix <+> measure rest') <+> measure suff in
   Deep annot prefix rest' suff
  Nil               => affixToTree prefix
viewr (Deep _ prefix deeper suffix) = 
 ViewEl suffixLast $ Deep annot prefix deeper suffixInit 
 where   
   annot           = (measure prefix <+> measure deeper) <+> measure suffixInit
   suffixLast      = case last' (toListAffix suffix) of 
                        Just t => t
   suffixInit      = fromListAffix xs  
                     where 
                        xs = case init' $ toListAffix suffix of
                               Just z => z
                                                                
   

||| Analyze the left end of sequence
viewl : Measured v a => FingerTree v a -> View v a
viewl Empty = Nil
viewl (Single x) = ViewEl x Empty
viewl (Deep _ (One x) deeper suffix) = ViewEl x $
 case viewl deeper of 
  ViewEl node rest' => 
   let pref  = fromListAffix $ toListNode node
       annot = (measure pref <+> measure rest') <+> measure suffix in
   Deep annot pref rest' suffix
  Nil               => affixToTree suffix
viewl (Deep _ prefix deeper suffix) = 
 ViewEl prefixLast $ Deep annot prefixInit deeper suffix
 where   
   annot           = (measure prefixInit <+> measure deeper) <+> measure suffix
   prefixLast      = case last' (toListAffix prefix) of 
                        Just t => t
   prefixInit      = fromListAffix xs  
                     where 
                        xs = case init' $ toListAffix prefix of
                               Just z => z
|||? what about Nothing? here and in other cases abowe?

||| the deep function creates `Deep` fingertrees
deep : Measured v a => List a -> FingerTree v (Node v a) -> List a -> FingerTree v a
deep {v} prefix deeper suffix = 
  case (prefix,suffix) of
    ([],[]) => case viewl deeper of 
      Nil                 => Empty
      ViewEl node deeper' => deep (toListNode node) deeper' [] 
    ([],_)  => case viewr deeper of 
      Nil                 => affixToTree $ fromListAffix suffix  
      ViewEl node deeper' => deep (toListNode node) deeper' suffix
    (_,[])  => case viewr deeper of 
      Nil                 => affixToTree $ fromListAffix prefix
      ViewEl node deeper' => deep prefix deeper' (toListNode node)
    _                     => Deep annotat (fromListAffix prefix) deeper (fromListAffix suffix)
  where
     annotat : v
     annotat = concat (map measure prefix) <+> measure deeper <+> concat (map measure suffix)

||| if ((length prefix) > 4) || ((length suffix) > 4)
|||            then error "Affixes can not be longer than 4 elem"            

||| CONSTRUCTION

||| The empty sequence
empty : Measured v a => FingerTree v a
empty = Empty

||| A singleton sequence
singleton : Measured v a => a -> FingerTree v a
singleton = Single 
     
||| is this the empty sequence?
null : FingerTree v a -> Bool
null Empty = True
null _     = False 
          
||| Create a sequence from a finite list of elements
|||fromList : Measured v a => List a -> FingerTree v a
|||fromList = foldr (<|) Empty

||| Create a list from a sequence 
toList : Measured v a => FingerTree v a -> List a
toList tree = case viewl tree of 
                Nil => []
                ViewEl x tree' => x :: toList tree'          


-- PROBLEM can't implement Eq and Ord  due to `possibly not total error`
{-
(Eq a, Measured v a) => Eq (FingerTree v a) where
    xs == ys = (FingerTree.toList xs == FingerTree.toList ys)


(Eq (FingerTree v a) , Ord a, Measured v a) => Ord (FingerTree v a) where
    compare xs ys = compare (FingerTree.toList xs) (FingerTree.toList ys)                          
    
-}        
                
                                                                                          
||| Add an element to the left end of sequence
(<|) : Measured v a => a -> FingerTree v a -> FingerTree v a
x <| Empty      = Single x
x <| (Single y) = Deep (measure x <+> measure y) (One x) Empty (One y)
x <| (Deep w (Four a1 a2 a3 a4) deeper suffix) = Deep (w <+> measure x) (Two x a1) (node <| deeper) suffix where
                                                 node = Branch3 (measure a2 <+> measure a3 <+> measure a4 ) a2 a3 a4
x <| (Deep w pref deeper suf) = Deep (w <+> measure x) (affixPrepend x pref) deeper suf

||| Add an element to the right end of sequence
(|>) : Measured v a => FingerTree v a -> a -> FingerTree v a
Empty |> x      = Single x
(Single x) |> y = Deep (measure x <+> measure y) (One x) Empty (One y)
(Deep w prefix deeper (Four a1 a2 a3 a4)) |> x = Deep (w <+> measure x) prefix (deeper |> node) (Two a4 x ) where
                                                 node = Branch3 (measure a1 <+> measure a2 <+> measure a3 ) a1 a2 a3
(Deep w pref deeper suf) |> x = Deep (w <+> measure x) pref deeper (affixAppend x suf)


||| Concatenate two sequences

nodes : Measured v a => List a -> List (Node v a)
nodes xs = case xs of 
   [x,y]      => [Branch2 ((measure x) <+> (measure y)) x y]
   [x,y,z]    => [Branch3 ((measure x) <+> (measure y) <+> measure z) x y z]
   x::y::rest => (Branch2 ((measure x) <+> (measure y)) x y) :: nodes rest

getPrefix : FingerTree v a -> Affix a
getPrefix (Deep _ prefix _ _) = prefix

getSuffix : FingerTree v a -> Affix a
getSuffix (Deep _ _ _ suffix) = suffix

getDeeper : FingerTree v a -> FingerTree v (Node v a)
getDeeper (Deep _ _ deeper _) = deeper

||| Possible ala-Idris improvement: 
||| FingerTree v a -> List a -> FingerTree w a -> FingerTree (v <+> m <+> (foldr (<+>) neutral (map measure (List a)))) a
concatWithMiddle : Measured v a => FingerTree v a -> List a -> FingerTree v a -> FingerTree v a
concatWithMiddle Empty      []      right = right
concatWithMiddle Empty      (x::xs) right = x <| concatWithMiddle Empty xs right
concatWithMiddle (Single y) xs      right = y <| concatWithMiddle Empty xs right

concatWithMiddle left [] Empty      = left
concatWithMiddle left xs Empty      = concatWithMiddle left initialList Empty |> lastList
                                      where
                                              initialList = case init' xs of 
                                                                  Just w => w
                                              lastList    = case last' xs of
                                                                  Just p => p
concatWithMiddle left xs (Single y) = concatWithMiddle left xs Empty |> y 

-- recursive case: both trees are deep
concatWithMiddle left mid right = Deep annot (getPrefix left) deeper' (getSuffix right) 
                                  where
                                     deeper' = concatWithMiddle (getDeeper left) mid' (getDeeper right)
                                     where 
                                        mid' = nodes $ (toListAffix $ getSuffix left) ++ mid ++ (toListAffix $ getPrefix right)    
                                     annot = annotation left <+> annotation right <+> foldr (<+>) neutral (map measure mid)


(><) : Measured v a => FingerTree v a -> FingerTree v a -> FingerTree v a
left >< right = concatWithMiddle left [] right 

||| Transformations
-- | /O(n)/. The reverse of a sequence.

reverseNode : (Measured v2 a2) => (a1 -> a2) -> Node v1 a1 -> Node v2 a2
reverseNode f (Branch2 _ a b) = branch2 (f b) (f a)
reverseNode f (Branch3 _ a b c) = branch3 (f c) (f b) (f a)

reverseAffix : (a -> b) -> Affix a -> Affix b
reverseAffix f (One a) = One (f a)
reverseAffix f (Two a b) = Two (f b) (f a)
reverseAffix f (Three a b c) = Three (f c) (f b) (f a)
reverseAffix f (Four a b c d) = Four (f d) (f c) (f b) (f a)

reverseTree : (Measured v2 a2) => (a1 -> a2) -> FingerTree v1 a1 -> FingerTree v2 a2
reverseTree _ Empty = Empty
reverseTree f (Single x) = Single (f x)
reverseTree f (Deep _ pr m sf) =
    deep (toListAffix (reverseAffix f sf)) (reverseTree (reverseNode f) m) (toListAffix (reverseAffix f pr))

reverse : (Measured v a) => FingerTree v a -> FingerTree v a
reverse = reverseTree id

||| Splitting and Search
-- | A result of 'search', attempting to find a point where a predicate
-- on splits of the sequence changes from 'False' to 'True'.

data SearchResult v a 
    = Position (FingerTree v a) a (FingerTree v a)
        -- ^ A tree opened at a particular element: the prefix to the
        -- left, the element, and the suffix to the right.
    | OnLeft
        -- ^ A position to the left of the sequence, indicating that the
        -- predicate is 'True' at both ends.
    | OnRight
        -- ^ A position to the right of the sequence, indicating that the
        -- predicate is 'False' at both ends.
    | Nowhere
        -- ^ No position in the tree, returned if the predicate is 'True'
        -- at the left end and 'False' at the right end.  This will not
        -- occur if the predicate in monotonic on the tree.     

-- making SearchResult an instance of Eq, Ord, Show 

(Show a, Show v) => Show (SearchResult v a) where
   show (Position tree1 e tree2) = "Position " ++ "(Tree1 = " ++ show tree1 ++ " )"
                                               ++ "(Element = " ++ show e ++ " )"
                                               ++ "(Tree1 = " ++ show tree1 ++ " )"
   show OnLeft = "OnLeft"
   show OnRight = "OnRight"
   show Nowhere = "Nowhere"      

{- PROBLEM: cant implement due to `possibly not total error`, see Ord, Eq (FingerTree v a)
(Eq (FingerTree v a), Eq a) => Eq (SearchResult v a) where
  (==) OnLeft OnLeft   = True
  (==) OnLeft _        = False
  (==) _      OnLeft   = False
  
  (==) OnRight OnRight  = True
  (==) OnRight _        = False
  (==) _       OnRight  = False
  
  (==) Nowhere Nowhere  = True
  (==) Nowhere _        = False
  (==) _       Nowhere  = False
  
  (==) (Position tree1 e tree2) (Position tree3 r tree4) = if ( tree1 == tree3 && 
                                                                e == r && 
                                                                tree2 == tree4 ) 
                                                           then True 
                                                           else False
  (==) (Position tree1 e tree2) _      = False
  (==) (Position tree1 e tree2) _      = False
-}  
  
{-Ord (SearchResult v a) where
  compare                                                                                            
  -}                                                                           




{- START TEST TEST TEST START ----------------------------- -}

-- 3-layered fingerTree
{-
layer3 : FingerTree v a
layer3 = Empty

layer2 : FingerTree Int (Node Int Char)
layer2 = Deep 9 pref layer3 suff
         where
            pref = Two (Branch2 2 'i' 's') (Branch2 2 'i' 's')
            suff = Two (Branch3 3 'n' 'o' 't') (Branch2 2 'a' 't')
            
layer1 : FingerTree Int  Char            
layer1 = Deep 14 prefi layer2 suffi
         where
            prefi = Two 't' 'h' 
            suffi = Three 'r' 'e' 'e'  

exampleTree : FingerTree Int Char
exampleTree = layer1
-}

{-
-- 4-layered fingerTree (hugeTree)

data SizeT = Size Int
data ValueT a = Value a

Show SizeT where
 show (Size x) = show x
 
Show b => Show (ValueT b) where
 show (Value x) = show x

Semigroup SizeT where
  (<+>) (Size x) (Size y) = Size $ x + y

Monoid SizeT where
  neutral               = Size 0

Monoid SizeT => Measured SizeT (ValueT a) where
  measure _ = Size 1 
 

layer4 : FingerTree v a                                          
layer4 = Empty

layer3 : FingerTree SizeT (Node SizeT (Node SizeT (ValueT Char)))                                       
layer3 = Deep (Size 27) pr layer4 su where
           pr = One (Branch2 (Size 4) 
                             (Branch2 (Size 2) (Value 'a') (Value 'b')) 
                             (Branch2 (Size 2) (Value 'a') (Value 'b')) )

           su = Four (Branch3 (Size 6) (Branch2 (Size 2) (Value 'a') (Value 'b')) (Branch2 (Size 2) (Value 'a') (Value 'b')) (Branch2 (Size 2) (Value 'a') (Value 'b')))
                     (Branch2 (Size 6) (Branch3 (Size 3) (Value 'a') (Value 'b') (Value 'c')) (Branch3 (Size 3) (Value 'a') (Value 'b') (Value 'c')))
                     (Branch2 (Size 6) (Branch3 (Size 3) (Value 'a') (Value 'b') (Value 'c')) (Branch3 (Size 3) (Value 'a') (Value 'b') (Value 'c')))
                     (Branch2 (Size 5) (Branch2 (Size 2) (Value 'a') (Value 'b')) (Branch3 (Size 3) (Value 'a') (Value 'b') (Value 'c')))

layer2 : FingerTree SizeT (Node SizeT (ValueT Char))
layer2 = Deep (Size 45) p layer3 s where
          p = Four (Branch3 (Size 3) (Value 'a') (Value 'b') (Value 'c'))
                   (Branch3 (Size 3) (Value 'a') (Value 'b') (Value 'c'))
                   (Branch3 (Size 3) (Value 'a') (Value 'b') (Value 'c'))
                   (Branch3 (Size 3) (Value 'a') (Value 'b') (Value 'c'))
          s = Three (Branch2 (Size 2) (Value 'a') (Value 'b'))
                    (Branch2 (Size 2) (Value 'a') (Value 'b'))
                    (Branch2 (Size 2) (Value 'a') (Value 'b'))

layer1 : FingerTree SizeT (ValueT Char)
layer1 = Deep (Size 50) (Three (Value 'a') (Value 'b') (Value 'c')) layer2 (Two (Value 'a') (Value 'b'))

hugeTree : FingerTree SizeT (ValueT Char)
hugeTree = layer1                     

-}

-- To TEST: 
{-show (viewr hugeTree)
show ((Value 't') <| ((Value 'd') <| hugeTree) )

--------   END TEST TEST TEST END  -------------------}

                                             
   
 
 

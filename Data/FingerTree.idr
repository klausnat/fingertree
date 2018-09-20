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

||| Annotations are monoidal: type v is a member of monoid interface ( typeclass in haskell )

interface Monoid v =>  Measured v a where
  measure : a -> v  

||| foldr : (a -> b -> b) -> b -> FingerTree v a -> b
Foldable (Node v) where
 foldr f acc (Branch2 _ x y) = f x (f y acc)
 foldr f acc (Branch3 _ x y z) = f z $ f y (f z acc)
 
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

{- Foldable (FingerTree v) where
 foldr f acc Empty                          = acc
 foldr f acc (Single x)                     = f x acc
 foldr f acc (Deep _ prefix deeper suffix ) = foldr f foldedDeeper prefix where
                                                foldedDeeper = foldr f foldedSuffix deeper
                                                foldedSuffix = foldr f acc suffix
-}

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
                                     mid' = nodes $ (toListAffix $ getSuffix left) ++ mid ++ (toListAffix $ getPrefix right)    
                                     annot = annotation left <+> annotation right <+> foldMap measure mid                                                                                     

(><) : Measured v a => FingerTree v a -> FingerTree v a -> FingerTree v a
left >< right = concatWithMiddle left [] right 


                                                                          

Show a => Show (FingerTree v a) where
 show Empty      = "Empty"
 show (Single x) = "x"            
 

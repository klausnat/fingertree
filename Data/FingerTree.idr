module FingerTree 

%default total

infixr 5 ><
infixr 5 <|, :<
infixl 5 |>, :>

data Digit a = One a | Two a a | Three a a a | Four a a a a
data Node v a = Node3 v a a a | Node2 v a a 

-- | A representation of a sequence of values of type @a@, allowing
-- access to the ends in constant time, and append and split in time
-- logarithmic in the size of the smaller piece.
--
-- The collection is also parameterized by a measure type @v@, which
-- is used to specify a position in the sequence for the 'split' operation.
-- The types of the operations enforce the constraint @'Measured' v a@,
-- which also implies that the type @v@ is determined by @a@.
--
-- A variety of abstract data types can be implemented by using different
-- element types and measurements.

data FingerTree v a 
  = Empty 
  | Single a
  | Deep 
    v                          -- annotation
    (Digit a)                  -- prefix
    (FingerTree v (Node v a))  -- deeper
    (Digit a)                  -- suffix
   
-- | View of the right end of a sequence.
data ViewR : (s : Type -> Type) -> (a: Type) -> Type where
    EmptyR : ViewR s a                -- ^ empty sequence
    (:>) : (s a) -> a -> ViewR s a    -- ^ the sequence minus the rightmost element,
                                      -- and the rightmost element
(Show (s a), Show a) => Show (ViewR s a) where
    show EmptyR = "EmptyR"
    show (tree :> a) = show tree ++ " :> " ++ show a

data ViewL : (s : Type -> Type) -> (a: Type) -> Type where
    EmptyL : ViewL s a                -- ^ empty sequence
    (:<) : a -> s a -> ViewL s a    -- ^ the sequence minus the rightmost element,
                                      -- and the rightmost element
(Show (s a), Show a) => Show (ViewL s a) where
    show EmptyL = "EmptyL"
    show (a :< tree) = show a ++ " :< " ++ show tree

(Functor s) => Functor (ViewL s) where
    map _ EmptyL    = EmptyL
    map f (x :< xs) = f x :< map f xs

(Functor s) => Functor (ViewR s) where
    map _ EmptyR    = EmptyR
    map f (xs :> x) = map f xs :> f x    
            
Show a => Show (Digit a) where
  show (One x) = "One " ++ (show x)
  show (Two x y) = "Two " ++ (show x) ++ " " ++ (show y)
  show (Three x y z) = "Three " ++ (show x) ++ " " ++ (show y) ++ " " ++ (show z)
  show (Four x y z w) = "Four " ++ (show x) ++ " " ++ (show y) ++ " " ++ (show z) ++ " " ++ (show w)
  
(Show a, Show v) => Show (Node v a) where
  show (Node3 p x y z) = " (Node3 node-annot: " ++ (show p) ++ " " ++ (show x) ++ " " ++ (show y) ++ " " ++ (show z) ++ ") "
  show (Node2 p x y) = " (Node2 node-annot: " ++ (show p) ++ " " ++ (show x) ++ " " ++ (show y) ++ ") "
  
(Show a, Show v) => Show (FingerTree v a) where
  show Empty                         = "Empty"
  show (Single x)                    = "Single " ++ show x    
  show (Deep v prefix deeper suffix) = "Deep { annotation = " ++ (show v) ++ ", prefix = " ++ show prefix ++ ", deeper = " ++ show deeper ++ ", suffix = "  ++ show suffix ++ "}" 
                                    
||| Annotations are monoidal: type v is a member of monoid interface ( typeclass in haskell )

interface Monoid v =>  Measured v a where
  measure : a -> v  

mapDigit : (a -> b) -> Digit a -> Digit b
mapDigit f (One a) = One (f a)
mapDigit f (Two a b) = Two (f a) (f b)
mapDigit f (Three a b c) = Three (f a) (f b) (f c)
mapDigit f (Four a b c d) = Four (f a) (f b) (f c) (f d)

||| foldr : (a -> b -> b) -> b -> FingerTree v a -> b
Foldable (Node v) where
 foldr f acc (Node2 _ x y) = f x (f y acc)
 foldr f acc (Node3 _ x y z) = f z $ f y (f z acc)
 
node2        :  (Measured v a) => a -> a -> Node v a
node2 a b    =   Node2 (measure a <+> measure b) a b

node3        :  (Measured v a) => a -> a -> a -> Node v a
node3 a b c  =   Node3 (measure a <+> measure b <+> measure c) a b c
 
Foldable Digit where
 foldr f acc (One x) = f x acc
 foldr f acc (Two x y) = f x (f y acc)
 foldr f acc (Three x y z) = f z $ f y (f z acc)
 foldr f acc (Four x y z w) = f x $ f y (f z (f w acc))


(Measured v a) => Measured v (Digit a) where
    measure (One x) = measure x 
    measure (Two x y) = measure x <+> measure y
    measure (Three x y z) = measure x <+> measure y <+> measure z
    measure (Four x y z w) = measure x <+> measure y <+> measure z <+> measure w

(Monoid v) => Measured v (Node v a) where
    measure (Node2 v _ _)    =  v
    measure (Node3 v _ _ _)  =  v

(Measured v a) => Measured v (FingerTree v a) where
    measure Empty           =  neutral
    measure (Single x)      =  measure x
    measure (Deep v _ _ _)  =  v


nodeToDigit : Node v a -> Digit a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

toListDigit : Digit a -> List a
toListDigit (One x)        = [x]
toListDigit (Two x y)      = [x,y]
toListDigit (Three x y z)  = [x,y,z]
toListDigit (Four x y z w) = [x,y,z,w]


toListNode : Node v a -> List a
toListNode (Node3 _ a b c) = [a,b,c]
toListNode (Node2 _ a b)   = [a,b]

deep : (Measured v a) =>
     Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deep pr m sf =
    Deep ((measure pr <+>  measure m) <+> measure sf) pr m sf

||| Convert an affix into an entire tree, doing rebalancing if nesassary
digitToTree : (Measured v a) => Digit a -> FingerTree v a
digitToTree (One a) = Single a
digitToTree (Two a b) = deep (One a) Empty (One b)
digitToTree (Three a b c) = deep (Two a b) Empty (One c)
digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

||| Analyze the left end of sequence
lheadDigit : Digit a -> a
lheadDigit (One a) = a
lheadDigit (Two a _) = a
lheadDigit (Three a _ _) = a
lheadDigit (Four a _ _ _) = a

ltailDigit : Digit a -> Digit a
ltailDigit (One x) = One x 
ltailDigit (Two _ b) = One b
ltailDigit (Three _ b c) = Two b c
ltailDigit (Four _ b c d) = Three b c d

mutual 
  rotL : (Measured v a) => FingerTree v (Node v a) -> Digit a -> FingerTree v a
  rotL m sf      =   case viewl m of
                      EmptyL  =>  digitToTree sf
                      a :< m' =>  Deep (measure m <+> measure sf) (nodeToDigit a) m' sf

  viewl : (Measured v a) => FingerTree v a -> ViewL (FingerTree v) a
  viewl Empty                     =  EmptyL
  viewl (Single x)                =  (:<) x Empty
  viewl (Deep _ (One x) m sf)     =  (:<) x (rotL m sf)
  viewl (Deep _ pr m sf)          =  (:<) (lheadDigit pr) (deep (ltailDigit pr) m sf)

-- | /O(1)/. Analyse the right end of a sequence.

rheadDigit : Digit a -> a
rheadDigit (One a) = a
rheadDigit (Two _ b) = b
rheadDigit (Three _ _ c) = c
rheadDigit (Four _ _ _ d) = d

rtailDigit : Digit a -> Digit a
rtailDigit (One z) = One z
rtailDigit (Two a _) = One a
rtailDigit (Three a b _) = Two a b
rtailDigit (Four a b c _) = Three a b c

mutual
  viewr : (Measured v a) => FingerTree v a -> ViewR (FingerTree v) a
  viewr Empty                     =  EmptyR
  viewr (Single x)                =  Empty :> x
  viewr (Deep _ pr m (One x))     =  rotR pr m :> x
  viewr (Deep _ pr m sf)          =  deep pr m (rtailDigit sf) :> rheadDigit sf

  rotR : (Measured v a) => Digit a -> FingerTree v (Node v a) -> FingerTree v a
  rotR pr m = case viewr m of
               EmptyR  =>  digitToTree pr
               m' :> a =>  Deep (measure pr <+> measure m) pr m' (nodeToDigit a)

||| Construction, deconstruction and concatenation

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
        
||| Add an element to the left end of sequence
(<|) : Measured v a => a -> FingerTree v a -> FingerTree v a
x <| Empty      = Single x
x <| (Single y) = Deep (measure x <+> measure y) (One x) Empty (One y)
x <| (Deep w (Four a1 a2 a3 a4) deeper suffix) = Deep (w <+> measure x) (Two x a1) (node <| deeper) suffix where
                                                 node = Node3 (measure a2 <+> measure a3 <+> measure a4 ) a2 a3 a4
x <| (Deep w (Three a1 a2 a3) deeper suf) = Deep (w <+> measure x) (Four x a1 a2 a3) deeper suf
x <| (Deep w (Two a1 a2 ) deeper suf) = Deep (w <+> measure x) (Three x a1 a2) deeper suf
x <| (Deep w (One a1) deeper suf) = Deep (w <+> measure x) (Two x a1) deeper suf

||| Add an element to the right end of sequence
(|>) : Measured v a => FingerTree v a -> a -> FingerTree v a
Empty |> x      = Single x
(Single x) |> y = Deep (measure x <+> measure y) (One x) Empty (One y)
(Deep w prefix deeper (Four a1 a2 a3 a4)) |> x = Deep (w <+> measure x) prefix (deeper |> node) (Two a4 x ) where
                                                 node = Node3 (measure a1 <+> measure a2 <+> measure a3 ) a1 a2 a3
(Deep w pref deeper (Three a1 a2 a3)) |> x = Deep (w <+> measure x) pref deeper (Four a1 a2 a3 x)
(Deep w pref deeper (Two a1 a2)) |> x = Deep (w <+> measure x) pref deeper (Three a1 a2 x)
(Deep w pref deeper (One a1)) |> x = Deep (w <+> measure x) pref deeper (Two a1 x)

-- | /O(n)/. Create a sequence from a finite list of elements.
-- The opposite operation 'toList' is supplied by the 'Foldable' instance.
fromList : (Measured v a) => List a -> FingerTree v a
fromList = foldr (<|) Empty

----------------
-- Concatenation
----------------

mutual
  appendTree0 : (Measured v a) => FingerTree v a -> FingerTree v a -> FingerTree v a
  appendTree0 Empty xs = xs
  appendTree0 xs Empty = xs
  appendTree0 (Single x) xs = x <| xs
  appendTree0 xs (Single x) = xs |> x
  appendTree0 (Deep _ pr1 m1 sf1) (Deep _ pr2 m2 sf2) = deep pr1 (addDigits0 m1 sf1 pr2 m2) sf2

  addDigits0 : (Measured v a) => FingerTree v (Node v a) -> Digit a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
  addDigits0 m1 (One a) (One b) m2 = appendTree1 m1 (node2 a b) m2
  addDigits0 m1 (One a) (Two b c) m2 = appendTree1 m1 (node3 a b c) m2
  addDigits0 m1 (One a) (Three b c d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits0 m1 (One a) (Four b c d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Two a b) (One c) m2 = appendTree1 m1 (node3 a b c) m2
  addDigits0 m1 (Two a b) (Two c d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits0 m1 (Two a b) (Three c d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Two a b) (Four c d e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits0 m1 (Three a b c) (One d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits0 m1 (Three a b c) (Two d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Three a b c) (Three d e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits0 m1 (Three a b c) (Four d e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits0 m1 (Four a b c d) (One e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Four a b c d) (Two e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits0 m1 (Four a b c d) (Three e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits0 m1 (Four a b c d) (Four e f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2

  appendTree1 : (Measured v a) => FingerTree v a -> a -> FingerTree v a -> FingerTree v a
  appendTree1 Empty a xs = a <| xs
  appendTree1 xs a Empty = xs |> a
  appendTree1 (Single x) a xs = x <| a <| xs
  appendTree1 xs a (Single x) = xs |> a |> x
  appendTree1 (Deep _ pr1 m1 sf1) a (Deep _ pr2 m2 sf2) = deep pr1 (addDigits1 m1 sf1 a pr2 m2) sf2

  addDigits1 : (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
  addDigits1 m1 (One a) b (One c) m2 = appendTree1 m1 (node3 a b c) m2
  addDigits1 m1 (One a) b (Two c d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits1 m1 (One a) b (Three c d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (One a) b (Four c d e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Two a b) c (One d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits1 m1 (Two a b) c (Two d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (Two a b) c (Three d e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Two a b) c (Four d e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Three a b c) d (One e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (Three a b c) d (Two e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Three a b c) d (Three e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Three a b c) d (Four e f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits1 m1 (Four a b c d) e (One f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Four a b c d) e (Two f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Four a b c d) e (Three f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits1 m1 (Four a b c d) e (Four f g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2

  appendTree2 : (Measured v a) => FingerTree v a -> a -> a -> FingerTree v a -> FingerTree v a
  appendTree2 Empty a b xs = a <| b <| xs
  appendTree2 xs a b Empty = xs |> a |> b
  appendTree2 (Single x) a b xs = x <| a <| b <| xs
  appendTree2 xs a b (Single x) = xs |> a |> b |> x
  appendTree2 (Deep _ pr1 m1 sf1) a b (Deep _ pr2 m2 sf2) = deep pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2

  addDigits2 : (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
  addDigits2 m1 (One a) b c (One d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits2 m1 (One a) b c (Two d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits2 m1 (One a) b c (Three d e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (One a) b c (Four d e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Two a b) c d (One e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits2 m1 (Two a b) c d (Two e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (Two a b) c d (Three e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Two a b) c d (Four e f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Three a b c) d e (One f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (Three a b c) d e (Two f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Three a b c) d e (Three f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Three a b c) d e (Four f g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits2 m1 (Four a b c d) e f (One g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Four a b c d) e f (Two g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Four a b c d) e f (Three g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2

  appendTree3 : (Measured v a) => FingerTree v a -> a -> a -> a -> FingerTree v a -> FingerTree v a
  appendTree3 Empty a b c xs = a <| b <| c <| xs
  appendTree3 xs a b c Empty = xs |> a |> b |> c
  appendTree3 (Single x) a b c xs = x <| a <| b <| c <| xs
  appendTree3 xs a b c (Single x) = xs |> a |> b |> c |> x
  appendTree3 (Deep _ pr1 m1 sf1) a b c (Deep _ pr2 m2 sf2) = deep pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2

  addDigits3 : (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
  addDigits3 m1 (One a) b c d (One e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits3 m1 (One a) b c d (Two e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits3 m1 (One a) b c d (Three e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (One a) b c d (Four e f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Two a b) c d e (One f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits3 m1 (Two a b) c d e (Two f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (Two a b) c d e (Three f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Two a b) c d e (Four f g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Three a b c) d e f (One g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (Three a b c) d e f (Two g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Three a b c) d e f (Three g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits3 m1 (Four a b c d) e f g (One h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Four a b c d) e f g (Two h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2

  appendTree4 : (Measured v a) => FingerTree v a -> a -> a -> a -> a -> FingerTree v a -> FingerTree v a
  appendTree4 Empty a b c d xs = a <| b <| c <| d <| xs
  appendTree4 xs a b c d Empty = xs |> a |> b |> c |> d
  appendTree4 (Single x) a b c d xs = x <| a <| b <| c <| d <| xs
  appendTree4 xs a b c d (Single x) = xs |> a |> b |> c |> d |> x
  appendTree4 (Deep _ pr1 m1 sf1) a b c d (Deep _ pr2 m2 sf2) = deep pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2

  addDigits4 : (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
  addDigits4 m1 (One a) b c d e (One f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits4 m1 (One a) b c d e (Two f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits4 m1 (One a) b c d e (Three f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (One a) b c d e (Four f g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Two a b) c d e f (One g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits4 m1 (Two a b) c d e f (Two g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (Two a b) c d e f (Three g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Three a b c) d e f g (One h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (Three a b c) d e f g (Two h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
  addDigits4 m1 (Four a b c d) e f g h (One i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
  addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2
  
-- | /O(log(min(n1,n2)))/. Concatenate two sequences.
(><) : (Measured v a) => FingerTree v a -> FingerTree v a -> FingerTree v a
(><) =  appendTree0

(Measured v a) => Semigroup (FingerTree v a) where
  (<+>) = (><)

(Semigroup (FingerTree v a)) => Monoid (FingerTree v a) where
    neutral = Empty


--foldr : (a -> b -> b) -> b -> FingerTree v a -> b

Foldable (FingerTree v) where
  foldr f acc Empty                          = acc
  foldr f acc (Single x)                     = f x acc
  foldr {v} f acc (Deep _ pref deep suff) = foldr f (foldr (flip $ foldr f) (foldr f acc suff) deep) pref 
--    where
--      func = ??

-- но deep может состоять из prefix deeper suffix, для афиксов не бывает neutral       


-- Foldable (FingerTree v) required
{-
(Eq a) => Eq (FingerTree v a) where
    xs == ys = toList xs == toList ys

-- | Lexicographical order from left to right.
(Ord a) => Ord (FingerTree v a) where
    compare xs ys = compare (toList xs) (toList ys)
-}


||| Transformations
-- | /O(n)/. The reverse of a sequence.

reverseNode : (Measured v2 a2) => (a1 -> a2) -> Node v1 a1 -> Node v2 a2
reverseNode f (Node2 _ a b) = node2 (f b) (f a)
reverseNode f (Node3 _ a b c) = node3 (f c) (f b) (f a)

reverseDigit : (a -> b) -> Digit a -> Digit b
reverseDigit f (One a) = One (f a)
reverseDigit f (Two a b) = Two (f b) (f a)
reverseDigit f (Three a b c) = Three (f c) (f b) (f a)
reverseDigit f (Four a b c d) = Four (f d) (f c) (f b) (f a)

reverseTree : (Measured v2 a2) => (a1 -> a2) -> FingerTree v1 a1 -> FingerTree v2 a2
reverseTree _ Empty = Empty
reverseTree f (Single x) = Single (f x)
reverseTree f (Deep _ pr m sf) =
    deep (reverseDigit f sf) (reverseTree (reverseNode f) m) (reverseDigit f pr)

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
{-
-- PROBLEM: cant implement due to `possibly not total error`, see Ord, Eq (FingerTree v a)
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
            pref = Two (Node2 2 'i' 's') (Node2 2 'i' 's')
            suff = Two (Node3 3 'n' 'o' 't') (Node2 2 'a' 't')
            
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
           pr = One (Node2 (Size 4) 
                             (Node2 (Size 2) (Value 'a') (Value 'b')) 
                             (Node2 (Size 2) (Value 'a') (Value 'b')) )

           su = Four (Node3 (Size 6) (Node2 (Size 2) (Value 'a') (Value 'b')) (Node2 (Size 2) (Value 'a') (Value 'b')) (Node2 (Size 2) (Value 'a') (Value 'b')))
                     (Node2 (Size 6) (Node3 (Size 3) (Value 'a') (Value 'b') (Value 'c')) (Node3 (Size 3) (Value 'a') (Value 'b') (Value 'c')))
                     (Node2 (Size 6) (Node3 (Size 3) (Value 'a') (Value 'b') (Value 'c')) (Node3 (Size 3) (Value 'a') (Value 'b') (Value 'c')))
                     (Node2 (Size 5) (Node2 (Size 2) (Value 'a') (Value 'b')) (Node3 (Size 3) (Value 'a') (Value 'b') (Value 'c')))

layer2 : FingerTree SizeT (Node SizeT (ValueT Char))
layer2 = Deep (Size 45) p layer3 s where
          p = Four (Node3 (Size 3) (Value 'a') (Value 'b') (Value 'c'))
                   (Node3 (Size 3) (Value 'a') (Value 'b') (Value 'c'))
                   (Node3 (Size 3) (Value 'a') (Value 'b') (Value 'c'))
                   (Node3 (Size 3) (Value 'a') (Value 'b') (Value 'c'))
          s = Three (Node2 (Size 2) (Value 'a') (Value 'b'))
                    (Node2 (Size 2) (Value 'a') (Value 'b'))
                    (Node2 (Size 2) (Value 'a') (Value 'b'))

layer1 : FingerTree SizeT (ValueT Char)
layer1 = Deep (Size 50) (Three (Value 'a') (Value 'b') (Value 'c')) layer2 (Two (Value 'a') (Value 'b'))

hugeTree : FingerTree SizeT (ValueT Char)
hugeTree = layer1                     

-}

-- To TEST: 
{-show (viewr hugeTree)
show ((Value 't') <| ((Value 'd') <| hugeTree) )

--------   END TEST TEST TEST END  -------------------}

                                             
   
 
 

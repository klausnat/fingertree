module FingerTree 

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

||| QUESTION: possible optimization. do we have interface IsList in Idris? 
||| to make Affix a and Node a it's instances? 
||| to use toList and fromList instead of toListAffix and toListNode?

toListAffix : Affix a -> List a
toListAffix (One x)        = [x]
toListAffix (Two x y)      = [x,y]
toListAffix (Three x y z)  = [x,y,z]
toListAffix (Four x y z w) = [x,y,z,w]

toListNode : Node v a -> List a
toListNode (Branch3 _ a b c) = [a,b,c]
toListNode (Branch2 _ a b)   = [a,b]
 
||| Annotations are monoidal: type v is a member of monoid interface ( typeclass in haskell )

interface MonoidT m where
  -- Called 'mempty' in the Haskell base library.
  neutral : m
  -- Called 'mappend' in the Haskell base library.
  (<+>) : m -> m -> m

interface MonoidT v =>  Measured a v where
  measure : a -> v  

concat : MonoidT m => List m -> m
concat = foldr (<+>) neutral

annotation : (Measured a v) => FingerTree v a -> v
annotation Empty          = neutral
annotation (Single x)     = measure x
annotation (Deep v _ _ _) =  v


||| Let's make data type (FingerTree v a) an instance of interface Measured
Measured a v => Measured (FingerTree v a) v where    
 measure Empty      = neutral
 measure (Single x) = measure x
 measure tree       = annotation tree
 
Measured a v => Measured (Affix a) v where
 measure = concat . map measure . toListAffix

Measured a v => Measured (Node v a) v where
 measure (Branch2 v _ _)   = v
 measure (Branch3 v _ _ _) = v

Show a => Show (FingerTree v a) where
 show Empty      = "Empty"
 show (Single x) = "x"            
 

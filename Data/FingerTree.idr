module FingerTree 

data Affix a = One a | Two a a | Tree a a a | Four a a a a  
data Node v a = Branch3 v a a a | Branch2 v a a 

data FingerTree v a 
  = Empty 
  | Single a
  | Deep 
    v                          -- annotation
    (Affix a)                  -- prefix
    (FingerTree v (Node v a))  -- deeper
    (Affix a)                  -- suffix
  
interface Measured a where
 measure : a -> b  

     
(Measured a, Algebra.Monoid v) => Measured v (FingerTree v a) where
 measure Empty      = neutral
 measure (Single x) = measure x 
 measure (Deep v _ _ _) = v

Show a => Show (FingerTree v a) where
 show Empty      = "Empty"
 show (Single x) = "x"            
 

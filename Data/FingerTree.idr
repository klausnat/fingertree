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

||| can data type and it's constructor have the same name? View instead of ViewEl
data View v a = Nil | ViewEl a (FingerTree v a)

||| Annotations are monoidal: type v is a member of monoid interface ( typeclass in haskell )

interface MonoidT m where
  -- Called 'mempty' in the Haskell base library.
  neutral : m
  -- Called 'mappend' in the Haskell base library.
  (<+>) : m -> m -> m

interface MonoidT v =>  Measured a v where
  measure : a -> v  

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

fromListNode : Measured a v => List a -> Node v a
fromListNode [x,y] = Branch2 m x y where 
                                     m = measure x <+> measure y
fromListNode [x,y,z] = Branch3 m x y z where 
                                     m = measure x <+> measure y <+> measure z
|||fromList _ = Error "Node must contain 2 or three elements"                                                                          
 
||| mconcat in haskell prelude
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

||| Convert an affix into an entire tree, doing rebalancing if nesassary
affixToTree : Measured a v => Affix a -> FingerTree v a
affixToTree affix = case (toListAffix affix) of
 [x]       => Single x
 [x,y]     => Deep (measure affix) (One x) Empty (One y)
 [x,y,z]   => Deep (measure affix) (One x) Empty (Two y z)
 [x,y,z,w] => Deep (measure affix) (Two x y) Empty (Two z w)

viewr : (Measured a v) => FingerTree v a -> View v a
viewr Empty = Nil
viewr (Single x) = ViewEl x Empty
viewr (Deep _ prefix deeper (One x)) = ViewEl x $
 case viewr deeper of 
  ViewEl node rest' => 
   let suff  = fromListAffix $ toListNode node
       annot = measure prefix <+> measure rest' <+> measure suff in
   Deep annot prefix rest' suff
  Nil               => affixToTree prefix
viewr (Deep _ prefix deeper suffix) = 
 ViewEl suffixLast $ Deep annot prefix deeper suffixInit 
 where   
   annot           = measure prefix <+> measure deeper <+> measure suffixInit
   suffixLast      = case last' (toListAffix suffix) of 
                        Just t => t
   suffixInit      = fromListAffix xs  
                     where 
                        xs = case init' $ toListAffix suffix of
                               Just z => z
                                                                
   


viewl : Measured a v => FingerTree v a -> View v a
viewl Empty = Nil
viewl (Single x) = ViewEl x Empty
viewl (Deep _ (One x) deeper suffix) = ViewEl x $
 case viewl deeper of 
  ViewEl node rest' => 
   let pref  = fromListAffix $ toListNode node
       annot = measure pref <+> measure rest' <+> measure suffix in
   Deep annot pref rest' suffix
  Nil               => affixToTree suffix
viewl (Deep _ prefix deeper suffix) = 
 ViewEl prefixLast $ Deep annot prefixInit deeper suffix
 where   
   annot           = measure prefixInit <+> measure deeper <+> measure suffix
   prefixLast      = case last' (toListAffix prefix) of 
                        Just t => t
   prefixInit      = fromListAffix xs  
                     where 
                        xs = case init' $ toListAffix prefix of
                               Just z => z


||| the deep function creates `Deep` fingertrees
deep : Measured a v => List a -> FingerTree v (Node v a) -> List a -> FingerTree v a
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
                                    
Show a => Show (FingerTree v a) where
 show Empty      = "Empty"
 show (Single x) = "x"            
 

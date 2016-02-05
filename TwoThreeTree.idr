module TwoThreeTree
%access abstract

data TwoThreeTree : Type -> Type where
  Nil  : TwoThreeTree a
  Leaf : a -> TwoThreeTree a
  Node : a -> a -> TwoThreeTree a -> TwoThreeTree a 
    -> Maybe (TwoThreeTree a) -> TwoThreeTree a
  
-- Lookup value
lookup : (Eq a, Ord a) => a -> TwoThreeTree a -> Bool
lookup x Nil = False
lookup x (Leaf r) = (x == r)
lookup x (Node lm mm lc mc rc) = 
  if x <= lm then
    lookup x lc
  else
    if (x > lm)  && (x <= mm) then
      lookup x mc
    else
      case rc of
        Nothing => False
        Just tt => lookup x tt

-- Tree2List function
Tree2List : TwoThreeTree a -> List a
Tree2List Nil = []
Tree2List (Leaf x) = [x]
Tree2List (Node x y z w Nothing) = (Tree2List z) ++ (Tree2List w)
Tree2List (Node x y z w (Just s)) = (Tree2List z) ++ (Tree2List w) ++ (Tree2List s)

Show a => Show (TwoThreeTree a) where
  show x = show (Tree2List x)

private
update_lm_mm : Ord a => TwoThreeTree a -> TwoThreeTree a
update_lm_mm Nil = Nil
update_lm_mm (Leaf x) = Leaf x
update_lm_mm (Node lm mm (Leaf u) (Leaf v) y1) = 
    Node (max lm u) (max mm v) (Leaf u) (Leaf v) y1
update_lm_mm (Node lm mm (Leaf u) mst y1) = 
    Node (max lm u) (foldl max mm (Tree2List mst)) (Leaf u) mst y1
update_lm_mm (Node lm mm lst (Leaf s1) y1) = 
    Node (foldl max lm (Tree2List lst)) (max mm s1) lst (Leaf s1) y1
update_lm_mm (Node lm mm lst mst y1) = 
    Node (foldl max lm (Tree2List lst)) (foldl max mm (Tree2List mst)) lst mst y1

private
insert : Ord a => a -> TwoThreeTree a 
  -> (TwoThreeTree a, Maybe(TwoThreeTree a))
insert x Nil = (Leaf x, Nothing)
insert x (Leaf y) = 
  if y <= x then
    (Node y x (Leaf y) (Leaf x) Nothing, Nothing)
  else
    (Node x y (Leaf x) (Leaf y) Nothing, Nothing)

insert x y = insert' x y where
  insert' : a -> TwoThreeTree a 
    -> (TwoThreeTree a, Maybe (TwoThreeTree a))
  insert' x (Node y z (Leaf w) (Leaf s) t) = 
    insert'' x y z w s t where
    insert'' : a -> a -> a -> a -> a -> Maybe (TwoThreeTree a) 
      -> (TwoThreeTree a, Maybe (TwoThreeTree a))
    insert'' x lm mm lsl msl Nothing =
      if x <= lm then
        (Node x lm (Leaf x) (Leaf lsl) (Just (Leaf msl)), Nothing)
      else
        if (x > lm) && (x <= mm) then
          (Node lm x (Leaf lsl) (Leaf x) (Just (Leaf msl)), Nothing)
        else
          (Node lm mm (Leaf lsl) (Leaf msl) (Just (Leaf x)), Nothing)
    insert'' k lm mm lf mf (Just (Leaf rf)) =
      if k <= lm then
        (Node k lm (Leaf k) (Leaf lm) Nothing,   -- This is node n
         Just (Node mm rf (Leaf mm) (Leaf rf) Nothing)) -- This is node m
      else 
        if (k > lm) && (k <= mm) then
          (Node lm k (Leaf lm) (Leaf k) Nothing,
           Just (Node mm rf (Leaf mm) (Leaf rf) Nothing))
        else
          if (k > mm) && (k <= rf) then
            (Node lm mm (Leaf lm) (Leaf mm) Nothing,
             Just (Node k rf (Leaf k) (Leaf rf) Nothing))
          else
            (Node lm mm (Leaf lm) (Leaf mm) Nothing,
             Just (Node rf k (Leaf rf) (Leaf k) Nothing))

    -- TODO This should never happen, because all leaves are the same
    -- level!
    -- insert'' x y z x1 y1 (Just (Node u v z1 w1 s1)) = ?b_2
  
  insert' x (Node y z lst mst t) = 
    if x <= y then
      let (n, m) = insert x lst in
          case m of
            Nothing => (Node y z n mst t, Nothing)
            Just m => 
              case t of
                Nothing => (Node y z n m (Just mst), Nothing)
                Just m1 => (Node y z n m (Just mst), Just m1)
    else
      if (x > y) && (x <= z) then
        let (n, m) = insert x mst in
          case m of
            Nothing => (Node y z lst n t, Nothing)
            Just m =>
              case t of
                Nothing => (Node y z lst n (Just m), Nothing)
                Just m1 => (Node y z lst n (Just m), Just m1)
      else
        case t of
          Just u => 
            let (n, m) = insert x u in
              case m of
                Nothing => (Node y z lst mst (Just n), Nothing) 
                Just w => (Node y z lst mst (Just n), Just w)
          Nothing => 
            let (n, m) = insert x mst in
            case m of
              Nothing => (Node y z lst n Nothing, Nothing)
              Just w => (Node y z lst n Nothing, m)

private
get : Ord a => TwoThreeTree a -> a
get (Leaf x) = x
get (Node x y z w s) = max x y

-- Insert function XXX: Make this update_lm_mm inlined with insertion
-- itself!
Insert : Ord a => a -> TwoThreeTree a -> TwoThreeTree a
Insert x y = 
  if (lookup x y) /= True then
    let (n, m) = insert x y in
      case m of
        Nothing => update_lm_mm n
        Just m => update_lm_mm (Node (get n) (get m) n m Nothing)
  else y

-- Functor on TwoThreeTree
Functor TwoThreeTree where
  map f Nil = Nil
  map f (Leaf x) = Leaf (f x)
  map f (Node x y z w Nothing) = Node (f x) (f y) (map f z) (map f w) Nothing
  map f (Node x y z w (Just s)) = Node (f x) (f y) (map f z) (map f w) 
    (Just (assert_total (map f s)))
  
  
private  
delete' : (Ord a, Eq a) => a -> TwoThreeTree a -> (TwoThreeTree a, Bool)

-- This is the case where there are 3 children
delete' k (Node y z (Leaf w) (Leaf s) (Just t)) = 
  -- Remove the left leaf
  if k == w then
    (Node z (get_val t) (Leaf s) t Nothing, False)
  else
    -- Remove the middle leaf
    if k == s then
      (Node y (get_val t) (Leaf w) t Nothing, False)
    -- Remove the right leaf
    else
      (Node y z (Leaf w) (Leaf s) Nothing, False) where
  get_val : TwoThreeTree a -> a
  get_val (Leaf x) = x

-- This is the case where there are only 2 children
delete' k (Node y z (Leaf w) (Leaf s) Nothing) = 
  if (k == y) || (k == z) then
    (Node y z (Leaf w) (Leaf s) Nothing, True)
  else
    (Node y z (Leaf w) (Leaf s) Nothing, False)
  
-- Still need to recurse trying to find the leafs!
delete' k (Node y z lst mst t) = 
  if k <= y then
    case delete' k lst of
      (tt, True) => 
        case mst of
          Node _ _ _ _ (Just _) => (delete'' k y z lst mst t, False)
          Node _ _ _ _ Nothing  => 
            case t of
              Just (Node na nb nc nd (Just ne)) => 
                (delete'' k y z lst (Node na nb nc nd (Just ne)) (Just mst), False)
              Just (Node _ _ _ _ Nothing) => (delete''' k y z lst mst t, False)
              Nothing => (delete''' k y z lst mst t, False)
      (tt, False) => (Node y z tt mst t, False)
  else
    if (k > y) && (k <= z) then
      case delete' k mst of 
        (tt, True) => 
          case lst of
            Node _ _ _ _ (Just _) => (delete'' k y z mst lst t, False)
            Node _ _ _ _ Nothing  => 
              case t of
                Just (Node na nb nc nd (Just ne)) => 
                  (delete'' k y z mst (Node na nb nc nd (Just ne)) (Just lst), False)
                Just (Node _ _ _ _ Nothing) => (delete''' k y z mst lst t, False)
                Nothing => (delete''' k y z mst lst t, False)
        (tt, False) => (Node y z lst tt t, False)
    else
      case t of
        Just ttt => 
          case delete' k ttt of
            (tt, True) => 
              case lst of
                Node _ _ _ _ (Just _) => (delete'' k y z ttt lst (Just mst), False)
                Node _ _ _ _ Nothing  => 
                  case mst of
                    Node _ _ _ _ (Just _) => (delete'' k y z ttt mst (Just lst), False)
                    Node _ _ _ _ Nothing => (delete''' k y z ttt lst (Just mst), False)
            (tt, False) => (Node y z lst mst (Just tt), False)
        Nothing => (Node y z lst mst t, False) 
  where
  -- The case when the sibling has 3 kids
  delete'' : (k : a) -> (lm : a) -> (mm : a) -> (td : TwoThreeTree a) 
             -> (sibling : TwoThreeTree a) -> (xtra: Maybe (TwoThreeTree a))
             -> TwoThreeTree a
  delete'' k lm mm td sibling xtra = 
    let (nsibling, sc) = steal_third_child sibling in
      Node lm mm (remove_k_td k td sc) nsibling xtra
    where
    -- This is the only case that should happen here!
    steal_third_child : TwoThreeTree a -> (TwoThreeTree a, TwoThreeTree a)
    steal_third_child (Node x w s u (Just v)) = (Node x w s u Nothing, v)
  
    -- Here we need to delete "Leaf k" and replace it with sc
    remove_k_td : (Eq a, Ord a) => (k : a) -> (td : TwoThreeTree a) 
                  -> (sc : TwoThreeTree a) -> TwoThreeTree a
    remove_k_td k (Node x w (Leaf s) (Leaf u) Nothing) sc = 
      let scv = get_val sc in
        if k == s then
          if w <= scv then
            Node w scv (Leaf u) sc Nothing
          else
            Node scv w sc (Leaf u) Nothing
        else
          if x <= scv then
            Node x scv (Leaf s) sc Nothing
          else
            Node scv x sc (Leaf x) Nothing
       where
         get_val : TwoThreeTree a -> a
         get_val (Leaf vv) = vv
  
  -- The case when the siblings only have 2 kids
  delete''' : (k : a) -> (lm : a) -> (mm : a) -> (td : TwoThreeTree a)
             -> (sibling : TwoThreeTree a) -> (xtra : Maybe (TwoThreeTree a))
             -> TwoThreeTree a
  delete''' k lm mm td sibling xtra = ?delete'''_rhs

-- Delete a key from the TwoThreeTree
Delete : (Eq a, Ord a) => a -> (TwoThreeTree a) -> TwoThreeTree a
Delete x [] = []
Delete x (Leaf y) = 
  if x == y then []
  else (Leaf y)
Delete x t = 
  if (lookup x t) then
    case (delete' x t) of
      (t, True) => remove_from_root t
      (t, False) => update_lm_mm t
  else 
    t where
  remove_from_root : TwoThreeTree a -> TwoThreeTree a
  remove_from_root [] = []
  remove_from_root (Leaf x) = (Leaf x)
  remove_from_root (Node lm mm (Leaf l) (Leaf m) Nothing) = 
    if x == l then
      Leaf m
    else Leaf l
  

-- Examples
aTwoThreeTree : TwoThreeTree Nat
aTwoThreeTree = (Node 10 11 (Node 8 9 (Leaf 8) (Leaf 9) (Just (Leaf 10))) 
                           (Leaf 11) Nothing)

-- Example of insert
ct : TwoThreeTree Nat
ct = map (+ 1) (Node 10 14 (Leaf 10) (Leaf 14) (Just (Leaf 15)))

bt : TwoThreeTree Nat
bt = Insert 17 ct

dt : TwoThreeTree Nat
dt = Insert 18 bt
  
et : TwoThreeTree Nat
et = Insert 19 dt

ft : TwoThreeTree Nat
ft = Insert 14 dt

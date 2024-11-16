{-# LANGUAGE StandaloneDeriving #-}
module Problems10 where

{-------------------------------------------------------------------------------

CS:3820 Fall 2024 Problem Set 10
================================

This problem set explores another extension of the λ-calculus with effects.

The new effect we're adding is *exceptions*.  We have two operations:

* The expression `Throw m` throws an exception; the exception's payload is the
  value of expression `m`.
* The expression `Catch m y n` runs expression `m`:
  - If that expression evaluates to `v`, then `Catch m y n` also evaluates to
    `v`.
  - If that expression throws an exception with payload `w`, then `Catch m y n`
    evaluates to `n[w/y]`.

To keep things interesting, our language will *also* have an accumulator.
Changes to the accumulator should persist, even if an exception is thrown.
Concretely, in the expression:

    Catch (Plus (Store (Const 2)) (Throw (Const 3))) "y" Recall

The `Recall` in the catch block should return the value `Const 2`, resulting
from the `Store` in the first addend, not whatever the initial value of the
accumulator was.

-------------------------------------------------------------------------------}

-- Here is our expression data type

data Expr = -- Arithmetic
            Const Int | Plus Expr Expr
            -- λ-calculus
          | Var String | Lam String Expr | App Expr Expr
            -- accumulator
          | Store Expr | Recall
            -- exceptions
          | Throw Expr | Catch Expr String Expr
  deriving Eq

deriving instance Show Expr

-- Here's a show instance that tries to be a little more readable than the
-- default Haskell one; feel free to uncomment it (but then, be sure to comment
-- out the `deriving instance` line above).


-- instance Show Expr where
--   showsPrec _ (Const i) = shows i
--   showsPrec i (Plus m n) = showParen (i > 1) $ showsPrec 2 m . showString " + " . showsPrec 2 n
--   showsPrec i (Var x) = showString x
--   showsPrec i (Lam x m) = showParen (i > 0) $ showString "\\" . showString x . showString " . " . showsPrec 0 m
--   showsPrec i (App m n) = showParen (i > 2) $ showsPrec 2 m . showChar ' ' . showsPrec 3 n
--   showsPrec i (Store m) = showParen (i > 2) $ showString "store " . showsPrec 3 m
--   showsPrec i Recall    = showString "recall"
--   showsPrec i (Throw m) = showParen (i > 2) $ showString "throw " . showsPrec 3 m
--   showsPrec i (Catch m y n) = showParen (i > 0) $ showString "try " . showsPrec 0 m . showString " catch " . showString y . showString " -> " . showsPrec 0 n


-- Values are, as usual, integer and function constants
isValue :: Expr -> Bool
isValue (Const _) = True
isValue (Lam _ _) = True
isValue _         = False

{-------------------------------------------------------------------------------

Problems 1 & 2: Substitution
----------------------------

For your first problems, you'll need to implement substitution for our language.

I've already provided the cases for the λ-calculus.  In the case for `Lam`, I've
used a helper function `substUnder`, which only substitutes if the new variable
does not shadow the variable being replaced.

In implementing your cases, remember: substitution is about variables.  While
most of the imperative features of this language don't interact with variables,
`Catch` absolutely *does*.

Consider this example:

    (\x -> try M catch x -> N) [L/x]

Or, in our `Expr` data type:

    subst "x" l (Lam "x" (Catch m "x" n))

Suppose there's an instance of variable `x` in `N`.  Do you think that it should
be replaced by the substitution?

-------------------------------------------------------------------------------}

substUnder :: String -> Expr -> String -> Expr -> Expr
substUnder m x n y
  | m == n    = y
  | otherwise = subst m x y

subst :: String -> Expr -> Expr -> Expr
subst _ _ (Const i)     = Const i
subst m x (Plus y z)    = Plus  (subst m x y) (subst m x z)
subst m x (App y z)     = App   (subst m x y) (subst m x z)
subst m x (Store y)     = Store (subst m x y)
subst m x Recall        = Recall
subst m x (Throw y)     = Throw (subst m x y)
subst m x (Catch y n z) = Catch (subst m x y) n (substUnder m x n z)
subst m x (Var n)
  | m == n = x
  | otherwise = Var n
subst m x (Lam n y)
  | m == n = Lam m (subst m x y)
  | otherwise = Lam n (subst m x y)

-- (1) for x in (1 (try throw x + 1 catch x -> x + y))
-- >>> (App (Const 1) (Catch (Plus (Throw (Var "x")) (Const 1)) "x" (Plus (Var "x") (Var "y"))))
-- >>> subst "x" (Const 1) (App (Const 1) (Catch (Plus (Throw (Var "x")) (Const 1)) "x" (Plus (Var "x") (Var "y"))))
-- 1 (try throw x + 1 catch x -> x + y)
-- 1 (try throw 1 + 1 catch x -> x + y)


{-------------------------------------------------------------------------------

Problems 3 - 10: Small-step semantics
-------------------------------------

For the remaining problems, you'll need to implement a small-step semantics for
our language.

Your semantics should be *left-to-right* and *call-by-value*.

The program state is a pair `(prog, acc)`, where `prog` is the program being
evaluated, and `acc` is the current accumulator.

Because `Store` gets call-by-value treatment, `acc` should always be a value.

Intuitively, `Store m` needs to evaluate `m` (however many steps that takes),
and then replace the current accumulator contents with the value of `m`.
`Recall` returns the contents of the accumulator.  For more detailed treatment,
please see Lecture 12 on ICON.

The more interesting cases are for `Throw` and `Catch`.

We'll implement `Throw` by "bubbling" exceptions up through computations.

For example, consider this expression

    Plus (Const 1) (Plus (Const 2) (Plus (Const 3) (Throw (Const 4))))

For this expression to step, we need

    Plus (Const 3) (Throw (Const 4))

to step.  But we can't add anything here: the second argument is a thrown
exception.  Instead, we replace the entire `Plus` expression with the exception.
That is, the first step is:

    Plus (Const 1) (Plus (Const 2) (Plus (Const 3) (Throw (Const 4))))
      ~~>
    Plus (Const 1) (Plus (Const 2) (Throw (Const 4)))

Note: the exception is still being thrown!  Now, by the same logic, our next
step is:

    Plus (Const 1) (Plus (Const 2) (Throw (Const 4)))
      ~~>
    Plus (Const 1) (Throw (Const 4))

and finally:

    Plus (Const 1) (Throw (Const 4))
      ~~>
    Throw (Const 4)

Now we can't make any more progress; this isn't a value, it's a thrown
exception, but without something to catch the exception we can't simplify any
further.

Exceptions "bubble" through all the points evaluation can happen: `Plus`, `App`,
and `Store`.  

`Throw` itself also gets call-by-value treatment: an exception does not start
"bubbling" until the thrown expression is itself a value.  Here is an example:

  Plus (Const 1) (Throw (Plus (Const 2) (Const 3)))
    ~~>
  Plus (Const 1) (Throw (Const 5))
    ~~>
  Throw (Const 5)

Note: exceptions bubble through `Throw` itself as well.

Now we can explain `Catch`.  `Catch m y n` begins by evaluating `m`.  If `m`
evaluates to a value `v`, then so does `Catch m y n`.  But, if `m` evaluates to
a thrown exception `Throw w`, then `Catch m y n` evaluates to `n[w/y]`.

For example:

    Catch (Plus (Const 1) (Throw (Const 2))) "y" (Plus (Var "y") (Const 1))
      ~~>
    Catch (Throw (Const 2)) "y" (Plus (Var "y") (Const 1))
      ~~>
    Plus (Const 2) (Const 1)
      ~~>
    Const 3

When implementing your `smallStep` function: feel free to start from the code in
Lecture 12.  But be sure to handle *all* the cases where exceptions need to
bubble; this won't *just* be `Throw` and `Catch.

-------------------------------------------------------------------------------}


smallStep :: (Expr, Expr) -> Maybe (Expr, Expr)

smallStep (Const i, s) = Nothing -- Just (Const i, s)
smallStep (Var _, _)   = Nothing

smallStep (Plus x y, s) =
  case (x, y) of
    (Const i, Const j)     -> Just (Const $ i + j, s)
    (Throw x, _)           -> smallStep (Throw x, s)
    (_, Throw x)           -> smallStep (Throw x, s)
    _                      ->
      case (smallStep (x, s), smallStep (y, s)) of
        (Just (x', s'), _) -> Just (Plus x' y, s')
        (_, Just (y', s')) -> Just (Plus x y', s')
        _                  -> Nothing

smallStep (Lam _ x, s) = 
  case x of
    Throw x -> smallStep (Throw x, s)
    _       -> Nothing

smallStep (App (Lam m x) y, s) = Just (subst m y x, s)
smallStep (App x y, s) =
  case (smallStep (x, s), smallStep (y, s)) of
    (Just (Throw z, s'), _) -> smallStep (Throw z, s)
    (_, Just (Throw z, s')) -> smallStep (Throw z, s)
    (Just (x', s'), _)      -> Just (App x' y, s')
    (_, Just (y', s'))      -> Just (App x y', s')
    _                       -> Nothing

smallStep (Store x, s) = 
  if   isValue x 
  then Just (x, x)      else
  case smallStep (x, s) of
    Just (Throw x, s) -> smallStep (Throw x, s)
    Just (m', s')     -> Just (Store m', s')
    _                 -> Nothing

smallStep (Recall, s) = Just (s, s)

smallStep (Throw x, s) =
  case x of
    Throw y -> smallStep (Throw y, s)
    _       -> Just      (Throw x, s)

smallStep (Catch x m y, s) = case x of
  (Throw z) -> smallStep (subst m z y, s)
  _         -> smallStep (x, s)

v :: Expr -> Maybe (Expr, Expr)
v x = smallStep (x, a)

u :: Maybe (Expr, Expr) -> Maybe (Expr, Expr)
u x = smallStep =<< x


a = Const 0
b = Const 1
t0 = Throw a
t1 = Throw b

c = Plus a t0
d = Lam "x" (Throw a)
e = App a (Throw b)
f = Store (Throw t0)

g = Catch t0 "x" (App (Lam "x" (Plus (Const 1) (Var "x"))) (Var "x"))

h = Catch a "x" (Lam "x" (Var "x"))
-- >>> v c
-- >>> u$ v c
-- Just (throw 0,0)
-- Just (throw 0,0)

-- >>> v d
-- >>> u$ v d
-- Just (throw 0,0)
-- Just (throw 0,0)

-- >>> v e
-- >>> u$ v e
-- Just (throw 1,0)
-- Just (throw 1,0)

-- >>> v f
-- >>> u$ v f
-- Just (throw 0,0)
-- Just (throw 0,0)

-- >>> v g
-- >>> u$ v g
-- Just (1 + 0,0)
-- Just (1,0)

-- >>> v h
-- >>> u$ v h
-- Just (0,0)
-- Just (0,0)




-- >>> steps (Lam "x" (Var "x"), Const 0)
-- >>> steps (Lam "x" (Plus (Const 1) (Const 2)), Const 0)
-- >>> steps (Lam "y" (Plus (Const 0) Recall), Const 12)
-- >>> steps (Lam "z" (Plus (Throw (Const 0)) (Var "z")), Const 3)
-- [(Lam "x" (Var "x"),Const 0)]
-- [(Lam "x" (Plus (Const 1) (Const 2)),Const 0)]
-- [(Lam "y" (Plus (Const 0) Recall),Const 12)]
-- [(Lam "z" (Plus (Throw (Const 0)) (Var "z")),Const 3)]



-- >> steps (Store (Const 2), Const 0)







-- >>> u$ (Just (Store (Const 2), Const 0))
-- >>> u$ u$ (Just (Store (Const 2), Const 0))
-- Just (Const 2,Const 2)
-- Nothing




-- >>> steps (Store (Plus (Const 1) (Const 2)), Const 0)
-- [(Store (Plus (Const 1) (Const 2)),Const 0),(Store (Const 3),Const 0),(Const 3,Const 3)]

-- >>> steps (Store (Plus (Store (Const 1)) (Const 2)), Const 0)
-- [(Store (Plus (Store (Const 1)) (Const 2)),Const 0),(Store (Plus (Const 1) (Const 2)),Const 1),(Store (Const 3),Const 1),(Const 3,Const 3)]

-- >>> steps (Store (Lam "x" (Store (Var "x"))), Const 12) 

-- >>> steps (Store (Plus (Const 1) (Throw (Const 2))), Const 1)
-- >>> steps (Store (Store (Throw (Const 3))), Const 1)
-- >>> steps (Store (Throw (Store (Const 2))), Const 1) 



steps :: (Expr, Expr) -> [(Expr, Expr)]
steps s = case smallStep s of
            Nothing -> [s]
            Just s' -> s : steps s'

prints :: Show a => [a] -> IO ()
prints = mapM_ print

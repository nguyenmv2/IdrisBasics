-- CSCI 490, Spring 2016
-- HW #7: Idris basics

{- For this week's assignment, follow the instructions and fill in
   definitions in this file.  When you are done, just turn in a copy
   of this file on Moodle.

   ***MAKE SURE THAT IDRIS ACCEPTS your submitted file!!***

   A file with syntax or type errors will receive a score of at most
   50% of the available points.

   The first part of this assignment is to make sure you have Idris
   installed.

   METHOD 1: Just run 'cabal install idris' at the command-line.
     Pros: simple.

     Cons: Installs all the required packages in your global Haskell
     package index, which can lead to version compatibility problems.
     Not easy to undo if something gets screwed up.  Also, prone to
     breakage if/when some new version of a package is uploaded to
     Hackage.

   METHOD 2:

     1. First, make sure you have 'stack' installed, by following the
        appropriate instructions at
        http://docs.haskellstack.org/en/stable/README/.

     2. At a command line, cd to a suitable location and then run

          cabal update && cabal get idris

        This will create a new directory like idris-0.10.2/ containing
        the source code of the latest Idris release.

     3. cd into this new directory and type

          stack setup && stack install

        This will build Idris *in a sandbox* and install just the
        final executable into a suitable location.  (Make sure the
        location is on your PATH, or copy the generated executable
        somewhere else.)

     Cons: somewhat more complex.
     Pros: repeatable, reliable, everything is built in a sandbox so
     it's easy to delete without affecting anything else.


  I highly recommend that you use an editor with Idris integration.
  As we saw in class, Idris can actually generate code for you in a
  type-directed way.  Modes exist for:

    + emacs: https://github.com/idris-hackers/idris-mode
    + vim:   https://github.com/idris-hackers/idris-vim
    + Atom:  https://github.com/idris-hackers/atom-language-idris

  There is also a repository with a Sublime Idris mode:

    + https://github.com/idris-hackers/idris-sublime

  but it looks unmaintained; try at your own risk.

-}

module IdrisBasics

-- First, recall the definition of "length-indexed" lists (i.e. lists
-- whose length is encoded in their type) from class.

-- This "namespace" thing just declares a new namespace; everything
-- indented in this section has full names like ListN.ListN,
-- ListN.listN1, ListN.head, and so on (but we can leave off the
-- ListN. part when unambiguous).
namespace ListN

  -- Instead of using NilN and ConsN as the constructors, like in
  -- class, we'll take advantage of Idris's ability to overload names
  -- and disambiguate based on type, and name the constructors Nil and
  -- (::), just like with the standard List type.
  data ListN : Nat -> Type -> Type where
    Nil  : ListN Z a
    (::) : a -> ListN n a -> ListN (S n) a

  -- It turns out that the syntax sugar [], [1,2,3], and so on, works
  -- for anything with constructors named Nil and (::), so we get to
  -- use list syntax for our new type ListN!
  listN1 : ListN 0 Nat
  listN1 = []

  listN2 : ListN 3 Nat
  listN2 = [1,2,3]

  -- We wrote the functions head and (++) in class (though we called
  -- them headN and appendN).
  head : ListN (S n) a -> a
  head (a :: as) = a

  (++) : ListN m a -> ListN n a -> ListN (m + n) a
  (++) Nil ys       = ys
  (++) (x :: xs) ys = x :: (xs ++ ys)

  -- EXERCISE 1. Your turn!  Fill in a definition for 'map' below.  Do
  -- it manually first, then (if using the emacs or vim Idris modes)
  -- see how much work you can get Idris to do for you (e.g. in Emacs
  -- using C-c C-s (start), C-c C-c (case split), C-c C-a (auto)).
  --
  -- Notice how the type of 'map' guarantees that the length of the
  -- list is preserved.  In Haskell, we had to prove this as a
  -- separate theorem (and the Haskell compiler gave us no help).
  -- Here, an type-correct implementation already itself constitutes a
  -- proof that map preserves the length of its input list!
  map : (a -> b) -> ListN n a -> ListN n b

  -- EXERCISE 2. Now implement 'replicate'.  The type of replicate
  -- uses some syntax we have not seen before.  What do you think it
  -- means?
  replicate : (n : Nat) -> a -> ListN n a

-- We might try to implement other standard list functions on ListN.
-- One that presents a special challenge is 'filter', since it can
-- change the length of the list (and we cannot know in advance what
-- the length of the output list will be).  Here is one possible
-- approach.
namespace FilteredList

  -- EXERCISE 3. First, define a new data type 'FilteredList', such
  -- that 'FilteredList n a' is the type of lists containing elements
  -- of type a, whose length is *at most* n. (Hint, rot13: Bar jnl gb
  -- qb guvf vf gb vagebqhpr na rkgen pbafgehpgbe (r.t. pnyyrq 'Fxvc')
  -- juvpu vapernfrf gur yratgu ohg qbrf abg pbagnva n yvfg ryrzrag.)
  data FilteredList : Nat -> Type -> Type where
    -- fill in constructors here

  -- EXERCISE 4. Now define filter.  You will probably want to use
  -- either a 'case' expression (see
  -- http://docs.idris-lang.org/en/latest/reference/syntax-guide.html#case-expressions)
  -- or a 'with' expression.  The latter is sort of like guards in
  -- Haskell, except it lets you pattern-match on an additional
  -- expression besides the function arguments (rather than testing a
  -- boolean expression).  For example, consider the function foo
  -- defined below:

  foo : Nat -> Nat -> String
  foo m n with (m + n)
    | Z   = "Both are zero"
    | S _ = "At least one is nonzero"

  -- This function takes two Nat arguments, m and n, and
  -- pattern-matches on *the result of (m+n)*.  If m + n is Z, it
  -- returns "Both are zero"; if m + n matches (S _), it returns "At
  -- least one is nonzero".

  -- Now you define filter:
  filter : (a -> Bool) -> ListN n a -> FilteredList n a

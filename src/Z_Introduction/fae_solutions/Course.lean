import data.complex.exponential
import data.real.basic
import data.real.nnreal
open real nnreal
open_locale nnreal

/-! ## #check
The command `check` returns the Type of its input-/

/-! The first two things below belong to _different_ types: it does not make sense (= it is semantically unsound) to say that they coincide
-/
#check 3
#check (3 : ℤ)
#check (3 : ℕ) = (3 : ℤ)

/-! Since `(5 : ℕ)` and `(5 : ℝ)` are different objects, it is not strange that raising `3` to the first makes sense, but not raising `3` to the second-/
#check 3 ^ 5 
#check 3 ^ (5 : ℝ) 

/-! Two different functions: they return different values as well!-/
#check sin
#check complex.sin 
#check (sin 3) = (complex.sin 3)


#check (1 : ℝ≥0) -- the terms of the type `ℝ≥0` are _pairs_ of a real number and a proof that it is positive
#check (1 : ℝ≥0).1
#check (1 : ℝ≥0).2 --The system has found a proof that (0 : ℝ) ≤ (1 : ℝ) 
#check ((- 3) : ℝ≥0) --The second element cannot be constructed

/-! ## Prop
Propositions are also types: their terms are the _proofs_ (if they exist) of the statement -/

#check (2 = 3) -- a (false) Proposition, so a type (with no elements)
#check (7 : ℝ) = (3 + 4 : ℝ) -- a (true) Proposition, so a type (with one element)

#check (∀ a b c : ℕ, a * (b + c) = a * b + a * c) -- this is a proposition
#check mul_add -- `mul_add` is a (the unique!) term of the above type, at least when we insist that all terms belong to ℕ
#check mul_add 1 --`mul_add 1` is a term of a slightly different type
#check mul_add (1 : ℝ) --even slightly different
#check mul_add 1 2 3 --this is the unique term of the type 1 * (2 + 3) = 1 * 2 + 1 * 3

/-! ## Implication
To produce a _proof_ of a statement `P` means to construct a term of the type `P`. The prototypical way to do so, is to construct a function `f : Q → P` from some other type `Q` that we know to have a term (this term is a proof of `Q`), say `hQ`. Then, `f (hQ)` is a term of type `P`, hence `P` is true.

This is the translation, in the language of Type Theory, of `Q ⇒ P`: the truth (= the existence of a proof of) `Q` implies the truth of `P`.
-/
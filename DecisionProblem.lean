import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic

structure DecisionProblem where
  Instance : Type
  Space : Instance → Type
  Solution : (Σ i : Instance, Space i) → Prop

def Solution_of {P : DecisionProblem} (i : P.Instance)
  := { val : P.Space i // P.Solution ⟨i,val⟩}

example (P : DecisionProblem) (i : P.Instance) (u v : Solution_of i) (h : u.val = v.val) :
u = v := Subtype.eq h

-- example (a b : PNat) (h: a.1 = b.1) : a=b := by exact PNat.eq h

example (α : Type) (P : α → Prop)
(u v : { x : α // P x}) (h : u.1 = v.1) : u = v
:= by exact Subtype.eq h

structure Reduction (P Q : DecisionProblem) where
  Map : P.Instance → Q.Instance
  Property : ∀ i : P.Instance, (∃ x, P.Solution ⟨i, x⟩) ↔ (∃ y, Q.Solution ⟨(Map i), y⟩)

structure Reduction' (P Q : DecisionProblem) where
  Map : P.Instance → Q.Instance
  Property : ∀ i : P.Instance,
    (Nonempty (Solution_of i)) ↔ (Nonempty (Solution_of (Map i)))

/-
Wikipedia (https://en.wikipedia.org/wiki/Parsimonious_reduction):
  "A general reduction from problem A to problem B is a transformation that guarantees that
  whenever A has a solution B also has at least one solution and vice versa."

  "A parsimonious reduction guarantees that
  for every solution of A, there exists a unique solution of B and vice versa."
  "A parsimonious reduction is a transformation from one problem to another (a reduction) that
  preserves the number of solutions."

  Instead of representing the number of solutions as a number in ℕ,
  here we just require a bijective function:
-/

structure ParsimoniousReduction (P Q : DecisionProblem) where
  Reduction : Reduction P Q
  SpaceMap : (i : P.Instance) → (P.Space i → Q.Space (Reduction.Map i))  -- or : Fun : Σ i : P.Instance, (P.Space i → Q.Space (Reduction.Map i))
  Preserves : ∀ i : P.Instance, ∀ v : P.Space i,
    P.Solution ⟨i,v⟩ → Q.Solution ⟨Reduction.Map i,SpaceMap i v⟩
  Property : ∀ i : P.Instance, Function.Bijective (
    (fun v ↦ ⟨SpaceMap i v.1,Preserves i v.1 v.2⟩) :
      {v : P.Space i           // P.Solution ⟨i,v⟩}
    → {w : Q.Space (Reduction.Map i) // Q.Solution ⟨Reduction.Map i,w⟩}
  )
-- don't call it Fun because λ is synonymous with fun

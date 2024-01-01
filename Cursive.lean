import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import MyProject.DecisionProblem
import MyProject.Bjoern
import MyProject.Cursive
import MyProject.Knapsack

set_option tactic.hygienic false

-- set_option maxHeartbeats 10000000

/-
Connect the diophantine equation (a.val 0)x+(a.val 1)y=n with
a walk in a digraph that has a cycle of length (a.val 0) followed by a cycle of length (a.val 1).
-/

-- We can prove my_reduction is a Reduction


def walk_of_solution' (i:KnapsackInstance 2)
  : {p : ℕ×ℕ // i.target.succ = i.wt.val 0 * p.1 + 1 + i.wt.val 1 * p.2}
  → {w : ℕ → ℕ // curs_walks i.wt w ∧ w i.target.succ = i.wt.val 0}
  := by {
    intro p; let k := p.1.1
    exists walk_' i.wt k; constructor
    exact walk_walks' i.wt k; rw [p.2];
    let pfun : Fin 2 → ℕ := λ i ↦ [p.1.1, p.1.2].get i
    exact keep_arriving' i.wt pfun
  }

theorem walk_of_solution_injective' (i:KnapsackInstance 2) :
Function.Injective (walk_of_solution' i) := by {
  unfold Function.Injective
  intro p₁ p₂ hp
  unfold walk_of_solution' at hp
  simp at hp
  have h₁₁: p₁.1.1 = p₂.1.1 := walk__injective' i.wt p₁.1.1 p₂.1.1 hp
  have h₁₂: p₁.1.2 = p₂.1.2 := l_unique' i.wt (Eq.trans p₁.2.symm (by {rw [h₁₁]; exact p₂.2}))
  exact SetCoe.ext (Prod.ext h₁₁ h₁₂)
}

theorem walk_of_solution_surjective' (i:KnapsackInstance 2) :
Function.Surjective (walk_of_solution' i) := by {
  unfold Function.Surjective
  intro wpair
  let ⟨hw,hT⟩ := wpair.2; let k := getk1' i.wt hw hT
  have hwp : wpair.1 = walk_' i.wt k := getk2' i.wt _ _
  rw [hwp] at hT
  rename wpair.1 (Nat.succ i.target) = (i.wt.val 0) => hTold
  let lpair := (getl' i.wt hT); let l := lpair.1
  exists ⟨(k,l), lpair.2⟩; exact SetCoe.ext (id hwp.symm)
}

theorem walk_of_solution_bijective' (i:KnapsackInstance 2) :
Function.Bijective (walk_of_solution' i) := by {
  constructor;
  exact walk_of_solution_injective' i
  exact walk_of_solution_surjective' i
}

theorem main' (i:KnapsackInstance 2) : (∃! p : ℕ×ℕ, i.target.succ = i.wt.val 0 * p.1 + 1 + i.wt.val 1 * p.2)
↔ (∃! w, curs_walks i.wt w ∧ w i.target.succ = i.wt.val 0)
  := unique_iff_of_bijective (walk_of_solution_bijective' i)

-- We can now elegantly get rid of the successor in theorem main:
theorem main_n' {n:ℕ}  (a : PF 2)
: (∃! p : ℕ×ℕ, n = a.val 0 * p.1 + 1 + a.val 1 * p.2)
↔ (∃! w, curs_walks a w ∧ w n = a.val 0) :=
by {
  cases n;
  -- n is 0:
  constructor; intro h; exfalso; rcases h with ⟨p,hp⟩; let g := hp.1
  have : 1 ≤ 0 := calc
         1 ≤ (a.val 0) * p.1 + 1 := Nat.le_add_left 1 ((a.val 0) * p.1)
         _ ≤ (a.val 0) * p.1 + 1 + (a.val 1) * p.2 := Nat.le_add_right ((a.val 0) * p.1 + 1) ((a.val 1) * p.2)
         _ = 0 := self_eq_add_left.mp g
  exact Nat.not_succ_le_zero 0 this

  intro h; exfalso; rcases h with ⟨w,hw⟩; let G := hw.1.2; rw [hw.1.1.1] at G
  exact LT.lt.false (Nat.lt_of_lt_of_eq (a.pos 0) (id G.symm))
  -- n is T.succ:
  let i : KnapsackInstance 2 := {
    target := n_1
    wt := a
  }
  exact main' i
}

theorem fin2cases (i : Fin 2) : i = 0 ∨ i = 1 := by {
  have : i ≤ 1 := Fin.le_last _
  have : i < 1 ∨ i = 1 := by exact lt_or_eq_of_le this
  cases this
  have : i ≤ 0 := by exact Fin.succ_le_succ_iff.mp h
  have : i = 0 := by exact Fin.le_zero_iff.mp this
  left
  exact this
  right
  exact h
}

theorem main_prod' {n:ℕ} (a : PF 2)
: (∃! p : Fin 2 → ℕ, n = a.val 0 * p 0 + 1 + a.val 1 * p 1)
↔ (∃! w, curs_walks a w ∧ w n = a.val 0) :=
by {
  constructor; intro h
  rcases h with ⟨p,hp⟩
  exact (main_n' a).mp (by {
    exists (p 0, p 1); simp
    constructor; exact hp.1
    intro p'0 p'1 hp'; let g := hp.2 (λ i ↦ [p'0, p'1].get i) hp'
    constructor
    exact congr_arg (λ x ↦ x 0) g
    exact congr_arg (λ x ↦ x 1) g
  })
  intro h
  let g := (main_n' a).mpr h
  rcases g with ⟨p,hp⟩
  exists (λ i ↦ [p.1, p.2].get i)
  constructor; simp; exact hp.1; intro p' hp'
  let g := hp.2 (p' 0, p' 1) hp'; apply funext; intro i
  have : i ≤ 1 := Fin.le_last _
  have : i < 1 ∨ i = 1 := by exact lt_or_eq_of_le this
  cases this
  have : i ≤ 0 := by exact Fin.succ_le_succ_iff.mp h_1
  have : i = 0 := by exact Fin.le_zero_iff.mp this
  rw [this]; simp; exact congr_arg (λ x ↦ x.1) g; rw [h_1]
  simp; exact congr_arg (λ x ↦ x.2) g
}

theorem main_dot' {n:ℕ} (a : PF 2)
: (∃! p : Fin 2 → ℕ, n = Matrix.dotProduct a.val p + 1)
↔ (∃! w, curs_walks a w ∧ w n = a.val 0) :=
by {
  constructor; intro h; rcases h with ⟨p,hp⟩
  have : (∃! p : Fin 2 → ℕ, n = (a.val 0) * p 0 + 1 + (a.val 1) * p 1) := by {
    exists p; constructor; let g := hp.1
    unfold Matrix.dotProduct at g; rw [g];
    simp; ring; intro y h
    apply hp.2 y; rw [h]
    have : (a.val 0) * y 0 + 1 + (a.val 1) * y 1 = (a.val 0) * y 0 + (a.val 1) * y 1 + 1 := by ring
    rw [this];
    unfold Matrix.dotProduct
    rfl
  }
  exact (main_prod' a).mp this
  intro h
  have : (∃! p : Fin 2 → ℕ, n = (a.val 0) * p 0 + 1 + (a.val 1) * p 1) := (main_prod' a).mpr h
  rcases this with ⟨p,hp⟩
  exists p; constructor; let g := hp.1; rw [g]; simp;unfold Matrix.dotProduct
  simp; ring
  intro y hy; let g := hp.2 y; simp at g;apply g -- smart!
  rw [hy]; unfold Matrix.dotProduct
  have : (a.val 0) * y 0 + 1 + (a.val 1) * y 1 = (a.val 0) * y 0 + (a.val 1) * y 1 + 1 := by ring
  rw [this]; rfl
}


def my_reduction {c:PNat} (i : KnapsackInstance c) : CursiveWalkInstance c :=
{
  length := ⟨i.target.succ,Nat.succ_pos _⟩
  cycleLength := i.wt
}

def my_reduction' (i : Knapsack2.Instance) : CursiveWalkInstance 2 :=
{
  length := ⟨i.target.succ,Nat.succ_pos _⟩
  cycleLength := i.wt
}

-- KnapsackInstance_of_CursiveWalkInstance
def KI_of_CI (i : CursiveWalk.Instance):
Knapsack2.Instance := {
  target := i.length.val.pred
  wt := i.cycleLength
}
def CI_of_KI (i : Knapsack2.Instance) : CursiveWalk.Instance :=
{
  length := ⟨i.target.succ,Nat.succ_pos _⟩
  cycleLength := i.wt
}

theorem inverses1 (i : Knapsack2.Instance) :
KI_of_CI (CI_of_KI i) = i := rfl

theorem inverses2 (i : CursiveWalk.Instance) :
CI_of_KI (KI_of_CI i) = i := by {
  unfold KI_of_CI; unfold CI_of_KI
  have :  Nat.succ (Nat.pred ↑i.length) = i.length.val := PNat.natPred_add_one _
  simp_rw [this]
  exact rfl
}

instance : Nonempty CursiveWalk.Instance :=
-- needed for more_inverses
  ⟨1,⟨λ _ ↦ (1:ℕ),by {intro;simp;}⟩⟩


theorem more_inverses : CI_of_KI = Function.invFun KI_of_CI := by {
  unfold Function.invFun
  apply funext
  intro i
  have h : ∃ x, KI_of_CI x = i := by {exists CI_of_KI i;}
  rw [dif_pos h]
  let P := (λ x ↦ KI_of_CI x = i)
  have : P (Exists.choose h) := Exists.choose_spec _
  have : KI_of_CI (Exists.choose h) = i := this
  have : CI_of_KI (KI_of_CI (Exists.choose h)) = CI_of_KI i := congrArg CI_of_KI this
  have : Exists.choose h = CI_of_KI i := by {
    rw [inverses2] at this;
    exact this
  }
  exact this.symm
}



def small_lemma (i:Knapsack2.Instance) (s : Fin 2 → ℕ):
  (Nat.succ (Matrix.dotProduct i.wt.val s)) =
             (i.wt.val 0 * s 0 + 1 + i.wt.val 1 * s 1)
      := by {
        have : (i.wt.val 0 * s 0 + 1 + i.wt.val 1 * s 1) =
               (i.wt.val 0 * s 0 + i.wt.val 1 * s 1) + 1 := by ring
        rw [this]
        rfl
      }


theorem CS_of_KS_property
 (i:Knapsack2.Instance) (s : Solution_of i) :
  curs_walks i.wt (walk_' i.wt (s.val 0))
  ∧ walk_' i.wt (s.val 0) (Nat.succ i.target) = i.wt.val 0
  := by {
      constructor
      exact walk_walks' _ _
      let g := keep_arriving' i.wt s.val
      rw [← g,s.property]
      have : (Nat.succ (Matrix.dotProduct i.wt.val s.val)) =
             (i.wt.val 0 * s.val 0 + 1 + i.wt.val 1 * s.val 1)
      := small_lemma _ _
      exact congr_arg _ this
    }

-- The parsimonious function, CursiveWalkSolution_of_KnapsackSolution
def CS_of_KS (i:Knapsack2.Instance)
: Solution_of i
→ Solution_of (CI_of_KI i)
:= λ s ↦ {
    val      := walk_' i.wt (s.val 0)
    property := CS_of_KS_property _ _
  }

theorem main_dot_knapsack' (i : Knapsack2.Instance)
: (∃! p : Fin 2 → ℕ, i.target = Matrix.dotProduct i.wt.val p)
↔ (∃! w, curs_walks i.wt w ∧ w i.target.succ = i.wt.val 0) :=
by {
  constructor; intro h; rcases h with ⟨p,hp⟩; apply (main_dot' i.wt).mp
  exists p; constructor; simp; simp at hp; exact hp.1
  intro y; let g := hp.2 y; simp at g; intro h; simp at h; exact g h

  intro h
  have : (∃! p : Fin 2 → ℕ, i.target.succ = Matrix.dotProduct i.wt.val p + 1) := (main_dot' i.wt).mpr h
  rcases this with ⟨p,hp⟩; exists p; simp; simp at hp; exact hp
}



theorem CS_of_KS_injective
  (i:Knapsack2.Instance) :
  Function.Injective (CS_of_KS i)
  := by {
  unfold Function.Injective; intro p₁ p₂ hp;
  unfold CS_of_KS at hp
  have h₁₁: p₁.val 0 = p₂.val 0
    := walk__injective' i.wt _ _ (congr_arg (λ x ↦ x.1) hp)
  have hmm : i.target.succ = i.wt.val 0 * p₁.1 0 + 1 + i.wt.val 1 * p₂.1 1
    := by {
      unfold Solution_of at p₂; let g := p₂.2
      unfold DecisionProblem.Solution Knapsack2 at g
      unfold Matrix.dotProduct at g; simp at g
      rw [← h₁₁] at g; let g' := congr_arg Nat.succ g
      rw [g',Nat.succ_eq_add_one]; ring
    }
  have : i.wt.val 0 * p₁.val 0 + 1 + i.wt.val 1 * p₁.val 1 =
         i.wt.val 0 * p₁.val 0 + 1 + i.wt.val 1 * p₂.val 1
  := calc
    _ = Nat.succ (Matrix.dotProduct i.wt.val p₁.val) := (small_lemma i p₁.1).symm
    _ = i.target.succ := congr_arg _ p₁.property.symm
    _ = _ := hmm
  have h₁₂: p₁.val 1 = p₂.val 1 := l_unique' i.wt this
  exact Subtype.eq (by {
    apply funext; intro i; have : i = 0 ∨ i = 1 := fin2cases _
    cases this; rw [h]; exact h₁₁; rw [h]; exact h₁₂
  })
}

-- KnapsackSolution_of_CursiveWalkSolution = KS_of_CS
noncomputable def KS_of_CS_val  (i : CursiveWalk.Instance):
Solution_of i → (Fin 2 → ℕ) :=
λ wpair ↦  by {
  let j := KI_of_CI i
  unfold KI_of_CI at j
  have : j.target.succ = i.length.val := PNat.natPred_add_one _
  let ⟨hw,hT⟩ := wpair.2;
  rw [← this] at hT
  let k := getk1' j.wt hw hT

  have hwp : wpair.1 = walk_' j.wt k := getk2' j.wt _ _
  rw [hwp] at hT
  let l := (getl' j.wt hT).1

  exact (λ i ↦ [k,l].get i)
  }


noncomputable def KS_of_CS_val'_of0  (i : CursiveWalk.Instance):
Solution_of i → (ℕ) :=
-- December 30. This is literally getk1''.
λ wpair ↦  getk1'' i wpair

noncomputable def KS_of_CS_val'_of1  (i : CursiveWalk.Instance):
Solution_of i → (ℕ) :=
-- December 30
λ wpair ↦  by {
  let j := KI_of_CI i
  unfold KI_of_CI at j
  have : j.target.succ = i.length.val := PNat.natPred_add_one _
  let hT := wpair.2.2;
  rw [← this] at hT
  let k := getk1'' i wpair

  have hwp : wpair.1 = walk_' j.wt k := getk2'' i _
  rw [hwp] at hT

  exact (getl' j.wt hT).1
  }


noncomputable def KS_of_CS_val'  (i : CursiveWalk.Instance):
Solution_of i → (Fin 2 → ℕ) :=
-- December 30
λ wpair b ↦
ite (b=0) (KS_of_CS_val'_of0 i wpair)
          (KS_of_CS_val'_of1 i wpair)

theorem QQQ  (i : CursiveWalk.Instance)
(wpair : Solution_of i) :
KS_of_CS_val' i wpair 0 = getk1'' i wpair := by {
  unfold KS_of_CS_val'
  rw [if_pos (rfl)]
  unfold KS_of_CS_val'_of0
  simp
}

-- December 30, 2023: an inverse of CS_of_KS
noncomputable def KS_of_CS (j : CursiveWalk.Instance):
Solution_of j → Solution_of (KI_of_CI j) :=
λ wpair ↦ {
  val := KS_of_CS_val' j wpair
  property := by {
    let i := KI_of_CI j; let ⟨hw,hT⟩ := wpair.2;
    have : i.target.succ = j.length.val := PNat.natPred_add_one _
    rw [← this,getk2''] at hT; rw [getk2''] at hw;
    have get_getl: KS_of_CS_val' j wpair 1
      = (getl' i.wt hT).1 := by {
        unfold KS_of_CS_val'; simp
        unfold KS_of_CS_val'_of1; simp
      }
    apply Nat.succ_injective; unfold Matrix.dotProduct; simp; apply Nat.succ_injective
    let pro := (getl' i.wt hT).2
    have move_one: i.wt.val 0 * getk1'' j wpair + 1 + i.wt.val 1 * ↑(getl' i.wt hT) =
         Nat.succ (i.wt.val 0 * getk1'' j wpair +     i.wt.val 1 * ↑(getl' i.wt hT))
         := by {simp_rw [Nat.succ_eq_add_one]; ring}
    simp_rw [QQQ,get_getl,pro,← move_one]
  }
}

-- theorem trys (j : CursiveWalk.Instance) (wpair : Solution_of j):
--   wpair.1 = (cast
--     (by {rw [inverses2]} :
--       { val // DecisionProblem.Solution CursiveWalk { fst := CI_of_KI (KI_of_CI j), snd := val } } =
--         { val // DecisionProblem.Solution CursiveWalk { fst := j, snd := val } })
--     { val := walk_' (KI_of_CI j).wt (getk1'' j wpair),
--       property :=
--         ((by {
--           rw[inverses2]; let H := getk2'' j wpair; have : j.cycleLength = (KI_of_CI j).wt := rfl
--           rw [← this,← H]; exact wpair.2
--         }) :
--           (fun val => DecisionProblem.Solution CursiveWalk { fst := CI_of_KI (KI_of_CI j), snd := val })
--             (walk_' (KI_of_CI j).wt (getk1'' j wpair))) }).1
-- := sorry


theorem inspired_by_dillies {α β: Type} (u₁ u₂ : β) {P : β → α → Prop} (a:α) (h₁ : P u₁ a) (h₂ : P u₂ a) (hu : u₁ = u₂)
(h₃ : {a // P u₁ a} = {a // P u₂ a}):
cast h₃ (⟨a,h₁⟩) = (⟨a,h₂⟩)
    := by {
      subst hu
      exact rfl
    }

-- Thanks to Dillies:
theorem cast_val (u₁ u₂ : CursiveWalk.Instance) (a:ℕ→ℕ)
(h₁ : CursiveWalk.Solution ⟨u₁,a⟩) (h₂ : CursiveWalk.Solution ⟨u₂,a⟩) (hu : u₁ = u₂)
(h₃ : {a // CursiveWalk.Solution ⟨u₁,a⟩} = {a // CursiveWalk.Solution ⟨u₂,a⟩}):
cast h₃ (⟨a,h₁⟩) = (⟨a,h₂⟩)
    := by {subst hu; exact rfl}

theorem inverses_dot1 (j : CursiveWalk.Instance) (wpair : Solution_of j):
wpair.1 = (Eq.mp
  ((congr_arg _ (inverses2 j)) : Solution_of (CI_of_KI (KI_of_CI j)) = Solution_of j)
  (CS_of_KS (KI_of_CI j) (KS_of_CS j wpair))).1 := by {
    unfold CS_of_KS; unfold KS_of_CS; unfold KS_of_CS_val'; simp; unfold KS_of_CS_val'_of0
    have : j.cycleLength = (KI_of_CI j).wt := rfl; simp_rw [← this]

    let wk := walk_' j.cycleLength (getk1'' j wpair)
    have h₂ : CursiveWalk.Solution ⟨j,wk⟩ := by {
      have : wk = wpair.1 := (getk2'' j wpair).symm
      rw [this]
      exact wpair.2
    }
    let H := getk2'' j wpair
    have h₁ : CursiveWalk.Solution ⟨CI_of_KI (KI_of_CI j), wk⟩
      := by {simp; rw [inverses2,← H]; exact wpair.2}
    have h₃ : Solution_of (CI_of_KI (KI_of_CI j)) = Solution_of j := by rw [inverses2]
    have : cast h₃ ⟨wk,h₁⟩ = ⟨wk,h₂⟩
      := cast_val ((CI_of_KI (KI_of_CI j))) j wk h₁ h₂ (inverses2 j) h₃
    rw [H,this]
    }


-- instance (j : CursiveWalk.Instance) : Nonempty (Solution_of (CI_of_KI (KI_of_CI j)))
-- := by {
--   sorry
-- }
-- instance (j : CursiveWalk.Instance) : Nonempty (Solution_of j)
-- := by {
--   sorry
-- }
-- This is type-inconsistent:
-- theorem inverses' (j : CursiveWalk.Instance) (wpair : Solution_of j):
--  CS_of_KS (KI_of_CI j) (KS_of_CS j wpair) = wpair := sorry
-- nor is this
-- theorem inverses' (j : CursiveWalk.Instance) :
--  CS_of_KS (KI_of_CI j) = Function.invFun (KS_of_CS j) := sorry


theorem inverses (j : CursiveWalk.Instance) (wpair : Solution_of j):
-- December 31, 2023.
 -- We first want to prove: CS_of_KS (KI_of_CI j) (KS_of_CS j wpair) = wpair, but that's not type-hygienic so we do:
-- ( by {
--   let wpair' := CS_of_KS (KI_of_CI j) (KS_of_CS j wpair)
--   rw [inverses2] at wpair'
--   exact (wpair = wpair')
-- })
-- which becomes:
wpair = Eq.mp
  ((congr_arg _ (inverses2 j)) : Solution_of (CI_of_KI (KI_of_CI j)) = Solution_of j)
  (CS_of_KS (KI_of_CI j) (KS_of_CS j wpair))

:= by {
    apply SetCoe.ext -- prove .1's are equal only
    exact inverses_dot1 _ _
}

theorem inverses''  : -- ci is a CursiveWalk.Instance but we don't have to say that!
id = λ cs ↦ Eq.mp (congr_arg _ (inverses2 _)) (CS_of_KS (KI_of_CI ci) (KS_of_CS ci cs))
  := by {
    apply funext
    intro wpair
    exact inverses _ _
  }


axiom c : Σ i : ℕ, Fin i
#check c.fst
#check c.snd


theorem CS_of_KS_surjective
  (i:Knapsack2.Instance) :
  Function.Surjective (CS_of_KS i)
  := by {
  unfold Function.Surjective
  intro wpair

  -- use KS_of_CS instead?
  let ⟨hw,hT⟩ := wpair.2;
  let k := getk1' i.wt hw hT

  have hwp : wpair.1 = walk_' i.wt k := getk2' i.wt _ _
  rw [hwp] at hT
  let lpair := (getl' i.wt hT);
  let l := lpair.1

  let s := (λ i ↦ [k,l].get i)

  exists ⟨s,by {
    apply Nat.succ_injective
    have hh: (CI_of_KI i).length = i.target.succ := rfl
    rw [← hh]
    let pro := lpair.2
    simp_rw [pro] -- "not motive correct"
    rename wpair.1 (Nat.succ i.target) = (i.wt.val 0) => hTold
    have : s = (λ i_1 ↦ List.get [getk1' i.wt hw hTold, ↑(getl' i.wt hT)] i_1) := rfl
    simp_rw [← this]
    let G := small_lemma i s
    rw [G]
    simp
  }⟩
  exact SetCoe.ext (id hwp.symm)
}


def CI_of_KI_reduction : Reduction Knapsack2 CursiveWalk := { -- my_reduction''
  Map := CI_of_KI
  Property := λ i ↦ by {
    constructor
    intro h; rcases h with ⟨p,hp⟩
    let CW := CS_of_KS i ⟨p,hp⟩; exact ⟨CW.1,CW.2⟩

    intro h; rcases h with ⟨w,hw⟩
    let KS := (KS_of_CS (CI_of_KI i) ⟨w,hw⟩); exact ⟨KS.1,KS.2⟩
  }
}


-- Note the following example doesn't require g to be injective.
example {α β γ δ: Type} (f : α → β) (g : α → γ → δ)
(hf : Function.Injective f)
(hg : ∀ x, Function.Injective (λ y  ↦ g x y))
: Function.Injective (λ (x,y) ↦ (f x, g x y))
:= by {
  intro p₁ p₂ h; let R := hf (congr_arg (λ u ↦ u.1) h)
  apply Prod.ext; exact R
  let Q := (congr_arg (λ u ↦ u.2) h)
  simp at Q; rw [← R] at Q; exact hg p₁.1 Q
}

-- Here is a dependent type version. However, the output type δ is constant.
example {α β δ: Type} {γ : α → Type} (f : α → β) (g : (a:α) → (γ a) → δ)
(hf : Function.Injective f)
(hg : ∀ x, Function.Injective (λ y  ↦ g x y))
: Function.Injective (λ (p : Σ a : α, γ a) ↦ (f p.fst, g p.fst p.snd))
:= by {
  intro ⟨x₁,y₁⟩ ⟨x₂,y₂⟩ h;
  simp at h
  have : x₁ = x₂ := hf h.1
  subst this
  have : y₁ = y₂ := hg x₁ h.2
  subst this
  rfl
}

-- The general statement that can be applied to our case
theorem jointly_inductive_general {I₁ I₂: Type}
  {space₁ : I₁ → Type} {space₂ : I₂ → Type}
  (reduction : I₁ → I₂) (parsimone : (i:I₁) → (space₁ i) → (space₂ (reduction i)))
(hf : Function.Injective reduction)
(hg : ∀ i, Function.Injective (λ s  ↦ parsimone i s))
: Function.Injective (
  λ (⟨i,s⟩ : Σ i' : I₁, space₁ _) ↦ ((⟨reduction i, parsimone i s⟩) : Σ j : I₂, _)
)
:= by {
  intro ⟨i₁,s₁⟩ ⟨i₂,s₂⟩ h; simp at h; have : i₁ = i₂ := hf h.1
  subst this; simp at h; have : s₁ = s₂ := hg _ h; subst this; rfl
}

theorem KI_of_CI_injective : Function.Injective KI_of_CI := by {
  intro x y h
  have : CI_of_KI (KI_of_CI x) = CI_of_KI (KI_of_CI y) := congrArg CI_of_KI h
  rw [inverses2] at this
  rw [inverses2] at this
  exact this
}

theorem CI_of_KI_injective : Function.Injective CI_of_KI := by {
  intro x y h
  exact congr_arg KI_of_CI h
}

theorem KS_of_CS_injective : ∀ (i : CursiveWalk.Instance), Function.Injective fun s => KS_of_CS i s
:= sorry -- similar to CS_of_KS_injective


theorem jointly_inductive_specific :
Function.Injective (
  λ (⟨i,s⟩ : Σ i' : CursiveWalk.Instance, Solution_of i')
  ↦ ((⟨KI_of_CI i, KS_of_CS i s⟩) : Σ j : Knapsack2.Instance, _)
) := jointly_inductive_general _ _ KI_of_CI_injective KS_of_CS_injective

theorem jointly_inductive_specific2 :
Function.Injective (
  λ (⟨i,s⟩ : Σ i' : Knapsack2.Instance, Solution_of _)
  ↦ ((⟨CI_of_KI i, CS_of_KS i s⟩) : Σ j : CursiveWalk.Instance, _)
) := jointly_inductive_general _ _ CI_of_KI_injective CS_of_KS_injective





-- OLD-FASHIONED RESULTS involving CursiveWalkSolution:
def walk_of_solution'' (i:Knapsack2.Instance)
: Solution_of i → CursiveWalkSolution (my_reduction i)
:= by {
  intro s
  -- let k := s.val 0
  exact {
    w           := walk_' i.wt (s.val 0)
    walks       := walk_walks' _ _
    timed       := by {
      let g := keep_arriving' i.wt s.val
      unfold my_reduction; simp; rw [← g,s.property]
      have : (Nat.succ (Matrix.dotProduct i.wt.val s.val)) =
             (i.wt.val 0 * s.val 0 + 1 + i.wt.val 1 * s.val 1)
      := small_lemma _ _
      exact congr_arg _ this
    }
  }
}
def walk_of_solution''' (i:Knapsack2.Instance)
: Solution_of i → CursiveWalkSolution (CI_of_KI i)
:= by {
  intro s
  -- let k := s.val 0
  exact {
    w           := walk_' i.wt (s.val 0)
    walks       := walk_walks' _ _
    timed       := by {
      let g := keep_arriving' i.wt s.val
      unfold CI_of_KI; simp; rw [← g,s.property]
      have : (Nat.succ (Matrix.dotProduct i.wt.val s.val)) =
             (i.wt.val 0 * s.val 0 + 1 + i.wt.val 1 * s.val 1)
      := small_lemma _ _
      exact congr_arg _ this
    }
  }
}
theorem walk_of_solution_injective'' (i:Knapsack2.Instance) :
Function.Injective (walk_of_solution'' i) := by {
  unfold Function.Injective; intro p₁ p₂ hp; unfold walk_of_solution'' at hp
  simp at hp
  have h₁₁: p₁.val 0 = p₂.val 0 := walk__injective' i.wt _ _ hp
  have hmm : i.target.succ = i.wt.val 0 * p₁.1 0 + 1 + i.wt.val 1 * p₂.1 1
    := by {
      unfold Solution_of at p₂; let g := p₂.2
      unfold DecisionProblem.Solution Knapsack2 at g
      unfold Matrix.dotProduct at g; simp at g
      rw [← h₁₁] at g; let g' := congr_arg Nat.succ g
      rw [g',Nat.succ_eq_add_one]; ring
    }
  have : i.wt.val 0 * p₁.val 0 + 1 + i.wt.val 1 * p₁.val 1 =
         i.wt.val 0 * p₁.val 0 + 1 + i.wt.val 1 * p₂.val 1
  := calc
    _ = Nat.succ (Matrix.dotProduct i.wt.val p₁.val) := (small_lemma i p₁.1).symm
    _ = i.target.succ := congr_arg _ p₁.property.symm
    _ = _ := hmm
  have h₁₂: p₁.val 1 = p₂.val 1 := l_unique' i.wt this
  exact Subtype.eq (by {
    apply funext; intro i; have : i = 0 ∨ i = 1 := fin2cases _
    cases this; rw [h]; exact h₁₁; rw [h]; exact h₁₂
  })
}
theorem walk_of_solution_injective''' (i:Knapsack2.Instance) :
Function.Injective (walk_of_solution''' i) := by {
  unfold Function.Injective; intro p₁ p₂ hp; unfold walk_of_solution''' at hp
  simp at hp
  have h₁₁: p₁.val 0 = p₂.val 0 := walk__injective' i.wt _ _ hp
  have hmm : i.target.succ = i.wt.val 0 * p₁.1 0 + 1 + i.wt.val 1 * p₂.1 1
    := by {
      unfold Solution_of at p₂; let g := p₂.2
      unfold DecisionProblem.Solution Knapsack2 at g
      unfold Matrix.dotProduct at g; simp at g
      rw [← h₁₁] at g; let g' := congr_arg Nat.succ g
      rw [g',Nat.succ_eq_add_one]; ring
    }
  have : i.wt.val 0 * p₁.val 0 + 1 + i.wt.val 1 * p₁.val 1 =
         i.wt.val 0 * p₁.val 0 + 1 + i.wt.val 1 * p₂.val 1
  := calc
    _ = Nat.succ (Matrix.dotProduct i.wt.val p₁.val) := (small_lemma i p₁.1).symm
    _ = i.target.succ := congr_arg _ p₁.property.symm
    _ = _ := hmm
  have h₁₂: p₁.val 1 = p₂.val 1 := l_unique' i.wt this
  exact Subtype.eq (by {
    apply funext; intro i; have : i = 0 ∨ i = 1 := fin2cases _
    cases this; rw [h]; exact h₁₁; rw [h]; exact h₁₂
  })
}
-- theorem main_dot_knapsack'' (i : Knapsack2.Instance)
-- : Nonempty (Unique (Knapsack2Solution i))
-- ↔ Nonempty (Unique (CursiveWalkSolution (my_reduction i)))
-- :=
-- by {
--   rw [unique_iff_exists_unique]
--   rw [unique_iff_exists_unique]
--   let H := main_dot_knapsack' i
--   constructor
--   intro h

--   unfold KnapsackSolution at h
--   rcases h with ⟨s,hs⟩
--   exists {
--     w := walk_' i.wt (s.val 0)
--     walks := sorry
--     timed := sorry
--   }
--   sorry
--   sorry
-- }
-- END OF OLD-FASHIONED RESULTS

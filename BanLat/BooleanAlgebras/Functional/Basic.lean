/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.SigmaComplete
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Countably additive functionals on Boolean algebras

This file introduces **nonnegative countably additive functionals** defined on
`σ`-complete Boolean algebras, with some of their basic properties.
-/

open Function
open Filter Topology
open scoped ENNReal

universe u v

/-- `ν : B → ℝ≥0∞` is a **countably additive functional** on a `σ`-complete Boolean algebra
if `ν(⊥) = 0` and `ν(⨆ n, a n) = ∑ n, ν(a n)` for each pair-wise disjoint sequence. -/
structure CountablyAdditiveFunctional (B : Type u)
    [SigmaCompleteBooleanAlgebra B] where
  /-- The value of the functional. -/
  toFun : B → ℝ≥0∞
  /-- The functional vanishes at the bottom element. -/
  map_bot' : toFun ⊥ = 0
  /-- The functional is countably additive on pairwise disjoint sequences. -/
  map_iSup' ⦃a : ℕ → B⦄ : Pairwise (Disjoint on a) →
    toFun (⨆ n, a n) = ∑' n, toFun (a n)

instance {B : Type u} [SigmaCompleteBooleanAlgebra B] :
    CoeFun (CountablyAdditiveFunctional B) (fun _ ↦ B → ℝ≥0∞) :=
  ⟨CountablyAdditiveFunctional.toFun⟩

namespace CountablyAdditiveFunctional

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]
variable (ν : CountablyAdditiveFunctional B)

/-- A countably additive functional vanishes at the bottom element. -/
@[simp]
theorem map_bot : ν ⊥ = 0 := by
  exact ν.map_bot'

/-- A countably additive functional preserves disjoint countable suprema. -/
theorem map_iSup {a : ℕ → B} (ha : Pairwise (Disjoint on a)) :
    ν (⨆ n, a n) = ∑' n, ν (a n) := by
  exact ν.map_iSup' ha

/-- A countably additive functional is additive on disjoint elements. -/
theorem map_sup {a b : B} (h : Disjoint a b) :
    ν (a ⊔ b) = ν a + ν b := by
  let c : ℕ → B := fun n ↦ if n = 0 then a else if n = 1 then b else ⊥
  have hc : Pairwise (Disjoint on c) := by
    rintro i j hij
    change Disjoint (c i) (c j)
    simp only [c]
    split_ifs
    all_goals first | omega | exact h | exact h.symm | simp
  have hiSup : (⨆ n, c n) = a ⊔ b := by
    apply le_antisymm
    · apply SigmaCompleteBooleanAlgebra.iSup_nat_le
      intro n
      simp only [c]
      split_ifs <;> simp
    · exact sup_le (by simpa [c] using SigmaCompleteBooleanAlgebra.le_iSup_nat c 0)
        (by simpa [c] using SigmaCompleteBooleanAlgebra.le_iSup_nat c 1)
  have hsum : ∑' n, ν (c n) = ν a + ν b := by
    rw [ENNReal.tsum_eq_add_tsum_ite 0, ENNReal.tsum_eq_add_tsum_ite 1]
    have hz (x : ℕ) : (if x = 1 then 0 else if x = 0 then 0 else ν (c x)) = 0 := by
      simp only [c]
      split_ifs <;> simp
    simp only [hz, tsum_zero, add_zero, c, if_pos, if_false, Nat.one_ne_zero]
  rw [← hiSup, ν.map_iSup hc, hsum]

/-- A countably additive functional is monotone. -/
theorem monotone : Monotone ν := by
  intro a b h
  rw [← sup_sdiff_cancel_right h, ν.map_sup disjoint_sdiff_self_right]
  simp

/-- Decomposing an element into its difference and intersection preserves its
functional value. -/
theorem map_sdiff_add_inf (a b : B) :
    ν (a \ b) + ν (a ⊓ b) = ν a := by
  rw [← ν.map_sup disjoint_inf_sdiff.symm, sup_sdiff_inf]

/-- A countably additive functional is finite if its value at the top element
is finite. -/
def IsFinite : Prop := ν ⊤ ≠ ∞

/-- Every value of a finite countably additive functional is finite. -/
theorem ne_top (hν : ν.IsFinite) (a : B) : ν a ≠ ∞ := by
  exact ne_top_of_le_ne_top hν (ν.monotone le_top)

/-- For `r ∈ ℝ≥0` and `ν : B → ℝ≥0∞`, `ν.scaledFunctional r` is the countably
additive functional given by `b ↦ r * ν b`. -/
noncomputable def scaledFunctional (r : NNReal) :
    CountablyAdditiveFunctional B where
  toFun := fun b ↦ (r : ℝ≥0∞) * ν b
  map_bot' := by simp
  map_iSup' := by
    intro a ha
    rw [ν.map_iSup ha, ENNReal.tsum_mul_left]

@[simp]
theorem scaledFunctional_apply (r : NNReal) (b : B) :
    scaledFunctional ν r b = (r : ℝ≥0∞) * ν b := rfl

/-- If `ν` is finite, then `ν.scaledFunctional r` is finite for every
`r ∈ ℝ≥0`. -/
theorem scaledFunctional_isFinite (r : NNReal) (hν : ν.IsFinite) :
    (scaledFunctional ν r).IsFinite := by
  exact ENNReal.mul_ne_top (by simp) hν

/-- Let `ρ, ν : B → ℝ≥0∞` be countably additive functionals such that `ν` is
finite and `ρ b ≤ ν b` for every `b ∈ B`. Then `subFunctional ν ρ hν hρν` is
the countably additive functional given by `b ↦ ν b - ρ b`. -/
noncomputable def subFunctional (ρ : CountablyAdditiveFunctional B)
    (hν : ν.IsFinite) (hρν : ∀ b, ρ b ≤ ν b) :
    CountablyAdditiveFunctional B where
  toFun := fun b ↦ ν b - ρ b
  map_bot' := by simp
  map_iSup' := by
    intro a ha
    have hsum : ∑' n, ρ (a n) ≠ ∞ := by
      rw [← ρ.map_iSup ha]
      exact ne_top_of_le_ne_top (ν.ne_top hν _) (hρν _)
    rw [ν.map_iSup ha, ρ.map_iSup ha]
    exact (ENNReal.tsum_sub hsum fun n ↦ hρν (a n)).symm

/-- Let `e : B ≃o C` be an order isomorphism and let `ρ : C → ℝ≥0∞` be a
countably additive functional. Then `pullbackFunctional e ρ` is the countably
additive functional on `B` given by `b ↦ ρ (e b)`. -/
noncomputable def pullbackFunctional {C : Type v} [SigmaCompleteBooleanAlgebra C]
    (e : B ≃o C) (ρ : CountablyAdditiveFunctional C) :
    CountablyAdditiveFunctional B where
  toFun := fun b ↦ ρ (e b)
  map_bot' := by rw [e.map_bot, ρ.map_bot]
  map_iSup' := by
    intro a ha
    rw [OrderIso.map_iSup_nat e a]
    apply ρ.map_iSup
    intro i j hij
    exact (ha hij).map_orderIso e

private theorem map_partialSups_of_pairwise_disjoint (a : ℕ → B)
    (ha : Pairwise (Disjoint on a)) (n : ℕ) :
    ν (partialSups a n) = ∑ i ∈ Finset.range (n + 1), ν (a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpartial : partialSups a (n + 1) = partialSups a n ⊔ a (n + 1) := by
        simpa using partialSups_succ a n
      rw [hpartial,
        ν.map_sup (partialSups_disjoint_of_disjoint a ha (Nat.lt_succ_self n)), ih,
        Finset.sum_range_succ]
      simp [Finset.sum_range_succ, add_assoc]

/-- A countably additive functional preserves suprema of increasing
sequences. -/
theorem map_iSup_eq_iSup {a : ℕ → B} (ha : Monotone a) :
    ν (⨆ n, a n) = ⨆ n, ν (a n) := by
  rw [← SigmaCompleteBooleanAlgebra.iSup_disjointed_nat a,
    ν.map_iSup (disjoint_disjointed a),
    ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)]
  simp_rw [← map_partialSups_of_pairwise_disjoint ν (disjointed a)
    (disjoint_disjointed a), partialSups_disjointed, ha.partialSups_eq]

/-- The values of a countably additive functional along an increasing
sequence converge to the value of its supremum. -/
theorem tendsto_map_iSup {a : ℕ → B} (ha : Monotone a) :
    Filter.Tendsto (fun n ↦ ν (a n)) Filter.atTop (𝓝 (ν (⨆ n, a n))) := by
  rw [ν.map_iSup_eq_iSup ha]
  exact tendsto_atTop_iSup (ν.monotone.comp ha)

end CountablyAdditiveFunctional

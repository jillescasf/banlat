/-
Author: Jesús Illescas-Fiorito
-/

import BanLat.Examples.Ellp.Basic
import BanLat.OrderUnit
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Weak order units in `ℓ^p` spaces

This file proves that:
* For all `1 ≤ p ≤ ∞`, `x` is a weak order unit of `ℓ^p(ι, ℝ)` if, and
only if, all its coordinates are strictly positive.
* For all `1 ≤ p < ∞`, `ℓ^p(ι, ℝ)` has a weak order unit if, and
only if, `ι` is countable.
-/

open scoped ENNReal NNReal lp

noncomputable section

namespace lp

variable {ι : Type*} {p : ENNReal}

/-- `x ∈ ℓ^p(ι, ℝ)` is a weak order unit iff `∀ i ∈ ι, x i > 0`. -/
theorem weakOrderUnit_iff_forall_pos {x : ℓ^p(ι, ℝ)} :
    WeakOrderUnit x ↔ ∀ i, 0 < x i := by
  classical
  constructor
  · intro hwu i
    have hxi : 0 ≤ x i := hwu.1 i
    refine lt_of_le_of_ne hxi fun hi ↦ ?_
    let g : ℓ^p(ι, ℝ) := lp.single p i (1 : ℝ)
    have hdisj : IsVLDisjoint g x := by
      unfold IsVLDisjoint
      apply lp.ext
      funext j
      change min |g j| |x j| = 0
      by_cases hji : j = i
      · subst j
        simp [g, hi.symm]
      · have hgj : g j = 0 := by
          change lp.single (E := fun _ : ι ↦ ℝ) p i (1 : ℝ) j = 0
          exact lp.single_apply_ne (E := fun _ : ι ↦ ℝ) p i (1 : ℝ) hji
        simp [hgj]
    have hg := hwu.2 g hdisj
    have heval := congrArg (fun u : ℓ^p(ι, ℝ) ↦ u i) hg
    have hzero : (0 : ℓ^p(ι, ℝ)) i = 0 := rfl
    change g i = (0 : ℓ^p(ι, ℝ)) i at heval
    rw [show g i = 1 by simp [g], hzero] at heval
    norm_num at heval
  · intro hpos
    have hx : 0 ≤ x := fun i ↦ (hpos i).le
    refine ⟨hx, fun g hdisj ↦ ?_⟩
    apply lp.ext
    funext i
    have hi := congrArg (fun u : ℓ^p(ι, ℝ) ↦ u i) hdisj
    change min |g i| |x i| = 0 at hi
    by_cases hle : |g i| ≤ |x i|
    · rw [min_eq_left hle] at hi
      exact abs_eq_zero.mp hi
    · rw [min_eq_right (le_of_not_ge hle)] at hi
      exact ((hpos i).ne' (abs_eq_zero.mp hi)).elim

variable [Fact (1 ≤ p)]

/-- For `1 ≤ p < ∞`, `ℓ^p(ι, ℝ)` has a weak order unit iff `ι` is countable. -/
theorem nonempty_weakOrderUnit_iff_countable (hp : p ≠ ∞) :
    (∃ x : ℓ^p(ι, ℝ), WeakOrderUnit x) ↔ Countable ι := by
  have hp0 : p ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) Fact.out)
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  constructor
  · rintro ⟨x, hwu⟩
    have hpos := weakOrderUnit_iff_forall_pos.mp hwu
    have hsum := (lp.memℓp x).summable hpR
    have hsupp : Function.support (fun i ↦ ‖x i‖ ^ p.toReal) = Set.univ := by
      ext i
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr (hpos i).ne') _).ne'
    have hcount := hsum.countable_support
    rw [hsupp] at hcount
    exact Set.countable_univ_iff.mp hcount
  · intro hι
    letI : Countable ι := hι
    obtain ⟨g, hgpos, c, hgsum, -⟩ :=
      NNReal.exists_pos_sum_of_countable (ε := 1) one_ne_zero ι
    let r : ℝ := 1 / p.toReal
    let x₀ : ι → ℝ := fun i ↦ (g i ^ r : ℝ≥0)
    have hxmem : Memℓp x₀ p := by
      rw [memℓp_gen_iff hpR]
      have hsum : Summable fun i ↦ (g i : ℝ) := NNReal.summable_coe.mpr hgsum.summable
      convert hsum using 1
      funext i
      change ‖((g i ^ r : ℝ≥0) : ℝ)‖ ^ p.toReal = (g i : ℝ)
      rw [Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      simp only [NNReal.coe_rpow]
      rw [← Real.rpow_mul (NNReal.coe_nonneg _)]
      simp [r, hpR.ne']
    let x : ℓ^p(ι, ℝ) := ⟨x₀, hxmem⟩
    refine ⟨x, weakOrderUnit_iff_forall_pos.mpr ?_⟩
    intro i
    change 0 < (g i ^ r : ℝ≥0)
    exact_mod_cast NNReal.rpow_pos (hgpos i)

end lp

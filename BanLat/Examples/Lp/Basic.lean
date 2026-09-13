/-
Authors: David Muñoz-Lahoz, Jesús Illescas-Fiorito
-/

import BanLat.ALSpace.Basic
import BanLat.ALpSpace.Basic
import BanLat.Normed
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `Lp` spaces as Banach lattices

For a measure space `(α, μ)` and `1 ≤ p ≤ ∞`, the space `Lp ℝ p μ` of real-valued
`Lp` functions is a Banach lattice under the pointwise order and the `Lp` norm.

Some simple properties about indicator functions in `Lp ℝ p μ` are deduced.

Moreover:
* `L₁` is an AL-space.
* `Lₚ` is an ALₚ-space for `1 ≤ p < ∞`.
-/

open MeasureTheory Filter

open scoped NNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Lattice and order structure

Mathlib provides `Lattice (Lp ℝ p μ)`, `IsOrderedAddMonoid (Lp ℝ p μ)`,
`HasSolidNorm (Lp ℝ p μ)`, `NormedAddCommGroup (Lp ℝ p μ)`, and
`CompleteSpace (Lp ℝ p μ)` via `MeasureTheory.Lp.instLattice`,
`MeasureTheory.Lp.instHasSolidNorm`, and
`MeasureTheory.Lp.instCompleteSpace`.
-/

/-! ### Vector lattice -/

/-- `Lp ℝ p μ` is a vector lattice. -/
noncomputable instance instVectorLatticeLp : VectorLattice (Lp ℝ p μ) where
  smul_le_smul_of_nonneg_left a ha x y hxy := by
    rw [← Lp.coeFn_le] at hxy ⊢
    filter_upwards [Lp.coeFn_smul a x, Lp.coeFn_smul a y, hxy] with i h1 h2 h3
    rw [h1, h2]
    exact smul_le_smul_of_nonneg_left h3 ha

/-! ### Normed vector lattice -/

/-- `Lp ℝ p μ` is a normed vector lattice. -/
noncomputable instance instNormedVectorLatticeLp :
    NormedVectorLattice (Lp ℝ p μ) where

/-! ### Banach lattice -/

/-- `Lp ℝ p μ` is a Banach lattice. -/
noncomputable instance instBanachLatticeLp : BanachLattice (Lp ℝ p μ) where

/-! ### p-th power of the `L^p` norm formula -/

namespace MeasureTheory.Lp

variable {E : Type*} [NormedAddCommGroup E]

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module

/-- The `p`-th power of the `L^p`-norm as an integral. -/
lemma norm_rpow_eq_integral_norm_rpow
    {p : ℝ≥0} (hp : p ≠ 0) (f : Lp E (p : ENNReal) μ) :
    ‖f‖ ^ (p : ℝ) = ∫ x, ‖f x‖ ^ (p : ℝ) ∂μ := by
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm
    (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top]
  rw [ENNReal.toReal_ofReal]
  · exact Real.rpow_inv_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (NNReal.coe_ne_zero.mpr hp)
  · exact Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

omit [Fact (1 ≤ p)] in
/-- A real-valued constant indicator is a scalar multiple of the indicator with value one. -/
theorem indicatorConstLp_eq_smul {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (c : ℝ) :
    indicatorConstLp p hs hμs c = c • indicatorConstLp p hs hμs (1 : ℝ) := by
  rw [Lp.ext_iff]
  filter_upwards [indicatorConstLp_coeFn (hs := hs) (hμs := hμs) (c := c),
    Lp.coeFn_smul c (indicatorConstLp p hs hμs (1 : ℝ)),
    indicatorConstLp_coeFn (hs := hs) (hμs := hμs) (c := (1 : ℝ))]
    with x hc hsmul hone
  rw [hc, hsmul, Pi.smul_apply, hone]
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

omit [Fact (1 ≤ p)] in
/-- Scalar multiplication can be moved into the value of a real constant indicator. -/
theorem smul_indicatorConstLp {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (r c : ℝ) :
    r • indicatorConstLp p hs hμs c = indicatorConstLp p hs hμs (r * c) := by
  rw [indicatorConstLp_eq_smul hs hμs c,
    indicatorConstLp_eq_smul hs hμs (r * c), smul_smul]

omit [Fact (1 ≤ p)] in
/-- The absolute value of a real constant indicator is obtained by taking the absolute value of
its value. -/
theorem abs_indicatorConstLp {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (c : ℝ) :
    |indicatorConstLp p hs hμs c| = indicatorConstLp p hs hμs |c| := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_abs (indicatorConstLp p hs hμs c),
    indicatorConstLp_coeFn (p := p) (μ := μ) (s := s) (c := c),
    indicatorConstLp_coeFn (p := p) (μ := μ) (s := s) (c := |c|)]
    with x habs hc hcabs
  rw [habs, hc, hcabs]
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

omit [Fact (1 ≤ p)] in
/-- Constant indicators of disjoint measurable sets are lattice-disjoint in real `Lp`. -/
theorem indicatorConstLp_isVLDisjoint {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμs : μ s ≠ ⊤) (hμt : μ t ≠ ⊤)
    (hst : Disjoint s t) (c d : ℝ) :
    IsVLDisjoint (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt d) := by
  unfold IsVLDisjoint
  apply Lp.ext
  filter_upwards [Lp.coeFn_inf |indicatorConstLp p hs hμs c|
      |indicatorConstLp p ht hμt d|,
    Lp.coeFn_abs (indicatorConstLp p hs hμs c),
    Lp.coeFn_abs (indicatorConstLp p ht hμt d),
    indicatorConstLp_coeFn (p := p) (μ := μ) (s := s) (c := c),
    indicatorConstLp_coeFn (p := p) (μ := μ) (s := t) (c := d),
    Lp.coeFn_zero ℝ p μ] with x hinf habsc habsd hc hd hzero
  rw [hinf, hzero]
  change min _ _ = 0
  rw [habsc, habsd, hc, hd]
  by_cases hxs : x ∈ s
  · have hxt : x ∉ t := Set.disjoint_left.1 hst hxs
    simp [Set.indicator, hxs, hxt]
  · simp [Set.indicator, hxs]

omit [Fact (1 ≤ p)] in
/-- A real-valued simple constant indicator is a scalar multiple of the indicator with value
one. -/
theorem simpleFunc.indicatorConst_eq_smul {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (c : ℝ) :
    Lp.simpleFunc.indicatorConst p hs hμs c =
      c • Lp.simpleFunc.indicatorConst p hs hμs (1 : ℝ) := by
  apply Subtype.ext
  change indicatorConstLp p hs hμs c = c • indicatorConstLp p hs hμs (1 : ℝ)
  exact indicatorConstLp_eq_smul hs hμs c

omit [Fact (1 ≤ p)] in
/-- Simple functions with disjoint supports define lattice-disjoint elements of real `Lp`. -/
theorem simpleFunc.toLp_isVLDisjoint {f g : SimpleFunc α ℝ}
    (hf : MemLp f p μ) (hg : MemLp g p μ)
    (hfg : Disjoint (Function.support f) (Function.support g)) :
    IsVLDisjoint (SimpleFunc.toLp f hf : Lp ℝ p μ) (SimpleFunc.toLp g hg : Lp ℝ p μ) := by
  unfold IsVLDisjoint
  apply Lp.ext
  filter_upwards [Lp.coeFn_inf |(SimpleFunc.toLp f hf : Lp ℝ p μ)|
      |(SimpleFunc.toLp g hg : Lp ℝ p μ)|,
    Lp.coeFn_abs (SimpleFunc.toLp f hf : Lp ℝ p μ),
    Lp.coeFn_abs (SimpleFunc.toLp g hg : Lp ℝ p μ), hf.coeFn_toLp, hg.coeFn_toLp,
    Lp.coeFn_zero ℝ p μ] with x hinf habsf habsg hfx hgx hzero
  rw [hinf, hzero]
  change min _ _ = 0
  rw [habsf, habsg, hfx, hgx]
  by_cases hfx0 : f x = 0
  · simp [hfx0]
  have hgx0 : g x = 0 := by
    by_contra hgx0
    exact Set.disjoint_left.1 hfg hfx0 hgx0
  simp [hgx0]

end MeasureTheory.Lp

/-! ### Lₚ(μ) spaces are ALₚ-spaces -/
section ALpSpace

variable {p : ℝ≥0} [Fact (1 ≤ p)]

private instance instFactOneLEENNRealALp :
    Fact (1 ≤ (p : ENNReal)) :=
  ⟨by exact_mod_cast (Fact.out : (1 : ℝ≥0) ≤ p)⟩

/-- If `f ⟂ g`, `|f+g|ᵖ = |f|ᵖ + |g|ᵖ` a.e. -/
private lemma ae_norm_add_rpow_eq_of_isVLDisjoint
    {f g : Lp ℝ (p : ENNReal) μ} (hfg : IsVLDisjoint f g) :
    (fun x ↦ ‖(f + g) x‖ ^ (p : ℝ)) =ᵐ[μ]
      fun x ↦ ‖f x‖ ^ (p : ℝ) + ‖g x‖ ^ (p : ℝ) := by
  have hp : p ≠ 0 := (lt_of_lt_of_le zero_lt_one Fact.out).ne'
  have heq : |f| ⊓ |g| = 0 := hfg
  have hzero : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0 := by
    filter_upwards [Lp.coeFn_inf |f| |g|, Lp.coeFn_abs f,
      Lp.coeFn_abs g, Lp.coeFn_zero ℝ (p : ENNReal) μ] with x hinf hf hg hzero
    rw [heq, hzero] at hinf
    change (0 : ℝ) = min ((|f| : Lp ℝ (p : ENNReal) μ) x)
      ((|g| : Lp ℝ (p : ENNReal) μ) x) at hinf
    rw [hf, hg] at hinf
    rcases le_total |f x| |g x| with hle | hle
    · left
      exact abs_eq_zero.mp ((min_eq_left hle ▸ hinf).symm)
    · right
      exact abs_eq_zero.mp ((min_eq_right hle ▸ hinf).symm)
  filter_upwards [Lp.coeFn_add f g, hzero] with x hadd hx
  rw [hadd]
  rcases hx with hf | hg
  · simp [hf, Real.zero_rpow (NNReal.coe_ne_zero.mpr hp)]
  · simp [hg, Real.zero_rpow (NNReal.coe_ne_zero.mpr hp)]

/-- For every `1 ≤ p < ∞`, the real space `L^p(μ)` is an ALₚ-space -/
noncomputable instance instALpSpaceLp :
    ALpSpace p (Lp ℝ (p : ENNReal) μ) where
  norm_add_rpow_eq_of_isVLDisjoint {f g} hfg := by
    have hp : p ≠ 0 := (lt_of_lt_of_le zero_lt_one Fact.out).ne'
    rw [Lp.norm_rpow_eq_integral_norm_rpow hp, Lp.norm_rpow_eq_integral_norm_rpow hp,
      Lp.norm_rpow_eq_integral_norm_rpow hp,
      integral_congr_ae (ae_norm_add_rpow_eq_of_isVLDisjoint hfg)]
    exact integral_add ((Lp.memLp f).integrable_norm_rpow
      (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top)
      ((Lp.memLp g).integrable_norm_rpow
        (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top)

end ALpSpace

/-! ### AL-space -/

/-- The `L¹` norm is additive on non-negative elements, so `L¹(μ)` is an AL-space; in
particular the norm of `L¹(μ)` is order continuous. -/
noncomputable instance instALSpaceL1 : ALSpace (Lp ℝ 1 μ) :=
  instALpSpaceLp (p := (1 : NNReal))

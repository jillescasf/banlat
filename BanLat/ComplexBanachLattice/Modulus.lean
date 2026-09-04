/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.AMSpace.Kakutani
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Complex modulus

This file introduces the **complex modulus** associated to each pair `(x, y)` of elements of a
real Banach lattice `E`, defined as `|(x, y)| := sup{cos(θ)x+sin(θ)y | θ ∈ ℝ} ∈ E₊`.

This is done first for `x, y ∈ ℝ`, where `|(x, y)| = sqrt(x^2+y^2)`, then point-wise for
`x, y ∈  C(K, ℝ)`. Kakutani's representation theorem is used to prove that such supremum always
exist for any two elements of a real Banach lattice.

Usual properties of this modulus are also derived.
-/

private theorem sqrt_sq_add_sq_eq_rotation_arg (a b : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2) =
      Real.cos (Complex.arg ⟨a, b⟩) * a + Real.sin (Complex.arg ⟨a, b⟩) * b := by
  rw [← Complex.norm_eq_sqrt_sq_add_sq (⟨a, b⟩ : ℂ)]
  change ‖(⟨a, b⟩ : ℂ)‖ =
    Real.cos (Complex.arg ⟨a, b⟩) * (⟨a, b⟩ : ℂ).re +
      Real.sin (Complex.arg ⟨a, b⟩) * (⟨a, b⟩ : ℂ).im
  rw [← Complex.norm_mul_cos_arg (⟨a, b⟩ : ℂ),
    ← Complex.norm_mul_sin_arg (⟨a, b⟩ : ℂ)]
  calc
    ‖(⟨a, b⟩ : ℂ)‖ = ‖(⟨a, b⟩ : ℂ)‖ * 1 := (mul_one _).symm
    _ = ‖(⟨a, b⟩ : ℂ)‖ *
        (Real.cos (Complex.arg ⟨a, b⟩) ^ 2 + Real.sin (Complex.arg ⟨a, b⟩) ^ 2) := by
      rw [Real.cos_sq_add_sin_sq]
    _ = _ := by ring

private theorem real_rotationRange_isLUB (a b : ℝ) :
    IsLUB (Set.range fun θ : ℝ ↦ Real.cos θ * a + Real.sin θ * b)
      (Real.sqrt (a ^ 2 + b ^ 2)) := by
  constructor
  · rintro _ ⟨θ, rfl⟩
    apply Real.le_sqrt_of_sq_le
    calc
      (Real.cos θ * a + Real.sin θ * b) ^ 2 ≤
          (Real.cos θ * a + Real.sin θ * b) ^ 2 +
            (Real.sin θ * a - Real.cos θ * b) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (a ^ 2 + b ^ 2) := by ring
      _ = a ^ 2 + b ^ 2 := by rw [Real.cos_sq_add_sin_sq, one_mul]
  · intro u hu
    have h := hu ⟨Complex.arg ⟨a, b⟩, rfl⟩
    rw [sqrt_sq_add_sq_eq_rotation_arg]
    exact h

private noncomputable def continuousMapModulus {K : Type*} [TopologicalSpace K]
    (f g : C(K, ℝ)) : C(K, ℝ) where
  toFun t := Real.sqrt (f t ^ 2 + g t ^ 2)
  continuous_toFun := Real.continuous_sqrt.comp ((f.continuous.pow 2).add (g.continuous.pow 2))

private theorem continuousMapModulus_isLUB {K : Type*} [TopologicalSpace K]
    (f g : C(K, ℝ)) :
    IsLUB (Set.range fun θ : ℝ ↦ Real.cos θ • f + Real.sin θ • g)
      (continuousMapModulus f g) := by
  constructor
  · rintro _ ⟨θ, rfl⟩ t
    exact (real_rotationRange_isLUB (f t) (g t)).1 ⟨θ, rfl⟩
  · intro u hu t
    apply (real_rotationRange_isLUB (f t) (g t)).2
    rintro _ ⟨θ, rfl⟩
    exact (hu ⟨θ, rfl⟩) t

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [BanachLattice E]

/-- The set of rotations of a pair of elements in a Banach lattice. -/
def rotationRange (x y : E) : Set E :=
  Set.range fun θ : ℝ ↦ Real.cos θ • x + Real.sin θ • y

private theorem rotation_le_abs_add_abs (x y : E) (θ : ℝ) :
    Real.cos θ • x + Real.sin θ • y ≤ |x| + |y| := by
  calc
    Real.cos θ • x + Real.sin θ • y ≤
        |Real.cos θ • x + Real.sin θ • y| := le_abs_self _
    _ ≤ |Real.cos θ • x| + |Real.sin θ • y| := abs_add_le _ _
    _ = |Real.cos θ| • |x| + |Real.sin θ| • |y| := by
      rw [abs_smul', abs_smul']
    _ ≤ (1 : ℝ) • |x| + (1 : ℝ) • |y| := add_le_add
      (smul_le_smul_of_nonneg_right (Real.abs_cos_le_one θ) (abs_nonneg x))
      (smul_le_smul_of_nonneg_right (Real.abs_sin_le_one θ) (abs_nonneg y))
    _ = |x| + |y| := by rw [one_smul, one_smul]

private theorem sup_abs_le_of_upperBound_rotationRange {x y u : E}
    (hu : u ∈ upperBounds (rotationRange x y)) : |x| ⊔ |y| ≤ u := by
  apply sup_le
  · apply abs_le'.mpr
    constructor
    · simpa only [rotationRange, Real.cos_zero, Real.sin_zero, one_smul, zero_smul,
        add_zero] using hu ⟨0, rfl⟩
    · simpa only [rotationRange, Real.cos_pi, Real.sin_pi, neg_smul, one_smul,
        zero_smul, add_zero] using hu ⟨Real.pi, rfl⟩
  · apply abs_le'.mpr
    constructor
    · simpa only [rotationRange, Real.cos_pi_div_two, Real.sin_pi_div_two,
        zero_smul, one_smul, zero_add] using hu ⟨Real.pi / 2, rfl⟩
    · simpa only [rotationRange, Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg,
        Real.sin_pi_div_two, zero_smul, neg_smul, one_smul, zero_add] using
        hu ⟨-(Real.pi / 2), rfl⟩

private theorem nonneg_of_upperBound_rotationRange {x y u : E}
    (hu : u ∈ upperBounds (rotationRange x y)) : 0 ≤ u := by
  exact (abs_nonneg x).trans
    (le_sup_left.trans (sup_abs_le_of_upperBound_rotationRange hu))

private theorem rotationRange_neg_left (x y : E) :
    rotationRange (-x) y = rotationRange x y := by
  apply Set.Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Real.pi - θ, ?_⟩
    change Real.cos (Real.pi - θ) • x + Real.sin (Real.pi - θ) • y =
      Real.cos θ • (-x) + Real.sin θ • y
    rw [Real.cos_pi_sub, Real.sin_pi_sub]
    module
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Real.pi - θ, ?_⟩
    change Real.cos (Real.pi - θ) • (-x) + Real.sin (Real.pi - θ) • y =
      Real.cos θ • x + Real.sin θ • y
    rw [Real.cos_pi_sub, Real.sin_pi_sub]
    module

private theorem rotationRange_neg_right (x y : E) :
    rotationRange x (-y) = rotationRange x y := by
  apply Set.Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    refine ⟨-θ, ?_⟩
    change Real.cos (-θ) • x + Real.sin (-θ) • y =
      Real.cos θ • x + Real.sin θ • (-y)
    rw [Real.cos_neg, Real.sin_neg]
    module
  · rintro _ ⟨θ, rfl⟩
    refine ⟨-θ, ?_⟩
    change Real.cos (-θ) • x + Real.sin (-θ) • (-y) =
      Real.cos θ • x + Real.sin θ • y
    rw [Real.cos_neg, Real.sin_neg]
    module

private theorem rotationRange_comm (x y : E) :
    rotationRange x y = rotationRange y x := by
  apply Set.Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Real.pi / 2 - θ, ?_⟩
    change Real.cos (Real.pi / 2 - θ) • y + Real.sin (Real.pi / 2 - θ) • x =
      Real.cos θ • x + Real.sin θ • y
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    module
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Real.pi / 2 - θ, ?_⟩
    change Real.cos (Real.pi / 2 - θ) • x + Real.sin (Real.pi / 2 - θ) • y =
      Real.cos θ • y + Real.sin θ • x
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    module

private theorem rotationRange_linear_transform (a b : ℝ) (x y : E) :
    rotationRange (a • x - b • y) (b • x + a • y) =
      (fun z ↦ Real.sqrt (a ^ 2 + b ^ 2) • z) '' rotationRange x y := by
  let r := Real.sqrt (a ^ 2 + b ^ 2)
  let δ := Complex.arg (⟨a, b⟩ : ℂ)
  change rotationRange (a • x - b • y) (b • x + a • y) =
    (fun z ↦ r • z) '' rotationRange x y
  have ha : r * Real.cos δ = a := by
    dsimp [r, δ]
    rw [← Complex.norm_eq_sqrt_sq_add_sq (⟨a, b⟩ : ℂ)]
    exact Complex.norm_mul_cos_arg (⟨a, b⟩ : ℂ)
  have hb : r * Real.sin δ = b := by
    dsimp [r, δ]
    rw [← Complex.norm_eq_sqrt_sq_add_sq (⟨a, b⟩ : ℂ)]
    exact Complex.norm_mul_sin_arg (⟨a, b⟩ : ℂ)
  apply Set.Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Real.cos (θ - δ) • x + Real.sin (θ - δ) • y, ⟨θ - δ, rfl⟩, ?_⟩
    change r • (Real.cos (θ - δ) • x + Real.sin (θ - δ) • y) =
      Real.cos θ • (a • x - b • y) + Real.sin θ • (b • x + a • y)
    rw [Real.cos_sub, Real.sin_sub, ← ha, ← hb]
    module
  · rintro _ ⟨_, ⟨θ, rfl⟩, rfl⟩
    refine ⟨θ + δ, ?_⟩
    change Real.cos (θ + δ) • (a • x - b • y) +
        Real.sin (θ + δ) • (b • x + a • y) =
      r • (Real.cos θ • x + Real.sin θ • y)
    rw [Real.cos_add, Real.sin_add, ← ha, ← hb]
    match_scalars
    · calc
        (Real.cos θ * Real.cos δ - Real.sin θ * Real.sin δ) *
              (r * Real.cos δ * 1) +
            (Real.sin θ * Real.cos δ + Real.cos θ * Real.sin δ) *
              (r * Real.sin δ * 1) =
          r * Real.cos θ * (Real.cos δ ^ 2 + Real.sin δ ^ 2) := by ring
        _ = r * (Real.cos θ * 1) := by rw [Real.cos_sq_add_sin_sq]; ring
    · calc
        (Real.cos θ * Real.cos δ - Real.sin θ * Real.sin δ) *
              -(r * Real.sin δ * 1) +
            (Real.sin θ * Real.cos δ + Real.cos θ * Real.sin δ) *
              (r * Real.cos δ * 1) =
          r * Real.sin θ * (Real.cos δ ^ 2 + Real.sin δ ^ 2) := by ring
        _ = r * (Real.sin θ * 1) := by rw [Real.cos_sq_add_sin_sq]; ring

/-- For all `x, y ∈ E`, `sup{cos(θ)x+sin(θ)y}` exists as an element of `E`. -/
private theorem exists_isLUB_rotationRange (x y : E) :
    ∃ z, IsLUB (rotationRange x y) z := by
  let e := |x| + |y|
  have he : 0 ≤ e := add_nonneg (abs_nonneg x) (abs_nonneg y)
  by_cases hzero : e = 0
  · have hxabs : |x| = 0 := le_antisymm
      (le_trans (le_add_of_nonneg_right (abs_nonneg y)) (hzero.le)) (abs_nonneg x)
    have hyabs : |y| = 0 := le_antisymm
      (le_trans (le_add_of_nonneg_left (abs_nonneg x)) (hzero.le)) (abs_nonneg y)
    have hx0 : x = 0 := (abs_eq_zero_iff_zero x).mp hxabs
    have hy0 : y = 0 := (abs_eq_zero_iff_zero y).mp hyabs
    subst x
    subst y
    refine ⟨0, ?_⟩
    constructor
    · rintro _ ⟨θ, rfl⟩
      simp
    · intro u hu
      simpa using hu ⟨0, rfl⟩
  · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm hzero)
    letI := isUniformlyCompleteVectorLattice_of_banachLattice E
    letI : NormedAddCommGroup ↥(OrderIdeal.principal e) :=
      OrderIdeal.principalNormedAddCommGroup e
    letI : Lattice ↥(OrderIdeal.principal e) := OrderIdeal.instLatticePrincipal e
    letI : IsOrderedAddMonoid ↥(OrderIdeal.principal e) :=
      OrderIdeal.instIsOrderedAddMonoidPrincipal e
    letI : AMSpaceWithUnit ↥(OrderIdeal.principal e) :=
      OrderIdeal.principalAMSpaceWithUnit he
        (IsUniformlyCompleteVectorLattice.complete_principal e hepos)
    let T := OrderIdeal.principalKakutaniEquiv hepos
    have hx : x ∈ OrderIdeal.principal e := by
      rw [OrderIdeal.mem_principal]
      refine ⟨1, zero_le_one, ?_⟩
      rw [one_smul, abs_of_nonneg he]
      exact le_add_of_nonneg_right (abs_nonneg y)
    have hy : y ∈ OrderIdeal.principal e := by
      rw [OrderIdeal.mem_principal]
      refine ⟨1, zero_le_one, ?_⟩
      rw [one_smul, abs_of_nonneg he]
      exact le_add_of_nonneg_left (abs_nonneg x)
    let f := T ⟨x, hx⟩
    let g := T ⟨y, hy⟩
    let z := T.symm (continuousMapModulus f g)
    refine ⟨z, ?_⟩
    constructor
    · rintro _ ⟨θ, rfl⟩
      let r : ↥(OrderIdeal.principal e) :=
        Real.cos θ • (⟨x, hx⟩ : ↥(OrderIdeal.principal e)) +
          Real.sin θ • (⟨y, hy⟩ : ↥(OrderIdeal.principal e))
      have hrmap : T r = Real.cos θ • f + Real.sin θ • g := by
        change T.toLinearIsometryEquiv
            (Real.cos θ • (⟨x, hx⟩ : ↥(OrderIdeal.principal e)) +
              Real.sin θ • (⟨y, hy⟩ : ↥(OrderIdeal.principal e))) =
          Real.cos θ • T.toLinearIsometryEquiv ⟨x, hx⟩ +
            Real.sin θ • T.toLinearIsometryEquiv ⟨y, hy⟩
        rw [map_add, map_smul, map_smul]
      have hfun := (continuousMapModulus_isLUB f g).1 ⟨θ, rfl⟩
      change Real.cos θ • f + Real.sin θ • g ≤ continuousMapModulus f g at hfun
      rw [← hrmap] at hfun
      have hback := T.symm.toVecLatEquiv.toVecLatHom.monotone hfun
      change T.symm (T r) ≤ T.symm (continuousMapModulus f g) at hback
      have hleft : T.symm (T r) = r := by
        change T.toLinearIsometryEquiv.symm (T.toLinearIsometryEquiv r) = r
        exact T.toLinearIsometryEquiv.symm_apply_apply r
      rw [hleft] at hback
      exact hback
    · intro u hu
      have hu0 : 0 ≤ u := nonneg_of_upperBound_rotationRange hu
      have huv0 : 0 ≤ u ⊓ e := le_inf hu0 he
      have huv_mem : u ⊓ e ∈ OrderIdeal.principal e := by
        rw [OrderIdeal.mem_principal]
        refine ⟨1, zero_le_one, ?_⟩
        rw [one_smul, abs_of_nonneg huv0, abs_of_nonneg he]
        exact inf_le_right
      let v : ↥(OrderIdeal.principal e) := ⟨u ⊓ e, huv_mem⟩
      have hTv : T v ∈ upperBounds
          (Set.range fun θ : ℝ ↦ Real.cos θ • f + Real.sin θ • g) := by
        rintro _ ⟨θ, rfl⟩
        let r : ↥(OrderIdeal.principal e) :=
          Real.cos θ • (⟨x, hx⟩ : ↥(OrderIdeal.principal e)) +
            Real.sin θ • (⟨y, hy⟩ : ↥(OrderIdeal.principal e))
        have hr : r ≤ v := by
          change Real.cos θ • x + Real.sin θ • y ≤ u ⊓ e
          exact le_inf (hu ⟨θ, rfl⟩) (rotation_le_abs_add_abs x y θ)
        have hmap := T.toVecLatEquiv.toVecLatHom.monotone hr
        change T r ≤ T v at hmap
        have hrmap : T r = Real.cos θ • f + Real.sin θ • g := by
          change T.toLinearIsometryEquiv
              (Real.cos θ • (⟨x, hx⟩ : ↥(OrderIdeal.principal e)) +
                Real.sin θ • (⟨y, hy⟩ : ↥(OrderIdeal.principal e))) =
            Real.cos θ • T.toLinearIsometryEquiv ⟨x, hx⟩ +
              Real.sin θ • T.toLinearIsometryEquiv ⟨y, hy⟩
          rw [map_add, map_smul, map_smul]
        rw [hrmap] at hmap
        exact hmap
      have hmod : continuousMapModulus f g ≤ T v :=
        (continuousMapModulus_isLUB f g).2 hTv
      have hzv : z ≤ v := by
        have hback := T.symm.toVecLatEquiv.toVecLatHom.monotone hmod
        change T.symm (continuousMapModulus f g) ≤ v
        change T.symm (continuousMapModulus f g) ≤ T.symm (T v) at hback
        have hright : T.symm (T v) = v := by
          change T.toLinearIsometryEquiv.symm (T.toLinearIsometryEquiv v) = v
          exact T.toLinearIsometryEquiv.symm_apply_apply v
        rw [hright] at hback
        exact hback
      calc
        (z : E) ≤ (v : E) := hzv
        _ = u ⊓ e := rfl
        _ ≤ u := inf_le_left

/-- The complex modulus associated with a pair of elements in a real Banach lattice. -/
noncomputable def complexModulus (x y : E) : E :=
  Classical.choose (exists_isLUB_rotationRange x y)

/-- The complex modulus is the least upper bound of all rotations of the pair. -/
theorem complexModulus_isLUB (x y : E) :
    IsLUB (rotationRange x y) (complexModulus x y) :=
  Classical.choose_spec (exists_isLUB_rotationRange x y)

/-- The complex modulus is nonnegative. -/
theorem complexModulus_nonneg (x y : E) :
    0 ≤ complexModulus x y :=
  nonneg_of_upperBound_rotationRange (complexModulus_isLUB x y).1

/-- The complex modulus of `(x, 0)` is the absolute value of `x`. -/
theorem complexModulus_zero_right (x : E) :
    complexModulus x 0 = |x| := by
  apply le_antisymm
  · apply (complexModulus_isLUB x 0).2
    rintro _ ⟨θ, rfl⟩
    simpa using rotation_le_abs_add_abs x 0 θ
  · have hx : x ≤ complexModulus x 0 := by
      simpa only [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero] using
        (complexModulus_isLUB x 0).1 ⟨0, rfl⟩
    have hnx : -x ≤ complexModulus x 0 := by
      simpa only [Real.cos_pi, Real.sin_pi, neg_smul, one_smul, zero_smul, add_zero] using
        (complexModulus_isLUB x 0).1 ⟨Real.pi, rfl⟩
    exact abs_le'.mpr ⟨hx, hnx⟩

/-- The complex modulus of `(0, y)` is the absolute value of `y`. -/
theorem complexModulus_zero_left (y : E) :
    complexModulus 0 y = |y| := by
  apply le_antisymm
  · apply (complexModulus_isLUB 0 y).2
    rintro _ ⟨θ, rfl⟩
    simpa using rotation_le_abs_add_abs 0 y θ
  · have hy : y ≤ complexModulus 0 y := by
      simpa only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add] using
        (complexModulus_isLUB 0 y).1 ⟨Real.pi / 2, rfl⟩
    have hny : -y ≤ complexModulus 0 y := by
      simpa only [Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two,
        zero_smul, neg_smul, one_smul, zero_add] using
        (complexModulus_isLUB 0 y).1 ⟨-(Real.pi / 2), rfl⟩
    exact abs_le'.mpr ⟨hy, hny⟩

/-- Changing the sign of the first component does not change the complex modulus. -/
theorem complexModulus_neg_left (x y : E) :
    complexModulus (-x) y = complexModulus x y := by
  apply (complexModulus_isLUB (-x) y).unique
  rw [rotationRange_neg_left]
  exact complexModulus_isLUB x y

/-- Changing the sign of the second component does not change the complex modulus. -/
theorem complexModulus_neg_right (x y : E) :
    complexModulus x (-y) = complexModulus x y := by
  apply (complexModulus_isLUB x (-y)).unique
  rw [rotationRange_neg_right]
  exact complexModulus_isLUB x y

/-- Interchanging the two components does not change the complex modulus. -/
theorem complexModulus_comm (x y : E) :
    complexModulus x y = complexModulus y x := by
  apply (complexModulus_isLUB x y).unique
  rw [rotationRange_comm]
  exact complexModulus_isLUB y x

/-- The absolute value of the first component is bounded by the complex modulus. -/
theorem abs_le_complexModulus_left (x y : E) :
    |x| ≤ complexModulus x y := by
  exact le_sup_left.trans
    (sup_abs_le_of_upperBound_rotationRange (complexModulus_isLUB x y).1)

/-- The absolute value of the second component is bounded by the complex modulus. -/
theorem abs_le_complexModulus_right (x y : E) :
    |y| ≤ complexModulus x y := by
  exact le_sup_right.trans
    (sup_abs_le_of_upperBound_rotationRange (complexModulus_isLUB x y).1)

/-- The complex modulus is bounded by the sum of the absolute values of its components. -/
theorem complexModulus_le_abs_add_abs (x y : E) :
    complexModulus x y ≤ |x| + |y| := by
  apply (complexModulus_isLUB x y).2
  rintro _ ⟨θ, rfl⟩
  exact rotation_le_abs_add_abs x y θ

/-- The complex modulus is zero exactly when both components are zero. -/
theorem complexModulus_eq_zero_iff (x y : E) :
    complexModulus x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hxabs : |x| = 0 := le_antisymm ((abs_le_complexModulus_left x y).trans_eq h)
      (abs_nonneg x)
    have hyabs : |y| = 0 := le_antisymm ((abs_le_complexModulus_right x y).trans_eq h)
      (abs_nonneg y)
    exact ⟨(abs_eq_zero_iff_zero x).mp hxabs, (abs_eq_zero_iff_zero y).mp hyabs⟩
  · rintro ⟨rfl, rfl⟩
    simpa using complexModulus_zero_right (0 : E)

/-- The complex modulus satisfies the triangle inequality. -/
theorem complexModulus_add_le (x₁ y₁ x₂ y₂ : E) :
    complexModulus (x₁ + x₂) (y₁ + y₂) ≤
      complexModulus x₁ y₁ + complexModulus x₂ y₂ := by
  apply (complexModulus_isLUB (x₁ + x₂) (y₁ + y₂)).2
  rintro _ ⟨θ, rfl⟩
  calc
    Real.cos θ • (x₁ + x₂) + Real.sin θ • (y₁ + y₂) =
        (Real.cos θ • x₁ + Real.sin θ • y₁) +
          (Real.cos θ • x₂ + Real.sin θ • y₂) := by module
    _ ≤ complexModulus x₁ y₁ + complexModulus x₂ y₂ := add_le_add
      ((complexModulus_isLUB x₁ y₁).1 ⟨θ, rfl⟩)
      ((complexModulus_isLUB x₂ y₂).1 ⟨θ, rfl⟩)

/-- The complex modulus satisfies the reversed triangle inequality. -/
theorem abs_complexModulus_sub_complexModulus_le (x₁ y₁ x₂ y₂ : E) :
    |complexModulus x₁ y₁ - complexModulus x₂ y₂| ≤
      complexModulus (x₁ - x₂) (y₁ - y₂) := by
  apply abs_le'.mpr
  constructor
  · rw [sub_le_iff_le_add]
    simpa using complexModulus_add_le (x₁ - x₂) (y₁ - y₂) x₂ y₂
  · rw [neg_sub, sub_le_iff_le_add]
    have hneg :
        complexModulus (x₂ - x₁) (y₂ - y₁) =
          complexModulus (x₁ - x₂) (y₁ - y₂) := by
      rw [← neg_sub x₁ x₂, ← neg_sub y₁ y₂, complexModulus_neg_left,
        complexModulus_neg_right]
    rw [← hneg]
    simpa using complexModulus_add_le (x₂ - x₁) (y₂ - y₁) x₁ y₁

/-- Multiplication by a complex scalar scales the complex modulus by its Euclidean norm. -/
theorem complexModulus_linear_transform (a b : ℝ) (x y : E) :
    complexModulus (a • x - b • y) (b • x + a • y) =
      Real.sqrt (a ^ 2 + b ^ 2) • complexModulus x y := by
  apply (complexModulus_isLUB (a • x - b • y) (b • x + a • y)).unique
  have h := isLUB_smul_of_nonneg (Real.sqrt_nonneg (a ^ 2 + b ^ 2))
    (complexModulus_isLUB x y)
  rw [← rotationRange_linear_transform] at h
  exact h

/-- The norm of either component is bounded by the norm of the complex modulus. -/
theorem norm_le_norm_complexModulus_left (x y : E) :
    ‖x‖ ≤ ‖complexModulus x y‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (complexModulus_nonneg x y)]
  exact abs_le_complexModulus_left x y

/-- The norm of either component is bounded by the norm of the complex modulus. -/
theorem norm_le_norm_complexModulus_right (x y : E) :
    ‖y‖ ≤ ‖complexModulus x y‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (complexModulus_nonneg x y)]
  exact abs_le_complexModulus_right x y

/-- The norm of the complex modulus is bounded by the sum of the component norms. -/
theorem norm_complexModulus_le_add_norm (x y : E) :
    ‖complexModulus x y‖ ≤ ‖x‖ + ‖y‖ := by
  calc
    ‖complexModulus x y‖ ≤ ‖|x| + |y|‖ := norm_le_norm_of_abs_le_abs (by
      rw [abs_of_nonneg (complexModulus_nonneg x y),
        abs_of_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg y))]
      exact complexModulus_le_abs_add_abs x y)
    _ ≤ ‖|x|‖ + ‖|y|‖ := norm_add_le _ _
    _ = ‖x‖ + ‖y‖ := by rw [norm_abs_eq_norm, norm_abs_eq_norm]

end BanachLattice

namespace VecLatEquiv

variable {E F : Type*}
  [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [BanachLattice F]

/-- A vector lattice equivalence preserves the complex modulus. -/
@[simp]
theorem map_complexModulus (e : VecLatEquiv E F) (x y : E) :
    e (BanachLattice.complexModulus x y) =
      BanachLattice.complexModulus (e x) (e y) := by
  symm
  apply (BanachLattice.complexModulus_isLUB (e x) (e y)).unique
  constructor
  · rintro _ ⟨θ, rfl⟩
    change Real.cos θ • e.toLinearEquiv x + Real.sin θ • e.toLinearEquiv y ≤
      e.toLinearEquiv (BanachLattice.complexModulus x y)
    rw [← map_smul, ← map_smul, ← map_add]
    exact e.toVecLatHom.monotone
      ((BanachLattice.complexModulus_isLUB x y).1 ⟨θ, rfl⟩)
  · intro u hu
    rw [← e.toLinearEquiv.apply_symm_apply u]
    apply e.toVecLatHom.monotone
    apply (BanachLattice.complexModulus_isLUB x y).2
    rintro _ ⟨θ, rfl⟩
    apply e.toVecLatHom.le_of_map_le e.toLinearEquiv.injective
    change e.toLinearEquiv (Real.cos θ • x + Real.sin θ • y) ≤
      e.toLinearEquiv (e.toLinearEquiv.symm u)
    rw [map_add, map_smul, map_smul, e.toLinearEquiv.apply_symm_apply]
    exact hu ⟨θ, rfl⟩

end VecLatEquiv

/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Functional.Basic

/-!
# Measure algebras

This file introduces **measure algebras** `(B, μ)`, where `B` is a `σ`-order complete
Boolean algebra and `μ : B → [0, ∞]` is a function, satisfying that:
* `μ(b) = 0 ↔ b = ⊥`
* `μ(⊤) < ∞`.
* `μ(∨ b i) = ∑ μ(b i)` for every pairwise disjoint sequence `b i` in `B`.

It also proves that on every `σ`-complete Boolean subalgebra `A`, the maps `• ↦ μ(• ⊓ b)`
define countably additive functionals.

Lastly, it introduces **equivalences of measure algebras** as order isomorphisms that preserve
the measure.
-/

open Function
open scoped ENNReal symmDiff

universe u v

/-- A measure algebra on `B` is a finite faithful countably additive functional
on a `σ`-complete Boolean algebra. -/
structure MeasureAlgebra (B : Type u) [SigmaCompleteBooleanAlgebra B]
    extends CountablyAdditiveFunctional B where
  /-- The total measure is finite. -/
  isFinite : toCountablyAdditiveFunctional.IsFinite
  /-- The measure vanishes exactly at the bottom element. -/
  isFaithful : toCountablyAdditiveFunctional.IsFaithful

instance {B : Type u} [SigmaCompleteBooleanAlgebra B] :
    CoeFun (MeasureAlgebra B) (fun _ ↦ B → ℝ≥0∞) :=
  ⟨fun μ ↦ μ.toCountablyAdditiveFunctional⟩

namespace CountablyAdditiveFunctional

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- A countably additive functional `ν` that vanishes only at the bottom
element and satisfies `ν ⊤ < ∞` defines a measure algebra. -/
def toMeasureAlgebra (ν : CountablyAdditiveFunctional B) (hν : ν.IsFinite)
    (hν_faith : ν.IsFaithful) : MeasureAlgebra B where
  toCountablyAdditiveFunctional := ν
  isFinite := hν
  isFaithful := hν_faith

@[simp]
theorem toMeasureAlgebra_apply (ν : CountablyAdditiveFunctional B) (hν : ν.IsFinite)
    (hν_faith : ν.IsFaithful) (b : B) :
    ν.toMeasureAlgebra hν hν_faith b = ν b := by
  rfl

@[simp]
theorem toMeasureAlgebra_toCountablyAdditiveFunctional
    (ν : CountablyAdditiveFunctional B) (hν : ν.IsFinite)
    (hν_faith : ν.IsFaithful) :
    (ν.toMeasureAlgebra hν hν_faith).toCountablyAdditiveFunctional = ν := by
  rfl

end CountablyAdditiveFunctional

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]
variable (μ : MeasureAlgebra B)

/-- The measure vanishes exactly at the bottom element. -/
theorem measure_eq_zero_iff (b : B) : μ b = 0 ↔ b = ⊥ := by
  exact μ.isFaithful b

/-- The total measure is finite. -/
theorem m_top_ne_top : μ ⊤ ≠ ∞ := by
  exact μ.isFinite

/-- The bottom element has measure zero. -/
@[simp]
theorem measure_bot : μ ⊥ = 0 := by
  exact μ.toCountablyAdditiveFunctional.map_bot

/-- The measure is countably additive on pairwise disjoint sequences. -/
theorem measure_iSup {b : ℕ → B} (hb : Pairwise (Disjoint on b)) :
    μ (⨆ i, b i) = ∑' i, μ (b i) := by
  exact μ.toCountablyAdditiveFunctional.map_iSup hb

@[simp]
theorem toCountablyAdditiveFunctional_apply (b : B) :
    μ.toCountablyAdditiveFunctional b = μ b := by
  rfl

@[simp]
theorem toCountablyAdditiveFunctional_toMeasureAlgebra :
    μ.toCountablyAdditiveFunctional.toMeasureAlgebra μ.isFinite μ.isFaithful = μ := by
  cases μ
  rfl

/-- Measure algebras are exactly countably additive functionals which are
finite and vanish only at the bottom element. -/
def equivFiniteFaithfulFunctional :
    MeasureAlgebra B ≃
      {ν : CountablyAdditiveFunctional B //
        ν.IsFinite ∧ ν.IsFaithful} where
  toFun μ := ⟨μ.toCountablyAdditiveFunctional, μ.isFinite, μ.isFaithful⟩
  invFun ν := ν.1.toMeasureAlgebra ν.2.1 ν.2.2
  left_inv μ := μ.toCountablyAdditiveFunctional_toMeasureAlgebra
  right_inv ν := Subtype.ext <| ν.1.toMeasureAlgebra_toCountablyAdditiveFunctional ν.2.1 ν.2.2

/-- The measure is additive on disjoint elements. -/
theorem measure_sup {b c : B} (h : Disjoint b c) :
    μ (b ⊔ c) = μ b + μ c := by
  exact μ.toCountablyAdditiveFunctional.map_sup h

/-- The measure of the supremum of a finite pairwise disjoint family is the
sum of the measures. -/
theorem measure_finset_sup (s : Finset B)
    (hs : (s : Set B).PairwiseDisjoint id) :
    μ (s.sup id) = ∑ b ∈ s, μ b := by
  exact μ.toCountablyAdditiveFunctional.map_finset_sup s hs

/-- An element is the disjoint supremum of its difference and intersection
with another element. -/
theorem measure_sdiff_add_inf (b c : B) :
    μ (b \ c) + μ (b ⊓ c) = μ b := by
  exact μ.toCountablyAdditiveFunctional.map_sdiff_add_inf b c

/-- For all `b, c` in a measure algebra,
`μ (b ∆ c) = μ (b \ c) + μ (c \ b)`. -/
theorem measure_symmDiff (b c : B) :
    μ (b ∆ c) = μ (b \ c) + μ (c \ b) := by
  exact μ.toCountablyAdditiveFunctional.map_symmDiff b c

/-- The measure of a measure algebra is monotone. -/
@[gcongr]
theorem measure_mono {b c : B} (hbc : b ≤ c) : μ b ≤ μ c := by
  exact μ.toCountablyAdditiveFunctional.monotone hbc

/-- The measure of every element is finite. -/
@[simp]
theorem measure_ne_top (b : B) : μ b ≠ ∞ := by
  exact μ.toCountablyAdditiveFunctional.ne_top μ.isFinite b

/-- The measure of a measure algebra is strictly monotone. -/
theorem measure_strictMono : StrictMono μ := by
  exact μ.toCountablyAdditiveFunctional.strictMono μ.isFinite μ.isFaithful

/-- The measure of a supremum is at most the sum of the measures. -/
theorem measure_sup_le (b c : B) : μ (b ⊔ c) ≤ μ b + μ c := by
  exact μ.toCountablyAdditiveFunctional.map_sup_le b c

/-- The measure of a measure algebra is a valuation. -/
theorem measure_sup_add_inf (b c : B) :
    μ (b ⊔ c) + μ (b ⊓ c) = μ b + μ c := by
  exact μ.toCountablyAdditiveFunctional.map_sup_add_inf b c

/-- The measures of an element and its complement add up to the total measure. -/
theorem measure_add_measure_compl (b : B) :
    μ b + μ bᶜ = μ ⊤ := by
  exact μ.toCountablyAdditiveFunctional.map_add_map_compl b

/-- The measure of a countable supremum is at most the sum of the measures. -/
theorem measure_iSup_le (b : ℕ → B) :
    μ (⨆ i, b i) ≤ ∑' i, μ (b i) := by
  exact μ.toCountablyAdditiveFunctional.map_iSup_le b

/-- The measure of the supremum of an increasing sequence is the supremum
of its measures. -/
theorem measure_iSup_eq_iSup {b : ℕ → B} (hb : Monotone b) :
    μ (⨆ i, b i) = ⨆ i, μ (b i) := by
  exact μ.toCountablyAdditiveFunctional.map_iSup_eq_iSup hb

/-- For `b ∈ B`, `μ.restrict b` is the measure algebra on the principal interval
`Set.Iic b = {c ∈ B | c ≤ b}` given by `(μ.restrict b) c = μ c`. -/
noncomputable def restrict (b : B) : MeasureAlgebra (Set.Iic b) :=
  (μ.toCountablyAdditiveFunctional.restrict b).toMeasureAlgebra
    (μ.toCountablyAdditiveFunctional.restrict_isFinite b (μ.measure_ne_top b))
    (μ.toCountablyAdditiveFunctional.restrict_isFaithful b μ.isFaithful)

/-- On every `σ`-complete Boolean subalgebra `A`, for any fixed `b ∈ B`, the map
`• ↦ μ(• ⊓ b)` defines a countably additive functional. -/
noncomputable def infFunctional (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) (b : B) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    CountablyAdditiveFunctional A := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  exact μ.toCountablyAdditiveFunctional.infFunctional A hA b

/-- The functional `• ↦ μ(• ⊓ b)` evaluates `a` as `μ (a ⊓ b)`. -/
@[simp]
theorem infFunctional_apply (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) (b : B) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    μ.infFunctional A hA b a = μ ((a : B) ⊓ b) := by
  exact μ.toCountablyAdditiveFunctional.infFunctional_apply A hA b a

/-- The functional `• ↦ μ(• ⊓ b)` is dominated by the restriction of the
ambient measure. -/
theorem infFunctional_le (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) (b : B) (a : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    μ.infFunctional A hA b a ≤ μ (a : B) := by
  exact μ.toCountablyAdditiveFunctional.infFunctional_le A hA b a

end MeasureAlgebra

/-- An **equivalence of measure algebras** is an order isomorphism that preserves the measure. -/
structure MeasureAlgebraEquiv
    {B : Type u} {C : Type v}
    [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (ν : MeasureAlgebra C)
    extends B ≃o C where
  /-- The order isomorphism preserves the measure. -/
  map_measure' (b : B) : ν (toFun b) = μ b

namespace MeasureAlgebraEquiv

variable {B : Type u} {C : Type v}
variable [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
variable {μ : MeasureAlgebra B} {ν : MeasureAlgebra C}

instance : CoeFun (MeasureAlgebraEquiv μ ν) (fun _ ↦ B → C) := by
  exact ⟨fun e ↦ e.toFun⟩

/-- A measure-algebra equivalence preserves the measure. -/
@[simp]
theorem map_measure (e : MeasureAlgebraEquiv μ ν) (b : B) :
    ν (e.toRelIso b) = μ b := by
  exact e.map_measure' b

/-- The inverse of a measure-algebra equivalence. -/
def symm (e : MeasureAlgebraEquiv μ ν) : MeasureAlgebraEquiv ν μ where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_rel_iff' := e.toRelIso.symm.map_rel_iff
  map_measure' b := by
    simpa using (e.map_measure (e.invFun b)).symm

/-- For `b ∈ B`, a measure-algebra equivalence `e : (B, μ) ≃ (C, ν)` restricts
to a measure-algebra equivalence between the principal intervals below `b`
and `e b`. -/
noncomputable def restrict (e : MeasureAlgebraEquiv μ ν) (b : B) :
    MeasureAlgebraEquiv (μ.restrict b) (ν.restrict (e.toRelIso b)) := by
  refine
    { toFun := fun c ↦ ⟨e c, e.toRelIso.map_rel_iff.mpr c.property⟩
      invFun := fun d ↦
        ⟨e.toRelIso.symm d, by simpa using e.toRelIso.symm.map_rel_iff.mpr d.property⟩
      left_inv := fun c ↦ Subtype.ext (e.toRelIso.left_inv c)
      right_inv := fun d ↦ Subtype.ext (e.toRelIso.right_inv d)
      map_rel_iff' := e.toRelIso.map_rel_iff
      map_measure' := fun c ↦ e.map_measure c }

/-- The restriction of `e` to the principal interval below `b` sends
`c ∈ Set.Iic b` to `e c ∈ Set.Iic (e b)`. -/
@[simp]
theorem restrict_apply (e : MeasureAlgebraEquiv μ ν) (b : B)
    (c : Set.Iic b) :
    (((e.restrict b).toRelIso c : Set.Iic (e.toRelIso b)) : C) = e (c : B) := by
  rfl

end MeasureAlgebraEquiv

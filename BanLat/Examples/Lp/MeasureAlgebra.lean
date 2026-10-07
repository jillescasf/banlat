/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.OfMeasure
import BanLat.Examples.Lp.Basic
import BanLat.Operators.Hom
import Mathlib.MeasureTheory.Integral.FinMeasAdditive

/-!
# Measure algebra equivalences and the associated `L^p` spaces

Let `1 ≤ p < +∞`. An equivalence between the measure algebras of two finite
measure spaces induces a Banach lattice equivalence between their real `L^p`
spaces.

The equivalence is first constructed on the dense subspaces
represented by simple functions and then extended to the full `L^p` spaces.
-/

open MeasureTheory
open scoped ENNReal NNReal symmDiff

universe u v

namespace MeasureAlgebraEquiv

variable {α : Type u} {β : Type v}
variable [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable {p : ℝ≥0} [Fact (1 ≤ p)]

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module
  Lp.simpleFunc.normedSpace Lp.simpleFunc.isBoundedSMul

/-- Every image of a measurable set under a measure-algebra equivalence has a
measurable representative. -/
private theorem exists_image_measuredSet
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (s : MeasuredSets μ) :
    ∃ t : MeasuredSets ν,
      e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) =
        MeasureAlgebra.InducedBooleanAlgebra.mk ν t := by
  obtain ⟨t, ht⟩ := MeasureAlgebra.InducedBooleanAlgebra.mk_surjective ν
    (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s))
  exact ⟨t, ht.symm⟩

/-- A chosen measurable representative of an element of an induced measure algebra. -/
private noncomputable def representative (q : MeasureAlgebra.InducedBooleanAlgebra μ) :
    MeasuredSets μ :=
  Classical.choose (MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ q)

omit [IsFiniteMeasure μ] in
@[simp]
private theorem mk_representative (q : MeasureAlgebra.InducedBooleanAlgebra μ) :
    MeasureAlgebra.InducedBooleanAlgebra.mk μ (representative q) = q :=
  Classical.choose_spec (MeasureAlgebra.InducedBooleanAlgebra.mk_surjective μ q)

/-- The characteristic function associated with a measure-algebra element. -/
private noncomputable def indicatorOfClass
    (q : MeasureAlgebra.InducedBooleanAlgebra μ) :
    Lp.simpleFunc ℝ (p : ENNReal) μ :=
  Lp.simpleFunc.indicatorConst (p : ENNReal) (representative q).property
    (measure_ne_top μ _) 1

omit [Fact (1 ≤ p)] in
private theorem indicatorOfClass_eq_indicatorConst
    (q : MeasureAlgebra.InducedBooleanAlgebra μ) (s : MeasuredSets μ)
    (hs : MeasureAlgebra.InducedBooleanAlgebra.mk μ s = q) :
    indicatorOfClass (p := p) q =
      Lp.simpleFunc.indicatorConst (p : ENNReal) s.property (measure_ne_top μ _) 1 := by
  apply Subtype.ext
  change indicatorConstLp (p : ENNReal) (representative q).property
      (measure_ne_top μ _) 1 =
    indicatorConstLp (p : ENNReal) s.property (measure_ne_top μ _) 1
  apply (indicatorConstLp_inj (p := (p : ENNReal))
    (representative q).property (measure_ne_top μ _)
    s.property (measure_ne_top μ _) (by norm_num : (1 : ℝ) ≠ 0)).2
  apply measure_symmDiff_eq_zero_iff.mp
  exact (MeasureAlgebra.InducedBooleanAlgebra.mk_eq_mk μ _ _).mp
    ((mk_representative q).trans hs.symm)

omit [Fact (1 ≤ p)] in
private theorem indicatorOfClass_sup_of_disjoint
    {q r : MeasureAlgebra.InducedBooleanAlgebra μ} (hqr : Disjoint q r) :
    indicatorOfClass (p := p) (q ⊔ r) =
      indicatorOfClass (p := p) q + indicatorOfClass (p := p) r := by
  let s := representative q
  let t := representative r \ s
  have hs : MeasureAlgebra.InducedBooleanAlgebra.mk μ s = q := mk_representative q
  have ht : MeasureAlgebra.InducedBooleanAlgebra.mk μ t = r := by
    change MeasureAlgebra.InducedBooleanAlgebra.mk μ (representative r \ representative q) = r
    rw [MeasureAlgebra.InducedBooleanAlgebra.mk_sdiff, mk_representative,
      mk_representative, hqr.symm.sdiff_eq_left]
  rw [indicatorOfClass_eq_indicatorConst (p := p) q s hs,
    indicatorOfClass_eq_indicatorConst (p := p) r t ht,
    indicatorOfClass_eq_indicatorConst (p := p) (q ⊔ r) (s ⊔ t)]
  · apply Subtype.ext
    exact indicatorConstLp_disjoint_union (p := (p : ENNReal)) s.property t.property
      (measure_ne_top μ _) (measure_ne_top μ _) disjoint_sdiff_self_right 1
  · rw [MeasureAlgebra.InducedBooleanAlgebra.mk_sup, hs, ht]

omit [Fact (1 ≤ p)] in
private theorem indicatorOfClass_isVLDisjoint
    {q r : MeasureAlgebra.InducedBooleanAlgebra μ} (hqr : Disjoint q r) :
    IsVLDisjoint
      (indicatorOfClass (p := p) q : Lp ℝ (p : ENNReal) μ)
      (indicatorOfClass (p := p) r : Lp ℝ (p : ENNReal) μ) := by
  let s := representative q
  let t := representative r \ s
  have hs : MeasureAlgebra.InducedBooleanAlgebra.mk μ s = q := mk_representative q
  have ht : MeasureAlgebra.InducedBooleanAlgebra.mk μ t = r := by
    change MeasureAlgebra.InducedBooleanAlgebra.mk μ (representative r \ representative q) = r
    rw [MeasureAlgebra.InducedBooleanAlgebra.mk_sdiff, mk_representative,
      mk_representative, hqr.symm.sdiff_eq_left]
  rw [indicatorOfClass_eq_indicatorConst (p := p) q s hs,
    indicatorOfClass_eq_indicatorConst (p := p) r t ht,
    Lp.simpleFunc.coe_indicatorConst, Lp.simpleFunc.coe_indicatorConst]
  exact Lp.indicatorConstLp_isVLDisjoint s.property t.property
    (measure_ne_top μ _) (measure_ne_top μ _) disjoint_sdiff_self_right 1 1

private theorem norm_indicatorOfClass_image
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (s : MeasuredSets μ) :
    ‖indicatorOfClass (p := p)
        (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s))‖ =
      ‖Lp.simpleFunc.indicatorConst (p : ENNReal) s.property
        (measure_ne_top μ _) (1 : ℝ)‖ := by
  have hmeasure : ν (representative
      (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s)) : Set β) = μ (s : Set α) := by
    calc
      ν (representative (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s)) : Set β) =
          MeasureAlgebra.ofMeasure ν
            (MeasureAlgebra.InducedBooleanAlgebra.mk ν
              (representative (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s)))) :=
        (MeasureAlgebra.ofMeasure_mk ν _).symm
      _ = MeasureAlgebra.ofMeasure μ
          (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) := by
        rw [mk_representative]
        exact e.map_measure' _
      _ = μ (s : Set α) := MeasureAlgebra.ofMeasure_mk μ s
  have hreal := congrArg ENNReal.toReal hmeasure
  change ‖indicatorConstLp (p : ENNReal)
      (representative (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s))).property
      (measure_ne_top ν _) (1 : ℝ)‖ =
    ‖indicatorConstLp (p : ENNReal) s.property (measure_ne_top μ _) (1 : ℝ)‖
  rw [norm_indicatorConstLp (by simp [ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)])
      (by simp),
    norm_indicatorConstLp (by simp [ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)])
      (by simp)]
  change ‖(1 : ℝ)‖ *
      (ν (representative (e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s)) : Set β)).toReal ^
        (1 / (p : ENNReal).toReal) =
    ‖(1 : ℝ)‖ * (μ (s : Set α)).toReal ^ (1 / (p : ENNReal).toReal)
  rw [hreal]

private noncomputable def classOfSet (μ : Measure α) (s : Set α) :
    MeasureAlgebra.InducedBooleanAlgebra μ :=
  MeasureAlgebra.InducedBooleanAlgebra.mk μ
    ⟨toMeasurable μ s, measurableSet_toMeasurable μ s⟩

omit [IsFiniteMeasure μ] in
private theorem classOfSet_eq_mk {s : Set α} (hs : MeasurableSet s) :
    classOfSet μ s = MeasureAlgebra.InducedBooleanAlgebra.mk μ ⟨s, hs⟩ := by
  apply (MeasureAlgebra.InducedBooleanAlgebra.mk_eq_mk μ _ _).2
  apply measure_symmDiff_eq_zero_iff.mpr
  exact hs.nullMeasurableSet.toMeasurable_ae_eq

omit [IsFiniteMeasure μ] in
private theorem classOfSet_eq_bot {s : Set α} (hs : MeasurableSet s) (hμs : μ s = 0) :
    classOfSet μ s = ⊥ := by
  rw [classOfSet_eq_mk hs, ← MeasureAlgebra.InducedBooleanAlgebra.mk_bot]
  apply (MeasureAlgebra.InducedBooleanAlgebra.mk_eq_mk μ _ _).2
  change μ (s ∆ ∅) = 0
  rw [show (∅ : Set α) = ⊥ from rfl, symmDiff_bot]
  exact hμs

omit [IsFiniteMeasure μ] in
private theorem classOfSet_disjoint {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : Disjoint s t) :
    Disjoint (classOfSet μ s) (classOfSet μ t) := by
  let sm : MeasuredSets μ := ⟨s, hs⟩
  let tm : MeasuredSets μ := ⟨t, ht⟩
  rw [classOfSet_eq_mk hs, classOfSet_eq_mk ht, disjoint_iff,
    ← MeasureAlgebra.InducedBooleanAlgebra.mk_inf]
  have hst' : sm ⊓ tm = ⊥ := by
    apply Subtype.ext
    exact hst.eq_bot
  rw [hst', MeasureAlgebra.InducedBooleanAlgebra.mk_bot]

omit [Fact (1 ≤ p)] in
@[simp]
private theorem indicatorOfClass_bot :
    indicatorOfClass (p := p) (⊥ : MeasureAlgebra.InducedBooleanAlgebra μ) = 0 := by
  rw [indicatorOfClass_eq_indicatorConst (p := p) ⊥ (⊥ : MeasuredSets μ)
    (MeasureAlgebra.InducedBooleanAlgebra.mk_bot μ)]
  apply Subtype.ext
  exact indicatorConstLp_empty

private noncomputable def indicatorOperator
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (s : Set α) : ℝ →L[ℝ] Lp.simpleFunc ℝ (p : ENNReal) ν :=
  ContinuousLinearMap.toSpanSingleton ℝ
    (indicatorOfClass (p := p) (e (classOfSet μ s)))

private theorem indicatorOperator_isVLDisjoint
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) (c d : ℝ) :
    IsVLDisjoint
      (indicatorOperator (p := p) e s c : Lp ℝ (p : ENNReal) ν)
      (indicatorOperator (p := p) e t d : Lp ℝ (p : ENNReal) ν) := by
  have hsource := classOfSet_disjoint (μ := μ) hs ht hst
  have htarget : Disjoint (e (classOfSet μ s)) (e (classOfSet μ t)) := by
    apply disjoint_iff.mpr
    change e.toRelIso (classOfSet μ s) ⊓ e.toRelIso (classOfSet μ t) = ⊥
    rw [← map_inf e.toRelIso, hsource.eq_bot, map_bot e.toRelIso]
  simpa [indicatorOperator, ContinuousLinearMap.toSpanSingleton_apply,
    Lp.simpleFunc.coe_smul] using
    ((indicatorOfClass_isVLDisjoint (p := p) htarget).smul_left c).smul_right d

private theorem indicatorOperator_finMeasAdditive
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν)) :
    FinMeasAdditive μ (indicatorOperator (p := p) e) := by
  intro s t hs ht _ _ hst
  let sm : MeasuredSets μ := ⟨s, hs⟩
  let tm : MeasuredSets μ := ⟨t, ht⟩
  have hclass : classOfSet μ (s ∪ t) = classOfSet μ s ⊔ classOfSet μ t := by
    rw [classOfSet_eq_mk (hs.union ht), classOfSet_eq_mk hs, classOfSet_eq_mk ht]
    change MeasureAlgebra.InducedBooleanAlgebra.mk μ (sm ⊔ tm) =
      MeasureAlgebra.InducedBooleanAlgebra.mk μ sm ⊔
        MeasureAlgebra.InducedBooleanAlgebra.mk μ tm
    exact MeasureAlgebra.InducedBooleanAlgebra.mk_sup μ sm tm
  have hsource : Disjoint (classOfSet μ s) (classOfSet μ t) := by
    rw [classOfSet_eq_mk hs, classOfSet_eq_mk ht, disjoint_iff,
      ← MeasureAlgebra.InducedBooleanAlgebra.mk_inf]
    have hst' : sm ⊓ tm = ⊥ := by
      apply Subtype.ext
      exact hst.eq_bot
    rw [hst', MeasureAlgebra.InducedBooleanAlgebra.mk_bot]
  have hdisj : Disjoint (e (classOfSet μ s)) (e (classOfSet μ t)) := by
    apply disjoint_iff.mpr
    change e.toRelIso (classOfSet μ s) ⊓ e.toRelIso (classOfSet μ t) = ⊥
    rw [← map_inf e.toRelIso, hsource.eq_bot, map_bot e.toRelIso]
  have he_sup : e (classOfSet μ s ⊔ classOfSet μ t) =
      e (classOfSet μ s) ⊔ e (classOfSet μ t) := by
    change e.toRelIso (classOfSet μ s ⊔ classOfSet μ t) =
      e.toRelIso (classOfSet μ s) ⊔ e.toRelIso (classOfSet μ t)
    exact map_sup e.toRelIso _ _
  apply ContinuousLinearMap.ext
  intro c
  simp only [indicatorOperator, ContinuousLinearMap.toSpanSingleton_apply]
  rw [hclass, he_sup, indicatorOfClass_sup_of_disjoint (p := p) hdisj,
    smul_add]
  rfl

private theorem indicatorOperator_eq_zero_of_measure_zero
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s = 0) :
    indicatorOperator (p := p) e s = 0 := by
  apply ContinuousLinearMap.ext
  intro c
  simp [indicatorOperator, classOfSet_eq_bot hs hμs]

private noncomputable def transportSimple
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    Lp.simpleFunc ℝ (p : ENNReal) ν :=
  (Lp.simpleFunc.toSimpleFunc f).setToSimpleFunc (indicatorOperator (p := p) e)

private theorem transportSimple_add
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f g : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    transportSimple e (f + g) = transportSimple e f + transportSimple e g := by
  have hp_one : (1 : ENNReal) ≤ (p : ENNReal) := by exact_mod_cast (Fact.out : (1 : ℝ≥0) ≤ p)
  have hf := (Lp.simpleFunc.memLp f).integrable hp_one
  have hg := (Lp.simpleFunc.memLp g).integrable hp_one
  have hfg := (Lp.simpleFunc.memLp (f + g)).integrable hp_one
  unfold transportSimple
  rw [SimpleFunc.setToSimpleFunc_congr (indicatorOperator (p := p) e)
    (fun s hs hμs ↦ indicatorOperator_eq_zero_of_measure_zero (p := p) e hs hμs)
    (indicatorOperator_finMeasAdditive (p := p) e) hfg
    (g := Lp.simpleFunc.toSimpleFunc f + Lp.simpleFunc.toSimpleFunc g)
    (Lp.simpleFunc.add_toSimpleFunc f g)]
  exact SimpleFunc.setToSimpleFunc_add _
    (indicatorOperator_finMeasAdditive (p := p) e) hf hg

private theorem transportSimple_smul
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (c : ℝ) (f : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    transportSimple e (c • f) = c • transportSimple e f := by
  have hp_one : (1 : ENNReal) ≤ (p : ENNReal) := by exact_mod_cast (Fact.out : (1 : ℝ≥0) ≤ p)
  have hf := (Lp.simpleFunc.memLp f).integrable hp_one
  have hcf := (Lp.simpleFunc.memLp (c • f)).integrable hp_one
  unfold transportSimple
  rw [SimpleFunc.setToSimpleFunc_congr (indicatorOperator (p := p) e)
    (fun s hs hμs ↦ indicatorOperator_eq_zero_of_measure_zero (p := p) e hs hμs)
    (indicatorOperator_finMeasAdditive (p := p) e) hcf
    (g := c • Lp.simpleFunc.toSimpleFunc f)
    (Lp.simpleFunc.smul_toSimpleFunc c f)]
  exact SimpleFunc.setToSimpleFunc_smul_real _
    (indicatorOperator_finMeasAdditive (p := p) e) c hf

private noncomputable def transportSimpleLinearMap
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν)) :
    Lp.simpleFunc ℝ (p : ENNReal) μ →ₗ[ℝ]
      Lp.simpleFunc ℝ (p : ENNReal) ν where
  toFun := transportSimple e
  map_add' := transportSimple_add e
  map_smul' := transportSimple_smul e

private theorem transportSimple_indicatorConst
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (s : MeasuredSets μ) (t : MeasuredSets ν)
    (hst : e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) =
      MeasureAlgebra.InducedBooleanAlgebra.mk ν t) (c : ℝ) :
    transportSimple e
        (Lp.simpleFunc.indicatorConst (p : ENNReal) s.property
          (measure_ne_top μ _) c) =
      Lp.simpleFunc.indicatorConst (p : ENNReal) t.property
        (measure_ne_top ν _) c := by
  rcases s with ⟨s, hs⟩
  rcases t with ⟨t, ht⟩
  have hp_one : (1 : ENNReal) ≤ (p : ENNReal) := by exact_mod_cast (Fact.out : (1 : ℝ≥0) ≤ p)
  let f := Lp.simpleFunc.indicatorConst (p : ENNReal) hs
    (measure_ne_top μ _) c
  have hf := (Lp.simpleFunc.memLp f).integrable hp_one
  have hempty : indicatorOperator (p := p) e ∅ = 0 :=
    (indicatorOperator_finMeasAdditive (p := p) e).map_empty_eq_zero
  unfold transportSimple
  rw [SimpleFunc.setToSimpleFunc_congr (indicatorOperator (p := p) e)
    (fun u hu hμu ↦ indicatorOperator_eq_zero_of_measure_zero (p := p) e hu hμu)
    (indicatorOperator_finMeasAdditive (p := p) e) hf
    (g := (SimpleFunc.const α c).piecewise s hs (SimpleFunc.const α 0))
    (Lp.simpleFunc.toSimpleFunc_indicatorConst hs (measure_ne_top μ _) c),
    SimpleFunc.setToSimpleFunc_indicator _ hempty hs c]
  simp only [indicatorOperator, ContinuousLinearMap.toSpanSingleton_apply]
  rw [Lp.simpleFunc.indicatorConst_eq_smul ht (measure_ne_top ν _) c]
  congr 1
  apply indicatorOfClass_eq_indicatorConst (p := p)
    (e (classOfSet μ s)) (⟨t, ht⟩ : MeasuredSets ν)
  rw [classOfSet_eq_mk hs, hst]

private theorem transportSimple_inverse_comp
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    transportSimple e.symm (transportSimple e f) = f := by
  refine Lp.simpleFunc.induction (α := α) (E := ℝ)
    (show (p : ENNReal) ≠ 0 by simp [ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)])
    (by simp) (P := fun f ↦ transportSimple e.symm (transportSimple e f) = f) ?_ ?_ f
  · intro c s hs _
    let sm : MeasuredSets μ := ⟨s, hs⟩
    obtain ⟨t, ht⟩ := exists_image_measuredSet e sm
    rw [transportSimple_indicatorConst (p := p) e sm t ht c,
      transportSimple_indicatorConst (p := p) e.symm t sm]
    change e.invFun (MeasureAlgebra.InducedBooleanAlgebra.mk ν t) =
      MeasureAlgebra.InducedBooleanAlgebra.mk μ sm
    rw [← ht]
    exact e.left_inv _
  · intro f g _ _ _ hf hg
    rw [transportSimple_add, transportSimple_add, hf, hg]

private theorem transportSimple_comp_inverse
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp.simpleFunc ℝ (p : ENNReal) ν) :
    transportSimple e (transportSimple e.symm f) = f := by
  refine Lp.simpleFunc.induction (α := β) (E := ℝ)
    (show (p : ENNReal) ≠ 0 by simp [ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)])
    (by simp) (P := fun f ↦ transportSimple e (transportSimple e.symm f) = f) ?_ ?_ f
  · intro c t ht _
    let tm : MeasuredSets ν := ⟨t, ht⟩
    obtain ⟨s, hs⟩ := exists_image_measuredSet e.symm tm
    rw [transportSimple_indicatorConst (p := p) e.symm tm s hs c,
      transportSimple_indicatorConst (p := p) e s tm]
    rw [← hs]
    exact e.right_inv _
  · intro f g _ _ _ hf hg
    rw [transportSimple_add, transportSimple_add, hf, hg]

private theorem transportSimple_isVLDisjoint
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    {f g : SimpleFunc α ℝ} (hf : MemLp f (p : ENNReal) μ)
    (hg : MemLp g (p : ENNReal) μ) (hfg : Disjoint (Function.support f) (Function.support g)) :
    IsVLDisjoint
      (transportSimple e (SimpleFunc.toLp f hf) : Lp ℝ (p : ENNReal) ν)
      (transportSimple e (SimpleFunc.toLp g hg) : Lp ℝ (p : ENNReal) ν) := by
  have hp_one : (1 : ENNReal) ≤ (p : ENNReal) := by exact_mod_cast (Fact.out : (1 : ℝ≥0) ≤ p)
  have hfi := hf.integrable hp_one
  have hgi := hg.integrable hp_one
  have hTf : transportSimple e (SimpleFunc.toLp f hf) =
      f.setToSimpleFunc (indicatorOperator (p := p) e) := by
    unfold transportSimple
    apply SimpleFunc.setToSimpleFunc_congr (indicatorOperator (p := p) e)
      (fun s hs hμs ↦ indicatorOperator_eq_zero_of_measure_zero (p := p) e hs hμs)
      (indicatorOperator_finMeasAdditive (p := p) e)
      ((Lp.simpleFunc.memLp (SimpleFunc.toLp f hf)).integrable hp_one)
    exact Lp.simpleFunc.toSimpleFunc_toLp f hf
  have hTg : transportSimple e (SimpleFunc.toLp g hg) =
      g.setToSimpleFunc (indicatorOperator (p := p) e) := by
    unfold transportSimple
    apply SimpleFunc.setToSimpleFunc_congr (indicatorOperator (p := p) e)
      (fun s hs hμs ↦ indicatorOperator_eq_zero_of_measure_zero (p := p) e hs hμs)
      (indicatorOperator_finMeasAdditive (p := p) e)
      ((Lp.simpleFunc.memLp (SimpleFunc.toLp g hg)).integrable hp_one)
    exact Lp.simpleFunc.toSimpleFunc_toLp g hg
  rw [hTf, hTg]
  simp only [SimpleFunc.setToSimpleFunc]
  push_cast
  apply isVLDisjoint_finset_sum_finset f.range g.range
    (fun c ↦ (indicatorOperator (p := p) e (f ⁻¹' {c}) c :
      Lp ℝ (p : ENNReal) ν))
    (fun d ↦ (indicatorOperator (p := p) e (g ⁻¹' {d}) d :
      Lp ℝ (p : ENNReal) ν))
  intro c _ d _
  by_cases hc : c = 0
  · subst c
    simpa only [map_zero, AddSubgroup.coe_zero] using isVLDisjoint_zero_left
      (indicatorOperator (p := p) e (g ⁻¹' {d}) d : Lp ℝ (p : ENNReal) ν)
  by_cases hd : d = 0
  · subst d
    simpa only [map_zero, AddSubgroup.coe_zero] using isVLDisjoint_zero_right
      (indicatorOperator (p := p) e (f ⁻¹' {c}) c : Lp ℝ (p : ENNReal) ν)
  apply indicatorOperator_isVLDisjoint (p := p) e
    (f.measurableSet_fiber c) (g.measurableSet_fiber d)
  apply Set.disjoint_left.2
  intro x hfx hgx
  exact Set.disjoint_left.1 hfg
    (by
      change f x ≠ 0
      change f x = c at hfx
      rw [hfx]
      exact hc)
    (by
      change g x ≠ 0
      change g x = d at hgx
      rw [hgx]
      exact hd)

private theorem transportSimple_norm
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (f : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    ‖transportSimple e f‖ = ‖f‖ := by
  refine Lp.simpleFunc.induction (α := α) (E := ℝ)
    (show (p : ENNReal) ≠ 0 by simp [ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)])
    (by simp) (P := fun f ↦ ‖transportSimple e f‖ = ‖f‖) ?_ ?_ f
  · intro c s hs _
    let sm : MeasuredSets μ := ⟨s, hs⟩
    let q := e (MeasureAlgebra.InducedBooleanAlgebra.mk μ sm)
    let t := representative q
    have ht : e (MeasureAlgebra.InducedBooleanAlgebra.mk μ sm) =
        MeasureAlgebra.InducedBooleanAlgebra.mk ν t := (mk_representative q).symm
    rw [transportSimple_indicatorConst (p := p) e sm t ht c,
      Lp.simpleFunc.indicatorConst_eq_smul t.property (measure_ne_top ν _) c,
      Lp.simpleFunc.indicatorConst_eq_smul sm.property (measure_ne_top μ _) c,
      norm_smul, norm_smul,
      ← indicatorOfClass_eq_indicatorConst (p := p) q t (mk_representative q),
      norm_indicatorOfClass_image (p := p) e sm]
  · intro f g hf hg hfg hnf hng
    have hp_le : (1 : ℝ≥0) ≤ p := Fact.out
    letI hp_fact : Fact ((1 : ℝ≥0) ≤ p) := ⟨hp_le⟩
    apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _)
      (show (p : ℝ) ≠ 0 by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one
          (Fact.out : (1 : ℝ≥0) ≤ p))))).mp
    have htarget :
        ‖(transportSimple e (SimpleFunc.toLp f hf) : Lp ℝ (p : ENNReal) ν) +
          (transportSimple e (SimpleFunc.toLp g hg) : Lp ℝ (p : ENNReal) ν)‖ ^ (p : ℝ) =
        ‖(transportSimple e (SimpleFunc.toLp f hf) : Lp ℝ (p : ENNReal) ν)‖ ^ (p : ℝ) +
          ‖(transportSimple e (SimpleFunc.toLp g hg) : Lp ℝ (p : ENNReal) ν)‖ ^ (p : ℝ) :=
      @ALpSpace.norm_add_rpow_eq_of_isVLDisjoint p
        (Lp ℝ (p : ENNReal) ν) hp_fact _ _ _ _ _ _
        (transportSimple_isVLDisjoint (p := p) e hf hg hfg)
    have hsource :
        ‖(SimpleFunc.toLp f hf : Lp ℝ (p : ENNReal) μ) +
          (SimpleFunc.toLp g hg : Lp ℝ (p : ENNReal) μ)‖ ^ (p : ℝ) =
        ‖(SimpleFunc.toLp f hf : Lp ℝ (p : ENNReal) μ)‖ ^ (p : ℝ) +
          ‖(SimpleFunc.toLp g hg : Lp ℝ (p : ENNReal) μ)‖ ^ (p : ℝ) :=
      @ALpSpace.norm_add_rpow_eq_of_isVLDisjoint p
        (Lp ℝ (p : ENNReal) μ) hp_fact _ _ _ _ _ _
        (Lp.simpleFunc.toLp_isVLDisjoint hf hg hfg)
    rw [transportSimple_add]
    change ‖(transportSimple e (SimpleFunc.toLp f hf) : Lp ℝ (p : ENNReal) ν) +
      (transportSimple e (SimpleFunc.toLp g hg) : Lp ℝ (p : ENNReal) ν)‖ ^ (p : ℝ) =
      ‖(SimpleFunc.toLp f hf : Lp ℝ (p : ENNReal) μ) +
        (SimpleFunc.toLp g hg : Lp ℝ (p : ENNReal) μ)‖ ^ (p : ℝ)
    rw [htarget, hsource]
    change ‖transportSimple e (SimpleFunc.toLp f hf)‖ ^ (p : ℝ) +
      ‖transportSimple e (SimpleFunc.toLp g hg)‖ ^ (p : ℝ) =
      ‖SimpleFunc.toLp f hf‖ ^ (p : ℝ) + ‖SimpleFunc.toLp g hg‖ ^ (p : ℝ)
    rw [hnf, hng]

/-- A measure-algebra equivalence induces an isometric linear equivalence on
the subspaces represented by simple functions. It transports characteristic
functions according to the underlying measure-algebra equivalence. -/
private theorem exists_simpleFunc_linearIsometryEquiv
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν)) :
    ∃ T :
        Lp.simpleFunc ℝ (p : ENNReal) μ ≃ₗᵢ[ℝ]
            Lp.simpleFunc ℝ (p : ENNReal) ν,
      ∀ (s : MeasuredSets μ) (t : MeasuredSets ν),
        e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) =
            MeasureAlgebra.InducedBooleanAlgebra.mk ν t →
          ∀ c : ℝ,
            T
                (Lp.simpleFunc.indicatorConst (p : ENNReal) s.property
                  (measure_ne_top μ _) c) =
              Lp.simpleFunc.indicatorConst (p : ENNReal) t.property
                (measure_ne_top ν _) c := by
  let L : Lp.simpleFunc ℝ (p : ENNReal) μ →ₗᵢ[ℝ]
      Lp.simpleFunc ℝ (p : ENNReal) ν :=
    { transportSimpleLinearMap (p := p) e with
      norm_map' := transportSimple_norm (p := p) e }
  have hL : Function.Surjective L := by
    intro f
    refine ⟨transportSimple e.symm f, ?_⟩
    exact transportSimple_comp_inverse (p := p) e f
  let T := LinearIsometryEquiv.ofSurjective L hL
  refine ⟨T, ?_⟩
  intro s t hst c
  change transportSimple e
      (Lp.simpleFunc.indicatorConst (p : ENNReal) s.property
        (measure_ne_top μ _) c) = _
  exact transportSimple_indicatorConst (p := p) e s t hst c

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
/-- An isometric equivalence between the dense simple-function subspaces
extends uniquely to an isometric equivalence of the full `L^p` spaces. -/
private theorem exists_linearIsometryEquiv_extension
    (T₀ :
      Lp.simpleFunc ℝ (p : ENNReal) μ ≃ₗᵢ[ℝ]
        Lp.simpleFunc ℝ (p : ENNReal) ν) :
    ∃ T :
        Lp ℝ (p : ENNReal) μ ≃ₗᵢ[ℝ]
          Lp ℝ (p : ENNReal) ν,
      ∀ f : Lp.simpleFunc ℝ (p : ENNReal) μ,
        T (f : Lp ℝ (p : ENNReal) μ) =
          (T₀ f : Lp ℝ (p : ENNReal) ν) := by
  let eμ := Lp.simpleFunc.coeToLp α ℝ ℝ (p := (p : ENNReal)) (μ := μ)
  let eν := Lp.simpleFunc.coeToLp β ℝ ℝ (p := (p : ENNReal)) (μ := ν)
  let T := T₀.toLinearEquiv.extendOfIsometry eμ.toLinearMap eν.toLinearMap
    (by
      change DenseRange ((↑) : Lp.simpleFunc ℝ (p : ENNReal) μ → Lp ℝ (p : ENNReal) μ)
      exact Lp.simpleFunc.denseRange (E := ℝ) (p := (p : ENNReal)) (μ := μ) (by simp))
    (by
      change DenseRange ((↑) : Lp.simpleFunc ℝ (p : ENNReal) ν → Lp ℝ (p : ENNReal) ν)
      exact Lp.simpleFunc.denseRange (E := ℝ) (p := (p : ENNReal)) (μ := ν) (by simp))
    (fun f ↦ by
      change ‖T₀ f‖ = ‖f‖
      exact T₀.norm_map f)
  refine ⟨T, ?_⟩
  intro f
  apply LinearEquiv.extendOfIsometry_eq

private theorem linearIsometryEquiv_map_simpleFunc
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (T : Lp ℝ (p : ENNReal) μ ≃ₗᵢ[ℝ] Lp ℝ (p : ENNReal) ν)
    (hT :
      ∀ (s : MeasuredSets μ) (t : MeasuredSets ν),
        e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) =
            MeasureAlgebra.InducedBooleanAlgebra.mk ν t →
          ∀ c : ℝ,
            T (indicatorConstLp (p : ENNReal) s.property
                (measure_ne_top μ _) c) =
              indicatorConstLp (p : ENNReal) t.property
                (measure_ne_top ν _) c)
    (f : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    T (f : Lp ℝ (p : ENNReal) μ) =
      (transportSimple e f : Lp ℝ (p : ENNReal) ν) := by
  refine Lp.simpleFunc.induction (α := α) (E := ℝ)
    (show (p : ENNReal) ≠ 0 by simp [ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)])
    (by simp) (P := fun f ↦ T (f : Lp ℝ (p : ENNReal) μ) =
      (transportSimple e f : Lp ℝ (p : ENNReal) ν)) ?_ ?_ f
  · intro c s hs _
    let sm : MeasuredSets μ := ⟨s, hs⟩
    obtain ⟨t, ht⟩ := exists_image_measuredSet e sm
    rw [Lp.simpleFunc.coe_indicatorConst, hT sm t ht c,
      transportSimple_indicatorConst (p := p) e sm t ht c,
      Lp.simpleFunc.coe_indicatorConst]
  · intro f g hf hg _ hTf hTg
    rw [transportSimple_add]
    change T ((SimpleFunc.toLp f hf : Lp ℝ (p : ENNReal) μ) +
      (SimpleFunc.toLp g hg : Lp ℝ (p : ENNReal) μ)) = _
    rw [map_add, hTf, hTg]
    rfl

private theorem linearIsometryEquiv_map_abs_simpleFunc
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (T : Lp ℝ (p : ENNReal) μ ≃ₗᵢ[ℝ] Lp ℝ (p : ENNReal) ν)
    (hT :
      ∀ (s : MeasuredSets μ) (t : MeasuredSets ν),
        e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) =
            MeasureAlgebra.InducedBooleanAlgebra.mk ν t →
          ∀ c : ℝ,
            T (indicatorConstLp (p : ENNReal) s.property
                (measure_ne_top μ _) c) =
              indicatorConstLp (p : ENNReal) t.property
                (measure_ne_top ν _) c)
    (f : Lp.simpleFunc ℝ (p : ENNReal) μ) :
    T |(f : Lp ℝ (p : ENNReal) μ)| =
      |T (f : Lp ℝ (p : ENNReal) μ)| := by
  refine Lp.simpleFunc.induction (α := α) (E := ℝ)
    (show (p : ENNReal) ≠ 0 by simp [ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)])
    (by simp) (P := fun f ↦ T |(f : Lp ℝ (p : ENNReal) μ)| =
      |T (f : Lp ℝ (p : ENNReal) μ)|) ?_ ?_ f
  · intro c s hs _
    let sm : MeasuredSets μ := ⟨s, hs⟩
    obtain ⟨t, ht⟩ := exists_image_measuredSet e sm
    rw [Lp.simpleFunc.coe_indicatorConst,
      Lp.abs_indicatorConstLp hs (measure_ne_top μ _) c,
      hT sm t ht |c|, hT sm t ht c,
      Lp.abs_indicatorConstLp t.property (measure_ne_top ν _) c]
  · intro f g hf hg hfg hTf hTg
    have hsource := Lp.simpleFunc.toLp_isVLDisjoint hf hg hfg
    have htarget : IsVLDisjoint
        (T (SimpleFunc.toLp f hf : Lp ℝ (p : ENNReal) μ))
        (T (SimpleFunc.toLp g hg : Lp ℝ (p : ENNReal) μ)) := by
      rw [linearIsometryEquiv_map_simpleFunc (p := p) e T hT (SimpleFunc.toLp f hf),
        linearIsometryEquiv_map_simpleFunc (p := p) e T hT (SimpleFunc.toLp g hg)]
      exact transportSimple_isVLDisjoint (p := p) e hf hg hfg
    change T |(SimpleFunc.toLp f hf : Lp ℝ (p : ENNReal) μ) +
      (SimpleFunc.toLp g hg : Lp ℝ (p : ENNReal) μ)| =
      |T ((SimpleFunc.toLp f hf : Lp ℝ (p : ENNReal) μ) +
        (SimpleFunc.toLp g hg : Lp ℝ (p : ENNReal) μ))|
    rw [abs_add_of_isVLDisjoint hsource, map_add, hTf, hTg, map_add,
      abs_add_of_isVLDisjoint htarget]

/-- An isometric equivalence that transports characteristic functions
according to a measure-algebra equivalence preserves absolute values. -/
private theorem linearIsometryEquiv_map_abs_of_map_indicatorConst
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν))
    (T :
      Lp ℝ (p : ENNReal) μ ≃ₗᵢ[ℝ]
        Lp ℝ (p : ENNReal) ν)
    (hT :
      ∀ (s : MeasuredSets μ) (t : MeasuredSets ν),
        e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) =
            MeasureAlgebra.InducedBooleanAlgebra.mk ν t →
          ∀ c : ℝ,
            T
                (indicatorConstLp (p : ENNReal) s.property
                  (measure_ne_top μ _) c) =
              indicatorConstLp (p : ENNReal) t.property
                (measure_ne_top ν _) c) :
    ∀ f : Lp ℝ (p : ENNReal) μ, T |f| = |T f| := by
  intro f
  refine (Lp.simpleFunc.denseRange (E := ℝ) (p := (p : ENNReal)) (μ := μ) (by simp)).induction_on
    f ?_ ?_
  · have habsμ : Continuous (|·| : Lp ℝ (p : ENNReal) μ → Lp ℝ (p : ENNReal) μ) :=
      NormedVectorLattice.lipschitzWith_abs.continuous
    have habsν : Continuous (|·| : Lp ℝ (p : ENNReal) ν → Lp ℝ (p : ENNReal) ν) :=
      NormedVectorLattice.lipschitzWith_abs.continuous
    exact isClosed_eq (T.continuous.comp habsμ) (habsν.comp T.continuous)
  · intro g
    exact linearIsometryEquiv_map_abs_simpleFunc (p := p) e T hT g

/-- Equivalent finite measure algebras induce lattice-isometric real `L^p` spaces
for every finite exponent `1 ≤ p`. -/
theorem nonempty_banachLatEquiv_lp
    (e : MeasureAlgebraEquiv
      (MeasureAlgebra.ofMeasure μ) (MeasureAlgebra.ofMeasure ν)) :
    Nonempty
      (BanachLatEquiv
        (Lp ℝ (p : ENNReal) μ)
        (Lp ℝ (p : ENNReal) ν)) := by
  obtain ⟨T₀, hT₀⟩ := exists_simpleFunc_linearIsometryEquiv (p := p) e
  obtain ⟨T, hT⟩ := exists_linearIsometryEquiv_extension (p := p) T₀
  have hT_indicator :
      ∀ (s : MeasuredSets μ) (t : MeasuredSets ν),
        e (MeasureAlgebra.InducedBooleanAlgebra.mk μ s) =
            MeasureAlgebra.InducedBooleanAlgebra.mk ν t →
          ∀ c : ℝ,
            T
                (indicatorConstLp (p : ENNReal) s.property
                  (measure_ne_top μ _) c) =
              indicatorConstLp (p : ENNReal) t.property
                (measure_ne_top ν _) c := by
    intro s t hst c
    rw [← Lp.simpleFunc.coe_indicatorConst, hT]
    exact congrArg Subtype.val (hT₀ s t hst c)
  let S := VecLatHom.ofAbs T.toLinearEquiv.toLinearMap
    (linearIsometryEquiv_map_abs_of_map_indicatorConst e T hT_indicator)
  exact ⟨{
    toLinearIsometryEquiv := T
    map_sup' := S.map_sup'
    map_inf' := S.map_inf' }⟩

end MeasureAlgebraEquiv

/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.MeasureAlgebras.ClosedSubalgebra
import BanLat.BooleanAlgebras.Adjoin
import BanLat.BooleanAlgebras.Functional.Hahn
import BanLat.BooleanAlgebras.MeasureAlgebras.Maharam.MaharamType
import BanLat.BooleanAlgebras.Atomless

open scoped ENNReal
open BooleanSubalgebra

/-!
# Extension machinery for Maharam's theorem

This file develops the relative-atomlessness and one-step extension results
used in the classification of homogeneous measure algebras.
-/

universe u v

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- Let `A` be a `σ`-complete Boolean subalgebra of a homogeneous measure algebra
`(B, μ)`. If the density character induced on `A` is less than `μ.maharamType`,
then `B` is relatively atomless with respect to `A`. -/
theorem isRelativelyAtomless_of_isHomogeneous_of_densityCharacter_lt
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (hμ : μ.IsHomogeneous)
    (hκ : μ.subalgebraDensityCharacter A < μ.maharamType) :
    A.IsRelativelyAtomless := by
  intro b hb
  by_contra hrel
  push Not at hrel
  letI := hA.toSigmaCompleteBooleanAlgebra
  let ν := μ.restrictToSubalgebra A hA
  let f : A → Set.Iic b := fun a ↦ ⟨b ⊓ (a : B), inf_le_left⟩
  letI := ν.toMetricSpace
  letI := (μ.restrict b).toMetricSpace
  have hf : Continuous f := by
    apply Metric.continuous_iff.2
    intro a ε hε
    refine ⟨ε, hε, ?_⟩
    intro a' ha'
    apply lt_of_le_of_lt _ ha'
    change (μ ((symmDiff (f a') (f a) : Set.Iic b) : B)).toReal ≤
      (μ ((symmDiff a' a : A) : B)).toReal
    rw [Set.Iic.coe_symmDiff]
    change (μ (symmDiff (b ⊓ (a' : B)) (b ⊓ (a : B)))).toReal ≤
      (μ (symmDiff (a' : B) (a : B))).toReal
    rw [← inf_symmDiff_distrib_left]
    exact ENNReal.toReal_mono (μ.measure_ne_top _)
      (μ.measure_mono inf_le_right)
  have hfs : Function.Surjective f := by
    intro c
    obtain ⟨a, ha⟩ := hrel (c : B) c.property
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha.symm
  have hle : (μ.restrict b).densityCharacter ≤ μ.subalgebraDensityCharacter A := by
    rw [← μ.restrictToSubalgebra_densityCharacter_eq_subalgebraDensityCharacter A hA]
    exact TopologicalSpace.densityCharacter_le_of_continuous_surjective hf hfs
  apply not_le_of_gt hκ
  rw [← hμ hb]
  exact hle

section

variable (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
variable (hA : A.IsSigmaComplete)

/-- If `B` is relatively atomless with respect to `A` and `b ∈ B`, `b ≠ ⊥`,
there is `d ∈ B`, `d ≠ ⊥`, with `d ≤ b` and `μ (a ⊓ d) ≤ μ (a ⊓ b) / 2`
for every `a ∈ A`. -/
private lemma exists_nonzero_infFunctional_le_half
    (hrel : A.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ {b : B}, b ≠ ⊥ →
      ∃ d : B, d ≠ ⊥ ∧ d ≤ b ∧
        ∀ a : A, μ.infFunctional A hA d a ≤ μ.infFunctional A hA b a / 2 := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro b hb
  obtain ⟨e, heb, he⟩ := hrel hb
  let α := μ.infFunctional A hA b
  let ε := μ.infFunctional A hA e
  let ρ := ε.scaledFunctional 2
  have hα : α.IsFinite := by
    exact μ.toCountablyAdditiveFunctional.infFunctional_isFinite
      A hA b (μ.measure_ne_top b)
  have hε : ε.IsFinite := by
    exact μ.toCountablyAdditiveFunctional.infFunctional_isFinite
      A hA e (μ.measure_ne_top e)
  have hρ : ρ.IsFinite := ε.scaledFunctional_isFinite 2 hε
  obtain ⟨p, hp⟩ := ρ.exists_isHahnDecomposition α hρ hα
  by_cases hep : e ⊓ (p : B) ≠ ⊥
  · refine ⟨e ⊓ (p : B), hep, inf_le_left.trans heb, ?_⟩
    intro a
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
    have hle := hp.le_on (show a ⊓ p ≤ p from inf_le_right)
    have hmono : α (a ⊓ p) ≤ α a := α.monotone inf_le_left
    exact le_trans (by simpa [ρ, ε, α, mul_comm, inf_assoc, inf_left_comm, inf_comm] using hle)
      (by simpa [α, inf_assoc, inf_left_comm, inf_comm] using hmono)
  · let d := b \ (e ⊔ (p : B))
    have hd_ne : d ≠ ⊥ := by
      intro hd
      have hb_le : b ≤ e ⊔ (p : B) := by
        rw [← sdiff_eq_bot_iff]
        exact hd
      have hep_disj : Disjoint e (p : B) := by
        rw [disjoint_iff]
        exact not_ne_iff.mp hep
      apply he pᶜ
      apply le_antisymm
      · exact le_inf heb (le_compl_iff_disjoint_right.mpr hep_disj)
      · calc
          b ⊓ ((p : B)ᶜ) ≤ (e ⊔ (p : B)) ⊓ ((p : B)ᶜ) :=
            inf_le_inf_right _ hb_le
          _ ≤ e := by simp [inf_sup_right]
    refine ⟨d, hd_ne, sdiff_le, ?_⟩
    intro a
    let q : A := a \ p
    have hq_disj : Disjoint q p := disjoint_sdiff_self_left
    have hle := hp.ge_on_compl hq_disj
    change μ ((q : B) ⊓ b) ≤ 2 * μ ((q : B) ⊓ e) at hle
    have hqb : ((q : B) ⊓ b) ⊓ e = (q : B) ⊓ e := by
      rw [inf_assoc, inf_eq_right.mpr heb]
    have had : (a : B) ⊓ d = ((q : B) ⊓ b) \ e := by
      change (a : B) ⊓ d = (((a : B) \ (p : B)) ⊓ b) \ e
      simp only [d, sdiff_eq, compl_sup]
      ac_rfl
    have hsplit := μ.measure_sdiff_add_inf ((q : B) ⊓ b) e
    rw [hqb] at hsplit
    change μ ((a : B) ⊓ d) ≤ μ ((a : B) ⊓ b) / 2
    rw [had]
    apply (ENNReal.toReal_le_toReal (μ.measure_ne_top _)
      (ENNReal.div_ne_top (μ.measure_ne_top _) (by norm_num))).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_ofNat]
    have hsplit_real := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add (μ.measure_ne_top _) (μ.measure_ne_top _)] at hsplit_real
    have hle_real := (ENNReal.toReal_le_toReal (α.ne_top hα q) (ρ.ne_top hρ q)).mpr hle
    simp only [α, ρ, ε, CountablyAdditiveFunctional.scaledFunctional_apply,
      ENNReal.toReal_mul] at hle_real
    change (μ ((q : B) ⊓ b)).toReal ≤ 2 * (μ ((q : B) ⊓ e)).toReal at hle_real
    have hmono : μ ((q : B) ⊓ b) ≤ μ ((a : B) ⊓ b) := by
      apply μ.measure_mono
      exact inf_le_inf_right b (show (q : B) ≤ a from sdiff_le)
    have hmono_real := (ENNReal.toReal_le_toReal (μ.measure_ne_top _)
      (μ.measure_ne_top _)).mpr hmono
    linarith

/-- If `B` is relatively atomless with respect to `A`, `b ∈ B`, `b ≠ ⊥`, and
`n ∈ ℕ`, there is `d ∈ B`, `d ≠ ⊥`, with `d ≤ b` and
`μ (a ⊓ d) ≤ μ (a ⊓ b) / 2 ^ n` for every `a ∈ A`. -/
private lemma exists_nonzero_infFunctional_le_two_pow
    (hrel : A.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ {b : B}, b ≠ ⊥ → ∀ n : ℕ,
      ∃ d : B, d ≠ ⊥ ∧ d ≤ b ∧
        ∀ a : A, μ.infFunctional A hA d a ≤
          μ.infFunctional A hA b a / (2 ^ n) := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro b hb n
  induction n with
  | zero =>
      exact ⟨b, hb, le_rfl, by simp⟩
  | succ n ih =>
      obtain ⟨c, hc, hcb, hsmall⟩ := ih
      obtain ⟨d, hd, hdc, hdhalf⟩ :=
        exists_nonzero_infFunctional_le_half μ A hA hrel hc
      refine ⟨d, hd, hdc.trans hcb, fun a ↦ (hdhalf a).trans ?_⟩
      calc
        μ.infFunctional A hA c a / 2 ≤
            (μ.infFunctional A hA b a / (2 ^ n)) / 2 :=
          ENNReal.div_le_div_right (hsmall a) 2
        _ = μ.infFunctional A hA b a / (2 ^ (n + 1)) := by
          rw [pow_succ]
          simp only [ENNReal.div_eq_inv_mul]
          rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by norm_num))]
          ac_rfl

/-- Let `B` be a relatively atomless with respect to `A`, `b ∈ B`, `ν : A → ℝ≥0∞` a countably
additive functional such that `ν ⊤ ≠ 0`, and `ν a ≤ μ (a ⊓ b)` for every `a ∈ A`. Then there is
`d ∈ B`, `d ≠ ⊥`, with `d ≤ b` and `μ (a ⊓ d) ≤ ν a` for every `a ∈ A`. -/
private lemma exists_nonzero_infFunctional_le
    (hrel : A.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ {b : B} (ν : CountablyAdditiveFunctional A), ν ⊤ ≠ 0 →
      (∀ a : A, ν a ≤ μ.infFunctional A hA b a) →
        ∃ d : B, d ≠ ⊥ ∧ d ≤ b ∧
          ∀ a : A, μ.infFunctional A hA d a ≤ ν a := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro b ν hν_top hν
  let α := μ.infFunctional A hA b
  have hα : α.IsFinite := by
    exact μ.toCountablyAdditiveFunctional.infFunctional_isFinite
      A hA b (μ.measure_ne_top b)
  have hν_fin : ν.IsFinite := ne_top_of_le_ne_top hα (hν ⊤)
  have hν_pos : 0 < (ν ⊤).toReal := ENNReal.toReal_pos hν_top hν_fin
  have hpowers := Filter.tendsto_atTop.1
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    ((α ⊤).toReal / (ν ⊤).toReal + 1)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hpowers
  have hn' : (α ⊤).toReal / (ν ⊤).toReal < (2 : ℝ) ^ n :=
    (lt_add_one _).trans_le (hn n le_rfl)
  have hsmall : α ⊤ / (2 ^ n) < ν ⊤ := by
    apply (ENNReal.toReal_lt_toReal
      (ENNReal.div_ne_top (α.ne_top hα ⊤) (by positivity)) hν_fin).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).2
    simpa [mul_comm] using (div_lt_iff₀ hν_pos).mp hn'
  let r : NNReal := (2 ^ n)⁻¹
  let ρ := α.scaledFunctional r
  have hρ : ρ.IsFinite := α.scaledFunctional_isFinite r hα
  obtain ⟨p, hp⟩ := ρ.exists_isHahnDecomposition ν hρ hν_fin
  let c := b ⊓ (p : B)
  have hc : c ≠ ⊥ := by
    intro hc
    have hαp : α p = 0 := by
      simp only [α, infFunctional_apply]
      rw [show (p : B) ⊓ b = ⊥ by simpa [c, inf_comm] using hc, μ.measure_bot]
    have hνp : ν p = 0 := le_antisymm ((hν p).trans_eq hαp) bot_le
    have hρp : ρ p = 0 := by simp [ρ, hαp]
    have hout := hp.ge_on_compl (disjoint_compl_left : Disjoint pᶜ p)
    have hνsplit := ν.map_sup (disjoint_compl_right : Disjoint p pᶜ)
    have hρsplit := ρ.map_sup (disjoint_compl_right : Disjoint p pᶜ)
    rw [sup_compl_eq_top, hνp, zero_add] at hνsplit
    rw [sup_compl_eq_top, hρp, zero_add] at hρsplit
    apply (not_le_of_gt hsmall)
    calc
      ν ⊤ = ν pᶜ := hνsplit
      _ ≤ ρ pᶜ := hout
      _ = ρ ⊤ := hρsplit.symm
      _ = α ⊤ / (2 ^ n) := by simp [ρ, r, ENNReal.div_eq_inv_mul]
  obtain ⟨d, hd, hdc, hdsmall⟩ :=
    exists_nonzero_infFunctional_le_two_pow μ A hA hrel hc n
  refine ⟨d, hd, hdc.trans inf_le_left, ?_⟩
  intro a
  have hle := hp.le_on (show a ⊓ p ≤ p from inf_le_right)
  calc
    μ.infFunctional A hA d a ≤ μ.infFunctional A hA c a / (2 ^ n) := hdsmall a
    _ = ρ (a ⊓ p) := by
      simp [ρ, r, α, c, ENNReal.div_eq_inv_mul, inf_left_comm, inf_comm]
    _ ≤ ν (a ⊓ p) := hle
    _ ≤ ν a := ν.monotone inf_le_left

/-- If `ν : A → ℝ≥0∞` is a countably additive functional, there is a maximal
element `b ∈ B` satisfying `μ (a ⊓ b) ≤ ν a` for every `a ∈ A`. -/
private lemma exists_maximal_infFunctional_le :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ (ν : CountablyAdditiveFunctional A),
      ∃ b : B, (∀ a : A, μ.infFunctional A hA b a ≤ ν a) ∧
        ∀ c : B, b ≤ c → (∀ a : A, μ.infFunctional A hA c a ≤ ν a) → c = b := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro ν
  let S : Set B := {b | ∀ a : A, μ.infFunctional A hA b a ≤ ν a}
  have hbot : ⊥ ∈ S := by simp [S]
  have hchain : ∀ s ⊆ S, IsChain (· ≤ ·) s → ∃ ub ∈ S, ∀ z ∈ s, z ≤ ub := by
    intro s hsS hs
    by_cases hs_empty : s = ∅
    · exact ⟨⊥, hbot, by simp [hs_empty]⟩
    · have hs_ne : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hs_empty
      let V : Set ℝ≥0∞ := μ '' s
      have hV_ne : V.Nonempty := hs_ne.image μ
      have hV_bdd : BddAbove V := by
        refine ⟨μ ⊤, ?_⟩
        rintro _ ⟨x, -, rfl⟩
        exact μ.measure_mono le_top
      obtain ⟨v, hv_mono, hv_lim, hv⟩ := exists_seq_tendsto_sSup hV_ne hV_bdd
      have hx_exists (n : ℕ) : ∃ x ∈ s, μ x = v n := by
        simpa only [V, Set.mem_image] using hv n
      choose x hx_mem hx_measure using hx_exists
      have hx_mono : Monotone x := by
        intro n m hnm
        have hmeasure : μ (x n) ≤ μ (x m) := by
          rw [hx_measure n, hx_measure m]
          exact hv_mono hnm
        rcases hs.total (hx_mem n) (hx_mem m) with hle | hle
        · exact hle
        · by_contra hge
          exact (not_lt_of_ge hmeasure) (μ.measure_strictMono (hle.lt_of_not_ge hge))
      let ub : B := ⨆ n, x n
      have hub_mem : ub ∈ S := by
        intro a
        change μ ((a : B) ⊓ ub) ≤ ν a
        rw [show (a : B) ⊓ ub = ⨆ n, (a : B) ⊓ x n by
          exact SigmaCompleteBooleanAlgebra.inf_iSup_nat (a : B) x]
        rw [μ.measure_iSup_eq_iSup]
        · exact iSup_le fun n ↦ hsS (hx_mem n) a
        · exact fun _ _ hnm ↦ inf_le_inf_left (a : B) (hx_mono hnm)
      refine ⟨ub, hub_mem, ?_⟩
      intro z hz
      by_cases hzx : ∃ n, z ≤ x n
      · obtain ⟨n, hn⟩ := hzx
        exact hn.trans (SigmaCompleteBooleanAlgebra.le_iSup_nat x n)
      · have hubz : ub ≤ z := by
          apply SigmaCompleteBooleanAlgebra.iSup_nat_le
          intro n
          exact (hs.total (hx_mem n) hz).resolve_right fun hzn ↦ hzx ⟨n, hzn⟩
        have hμx_lim : Filter.Tendsto (fun n ↦ μ (x n)) Filter.atTop (nhds (μ ub)) := by
          exact μ.toCountablyAdditiveFunctional.tendsto_map_iSup hx_mono
        have hv_lim' : Filter.Tendsto v Filter.atTop (nhds (μ ub)) :=
          hμx_lim.congr' <| Filter.Eventually.of_forall fun n ↦ hx_measure n
        have hμub : μ ub = sSup V := tendsto_nhds_unique hv_lim' hv_lim
        have hμzu : μ z ≤ μ ub := by
          rw [hμub]
          exact le_csSup hV_bdd ⟨z, hz, rfl⟩
        by_contra hge
        exact (not_lt_of_ge hμzu) (μ.measure_strictMono (hubz.lt_of_not_ge hge))
  obtain ⟨b, hb⟩ := zorn_le₀ S hchain
  refine ⟨b, hb.1, ?_⟩
  intro c hbc hc
  exact (hb.eq_of_le hc hbc).symm

/-- If `B` is relatively atomless with respect to `A` and `b ∈ B` is maximal subject to
`μ (a ⊓ b) ≤ ν a`, then `μ (a ⊓ b) = ν a` for every `a ∈ A`. -/
private theorem infFunctional_apply_eq_of_maximal
    (hrel : A.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ (ν : CountablyAdditiveFunctional A),
      (∀ a : A, ν a ≤ μ (a : B)) → ∀ b : B,
        (∀ a : A, μ.infFunctional A hA b a ≤ ν a) →
          (∀ c : B, b ≤ c →
            (∀ a : A, μ.infFunctional A hA c a ≤ ν a) → c = b) →
              ∀ a : A, μ.infFunctional A hA b a = ν a := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro ν hν b hb hbmax a
  apply le_antisymm (hb a)
  by_contra hle
  let ρ := μ.infFunctional A hA b
  have hρ_fin : ρ.IsFinite := by
    exact μ.toCountablyAdditiveFunctional.infFunctional_isFinite
      A hA b (μ.measure_ne_top b)
  let δ := ν.subFunctional ρ hρ_fin hb
  have hδa : δ a ≠ 0 := by
    change ν a - ρ a ≠ 0
    rw [ne_eq, tsub_eq_zero_iff_le]
    exact hle
  have hδ_top : δ ⊤ ≠ 0 := by
    intro hzero
    apply hδa
    exact le_antisymm ((δ.monotone le_top).trans_eq hzero) bot_le
  have hδ : ∀ a : A, δ a ≤ μ.infFunctional A hA bᶜ a := by
    intro a
    change ν a - ρ a ≤ μ.infFunctional A hA bᶜ a
    rw [tsub_le_iff_right]
    calc
      ν a ≤ μ (a : B) := hν a
      _ = μ.infFunctional A hA bᶜ a + ρ a := by
        change μ (a : B) = μ ((a : B) ⊓ bᶜ) + μ ((a : B) ⊓ b)
        simpa only [sdiff_eq] using (μ.measure_sdiff_add_inf (a : B) b).symm
  obtain ⟨d, hd, hdc, hdδ⟩ :=
    exists_nonzero_infFunctional_le μ A hA hrel δ hδ_top hδ
  have hbd_disj : Disjoint b d :=
    (le_compl_iff_disjoint_right.mp hdc).symm
  have hsup : ∀ a : A, μ.infFunctional A hA (b ⊔ d) a ≤ ν a := by
    intro a
    calc
      μ.infFunctional A hA (b ⊔ d) a = ρ a + μ.infFunctional A hA d a := by
        change μ ((a : B) ⊓ (b ⊔ d)) = μ ((a : B) ⊓ b) + μ ((a : B) ⊓ d)
        rw [inf_sup_left, μ.measure_sup]
        exact hbd_disj.mono inf_le_right inf_le_right
      _ ≤ ρ a + δ a := add_le_add le_rfl (hdδ a)
      _ = ν a := by
        change ρ a + (ν a - ρ a) = ν a
        rw [add_comm, tsub_add_cancel_of_le (hb a)]
  have heq : b ⊔ d = b := hbmax (b ⊔ d) le_sup_left hsup
  apply hd
  apply le_bot_iff.mp
  calc
    d ≤ d ⊓ b := le_inf le_rfl (le_sup_right.trans_eq heq)
    _ ≤ ⊥ := hbd_disj.symm.le_bot

/-- If `B` is relatively atomless with respect to `A` and the countably additive
functional `ν : A → ℝ≥0∞` satisfies `ν a ≤ μ a` for every `a ∈ A`, there is `b ∈ B`
such that `μ (a ⊓ b) = ν a` for every `a ∈ A`. -/
theorem exists_infFunctional_apply_eq_of_isRelativelyAtomless
    (hrel : A.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ∀ (ν : CountablyAdditiveFunctional A),
      (∀ a : A, ν a ≤ μ (a : B)) →
        ∃ b : B, ∀ a : A, μ.infFunctional A hA b a = ν a := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  intro ν hν
  obtain ⟨b, hb, hbmax⟩ := exists_maximal_infFunctional_le μ A hA ν
  exact ⟨b, infFunctional_apply_eq_of_maximal μ A hA hrel ν hν b hb hbmax⟩

end

section

variable {C : Type v} [SigmaCompleteBooleanAlgebra C]
variable (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
variable (A : BooleanSubalgebra B) (D : BooleanSubalgebra C)
variable (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete)

/-- Let `A ⊆ (B, μ)` and `D ⊆ (C, η)` be `σ`-complete Boolean subalgebras, and let
`e : A ≃ D` be a measure-algebra equivalence between them. Suppose that `C` is relatively
atomless with respect to `D`. Then, for every `b ∈ B` there is `c ∈ C` such that
`η (d ⊓ c) = μ (e⁻¹(d) ⊓ b)` for every `d ∈ D`. -/
theorem exists_targetElement_of_isRelativelyAtomless
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete)
    (hrel : D.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B),
      ∃ c : C, ∀ d : D, η ((d : C) ⊓ c) = μ (((e.symm d : A) : B) ⊓ b) := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := hD.toSigmaCompleteBooleanAlgebra
  intro e b
  let ρ := CountablyAdditiveFunctional.pullbackFunctional e.symm.toRelIso
    (μ.infFunctional A hA b)
  have hρ : ∀ d : D, ρ d ≤ η (d : C) := by
    intro d
    calc
      ρ d = μ.infFunctional A hA b (e.symm d) := rfl
      _ ≤ μ ((e.symm d : A) : B) := μ.infFunctional_le A hA b (e.symm d)
      _ = η (d : C) := by simpa using e.symm.map_measure d
  obtain ⟨c, hc⟩ :=
    exists_infFunctional_apply_eq_of_isRelativelyAtomless η D hD hrel ρ hρ
  refine ⟨c, ?_⟩
  intro d
  convert hc d using 1
  · exact (infFunctional_apply η D hD c d).symm
  · rfl

private lemma compl_inf_measure_eq_of_inf_measure_eq
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B) (c : C),
      (∀ d : D, η ((d : C) ⊓ c) = μ (((e.symm d : A) : B) ⊓ b)) →
        ∀ d : D, η ((d : C) ⊓ cᶜ) = μ (((e.symm d : A) : B) ⊓ bᶜ) := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := hD.toSigmaCompleteBooleanAlgebra
  intro e b c hc d
  have hη : η ((d : C) ⊓ cᶜ) = η (d : C) - η ((d : C) ⊓ c) := by
    have hsum := η.measure_sdiff_add_inf (d : C) c
    exact ENNReal.eq_sub_of_add_eq' (η.measure_ne_top _) (by
      simpa only [sdiff_eq] using hsum)
  have hμ : μ (((e.symm d : A) : B) ⊓ bᶜ) =
      μ ((e.symm d : A) : B) - μ (((e.symm d : A) : B) ⊓ b) := by
    have hsum := μ.measure_sdiff_add_inf ((e.symm d : A) : B) b
    exact ENNReal.eq_sub_of_add_eq' (μ.measure_ne_top _) (by
      simpa only [sdiff_eq] using hsum)
  have htotal : μ ((e.symm d : A) : B) = η (d : C) := by
    simpa using e.symm.map_measure d
  rw [hη, hμ, hc d, htotal]

private lemma inf_le_inf_iff_of_inf_measure_eq
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B) (c : C),
      (∀ d : D, η ((d : C) ⊓ c) = μ (((e.symm d : A) : B) ⊓ b)) →
        ∀ a₁ a₂ : A,
          b ⊓ (a₁ : B) ≤ b ⊓ (a₂ : B) ↔
            c ⊓ ((e a₁ : D) : C) ≤ c ⊓ ((e a₂ : D) : C) := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := hD.toSigmaCompleteBooleanAlgebra
  intro e b c hc a₁ a₂
  have hm : η (c ⊓ (((e a₁ : D) : C) \ ((e a₂ : D) : C))) =
      μ (b ⊓ ((a₁ : B) \ (a₂ : B))) := by
    have hm' := hc (e (a₁ \ a₂))
    have hinv : e.symm (e (a₁ \ a₂)) = a₁ \ a₂ := e.left_inv _
    have hmap : e (a₁ \ a₂) = e a₁ \ e a₂ := map_sdiff' e.toRelIso _ _
    rw [hinv, hmap] at hm'
    simpa only [BooleanSubalgebra.val_sdiff, inf_comm] using hm'
  calc
    b ⊓ (a₁ : B) ≤ b ⊓ (a₂ : B) ↔
        μ ((b ⊓ (a₁ : B)) \ (b ⊓ (a₂ : B))) = 0 := by
          rw [μ.measure_eq_zero_iff, sdiff_eq_bot_iff]
    _ ↔ μ (b ⊓ ((a₁ : B) \ (a₂ : B))) = 0 := by
      rw [inf_sdiff_distrib_left]
    _ ↔ η (c ⊓ (((e a₁ : D) : C) \ ((e a₂ : D) : C))) = 0 := by rw [hm]
    _ ↔ η ((c ⊓ ((e a₁ : D) : C)) \ (c ⊓ ((e a₂ : D) : C))) = 0 := by
      rw [inf_sdiff_distrib_left]
    _ ↔ c ⊓ ((e a₁ : D) : C) ≤ c ⊓ ((e a₂ : D) : C) := by
      rw [η.measure_eq_zero_iff, sdiff_eq_bot_iff]

/- Let `A ⊆ (B, μ)` and `D ⊆ (C, η)` be `σ`-complete Boolean subalgebras, and let
`e : A ≃ D` be a measure-algebra equivalence between them. Fix `b ∈ B` and `c ∈ C`
such that `η (d ⊓ c) = μ (e⁻¹(d) ⊓ b)` for every `d ∈ D`. Then, for every
`a₁, a₂ ∈ A`,
`η ((c ⊓ e(a₁)) ⊔ (cᶜ ⊓ e(a₂))) = μ ((b ⊓ a₁) ⊔ (bᶜ ⊓ a₂))`. -/
private lemma measure_adjoinValue_eq_of_inf_measure_eq
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B) (c : C),
      (∀ d : D, η ((d : C) ⊓ c) = μ (((e.symm d : A) : B) ⊓ b)) →
        ∀ p : A × A,
          η (adjoinValue D c (Prod.map e.toRelIso e.toRelIso p)) =
            μ (adjoinValue A b p) := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := hD.toSigmaCompleteBooleanAlgebra
  intro e b c hc p
  have hc_compl :=
    compl_inf_measure_eq_of_inf_measure_eq μ η A D hA hD e b c hc
  have h₁ := hc (e p.1)
  have h₂ := hc_compl (e p.2)
  have hinv₁ : e.symm (e p.1) = p.1 := e.left_inv _
  have hinv₂ : e.symm (e p.2) = p.2 := e.left_inv _
  rw [hinv₁] at h₁
  rw [hinv₂] at h₂
  calc
    η (adjoinValue D c (Prod.map e.toRelIso e.toRelIso p)) =
        η (c ⊓ ((e p.1 : D) : C)) + η (cᶜ ⊓ ((e p.2 : D) : C)) := by
      apply η.measure_sup
      exact disjoint_compl_right.mono inf_le_left inf_le_left
    _ = μ (b ⊓ (p.1 : B)) + μ (bᶜ ⊓ (p.2 : B)) := by
      rw [inf_comm c, h₁, inf_comm cᶜ, h₂]
      congr 1 <;> ac_rfl
    _ = μ (adjoinValue A b p) := by
      symm
      apply μ.measure_sup
      exact disjoint_compl_right.mono inf_le_left inf_le_left

/- Let `A ⊆ (B, μ)` and `D ⊆ (C, η)` be `σ`-complete Boolean subalgebras, and let
`e : A ≃ D` be a measure-algebra equivalence between them. Fix `b ∈ B` and `c ∈ C`
such that `η (d ⊓ c) = μ (e⁻¹(d) ⊓ b)` for every `d ∈ D`. Then `e` extends to a
measure-algebra equivalence `A.adjoin b ≃ D.adjoin c` that sends `b` to `c`. -/
private theorem exists_adjoinEquiv_of_inf_measure_eq
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B) (c : C),
      (∀ d : D, η ((d : C) ⊓ c) = μ (((e.symm d : A) : B) ⊓ b)) →
        let hAb := hA.adjoin b
        let hDc := hD.adjoin c
        letI := hAb.toSigmaCompleteBooleanAlgebra
        letI := hDc.toSigmaCompleteBooleanAlgebra
        ∃ f : MeasureAlgebraEquiv
            (μ.restrictToSubalgebra (A.adjoin b) hAb)
            (η.restrictToSubalgebra (D.adjoin c) hDc),
          (∀ a : A,
            ((f ⟨a, A.le_adjoin b a.property⟩ : D.adjoin c) : C) = (e a : D)) ∧
          ((f ⟨b, A.mem_adjoin b⟩ : D.adjoin c) : C) = c := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := hD.toSigmaCompleteBooleanAlgebra
  intro e b c hc
  dsimp only
  let hAb := hA.adjoin b
  let hDc := hD.adjoin c
  letI := hAb.toSigmaCompleteBooleanAlgebra
  letI := hDc.toSigmaCompleteBooleanAlgebra
  have hc_compl : ∀ d : D,
      η ((d : C) ⊓ cᶜ) = μ (((e.symm d : A) : B) ⊓ bᶜ) :=
    compl_inf_measure_eq_of_inf_measure_eq μ η A D hA hD e b c hc
  have hcut (a₁ a₂ : A) :
      b ⊓ (a₁ : B) ≤ b ⊓ (a₂ : B) ↔
        c ⊓ ((e a₁ : D) : C) ≤ c ⊓ ((e a₂ : D) : C) :=
    inf_le_inf_iff_of_inf_measure_eq μ η A D hA hD e b c hc a₁ a₂
  have hcut_compl (a₁ a₂ : A) :
      bᶜ ⊓ (a₁ : B) ≤ bᶜ ⊓ (a₂ : B) ↔
        cᶜ ⊓ ((e a₁ : D) : C) ≤ cᶜ ⊓ ((e a₂ : D) : C) :=
    inf_le_inf_iff_of_inf_measure_eq μ η A D hA hD e bᶜ cᶜ hc_compl a₁ a₂
  have horder (p q : A × A) :
      adjoinValue A b p ≤ adjoinValue A b q ↔
        adjoinValue D c (Prod.map e.toRelIso e.toRelIso p) ≤
          adjoinValue D c (Prod.map e.toRelIso e.toRelIso q) := by
    rw [adjoinValue_le_iff, adjoinValue_le_iff]
    exact and_congr (hcut p.1 q.1) (hcut_compl p.2 q.2)
  have hmeasure (p : A × A) :
      η (adjoinValue D c (Prod.map e.toRelIso e.toRelIso p)) =
        μ (adjoinValue A b p) :=
    measure_adjoinValue_eq_of_inf_measure_eq μ η A D hA hD e b c hc p
  let g : A.adjoin b ≃o D.adjoin c :=
    adjoinOrderIso e.toRelIso b c horder
  have hg_measure (x : A.adjoin b) : η ((g x : D.adjoin c) : C) = μ (x : B) := by
    let p := adjoinRepresentation A b x
    calc
      η ((g x : D.adjoin c) : C) =
          η (adjoinValue D c (Prod.map e.toRelIso e.toRelIso p)) := by
        apply congrArg η
        exact adjoinOrderIso_apply_eq_of_eq e.toRelIso b c horder x p
          (adjoinRepresentation_spec A b x)
      _ = μ (adjoinValue A b p) := hmeasure p
      _ = μ (x : B) := congrArg μ (adjoinRepresentation_spec A b x)
  let f : MeasureAlgebraEquiv
      (μ.restrictToSubalgebra (A.adjoin b) hAb)
      (η.restrictToSubalgebra (D.adjoin c) hDc) :=
    { g with
      map_measure' := fun x ↦ by simpa using hg_measure x }
  refine ⟨f, ?_, ?_⟩
  · intro a
    let x : A.adjoin b := ⟨a, A.le_adjoin b a.property⟩
    have hx : adjoinValue A b (a, a) = (x : B) := by
      change (b ⊓ (a : B)) ⊔ (bᶜ ⊓ (a : B)) = (a : B)
      rw [← inf_sup_right]
      simp
    change ((g x : D.adjoin c) : C) = (e a : D)
    rw [adjoinOrderIso_apply_eq_of_eq e.toRelIso b c horder x (a, a) hx]
    change (c ⊓ ((e a : D) : C)) ⊔ (cᶜ ⊓ ((e a : D) : C)) = (e a : D)
    rw [← inf_sup_right]
    simp
  · let x : A.adjoin b := ⟨b, A.mem_adjoin b⟩
    have hx : adjoinValue A b (⊤, ⊥) = (x : B) := by
      change adjoinValue A b (⊤, ⊥) = b
      simp [adjoinValue]
    change ((g x : D.adjoin c) : C) = c
    rw [adjoinOrderIso_apply_eq_of_eq e.toRelIso b c horder x (⊤, ⊥) hx]
    simp [adjoinValue]

/-- Let `A ⊆ B` and `D ⊆ C` be `σ`-complete Boolean subalgebras, and let
`e : A ≃ D` be a measure-algebra equivalence between them. Suppose that `C`
is relatively atomless with respect to `D`. Then, for every `b ∈ B` there are
`c ∈ C` and a measure-algebra equivalence `f : A.adjoin b ≃ D.adjoin c` such that
`f(a) = e(a)` for every `a ∈ A` and `f(b) = c`. -/
theorem exists_extension_of_isRelativelyAtomless
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete)
    (hrel : D.IsRelativelyAtomless) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∀ (e : MeasureAlgebraEquiv (μ.restrictToSubalgebra A hA)
        (η.restrictToSubalgebra D hD)) (b : B),
      ∃ c : C,
        let hAb := hA.adjoin b
        let hDc := hD.adjoin c
        letI := hAb.toSigmaCompleteBooleanAlgebra
        letI := hDc.toSigmaCompleteBooleanAlgebra
        ∃ f : MeasureAlgebraEquiv
            (μ.restrictToSubalgebra (A.adjoin b) hAb)
            (η.restrictToSubalgebra (D.adjoin c) hDc),
          (∀ a : A,
            ((f ⟨a, A.le_adjoin b a.property⟩ : D.adjoin c) : C) = (e a : D)) ∧
          ((f ⟨b, A.mem_adjoin b⟩ : D.adjoin c) : C) = c := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := hD.toSigmaCompleteBooleanAlgebra
  intro e b
  obtain ⟨c, hc⟩ := exists_targetElement_of_isRelativelyAtomless μ η A D hA hD hrel e b
  exact ⟨c, exists_adjoinEquiv_of_inf_measure_eq μ η A D hA hD e b c hc⟩

/-- A partial equivalence of `μ` and `η` consists of a measure-algebra equivalence
between restrictions to `σ`-complete Boolean subalgebras. -/
structure PartialEquiv where
  /-- The source `σ`-complete Boolean subalgebra. -/
  source : BooleanSubalgebra B
  /-- The target `σ`-complete Boolean subalgebra. -/
  target : BooleanSubalgebra C
  /-- The source is closed under countable suprema computed in `B`. -/
  source_isSigmaComplete : source.IsSigmaComplete
  /-- The target is closed under countable suprema computed in `C`. -/
  target_isSigmaComplete : target.IsSigmaComplete
  /-- The measure-algebra equivalence between the two restrictions. -/
  toMeasureAlgebraEquiv :
    letI := source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
    letI := target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
    MeasureAlgebraEquiv
      (μ.restrictToSubalgebra source source_isSigmaComplete)
      (η.restrictToSubalgebra target target_isSigmaComplete)

end

namespace PartialEquiv

variable {C : Type v} [SigmaCompleteBooleanAlgebra C]
variable {μ : MeasureAlgebra B} {η : MeasureAlgebra C}

/-- The partial order-isomorphism underlying a partial measure-algebra equivalence. -/
noncomputable def toOrderIso (e : PartialEquiv μ η) : e.source ≃o e.target := by
  letI := e.source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  letI := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  exact e.toMeasureAlgebraEquiv.toRelIso

/-- The partial order-isomorphism underlying a partial measure-algebra equivalence
preserves measure. -/
@[simp]
theorem map_measure (e : PartialEquiv μ η) (a : e.source) :
    η (e.toOrderIso a : C) = μ (a : B) := by
  letI := e.source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  letI := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  exact e.toMeasureAlgebraEquiv.map_measure a

/-- The trivial Boolean subalgebras `{⊥, ⊤} ⊆ B` and `{⊥, ⊤} ⊆ C` are
order-isomorphic when `B` is trivial if and only if `C` is trivial. -/
private noncomputable def orderIsoBot
    (htriv : (⊥ : B) = ⊤ ↔ (⊥ : C) = ⊤) :
    (⊥ : BooleanSubalgebra B) ≃o (⊥ : BooleanSubalgebra C) := by
  classical
  by_cases hB : (⊥ : B) = ⊤
  · have hC := htriv.mp hB
    letI : Subsingleton B := subsingleton_of_bot_eq_top hB
    letI : Subsingleton C := subsingleton_of_bot_eq_top hC
    letI : Unique (⊥ : BooleanSubalgebra B) :=
      { default := ⊥
        uniq := fun _ ↦ Subtype.ext (Subsingleton.elim _ _) }
    letI : Unique (⊥ : BooleanSubalgebra C) :=
      { default := ⊥
        uniq := fun _ ↦ Subtype.ext (Subsingleton.elim _ _) }
    exact OrderIso.ofUnique _ _
  · have hC : (⊥ : C) ≠ ⊤ := mt htriv.mpr hB
    letI : IsSimpleOrder (⊥ : BooleanSubalgebra B) :=
      { exists_pair_ne := ⟨⊥, ⊤, fun h ↦ hB (congrArg Subtype.val h)⟩
        eq_bot_or_eq_top := fun a ↦ by
          rcases a.property with ha | ha
          · exact Or.inl (Subtype.ext ha)
          · exact Or.inr (Subtype.ext ha) }
    letI : IsSimpleOrder (⊥ : BooleanSubalgebra C) :=
      { exists_pair_ne := ⟨⊥, ⊤, fun h ↦ hC (congrArg Subtype.val h)⟩
        eq_bot_or_eq_top := fun c ↦ by
          rcases c.property with hc | hc
          · exact Or.inl (Subtype.ext hc)
          · exact Or.inr (Subtype.ext hc) }
    exact (IsSimpleOrder.orderIsoBool : (⊥ : BooleanSubalgebra B) ≃o Bool).trans
      (IsSimpleOrder.orderIsoBool : (⊥ : BooleanSubalgebra C) ≃o Bool).symm

/-- If `μ ⊤ = η ⊤`, the trivial subalgebras `{⊥, ⊤} ⊆ B` and
`{⊥, ⊤} ⊆ C` always form a partial equivalence. -/
noncomputable def ofMeasureTopEq (h : μ ⊤ = η ⊤) : PartialEquiv μ η := by
  have htriv : (⊥ : B) = ⊤ ↔ (⊥ : C) = ⊤ := by
    constructor
    · intro hB
      symm
      apply (η.measure_eq_zero_iff ⊤).mp
      rw [← h, ← hB, μ.measure_bot]
    · intro hC
      symm
      apply (μ.measure_eq_zero_iff ⊤).mp
      rw [h, ← hC, η.measure_bot]
  let e := orderIsoBot htriv
  let hB : (⊥ : BooleanSubalgebra B).IsSigmaComplete :=
    BooleanSubalgebra.isSigmaComplete_bot
  let hC : (⊥ : BooleanSubalgebra C).IsSigmaComplete :=
    BooleanSubalgebra.isSigmaComplete_bot
  letI := hB.toSigmaCompleteBooleanAlgebra
  letI := hC.toSigmaCompleteBooleanAlgebra
  exact
    { source := ⊥
      target := ⊥
      source_isSigmaComplete := hB
      target_isSigmaComplete := hC
      toMeasureAlgebraEquiv :=
        { e with
          map_measure' := by
            intro a
            rcases BooleanSubalgebra.mem_bot.mp a.property with ha | ha
            · have ha' : a = ⊥ := Subtype.ext ha
              simp [ha']
            · have ha' : a = ⊤ := Subtype.ext ha
              simpa [ha'] using h.symm } }

@[simp]
theorem ofMeasureTopEq_source (h : μ ⊤ = η ⊤) :
    (ofMeasureTopEq h).source = (⊥ : BooleanSubalgebra B) := rfl

@[simp]
theorem ofMeasureTopEq_target (h : μ ⊤ = η ⊤) :
    (ofMeasureTopEq h).target = (⊥ : BooleanSubalgebra C) := rfl

/-- One partial measure-algebra equivalence extends another when its source and target
grow and its partial order-isomorphism agrees with the old partial order-isomorphism
on the old source. -/
structure Extends (e f : PartialEquiv μ η) : Prop where
  /-- Inclusion of the old source in the new source. -/
  source_le : e.source ≤ f.source
  /-- Inclusion of the old target in the new target. -/
  target_le : e.target ≤ f.target
  /-- The new partial order-isomorphism agrees with the old partial order-isomorphism
  on the old source. -/
  map_eq (a : e.source) :
    ((f.toOrderIso ⟨a, source_le a.property⟩ : f.target) : C) =
      (e.toOrderIso a : e.target)

/-- Every partial measure-algebra equivalence extends itself. -/
protected theorem Extends.refl (e : PartialEquiv μ η) : e.Extends e := by
  refine ⟨le_rfl, le_rfl, ?_⟩
  intro a
  rfl

/-- Extension of partial measure-algebra equivalences is transitive. -/
protected theorem Extends.trans {e f g : PartialEquiv μ η}
    (hef : e.Extends f) (hfg : f.Extends g) : e.Extends g := by
  refine ⟨hef.source_le.trans hfg.source_le, hef.target_le.trans hfg.target_le, ?_⟩
  intro a
  exact (hfg.map_eq ⟨a, hef.source_le a.property⟩).trans (hef.map_eq a)

/-- The inverse partial order-isomorphisms of two extending partial measure-algebra
equivalences agree on the old target. -/
theorem Extends.symm_map_eq {e f : PartialEquiv μ η} (hef : e.Extends f)
    (d : e.target) :
    ((f.toOrderIso.symm ⟨d, hef.target_le d.property⟩ : f.source) : B) =
      (e.toOrderIso.symm d : e.source) := by
  let a := e.toOrderIso.symm d
  have hmap := hef.map_eq a
  have hmap' : f.toOrderIso ⟨a, hef.source_le a.property⟩ =
      ⟨d, hef.target_le d.property⟩ := by
    apply Subtype.ext
    simpa only [a, e.toOrderIso.apply_symm_apply] using hmap
  have heq : f.toOrderIso.symm ⟨d, hef.target_le d.property⟩ =
      ⟨a, hef.source_le a.property⟩ := by
    calc
      f.toOrderIso.symm ⟨d, hef.target_le d.property⟩ =
        f.toOrderIso.symm (f.toOrderIso ⟨a, hef.source_le a.property⟩) :=
        congrArg f.toOrderIso.symm hmap'.symm
      _ = ⟨a, hef.source_le a.property⟩ := f.toOrderIso.symm_apply_apply _
  exact congrArg Subtype.val heq

/-- Let `(E i)_{i ∈ ι}` be a linearly ordered family of partial measure-algebra
equivalences between `(B, μ)` and `(D, ν)`, where `E j` extends `E i` whenever
`i ≤ j`. Set `A = ⋃ i, (E i).source` and `D = ⋃ i, (E i).target`. Then the partial
order-isomorphisms underlying the `E i` glue to an order isomorphism `e : A ≃ D`
such that `e(a) = (E i).toOrderIso(a)` for every `i ∈ ι` and
`a ∈ (E i).source`, and `η (e(a)) = μ(a)` for every `a ∈ A`. -/
private theorem exists_orderIso_increasingUnion
    {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (E : ι → PartialEquiv μ η)
    (hE : ∀ i j, i ≤ j → (E i).Extends (E j)) :
    let hsource : Monotone (fun i ↦ (E i).source) :=
      fun _ _ hij ↦ (hE _ _ hij).source_le
    let htarget : Monotone (fun i ↦ (E i).target) :=
      fun _ _ hij ↦ (hE _ _ hij).target_le
    let A := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).source) hsource
    let D := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).target) htarget
    ∃ e : A ≃o D,
      (∀ i (a : (E i).source),
        ((e ⟨a, Set.mem_iUnion.2 ⟨i, a.property⟩⟩ : D) : C) =
          ((E i).toOrderIso a : (E i).target)) ∧
      ∀ a : A, η (e a : C) = μ (a : B) := by
  dsimp only
  let hsource : Monotone (fun i ↦ (E i).source) :=
    fun _ _ hij ↦ (hE _ _ hij).source_le
  let htarget : Monotone (fun i ↦ (E i).target) :=
    fun _ _ hij ↦ (hE _ _ hij).target_le
  let A := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).source) hsource
  let D := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).target) htarget
  have hA_stage (a : A) : ∃ i, (a : B) ∈ (E i).source :=
    Set.mem_iUnion.mp a.property
  have hD_stage (d : D) : ∃ i, (d : C) ∈ (E i).target :=
    Set.mem_iUnion.mp d.property
  have source_mem (i) (a : B) (ha : a ∈ (E i).source) : a ∈ A :=
    Set.mem_iUnion.2 ⟨i, ha⟩
  have target_mem (i) (d : C) (hd : d ∈ (E i).target) : d ∈ D :=
    Set.mem_iUnion.2 ⟨i, hd⟩
  have hmap {i j : ι} (hij : i ≤ j) (a : B) (ha : a ∈ (E i).source) :
      (((E j).toOrderIso ⟨a, hsource hij ha⟩ : (E j).target) : C) =
        ((E i).toOrderIso ⟨a, ha⟩ : (E i).target) :=
    (hE i j hij).map_eq ⟨a, ha⟩
  have hmap_symm {i j : ι} (hij : i ≤ j) (d : C) (hd : d ∈ (E i).target) :
      (((E j).toOrderIso.symm ⟨d, htarget hij hd⟩ : (E j).source) : B) =
        ((E i).toOrderIso.symm ⟨d, hd⟩ : (E i).source) :=
    (hE i j hij).symm_map_eq ⟨d, hd⟩
  let stageA (a : A) := Classical.choose (hA_stage a)
  have mem_stageA (a : A) : (a : B) ∈ (E (stageA a)).source :=
    Classical.choose_spec (hA_stage a)
  let stageD (d : D) := Classical.choose (hD_stage d)
  have mem_stageD (d : D) : (d : C) ∈ (E (stageD d)).target :=
    Classical.choose_spec (hD_stage d)
  let f : A → D := fun a ↦
    ⟨(E (stageA a)).toOrderIso ⟨a, mem_stageA a⟩,
      target_mem (stageA a) _ ((E (stageA a)).toOrderIso ⟨a, mem_stageA a⟩).property⟩
  let g : D → A := fun d ↦
    ⟨(E (stageD d)).toOrderIso.symm ⟨d, mem_stageD d⟩,
      source_mem (stageD d) _
        ((E (stageD d)).toOrderIso.symm ⟨d, mem_stageD d⟩).property⟩
  have f_eq (i) (a : B) (ha : a ∈ (E i).source) :
      (f ⟨a, source_mem i a ha⟩ : C) = ((E i).toOrderIso ⟨a, ha⟩ : C) := by
    change ((E (stageA ⟨a, source_mem i a ha⟩)).toOrderIso
      ⟨a, mem_stageA ⟨a, source_mem i a ha⟩⟩ : C) =
        ((E i).toOrderIso ⟨a, ha⟩ : C)
    exact (hmap (i := stageA ⟨a, source_mem i a ha⟩)
      (j := max (stageA ⟨a, source_mem i a ha⟩) i) (le_max_left _ _) a
      (mem_stageA _)).symm.trans (hmap (i := i) (j := max _ i) (le_max_right _ _) a ha)
  have g_eq (i) (d : C) (hd : d ∈ (E i).target) :
      (g ⟨d, target_mem i d hd⟩ : B) = ((E i).toOrderIso.symm ⟨d, hd⟩ : B) := by
    change ((E (stageD ⟨d, target_mem i d hd⟩)).toOrderIso.symm
      ⟨d, mem_stageD ⟨d, target_mem i d hd⟩⟩ : B) =
        ((E i).toOrderIso.symm ⟨d, hd⟩ : B)
    exact (hmap_symm (i := stageD ⟨d, target_mem i d hd⟩)
      (j := max (stageD ⟨d, target_mem i d hd⟩) i) (le_max_left _ _) d
      (mem_stageD _)).symm.trans
        (hmap_symm (i := i) (j := max _ i) (le_max_right _ _) d hd)
  have f_mem_stage (a : A) : (f a : C) ∈ (E (stageA a)).target := by
    change ((E (stageA a)).toOrderIso ⟨a, mem_stageA a⟩ : C) ∈
      (E (stageA a)).target
    exact ((E (stageA a)).toOrderIso ⟨a, mem_stageA a⟩).property
  have g_mem_stage (d : D) : (g d : B) ∈ (E (stageD d)).source := by
    change ((E (stageD d)).toOrderIso.symm ⟨d, mem_stageD d⟩ : B) ∈
      (E (stageD d)).source
    exact ((E (stageD d)).toOrderIso.symm ⟨d, mem_stageD d⟩).property
  have gf (a : A) : g (f a) = a := by
    apply Subtype.ext
    rw [g_eq (stageA a) (f a : C) (f_mem_stage a)]
    have hf : (⟨f a, f_mem_stage a⟩ : (E (stageA a)).target) =
        (E (stageA a)).toOrderIso ⟨a, mem_stageA a⟩ := by
      apply Subtype.ext
      exact f_eq (stageA a) (a : B) (mem_stageA a)
    rw [hf, (E (stageA a)).toOrderIso.symm_apply_apply]
  have fg (d : D) : f (g d) = d := by
    apply Subtype.ext
    rw [f_eq (stageD d) (g d : B) (g_mem_stage d)]
    have hg : (⟨g d, g_mem_stage d⟩ : (E (stageD d)).source) =
        (E (stageD d)).toOrderIso.symm ⟨d, mem_stageD d⟩ := by
      apply Subtype.ext
      exact g_eq (stageD d) (d : C) (mem_stageD d)
    rw [hg, (E (stageD d)).toOrderIso.apply_symm_apply]
  let equiv : A ≃ D :=
    { toFun := f
      invFun := g
      left_inv := gf
      right_inv := fg }
  have hf_mono : Monotone f := by
    intro a a' haa'
    let i := max (stageA a) (stageA a')
    have ha : (a : B) ∈ (E i).source := hsource (le_max_left _ _) (mem_stageA a)
    have ha' : (a' : B) ∈ (E i).source := hsource (le_max_right _ _) (mem_stageA a')
    change (f a : C) ≤ (f a' : C)
    rw [f_eq i (a : B) ha, f_eq i (a' : B) ha']
    exact (E i).toOrderIso.monotone haa'
  have hg_mono : Monotone g := by
    intro d d' hdd'
    let i := max (stageD d) (stageD d')
    have hd : (d : C) ∈ (E i).target := htarget (le_max_left _ _) (mem_stageD d)
    have hd' : (d' : C) ∈ (E i).target := htarget (le_max_right _ _) (mem_stageD d')
    change (g d : B) ≤ (g d' : B)
    rw [g_eq i (d : C) hd, g_eq i (d' : C) hd']
    exact (E i).toOrderIso.symm.monotone hdd'
  let e : A ≃o D := equiv.toOrderIso hf_mono hg_mono
  refine ⟨e, ?_, ?_⟩
  · intro i a
    exact f_eq i a a.property
  · intro a
    change η ((E (stageA a)).toOrderIso ⟨a, mem_stageA a⟩ : C) = μ (a : B)
    exact (E (stageA a)).map_measure ⟨a, mem_stageA a⟩

/-- Under the hypotheses of the two-sided extension theorem, if the two sides of the
partial measure-algebra equivalence `e` have density character at most `κB` and `κC`,
where `ℵ₀ ≤ κB, κC`, then the enlarged sides satisfy the same bounds. -/
theorem exists_extension_both_of_isHomogeneous_of_densityCharacter_le
    (e : PartialEquiv μ η)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (hμ_inf : Cardinal.aleph0 ≤ μ.maharamType)
    (hη_inf : Cardinal.aleph0 ≤ η.maharamType)
    (he_source : μ.subalgebraDensityCharacter e.source < μ.maharamType)
    (he_target : η.subalgebraDensityCharacter e.target < η.maharamType)
    {κB : Cardinal.{u}} {κC : Cardinal.{v}}
    (hκB : Cardinal.aleph0 ≤ κB) (hκC : Cardinal.aleph0 ≤ κC)
    (he_source_le : μ.subalgebraDensityCharacter e.source ≤ κB)
    (he_target_le : η.subalgebraDensityCharacter e.target ≤ κC)
    (b : B) (c : C) :
    ∃ f : PartialEquiv μ η,
      e.Extends f ∧ b ∈ f.source ∧ c ∈ f.target ∧
        μ.subalgebraDensityCharacter f.source < μ.maharamType ∧
        η.subalgebraDensityCharacter f.target < η.maharamType ∧
        μ.subalgebraDensityCharacter f.source ≤ κB ∧
        η.subalgebraDensityCharacter f.target ≤ κC := by
  letI := e.source_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  letI := e.target_isSigmaComplete.toSigmaCompleteBooleanAlgebra
  let e₀ := e.toMeasureAlgebraEquiv
  have hrelC : e.target.IsRelativelyAtomless :=
    isRelativelyAtomless_of_isHomogeneous_of_densityCharacter_lt
      η e.target e.target_isSigmaComplete hη he_target
  obtain ⟨c₁, f₁, hf₁, hb⟩ :=
    exists_extension_of_isRelativelyAtomless μ η e.source e.target
      e.source_isSigmaComplete e.target_isSigmaComplete hrelC e₀ b
  let A₁ := e.source.adjoin b
  let D₁ := e.target.adjoin c₁
  let hA₁ := e.source_isSigmaComplete.adjoin b
  let hD₁ := e.target_isSigmaComplete.adjoin c₁
  letI := hA₁.toSigmaCompleteBooleanAlgebra
  letI := hD₁.toSigmaCompleteBooleanAlgebra
  have hA₁_small :
      μ.subalgebraDensityCharacter A₁ < μ.maharamType :=
    subalgebraDensityCharacter_adjoin_lt μ e.source b hμ_inf he_source
  have hD₁_small :
      η.subalgebraDensityCharacter D₁ < η.maharamType :=
    subalgebraDensityCharacter_adjoin_lt η e.target c₁ hη_inf he_target
  have hA₁_le :
      μ.subalgebraDensityCharacter A₁ ≤ κB :=
    subalgebraDensityCharacter_adjoin_le μ e.source b hκB he_source_le
  have hD₁_le :
      η.subalgebraDensityCharacter D₁ ≤ κC :=
    subalgebraDensityCharacter_adjoin_le η e.target c₁ hκC he_target_le
  have hrelB : A₁.IsRelativelyAtomless :=
    isRelativelyAtomless_of_isHomogeneous_of_densityCharacter_lt μ A₁ hA₁ hμ hA₁_small
  obtain ⟨b₁, g, hg, hc⟩ :=
    exists_extension_of_isRelativelyAtomless η μ D₁ A₁ hD₁ hA₁ hrelB f₁.symm c
  let A₂ := A₁.adjoin b₁
  let D₂ := D₁.adjoin c
  let hA₂ := hA₁.adjoin b₁
  let hD₂ := hD₁.adjoin c
  letI := hA₂.toSigmaCompleteBooleanAlgebra
  letI := hD₂.toSigmaCompleteBooleanAlgebra
  let f : PartialEquiv μ η :=
    { source := A₂
      target := D₂
      source_isSigmaComplete := hA₂
      target_isSigmaComplete := hD₂
      toMeasureAlgebraEquiv := g.symm }
  have hA₂_small :
      μ.subalgebraDensityCharacter A₂ < μ.maharamType :=
    subalgebraDensityCharacter_adjoin_lt μ A₁ b₁ hμ_inf hA₁_small
  have hD₂_small :
      η.subalgebraDensityCharacter D₂ < η.maharamType :=
    subalgebraDensityCharacter_adjoin_lt η D₁ c hη_inf hD₁_small
  have hA₂_le :
      μ.subalgebraDensityCharacter A₂ ≤ κB :=
    subalgebraDensityCharacter_adjoin_le μ A₁ b₁ hκB hA₁_le
  have hD₂_le :
      η.subalgebraDensityCharacter D₂ ≤ κC :=
    subalgebraDensityCharacter_adjoin_le η D₁ c hκC hD₁_le
  have hsource : e.source ≤ A₂ :=
    (e.source.le_adjoin b).trans (A₁.le_adjoin b₁)
  have htarget : e.target ≤ D₂ :=
    (e.target.le_adjoin c₁).trans (D₁.le_adjoin c)
  have hext : e.Extends f := by
    refine ⟨hsource, htarget, ?_⟩
    intro a
    let a₁ : A₁ := ⟨a, e.source.le_adjoin b a.property⟩
    let a₂ : A₂ := ⟨a, hsource a.property⟩
    let d₁ : D₁ := f₁ a₁
    let d₂ : D₂ := ⟨d₁, D₁.le_adjoin c d₁.property⟩
    have hga : g d₂ = a₂ := by
      apply Subtype.ext
      calc
        ((g d₂ : A₂) : B) = (f₁.symm d₁ : A₁) := hg d₁
        _ = (a₁ : B) := congrArg Subtype.val (f₁.symm_apply_apply a₁)
        _ = (a₂ : B) := rfl
    have hsymm : g.symm a₂ = d₂ := by
      calc
        g.symm a₂ = g.symm (g d₂) := congrArg g.symm hga.symm
        _ = d₂ := g.left_inv d₂
    change ((g.symm a₂ : D₂) : C) = (e₀ a : e.target)
    rw [hsymm]
    exact hf₁ a
  refine ⟨f, hext, ?_, ?_, hA₂_small, hD₂_small, hA₂_le, hD₂_le⟩
  · exact A₁.le_adjoin b₁ (e.source.mem_adjoin b)
  · exact D₁.mem_adjoin c

/-- If `μ` and `η` are homogeneous and both sides of the partial measure-algebra
equivalence `e` have density character below their infinite Maharam types, then its
partial order-isomorphism extends to include any `b ∈ B` in its source and any `c ∈ C`
in its target, while preserving both density bounds. -/
theorem exists_extension_both_of_isHomogeneous
    (e : PartialEquiv μ η)
    (hμ : μ.IsHomogeneous) (hη : η.IsHomogeneous)
    (hμ_inf : Cardinal.aleph0 ≤ μ.maharamType)
    (hη_inf : Cardinal.aleph0 ≤ η.maharamType)
    (he_source : μ.subalgebraDensityCharacter e.source < μ.maharamType)
    (he_target : η.subalgebraDensityCharacter e.target < η.maharamType)
    (b : B) (c : C) :
    ∃ f : PartialEquiv μ η,
      e.Extends f ∧ b ∈ f.source ∧ c ∈ f.target ∧
        μ.subalgebraDensityCharacter f.source < μ.maharamType ∧
        η.subalgebraDensityCharacter f.target < η.maharamType := by
  let κB := max Cardinal.aleph0 (μ.subalgebraDensityCharacter e.source)
  let κC := max Cardinal.aleph0 (η.subalgebraDensityCharacter e.target)
  obtain ⟨f, hext, hb, hc, hfB, hfC, _, _⟩ :=
    exists_extension_both_of_isHomogeneous_of_densityCharacter_le
      e hμ hη hμ_inf hη_inf he_source he_target
      (le_max_left _ _) (le_max_left _ _) (le_max_right _ _) (le_max_right _ _) b c
  exact ⟨f, hext, hb, hc, hfB, hfC⟩

/-- Let `(E i)_{i ∈ ι}` be a linearly ordered family of partial measure-algebra
equivalences between `(B, μ)` and `(C, η)`, where `E j` extends `E i` whenever
`i ≤ j`. Then there is a partial measure-algebra equivalence `f` extending every
`E i`, so that `f.toOrderIso(a) = (E i).toOrderIso(a)` for every
`a ∈ (E i).source`, `f.source = σCompleteClosure (⋃ i, (E i).source)` and
`f.target = σCompleteClosure (⋃ i, (E i).target)`. -/
theorem exists_extension_iUnion
    {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (E : ι → PartialEquiv μ η)
    (hE : ∀ i j, i ≤ j → (E i).Extends (E j)) :
    ∃ f : PartialEquiv μ η,
      (∀ i, (E i).Extends f) ∧
        f.source = BooleanSubalgebra.sigmaCompleteClosure
          (⋃ i, ((E i).source : Set B)) ∧
        f.target = BooleanSubalgebra.sigmaCompleteClosure
          (⋃ i, ((E i).target : Set C)) := by
  let hsource : Monotone (fun i ↦ (E i).source) :=
    fun _ _ hij ↦ (hE _ _ hij).source_le
  let htarget : Monotone (fun i ↦ (E i).target) :=
    fun _ _ hij ↦ (hE _ _ hij).target_le
  let A := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).source) hsource
  let D := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).target) htarget
  obtain ⟨e, he, hmeasure⟩ := exists_orderIso_increasingUnion E hE
  let hA := (μ.isClosedSubalgebra_iff_isSigmaComplete (μ.closure A)).1
    (μ.isClosedSubalgebra_closure A)
  let hD := (η.isClosedSubalgebra_iff_isSigmaComplete (η.closure D)).1
    (η.isClosedSubalgebra_closure D)
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := hD.toSigmaCompleteBooleanAlgebra
  obtain ⟨f, hf⟩ := exists_measureAlgebraEquiv_closure_extends μ η A D e hmeasure
  let F : PartialEquiv μ η :=
    { source := μ.closure A
      target := η.closure D
      source_isSigmaComplete := hA
      target_isSigmaComplete := hD
      toMeasureAlgebraEquiv := f }
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    have hsource_i : (E i).source ≤ μ.closure A := by
      intro a ha
      exact μ.le_closure A (Set.mem_iUnion.2 ⟨i, ha⟩)
    have htarget_i : (E i).target ≤ η.closure D := by
      intro d hd
      exact η.le_closure D (Set.mem_iUnion.2 ⟨i, hd⟩)
    refine ⟨hsource_i, htarget_i, ?_⟩
    intro a
    let a' : A := ⟨a, Set.mem_iUnion.2 ⟨i, a.property⟩⟩
    calc
      ((F.toOrderIso ⟨a, hsource_i a.property⟩ : F.target) : C) =
          (e a' : D) := hf a'
      _ = ((E i).toOrderIso a : (E i).target) := he i a
  · change μ.closure A = BooleanSubalgebra.sigmaCompleteClosure
      (⋃ i, ((E i).source : Set B))
    rw [μ.closure_eq_sigmaCompleteClosure A]
    congr 1
  · change η.closure D = BooleanSubalgebra.sigmaCompleteClosure
      (⋃ i, ((E i).target : Set C))
    rw [η.closure_eq_sigmaCompleteClosure D]
    congr 1

/-- Let `(E i)_{i ∈ ι}` be a linearly ordered family of partial measure-algebra
equivalences between `(B, μ)` and `(C, η)`, where `E j` extends `E i` whenever
`i ≤ j`. Suppose that `ℵ₀ ≤ κ`, `#ι ≤ κ`, and that the source and target of every
`E i` have density character at most `κ`. Then there is a partial measure-algebra
equivalence `f` extending every `E i` such that
`densityCharacter(f.source) ≤ κ` and `densityCharacter(f.target) ≤ κ`. -/
theorem exists_extension_iUnion_of_densityCharacter_le
    {C' : Type u} [SigmaCompleteBooleanAlgebra C']
    {ν : MeasureAlgebra C'}
    {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (E : ι → PartialEquiv μ ν)
    (hE : ∀ i j, i ≤ j → (E i).Extends (E j))
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hι : Cardinal.mk ι ≤ κ)
    (hsource : ∀ i, μ.subalgebraDensityCharacter (E i).source ≤ κ)
    (htarget : ∀ i, ν.subalgebraDensityCharacter (E i).target ≤ κ) :
    ∃ f : PartialEquiv μ ν,
      (∀ i, (E i).Extends f) ∧
        μ.subalgebraDensityCharacter f.source ≤ κ ∧
        ν.subalgebraDensityCharacter f.target ≤ κ := by
  obtain ⟨f, hf, hfsource, hftarget⟩ := exists_extension_iUnion E hE
  let S := BooleanSubalgebra.sigmaCompleteClosure
    (⋃ i, ((E i).source : Set B))
  let D := BooleanSubalgebra.sigmaCompleteClosure
    (⋃ i, ((E i).target : Set C'))
  have hsource' :=
    subalgebraDensityCharacter_sigmaCompleteClosure_iUnion_le
      μ (fun i ↦ (E i).source) hκ hι hsource
  have htarget' :=
    subalgebraDensityCharacter_sigmaCompleteClosure_iUnion_le
      ν (fun i ↦ (E i).target) hκ hι htarget
  have hsource_eq := subalgebraDensityCharacter_congr μ f.source S hfsource
  have htarget_eq := subalgebraDensityCharacter_congr ν f.target D hftarget
  refine ⟨f, hf, ?_, ?_⟩
  · exact hsource_eq.trans_le hsource'
  · exact htarget_eq.trans_le htarget'

end PartialEquiv

end MeasureAlgebra

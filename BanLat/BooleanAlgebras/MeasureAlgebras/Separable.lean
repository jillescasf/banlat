/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Adjoin
import BanLat.BooleanAlgebras.MeasureAlgebras.Metric
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Topology.Bases

/-!
# Separable measure algebras

Let `(B, μ)` be a measurable algebra and `d(a, b) = μ (a ∆ b)` its associated metric.

`(B, μ)` is said to be **separable** when it is separable as a metric space.

In this file we prove that separablity is equivalent to the existence of:
* a dense sequence.
* a countable dense subalgebra.
* a sequence of finite subalgebras whose union is dense.
-/

universe u

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]
variable (μ : MeasureAlgebra B)

private def finiteStage (u : ℕ → B) (n : ℕ) : BooleanSubalgebra B :=
  BooleanSubalgebra.closure (u '' (Finset.range n : Set ℕ))

private theorem finite_finiteStage (u : ℕ → B) (n : ℕ) :
    (finiteStage u n : Set B).Finite := by
  apply BooleanSubalgebra.finite_closure
  exact (Finset.range n).finite_toSet.image u

private theorem monotone_finiteStage (u : ℕ → B) : Monotone (finiteStage u) := by
  intro m n hmn
  apply BooleanSubalgebra.closure_mono
  apply Set.image_mono
  exact_mod_cast Finset.range_mono hmn

private theorem range_subset_finiteStage_union (u : ℕ → B) :
    Set.range u ⊆ ⋃ n, (finiteStage u n : Set B) := by
  rintro _ ⟨n, rfl⟩
  apply Set.mem_iUnion.2
  refine ⟨n + 1, BooleanSubalgebra.subset_closure ?_⟩
  exact ⟨n, by simp, rfl⟩

/-- A measure algebra is separable when its measure-metric topology is separable. -/
noncomputable def IsSeparable : Prop :=
  letI := μ.toMetricSpace
  TopologicalSpace.SeparableSpace B

/-- If the density character of the measure algebra `(B, μ)` satisfies
`densityCharacter(B, μ) ≤ ℵ₀`, then `(B, μ)` is separable. -/
theorem isSeparable_of_densityCharacter_le_aleph0
    (hμ : μ.densityCharacter ≤ Cardinal.aleph0) :
    μ.IsSeparable := by
  letI := μ.toMetricSpace
  exact (TopologicalSpace.separableSpace_iff_densityCharacter_le_aleph0 B).2 hμ

/-- A measure algebra is separable if and only if it admits a sequence with
dense range for the measure metric. -/
theorem isSeparable_iff_exists_dense_seq :
    μ.IsSeparable ↔
      letI := μ.toMetricSpace
      ∃ u : ℕ → B, DenseRange u := by
  letI := μ.toMetricSpace
  change TopologicalSpace.SeparableSpace B ↔ ∃ u : ℕ → B, DenseRange u
  exact TopologicalSpace.separableSpace_iff_exists_dense_seq B

/-- Metric separability is equivalent to the existence of a countable dense
(for the measure metric) Boolean subalgebra. -/
theorem isSeparable_iff_exists_countable_dense_booleanSubalgebra :
    μ.IsSeparable ↔
      letI := μ.toMetricSpace
      ∃ A : BooleanSubalgebra B,
        (A : Set B).Countable ∧ Dense (A : Set B) := by
  letI := μ.toMetricSpace
  change TopologicalSpace.SeparableSpace B ↔
    ∃ A : BooleanSubalgebra B, (A : Set B).Countable ∧ Dense (A : Set B)
  constructor
  · intro h
    letI := h
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq B
    refine ⟨BooleanSubalgebra.increasingUnion (finiteStage u) (monotone_finiteStage u),
      ?_, ?_⟩
    · exact Set.countable_iUnion fun n ↦ (finite_finiteStage u n).countable
    · exact hu.mono (range_subset_finiteStage_union u)
  · rintro ⟨A, hA, hA_dense⟩
    exact ⟨⟨(A : Set B), hA, hA_dense⟩⟩

/-- Metric separability is equivalent to approximation by an increasing
sequence of finite Boolean subalgebras with dense union. -/
theorem isSeparable_iff_exists_finite_approximation :
    μ.IsSeparable ↔
      letI := μ.toMetricSpace
      ∃ A : ℕ → BooleanSubalgebra B,
        Monotone A ∧
          (∀ n, (A n : Set B).Finite) ∧
          Dense (⋃ n, (A n : Set B)) := by
  letI := μ.toMetricSpace
  change TopologicalSpace.SeparableSpace B ↔
    ∃ A : ℕ → BooleanSubalgebra B,
      Monotone A ∧ (∀ n, (A n : Set B).Finite) ∧ Dense (⋃ n, (A n : Set B))
  constructor
  · intro h
    letI := h
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq B
    exact ⟨finiteStage u, monotone_finiteStage u, finite_finiteStage u,
      hu.mono (range_subset_finiteStage_union u)⟩
  · rintro ⟨A, _, hA, hA_dense⟩
    exact ⟨⟨⋃ n, (A n : Set B), Set.countable_iUnion fun n ↦ (hA n).countable,
      hA_dense⟩⟩

end MeasureAlgebra

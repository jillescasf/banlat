/-
Authors: David Muñoz-Lahoz
-/

import BanLat.ALSpace.OrderContinuous
import BanLat.Examples.MofK.Basic

/-!
# `M(K)` as an AL-space

For a compact Hausdorff space `K` with its Borel σ-algebra, the Banach lattice
`M(K)` of regular signed Borel measures is an AL-space. Consequently its norm
is order continuous, and `M(K)` is conditionally order complete.
-/

namespace MofK

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K] in
private theorem signedMeasure_norm_add_of_nonneg {s t : MeasureTheory.SignedMeasure K}
    (hs : 0 ≤ s) (ht : 0 ≤ t) : ‖s + t‖ = ‖s‖ + ‖t‖ := by
  rw [MeasureTheory.SignedMeasure.norm_of_nonneg (add_nonneg hs ht),
    MeasureTheory.SignedMeasure.norm_of_nonneg hs,
    MeasureTheory.SignedMeasure.norm_of_nonneg ht,
    MeasureTheory.VectorMeasure.add_apply]

/-- `M(K)` is an AL-space. -/
noncomputable instance instALSpace : ALSpace (MofK K) := by
  refine ⟨?_⟩
  simp only [NNReal.coe_one, Real.rpow_one]
  intro x y hxy
  rw [← norm_abs_eq_norm (x + y), abs_add_of_isVLDisjoint hxy,
    ← norm_abs_eq_norm x, ← norm_abs_eq_norm y]
  change ‖((|x| : MofK K) : MeasureTheory.SignedMeasure K) +
      ((|y| : MofK K) : MeasureTheory.SignedMeasure K)‖ =
    ‖((|x| : MofK K) : MeasureTheory.SignedMeasure K)‖ +
      ‖((|y| : MofK K) : MeasureTheory.SignedMeasure K)‖
  exact signedMeasure_norm_add_of_nonneg (abs_nonneg x) (abs_nonneg y)

/-- The norm on `M(K)` is order continuous. -/
instance instIsOrderContinuousNorm : IsOrderContinuousNorm (MofK K) := by
  infer_instance

/-- `M(K)` is conditionally order complete. -/
noncomputable instance instConditionallyCompleteLattice :
    ConditionallyCompleteLattice (MofK K) := by
  infer_instance

end MofK

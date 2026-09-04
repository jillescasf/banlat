/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.ComplexBanachLattice.Modulus
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Complex Banach lattices

A **complex Banach lattice** is a complex normed space with a compatible conjugation whose
self-adjoint part is a real Banach lattice and whose norm is determined by the that of the
complex modulus of real and imaginary parts.
-/

open scoped ComplexStarModule

namespace ComplexBanachLattice

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [BanachLattice (selfAdjoint Z)]

/-- The lattice-valued modulus of an element of a complex Banach lattice. -/
noncomputable def modulus (z : Z) : selfAdjoint Z :=
  BanachLattice.complexModulus (ℜ z) (ℑ z)

end ComplexBanachLattice

/-- A complex Banach lattice is a complex normed star module whose self-adjoint part is a
real Banach lattice and whose norm is induced by the lattice-valued modulus. -/
class ComplexBanachLattice (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    extends BanachLattice (selfAdjoint Z) where
  coe_smul (r : ℝ) (x : selfAdjoint Z) : ((r • x : selfAdjoint Z) : Z) = r • (x : Z)
  /-- The norm is determined by the lattice-valued modulus. -/
  norm_modulus (z : Z) : ‖ComplexBanachLattice.modulus z‖ = ‖z‖

attribute [simp] ComplexBanachLattice.coe_smul

namespace ComplexBanachLattice

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexBanachLattice Z]

/-- The modulus is the least upper bound of the rotations of the real and
imaginary parts. -/
theorem modulus_isLUB (z : Z) :
    IsLUB (BanachLattice.rotationRange (ℜ z) (ℑ z)) (modulus z) := by
  exact BanachLattice.complexModulus_isLUB (ℜ z) (ℑ z)

/-- The modulus is bounded above by an element exactly when every rotation is
bounded above by that element. -/
theorem modulus_le_iff {z : Z} {x : selfAdjoint Z} :
    modulus z ≤ x ↔
      ∀ θ : ℝ, Real.cos θ • ℜ z + Real.sin θ • ℑ z ≤ x := by
  constructor
  · intro h θ
    have hr := ((modulus_isLUB z).1 ⟨θ, rfl⟩).trans h
    convert hr using 1
    ext
    simp
  · intro h
    apply (modulus_isLUB z).2
    rintro _ ⟨θ, rfl⟩
    have hr := h θ
    convert hr using 1
    ext
    simp

/-- The modulus of an element is always nonnegative. -/
theorem modulus_nonneg (z : Z) :
    0 ≤ modulus z := by
  exact BanachLattice.complexModulus_nonneg (ℜ z) (ℑ z)

/-- The modulus of zero is zero. -/
@[simp]
theorem modulus_zero :
    modulus (0 : Z) = 0 := by
  rw [modulus, map_zero, map_zero, BanachLattice.complexModulus_zero_right, abs_zero]

/-- The modulus of an element is zero if, and only if, when the element is zero. -/
@[simp]
theorem modulus_eq_zero_iff (z : Z) :
    modulus z = 0 ↔ z = 0 := by
  rw [modulus, BanachLattice.complexModulus_eq_zero_iff]
  constructor
  · rintro ⟨hre, him⟩
    rw [← realPart_add_I_smul_imaginaryPart z, hre, him]
    simp
  · rintro rfl
    exact ⟨map_zero _, map_zero _⟩

/-- Negation preserves the lattice-valued modulus. -/
@[simp]
theorem modulus_neg (z : Z) :
    modulus (-z) = modulus z := by
  rw [modulus, modulus, map_neg, map_neg, BanachLattice.complexModulus_neg_left,
    BanachLattice.complexModulus_neg_right]

/-- Conjugation preserves the lattice-valued modulus. -/
@[simp]
theorem modulus_star (z : Z) : modulus (star z) = modulus z := by
  rw [modulus, modulus]
  have hre : ℜ (star z) = ℜ z := by
    ext
    simp only [realPart_apply_coe, star_star]
    module
  have him : ℑ (star z) = -ℑ z := by
    ext
    simp [imaginaryPart_apply_coe]
    module
  rw [hre, him, BanachLattice.complexModulus_neg_right]

/-- Complex scalar multiplication scales the lattice-valued modulus by the
norm of the scalar. -/
theorem modulus_smul (c : ℂ) (z : Z) :
    modulus (c • z) = ‖c‖ • modulus z := by
  rw [modulus, realPart_smul, imaginaryPart_smul, modulus]
  have h := BanachLattice.complexModulus_linear_transform c.re c.im (ℜ z) (ℑ z)
  simp only [Complex.norm_def, Complex.normSq_apply, pow_two] at h ⊢
  convert h using 1
  all_goals first | rfl | (congr 1 <;> (ext; simp [add_comm])) | (ext; simp)

/-- The absolute value of the real part is bounded by the modulus. -/
theorem abs_realPart_le_modulus (z : Z) :
    |ℜ z| ≤ modulus z := by
  exact BanachLattice.abs_le_complexModulus_left (ℜ z) (ℑ z)

/-- The absolute value of the imaginary part is bounded by the modulus. -/
theorem abs_imaginaryPart_le_modulus (z : Z) :
    |ℑ z| ≤ modulus z := by
  exact BanachLattice.abs_le_complexModulus_right (ℜ z) (ℑ z)

/-- The modulus is bounded by the sum of the absolute values of its real and
imaginary parts. -/
theorem modulus_le_abs_realPart_add_abs_imaginaryPart (z : Z) :
    modulus z ≤ |ℜ z| + |ℑ z| := by
  exact BanachLattice.complexModulus_le_abs_add_abs (ℜ z) (ℑ z)

/-- The lattice-valued modulus satisfies the triangle inequality. -/
theorem modulus_add_le (z w : Z) :
    modulus (z + w) ≤ modulus z + modulus w := by
  rw [modulus, map_add, map_add, modulus, modulus]
  exact BanachLattice.complexModulus_add_le (ℜ z) (ℑ z) (ℜ w) (ℑ w)

/-- On self-adjoint elements, the complex modulus agrees with the lattice
absolute value. -/
@[simp]
theorem modulus_coe (x : selfAdjoint Z) :
    modulus (x : Z) = |x| := by
  rw [modulus, selfAdjoint.realPart_coe, selfAdjoint.imaginaryPart_coe,
    BanachLattice.complexModulus_zero_right]

/-- The difference of two moduli is bounded in absolute value by the modulus
of the difference. -/
theorem abs_modulus_sub_modulus_le (z w : Z) :
    |modulus z - modulus w| ≤ modulus (z - w) := by
  rw [modulus, modulus, modulus, map_sub, map_sub]
  exact BanachLattice.abs_complexModulus_sub_complexModulus_le
    (ℜ z) (ℑ z) (ℜ w) (ℑ w)

/-- The lattice-valued modulus is Lipschitz with constant one. -/
theorem norm_modulus_sub_modulus_le (z w : Z) :
    ‖modulus z - modulus w‖ ≤ ‖z - w‖ := by
  calc
    ‖modulus z - modulus w‖ ≤ ‖modulus (z - w)‖ :=
      norm_le_norm_of_abs_le_abs (by
        rw [abs_of_nonneg (modulus_nonneg (z - w))]
        exact abs_modulus_sub_modulus_le z w)
    _ = ‖z - w‖ := norm_modulus (z - w)

/-- Conjugation is isometric on a complex Banach lattice. -/
noncomputable instance instNormedStarGroup : NormedStarGroup Z := by
  constructor
  intro z
  rw [← norm_modulus (star z), modulus_star, norm_modulus]

/-- The real and imaginary parts give a real continuous linear equivalence with two copies
of the self-adjoint part. -/
noncomputable def realImagEquiv :
    Z ≃L[ℝ] selfAdjoint Z × selfAdjoint Z := by
  let e : Z ≃ₗ[ℝ] selfAdjoint Z × selfAdjoint Z := by
    refine
      { toFun := fun z ↦ (ℜ z, ℑ z)
        invFun := fun p ↦ (p.1 : Z) + Complex.I • (p.2 : Z)
        left_inv := realPart_add_I_smul_imaginaryPart
        right_inv := by
          intro p
          ext <;> simp
        map_add' := by
          intro z w
          ext <;> simp
        map_smul' := by
          intro r z
          ext <;> simp }
  refine e.toContinuousLinearEquivOfBounds 1 2 ?_ ?_
  · intro z
    simpa [Prod.norm_def] using max_le (realPart.norm_le z) (imaginaryPart.norm_le z)
  · intro p
    rw [Prod.norm_def]
    calc
      ‖e.symm p‖ ≤ ‖(p.1 : Z)‖ + ‖Complex.I • (p.2 : Z)‖ := norm_add_le _ _
      _ ≤ ‖p.1‖ + ‖p.2‖ :=
        add_le_add_right (by simpa using norm_smul_le Complex.I (p.2 : Z)) _
      _ ≤ max ‖p.1‖ ‖p.2‖ + max ‖p.1‖ ‖p.2‖ :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max ‖p.1‖ ‖p.2‖ := by ring

/-- The real-imaginary equivalence sends an element to its real and imaginary parts. -/
@[simp]
theorem realImagEquiv_apply (z : Z) :
    realImagEquiv z = (ℜ z, ℑ z) := by
  rfl

/-- The inverse real-imaginary equivalence sends `(x, y)` to `x + I • y`. -/
@[simp]
theorem realImagEquiv_symm_apply (p : selfAdjoint Z × selfAdjoint Z) :
    realImagEquiv.symm p = (p.1 : Z) + Complex.I • (p.2 : Z) := by
  rfl

/-- A complex Banach lattice is complete. -/
noncomputable instance instCompleteSpace : CompleteSpace Z := by
  let e : Z ≃L[ℝ] selfAdjoint Z × selfAdjoint Z := realImagEquiv
  exact (completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding).mpr inferInstance

end ComplexBanachLattice

/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.ComplexBanachLattice.Basic

/-!
# Morphisms between complex Banach lattices

This file defines the following classes of maps between complex Banach lattices:

* **Complex Banach-lattice homomorphisms** as complex-linear maps preserving the
lattice-valued modulus.

* **Complex Banach-lattice isometric equivalences** as complex-linear isometric
equivalences preserving the lattice-valued modulus.

We show that:
* They map self-adjoint elements into self-adjoint elements.
* They commute with conjugation, real and imaginary parts,
* They restrict to (real) homomorphisms/equivalences between the self-adjoint
parts.
-/

open scoped ComplexStarModule

/-! ## Complex Banach-lattice homomorphisms -/

/-- A **complex Banach-lattice homomorphism** is a complex-linear map preserving the
lattice-valued modulus. -/
structure ComplexBanachLatHom (Z W : Type*)
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    [ComplexBanachLattice Z]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [StarAddMonoid W] [StarModule ℂ W]
    [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
    [ComplexBanachLattice W]
    extends Z →ₗ[ℂ] W where
  map_modulus' (z : Z) :
    toLinearMap ((ComplexBanachLattice.modulus z : selfAdjoint Z) : Z) =
      ((ComplexBanachLattice.modulus
        (toLinearMap z) : selfAdjoint W) : W)

namespace ComplexBanachLatHom

variable {Z : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexBanachLattice Z]

variable {W : Type*}
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [StarAddMonoid W] [StarModule ℂ W]
  [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
  [ComplexBanachLattice W]

/-- The canonical `FunLike` instance for complex Banach-lattice homomorphisms. -/
instance instFunLike : FunLike (ComplexBanachLatHom Z W) Z W := by
  exact
    { coe := fun T => T.toLinearMap
      coe_injective := by
        intro T S h
        cases T
        cases S
        congr
        exact LinearMap.ext (congrFun h) }

/-- Complex Banach-lattice homomorphisms form a class of complex-linear maps. -/
instance instLinearMapClass :
    LinearMapClass (ComplexBanachLatHom Z W) ℂ Z W := by
  exact
    { map_add := fun T x y => T.toLinearMap.map_add x y
      map_smulₛₗ := fun T c x => T.toLinearMap.map_smul c x }

/-- Complex Banach-lattice homomorphisms preserve complex modulus. -/
@[simp]
theorem map_modulus (T : ComplexBanachLatHom Z W) (z : Z) :
    T ((ComplexBanachLattice.modulus z : selfAdjoint Z) : Z) =
      ((ComplexBanachLattice.modulus (T z) : selfAdjoint W) : W) := by
  exact T.map_modulus' z

/-- Two complex Banach-lattice homomorphisms are equal if they agree pointwise. -/
@[ext]
theorem ext {T S : ComplexBanachLatHom Z W} (h : ∀ z, T z = S z) :
    T = S := by
  exact DFunLike.coe_injective (funext h)

/-- The identity complex Banach-lattice homomorphism. -/
def id (Z : Type*)
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    [ComplexBanachLattice Z] :
    ComplexBanachLatHom Z Z :=
  { toLinearMap := LinearMap.id
    map_modulus' := by intro z; rfl }

/-- The composition of two complex Banach-lattice homomorphisms. -/
def comp {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexBanachLattice V]
    (S : ComplexBanachLatHom W V) (T : ComplexBanachLatHom Z W) :
    ComplexBanachLatHom Z V where
  toLinearMap := S.toLinearMap.comp T.toLinearMap
  map_modulus' z := by
    change S (T ((ComplexBanachLattice.modulus z : selfAdjoint Z) : Z)) =
      ((ComplexBanachLattice.modulus (S (T z)) : selfAdjoint V) : V)
    rw [T.map_modulus, S.map_modulus]

/-- Evaluation of a composition of complex Banach-lattice homomorphisms. -/
@[simp]
theorem comp_apply {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexBanachLattice V]
    (S : ComplexBanachLatHom W V) (T : ComplexBanachLatHom Z W) (z : Z) :
    S.comp T z = S (T z) := by
  rfl

/-- A complex Banach-lattice homomorphism maps self-adjoint elements to
self-adjoint elements. -/
theorem isSelfAdjoint_map (T : ComplexBanachLatHom Z W)
    (x : selfAdjoint Z) :
    IsSelfAdjoint (T (x : Z)) := by
  have isSelfAdjoint_map_of_nonneg : ∀ (y : selfAdjoint Z), 0 ≤ y →
      IsSelfAdjoint (T (y : Z)) := by
    intro y hy
    have h := T.map_modulus (y : Z)
    rw [ComplexBanachLattice.modulus_coe, abs_of_nonneg hy] at h
    rw [h]
    exact (ComplexBanachLattice.modulus (T (y : Z))).2
  rw [show (x : Z) = ((x⁺ - x⁻ : selfAdjoint Z) : Z) by
    rw [posPart_sub_negPart]]
  rw [(selfAdjoint Z).coe_sub]
  change IsSelfAdjoint
    (T.toLinearMap
      (((x⁺ : selfAdjoint Z) : Z) - ((x⁻ : selfAdjoint Z) : Z)))
  rw [map_sub]
  exact (isSelfAdjoint_map_of_nonneg x⁺ (posPart_nonneg x)).sub
    (isSelfAdjoint_map_of_nonneg x⁻ (negPart_nonneg x))

/-- A complex Banach-lattice homomorphism commutes with conjugation. -/
@[simp]
theorem map_star (T : ComplexBanachLatHom Z W) (z : Z) :
    T (star z) = star (T z) := by
  change T.toLinearMap (star z) = star (T.toLinearMap z)
  rw [← realPart_add_I_smul_imaginaryPart z]
  rw [star_add, star_smul, map_add, map_smul]
  rw [T.toLinearMap.map_add, T.toLinearMap.map_smul, star_add, star_smul]
  rw [(ℜ z).property.star_eq, (ℑ z).property.star_eq]
  have hre : IsSelfAdjoint (T.toLinearMap (ℜ z : Z)) :=
    T.isSelfAdjoint_map (ℜ z)
  have him : IsSelfAdjoint (T.toLinearMap (ℑ z : Z)) :=
    T.isSelfAdjoint_map (ℑ z)
  rw [hre.star_eq, him.star_eq]

/-- Complex Banach-lattice homomorphisms form a class of star-preserving maps. -/
instance instStarHomClass : StarHomClass (ComplexBanachLatHom Z W) Z W where
  map_star := ComplexBanachLatHom.map_star

/-- The restriction of a complex Banach-lattice homomorphism to the
self-adjoint part. -/
noncomputable def toSelfAdjointVecLatHom (T : ComplexBanachLatHom Z W) :
    VecLatHom (selfAdjoint Z) (selfAdjoint W) := by
  let L : selfAdjoint Z →ₗ[ℝ] selfAdjoint W :=
    { toFun := fun x => ⟨T (x : Z), T.isSelfAdjoint_map x⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact T.toLinearMap.map_add (x : Z) (y : Z)
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp only [ComplexBanachLattice.coe_smul]
        rw [← IsScalarTower.algebraMap_smul ℂ]
        exact T.toLinearMap.map_smul (r : ℂ) (x : Z) }
  exact VecLatHom.ofAbs L (by
    intro x
    apply Subtype.ext
    change T ((|x| : selfAdjoint Z) : Z) =
      ((|⟨T (x : Z), T.isSelfAdjoint_map x⟩| : selfAdjoint W) : W)
    rw [← ComplexBanachLattice.modulus_coe x,
      ← ComplexBanachLattice.modulus_coe
        ⟨T (x : Z), T.isSelfAdjoint_map x⟩]
    exact T.map_modulus (x : Z))

/-- Restriction to the self-adjoint part is evaluated globally. -/
@[simp]
theorem toSelfAdjointVecLatHom_apply (T : ComplexBanachLatHom Z W)
    (x : selfAdjoint Z) :
    (T.toSelfAdjointVecLatHom x : W) = T (x : Z) := by
  rfl

/-- A complex Banach-lattice homomorphism commutes with real part. -/
@[simp]
theorem map_realPart (T : ComplexBanachLatHom Z W) (z : Z) :
    T (ℜ z : Z) = (ℜ (T z) : W) :=
  _root_.map_realPart T z

/-- A complex Banach-lattice homomorphism commutes with imaginary part. -/
@[simp]
theorem map_imaginaryPart (T : ComplexBanachLatHom Z W) (z : Z) :
    T (ℑ z : Z) = (ℑ (T z) : W) :=
  _root_.map_imaginaryPart T z

/-- A complex Banach-lattice homomorphism is continuous. -/
theorem continuous (T : ComplexBanachLatHom Z W) : Continuous T := by
  have hT : Continuous T.toSelfAdjointVecLatHom :=
    Positive.continuous
      (Positive.monotone_iff.mp T.toSelfAdjointVecLatHom.monotone)
  have hre : Continuous (fun z : Z => ℜ z) := by
    apply (continuous_fst.comp
      (ComplexBanachLattice.realImagEquiv (Z := Z)).continuous).congr
    intro z
    exact congrArg Prod.fst
      (ComplexBanachLattice.realImagEquiv_apply z)
  have him : Continuous (fun z : Z => ℑ z) := by
    apply (continuous_snd.comp
      (ComplexBanachLattice.realImagEquiv (Z := Z)).continuous).congr
    intro z
    exact congrArg Prod.snd
      (ComplexBanachLattice.realImagEquiv_apply z)
  have hreal : Continuous (fun z : Z => T (ℜ z : Z)) :=
    continuous_subtype_val.comp (hT.comp hre)
  have himaginary : Continuous (fun z : Z => T (ℑ z : Z)) :=
    continuous_subtype_val.comp (hT.comp him)
  apply (hreal.add (himaginary.const_smul Complex.I)).congr
  intro z
  change T (ℜ z : Z) + Complex.I • T (ℑ z : Z) = T z
  calc
    T (ℜ z : Z) + Complex.I • T (ℑ z : Z) =
        T ((ℜ z : Z) + Complex.I • (ℑ z : Z)) := by
      rw [map_add, map_smul]
    _ = T z := congrArg T (realPart_add_I_smul_imaginaryPart z)

/-- A complex Banach-lattice homomorphism as a continuous linear map. -/
noncomputable def toContinuousLinearMap (T : ComplexBanachLatHom Z W) :
    Z →L[ℂ] W :=
  { T.toLinearMap with cont := T.continuous }

/-- Evaluation of a complex Banach-lattice homomorphism as a continuous
linear map agrees with its original evaluation. -/
@[simp]
theorem toContinuousLinearMap_apply (T : ComplexBanachLatHom Z W) (z : Z) :
    T.toContinuousLinearMap z = T z := by
  rfl

end ComplexBanachLatHom

/-! ## Complex Banach-lattice isometric equivalences -/

/-- A **complex Banach-lattice isometric equivalence** is a complex-linear isometric
equivalence that preserves the lattice-valued modulus. -/
structure ComplexBanachLatEquiv (Z W : Type*)
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    [ComplexBanachLattice Z]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [StarAddMonoid W] [StarModule ℂ W]
    [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
    [ComplexBanachLattice W]
    extends Z ≃ₗᵢ[ℂ] W where
  map_modulus' (z : Z) :
    toLinearIsometryEquiv
        ((ComplexBanachLattice.modulus z : selfAdjoint Z) : Z) =
      ((ComplexBanachLattice.modulus
        (toLinearIsometryEquiv z) : selfAdjoint W) : W)

namespace ComplexBanachLatEquiv

variable {Z : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexBanachLattice Z]

variable {W : Type*}
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [StarAddMonoid W] [StarModule ℂ W]
  [Lattice (selfAdjoint W)] [IsOrderedAddMonoid (selfAdjoint W)]
  [ComplexBanachLattice W]

/-- The canonical `EquivLike` instance for complex Banach-lattice isometric equivalences. -/
instance instEquivLike : EquivLike (ComplexBanachLatEquiv Z W) Z W where
  coe e := e.toLinearIsometryEquiv
  inv e := e.toLinearIsometryEquiv.symm
  left_inv e := e.toLinearIsometryEquiv.left_inv
  right_inv e := e.toLinearIsometryEquiv.right_inv
  coe_injective' e f h _ := by
    cases e
    cases f
    congr
    exact LinearIsometryEquiv.toLinearEquiv_injective
      (LinearEquiv.toEquiv_injective (Equiv.coe_inj.mp h))

/-- Complex Banach-lattice isometric equivalences form a class of complex-linear
isometric equivalences. -/
instance instLinearIsometryEquivClass :
    LinearIsometryEquivClass (ComplexBanachLatEquiv Z W) ℂ Z W where
  map_add := fun e x y => e.toLinearIsometryEquiv.map_add x y
  map_smulₛₗ := fun e c x => e.toLinearIsometryEquiv.map_smul c x
  norm_map := fun e x => e.toLinearIsometryEquiv.norm_map x

/-- The complex Banach-lattice homomorphism underlying an isometric equivalence. -/
def toComplexBanachLatHom (e : ComplexBanachLatEquiv Z W) :
    ComplexBanachLatHom Z W where
  toLinearMap := e.toLinearIsometryEquiv.toLinearEquiv.toLinearMap
  map_modulus' := e.map_modulus'

/-- The underlying complex Banach-lattice homomorphism has the expected value. -/
@[simp]
theorem toComplexBanachLatHom_apply
    (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e.toComplexBanachLatHom z = e z := by
  rfl

/-- Complex Banach-lattice isometric equivalences preserve the lattice-valued modulus. -/
@[simp]
theorem map_modulus (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e ((ComplexBanachLattice.modulus z : selfAdjoint Z) : Z) =
      ((ComplexBanachLattice.modulus (e z) : selfAdjoint W) : W) := by
  exact e.map_modulus' z

/-- Two complex Banach-lattice isometric equivalences are equal if they agree pointwise. -/
@[ext]
theorem ext {e f : ComplexBanachLatEquiv Z W} (h : ∀ z, e z = f z) : e = f := by
  exact DFunLike.coe_injective (funext h)

/-- The identity complex Banach-lattice isometric equivalence. -/
def refl (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    [ComplexBanachLattice Z] : ComplexBanachLatEquiv Z Z where
  toLinearIsometryEquiv := LinearIsometryEquiv.refl ℂ Z
  map_modulus' _ := rfl

/-- The inverse of a complex Banach-lattice isometric equivalence. -/
def symm (e : ComplexBanachLatEquiv Z W) : ComplexBanachLatEquiv W Z where
  toLinearIsometryEquiv := e.toLinearIsometryEquiv.symm
  map_modulus' w := by
    apply e.toLinearIsometryEquiv.injective
    rw [e.toLinearIsometryEquiv.apply_symm_apply]
    symm
    have h := e.map_modulus' (e.toLinearIsometryEquiv.symm w)
    rw [e.toLinearIsometryEquiv.apply_symm_apply] at h
    exact h

/-- The composition of two complex Banach-lattice isometric equivalences. -/
def trans {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    [Lattice (selfAdjoint V)] [IsOrderedAddMonoid (selfAdjoint V)]
    [ComplexBanachLattice V]
    (e₁ : ComplexBanachLatEquiv Z W) (e₂ : ComplexBanachLatEquiv W V) :
    ComplexBanachLatEquiv Z V where
  toLinearIsometryEquiv :=
    e₁.toLinearIsometryEquiv.trans e₂.toLinearIsometryEquiv
  map_modulus' z := by
    change e₂ (e₁ ((ComplexBanachLattice.modulus z : selfAdjoint Z) : Z)) =
      ((ComplexBanachLattice.modulus (e₂ (e₁ z)) : selfAdjoint V) : V)
    rw [e₁.map_modulus, e₂.map_modulus]

/-- A complex Banach-lattice isometric equivalence maps self-adjoint elements to
self-adjoint elements. -/
theorem isSelfAdjoint_map (e : ComplexBanachLatEquiv Z W) (x : selfAdjoint Z) :
    IsSelfAdjoint (e (x : Z)) :=
  e.toComplexBanachLatHom.isSelfAdjoint_map x

/-- A complex Banach-lattice isometric equivalence commutes with conjugation. -/
@[simp]
theorem map_star (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e (star z) = star (e z) :=
  e.toComplexBanachLatHom.map_star z

/-- Complex Banach-lattice isometric equivalences form a class of star-preserving maps. -/
instance instStarHomClass : StarHomClass (ComplexBanachLatEquiv Z W) Z W where
  map_star := ComplexBanachLatEquiv.map_star

/-- The restriction of a complex Banach-lattice isometric equivalence to
self-adjoint parts, as a real-linear isometric equivalence. -/
noncomputable def toSelfAdjointLinearIsometryEquiv (e : ComplexBanachLatEquiv Z W) :
    selfAdjoint Z ≃ₗᵢ[ℝ] selfAdjoint W where
  toFun x := ⟨e (x : Z), e.isSelfAdjoint_map x⟩
  invFun y := ⟨e.symm (y : W), e.symm.isSelfAdjoint_map y⟩
  left_inv x := by
    apply Subtype.ext
    exact e.toLinearIsometryEquiv.symm_apply_apply (x : Z)
  right_inv y := by
    apply Subtype.ext
    exact e.toLinearIsometryEquiv.apply_symm_apply (y : W)
  map_add' x y := by
    apply Subtype.ext
    exact e.toLinearIsometryEquiv.map_add (x : Z) (y : Z)
  map_smul' r x := by
    apply Subtype.ext
    simp only [ComplexBanachLattice.coe_smul]
    rw [← IsScalarTower.algebraMap_smul ℂ]
    exact e.toLinearIsometryEquiv.map_smul (r : ℂ) (x : Z)
  norm_map' x := e.toLinearIsometryEquiv.norm_map (x : Z)

/-- A complex Banach-lattice isometric equivalence commutes with real part. -/
@[simp]
theorem map_realPart (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e (ℜ z : Z) = (ℜ (e z) : W) :=
  _root_.map_realPart e z

/-- A complex Banach-lattice isometric equivalence commutes with imaginary part. -/
@[simp]
theorem map_imaginaryPart (e : ComplexBanachLatEquiv Z W) (z : Z) :
    e (ℑ z : Z) = (ℑ (e z) : W) :=
  _root_.map_imaginaryPart e z

/-- The restriction of a complex Banach-lattice isometric equivalence to the
self-adjoint parts is a Banach-lattice isometric equivalence. -/
noncomputable def toSelfAdjointBanachLatEquiv (e : ComplexBanachLatEquiv Z W) :
    BanachLatEquiv (selfAdjoint Z) (selfAdjoint W) := by
  let T := e.toSelfAdjointLinearIsometryEquiv
  let V := e.toComplexBanachLatHom.toSelfAdjointVecLatHom
  exact
    { toLinearIsometryEquiv := T
      map_sup' := V.map_sup'
      map_inf' := V.map_inf' }

/-- The Banach-lattice equivalence on self-adjoint parts has the expected underlying
real-linear isometric equivalence. -/
@[simp]
theorem toSelfAdjointBanachLatEquiv_apply (e : ComplexBanachLatEquiv Z W)
    (x : selfAdjoint Z) :
    e.toSelfAdjointBanachLatEquiv x = e.toSelfAdjointLinearIsometryEquiv x := rfl

end ComplexBanachLatEquiv

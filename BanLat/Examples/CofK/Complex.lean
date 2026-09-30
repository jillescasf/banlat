/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.AMSpace.Complex
import BanLat.ComplexBanachLattice.Complexification
import BanLat.Examples.CofK.Basic

/-!
# Complex-valued continuous functions as a complex Banach lattice

For a compact topological space `K`, this file identifies the self-adjoint part of
`C(K, ℂ)` with `C(K, ℝ)`. This identification is used to equip `C(K, ℂ)` with a
complex Banach-lattice structure and identify it with the complexification of
`C(K, ℝ)`.
-/

open scoped ComplexStarModule

namespace ContinuousMap

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The self-adjoint complex-valued continuous functions are real-linearly
isometrically equivalent to the real-valued continuous functions. -/
noncomputable def selfAdjointRealEquiv :
    selfAdjoint C(K, ℂ) ≃ₗᵢ[ℝ] C(K, ℝ) := by
  refine
    { toLinearEquiv :=
        { toFun := fun f =>
            ⟨fun t => (f.1 t).re, Complex.continuous_re.comp f.1.continuous⟩
          invFun := fun f =>
            ⟨⟨fun t => (f t : ℂ), Complex.continuous_ofReal.comp f.continuous⟩, ?_⟩
          left_inv := ?_
          right_inv := ?_
          map_add' := ?_
          map_smul' := ?_ }
      norm_map' := ?_ }
  · intro f g
    ext t
    simp
  · intro r f
    ext t
    simp
  · change IsSelfAdjoint (⟨fun t => (f t : ℂ),
      Complex.continuous_ofReal.comp f.continuous⟩ : C(K, ℂ))
    rw [isSelfAdjoint_iff]
    ext t
    simp [ContinuousMap.star_apply]
  · intro f
    apply Subtype.ext
    ext t
    have hf : star (f.1 t) = f.1 t := by
      simpa only [ContinuousMap.star_apply] using
        congrArg (fun g : C(K, ℂ) => g t) f.2.star_eq
    exact Complex.conj_eq_iff_re.mp (by simpa [Complex.star_def] using hf)
  · intro f
    ext t
    simp
  · intro f
    change ‖((⟨fun t => (f.1 t).re,
      Complex.continuous_re.comp f.1.continuous⟩ : C(K, ℝ)))‖ = ‖(f.1 : C(K, ℂ))‖
    rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
    apply iSup_congr
    intro t
    rw [Real.norm_eq_abs]
    apply Complex.abs_re_eq_norm.mpr
    have hf : star (f.1 t) = f.1 t := by
      simpa only [ContinuousMap.star_apply] using
        congrArg (fun g : C(K, ℂ) => g t) f.2.star_eq
    exact Complex.conj_eq_iff_im.mp (by simpa [Complex.star_def] using hf)

/-- The equivalence from self-adjoint complex-valued functions to real-valued
functions is given pointwise by the real part. -/
@[simp]
theorem selfAdjointRealEquiv_apply_apply
    (f : selfAdjoint C(K, ℂ)) (t : K) :
    selfAdjointRealEquiv f t = (f.1 t).re := by
  rfl

/-- Under the self-adjoint equivalence, the abstract real part is the
pointwise real part. -/
@[simp]
theorem selfAdjointRealEquiv_realPart_apply
    (f : C(K, ℂ)) (t : K) :
    selfAdjointRealEquiv (ℜ f) t = (f t).re := by
  rw [selfAdjointRealEquiv_apply_apply, realPart_apply_coe]
  simp [ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.star_apply]
  ring

/-- Under the self-adjoint equivalence, the abstract imaginary part is the
pointwise imaginary part. -/
@[simp]
theorem selfAdjointRealEquiv_imaginaryPart_apply
    (f : C(K, ℂ)) (t : K) :
    selfAdjointRealEquiv (ℑ f) t = (f t).im := by
  rw [selfAdjointRealEquiv_apply_apply]
  change ((ℑ f : C(K, ℂ)) t).re = _
  rw [imaginaryPart_apply_coe]
  simp [ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    ContinuousMap.star_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The inverse equivalence embeds a real-valued continuous function pointwise
into the complex numbers. -/
@[simp]
theorem selfAdjointRealEquiv_symm_apply_apply
    (f : C(K, ℝ)) (t : K) :
    ((selfAdjointRealEquiv.symm f : selfAdjoint C(K, ℂ)) : C(K, ℂ)) t =
      (f t : ℂ) := by
  rfl

/-! ### `selfAdjoint C(K, ℂ)` as a real Banach lattice -/

/-- The lattice structure on `selfAdjoint C(K, ℂ)` functions induced by
their identification with the real-valued functions. -/
noncomputable instance instLatticeSelfAdjoint :
    Lattice (selfAdjoint C(K, ℂ)) := by
  exact selfAdjointRealEquiv.toEquiv.lattice

/-- Addition on `selfAdjoint C(K, ℂ)` is compatible with the transported
order. -/
instance instIsOrderedAddMonoidSelfAdjoint :
    IsOrderedAddMonoid (selfAdjoint C(K, ℂ)) := by
  exact Function.Injective.isOrderedAddMonoid selfAdjointRealEquiv
    selfAdjointRealEquiv.map_add Iff.rfl

private theorem selfAdjointRealEquiv_sup
    (x y : selfAdjoint C(K, ℂ)) :
    selfAdjointRealEquiv (x ⊔ y) =
      selfAdjointRealEquiv x ⊔ selfAdjointRealEquiv y := by
  exact selfAdjointRealEquiv.apply_symm_apply _

private theorem selfAdjointRealEquiv_inf
    (x y : selfAdjoint C(K, ℂ)) :
    selfAdjointRealEquiv (x ⊓ y) =
      selfAdjointRealEquiv x ⊓ selfAdjointRealEquiv y := by
  exact selfAdjointRealEquiv.apply_symm_apply _

/-- `selfAdjoint C(K, ℂ)` forms a Banach lattice. -/
noncomputable instance instBanachLatticeSelfAdjoint :
    BanachLattice (selfAdjoint C(K, ℂ)) := by
  refine
    { smul_le_smul_of_nonneg_left := by
        intro a ha x y hxy
        change selfAdjointRealEquiv (a • x) ≤ selfAdjointRealEquiv (a • y)
        change selfAdjointRealEquiv x ≤ selfAdjointRealEquiv y at hxy
        rw [map_smul, map_smul]
        rw [ContinuousMap.le_def] at hxy ⊢
        intro t
        simp only [ContinuousMap.smul_apply]
        exact smul_le_smul_of_nonneg_left (hxy t) ha
      solid := by
        intro x y hxy
        rw [← selfAdjointRealEquiv.norm_map x, ← selfAdjointRealEquiv.norm_map y]
        apply norm_le_norm_of_abs_le_abs
        change selfAdjointRealEquiv |x| ≤ selfAdjointRealEquiv |y| at hxy
        simpa only [abs, selfAdjointRealEquiv_sup, map_neg] using hxy
      norm_smul := by
        intro r x
        rw [← selfAdjointRealEquiv.norm_map (r • x),
          ← selfAdjointRealEquiv.norm_map x, map_smul, norm_smul]
      toCompleteSpace := ?_ }
  exact
    (completeSpace_congr (e := (selfAdjointRealEquiv (K := K)).toEquiv)
      (AddMonoidHomClass.isometry_of_norm (selfAdjointRealEquiv (K := K))
        (selfAdjointRealEquiv (K := K)).norm_map).isUniformEmbedding).mpr inferInstance

/-- `selfAdjoint C(K, ℂ)` is Banach-lattice isometrically equivalent to `C(K, ℝ)`. -/
noncomputable def selfAdjointBanachLatEquiv :
    BanachLatEquiv (selfAdjoint C(K, ℂ)) C(K, ℝ) := by
  exact
    { toLinearIsometryEquiv := selfAdjointRealEquiv
      map_sup' := selfAdjointRealEquiv_sup
      map_inf' := selfAdjointRealEquiv_inf }

/-- `selfAdjointBanachLatEquiv` is defined pointwise by the real part. -/
@[simp]
theorem selfAdjointBanachLatEquiv_apply_apply
    (f : selfAdjoint C(K, ℂ)) (t : K) :
    selfAdjointBanachLatEquiv f t = (f.1 t).re := by
  rfl

/-! ### Complex Banach-lattice structure -/

/-- Under `selfAdjointRealEquiv`, the lattice-valued modulus is the
pointwise complex norm. -/
@[simp]
theorem selfAdjointRealEquiv_modulus_apply
    (f : C(K, ℂ)) (t : K) :
    selfAdjointRealEquiv (ComplexBanachLattice.modulus f) t = ‖f t‖ := by
  change selfAdjointRealEquiv
      (BanachLattice.complexModulus (ℜ f) (ℑ f)) t = ‖f t‖
  change selfAdjointBanachLatEquiv.toVecLatEquiv
      (BanachLattice.complexModulus (ℜ f) (ℑ f)) t = ‖f t‖
  have h := congrArg (fun g : C(K, ℝ) => g t)
    (VecLatEquiv.map_complexModulus selfAdjointBanachLatEquiv.toVecLatEquiv
      (ℜ f) (ℑ f))
  rw [h]
  change BanachLattice.complexModulus (selfAdjointBanachLatEquiv (ℜ f))
      (selfAdjointBanachLatEquiv (ℑ f)) t = ‖f t‖
  rw [BanachLattice.complexModulus_apply,
    selfAdjointBanachLatEquiv_apply_apply,
    selfAdjointBanachLatEquiv_apply_apply,
    realPart_apply_coe, imaginaryPart_apply_coe]
  simp [ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.star_apply, Complex.mul_re, Complex.mul_im]
  ring_nf
  rw [← Complex.norm_eq_sqrt_sq_add_sq (f t)]

/-- `C(K, ℂ)` forms a complex Banach lattice. -/
noncomputable instance instComplexBanachLattice :
    ComplexBanachLattice C(K, ℂ) := by
  refine { coe_smul := ?_, norm_modulus := ?_ }
  · intro r x
    simp
  · intro f
    rw [← (selfAdjointRealEquiv (K := K)).norm_map]
    rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
    apply iSup_congr
    intro t
    rw [selfAdjointRealEquiv_modulus_apply]
    simp

private theorem selfAdjointRealEquiv_le_iff
    {x y : selfAdjoint C(K, ℂ)} :
    x ≤ y ↔ (selfAdjointBanachLatEquiv (K := K)) x ≤
      (selfAdjointBanachLatEquiv (K := K)) y := by
  let e := selfAdjointBanachLatEquiv (K := K)
  constructor
  · intro hxy
    change e.toVecLatEquiv.toVecLatHom x ≤ e.toVecLatEquiv.toVecLatHom y
    exact e.toVecLatEquiv.toVecLatHom.monotone hxy
  · intro hxy
    apply e.toVecLatEquiv.toVecLatHom.le_of_map_le e.injective
    change e.toVecLatEquiv.toVecLatHom x ≤ e.toVecLatEquiv.toVecLatHom y at hxy
    exact hxy

private theorem selfAdjointRealEquiv_symm_one_strongOrderUnit :
    StrongOrderUnit
      ((selfAdjointBanachLatEquiv (K := K)).toLinearIsometryEquiv.symm (1 : C(K, ℝ))) := by
  let e := selfAdjointBanachLatEquiv (K := K)
  have hone : StrongOrderUnit (1 : C(K, ℝ)) := by
    change StrongOrderUnit (AMSpaceWithUnit.unit : C(K, ℝ))
    exact AMSpaceWithUnit.strongOrderUnit_unit'
  refine ⟨?_, ?_⟩
  · apply (selfAdjointRealEquiv_le_iff (K := K)).mpr
    change e.toLinearIsometryEquiv 0 ≤
      e.toLinearIsometryEquiv (e.toLinearIsometryEquiv.symm 1)
    rw [map_zero, e.toLinearIsometryEquiv.apply_symm_apply]
    exact hone.1
  · intro x
    obtain ⟨c, hc, hcx⟩ := hone.2 (e x)
    refine ⟨c, hc, (selfAdjointRealEquiv_le_iff (K := K)).mpr ?_⟩
    have habs : e.toLinearIsometryEquiv |x| =
        |e.toLinearIsometryEquiv x| :=
      e.toVecLatEquiv.toVecLatHom.map_abs x
    have hsmul : e.toLinearIsometryEquiv
        (c • e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))) =
        c • (1 : C(K, ℝ)) := by
      rw [map_smul, e.toLinearIsometryEquiv.apply_symm_apply]
    change e.toLinearIsometryEquiv |x| ≤
      e.toLinearIsometryEquiv
        (c • e.toLinearIsometryEquiv.symm (1 : C(K, ℝ)))
    rwa [habs, hsmul]

private theorem gaugeNorm_selfAdjointRealEquiv_symm_one
    (x : selfAdjoint C(K, ℂ)) :
    OrderIdeal.gaugeNorm
        ((selfAdjointBanachLatEquiv (K := K)).toLinearIsometryEquiv.symm (1 : C(K, ℝ))) x =
      OrderIdeal.gaugeNorm (1 : C(K, ℝ))
        ((selfAdjointBanachLatEquiv (K := K)) x) := by
  let e := selfAdjointBanachLatEquiv (K := K)
  unfold OrderIdeal.gaugeNorm
  apply congrArg sInf
  ext c
  simp only [Set.mem_setOf_eq]
  have habs : e.toLinearIsometryEquiv |x| =
      |e.toLinearIsometryEquiv x| :=
    e.toVecLatEquiv.toVecLatHom.map_abs x
  have hunit : e.toLinearIsometryEquiv
      |e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))| = |(1 : C(K, ℝ))| := by
    calc
      e.toLinearIsometryEquiv |e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))| =
          |e.toLinearIsometryEquiv
            (e.toLinearIsometryEquiv.symm (1 : C(K, ℝ)))| :=
        e.toVecLatEquiv.toVecLatHom.map_abs _
      _ = |(1 : C(K, ℝ))| := by rw [e.toLinearIsometryEquiv.apply_symm_apply]
  have hsmul : e.toLinearIsometryEquiv
      (c • |e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))|) =
      c • |(1 : C(K, ℝ))| := by
    rw [map_smul, hunit]
  constructor
  · rintro ⟨hc, hx⟩
    refine ⟨hc, ?_⟩
    have hx' : e.toLinearIsometryEquiv |x| ≤ e.toLinearIsometryEquiv
        (c • |e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))|) :=
      e.toVecLatEquiv.toVecLatHom.monotone hx
    rwa [habs, hsmul] at hx'
  · rintro ⟨hc, hx⟩
    refine ⟨hc, (selfAdjointRealEquiv_le_iff (K := K)).mpr ?_⟩
    change e.toLinearIsometryEquiv |x| ≤ e.toLinearIsometryEquiv
      (c • |e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))|)
    rwa [habs, hsmul]

/-- With the constant-one function, `C(K, ℂ)` is a complex AM-space with unit. -/
noncomputable instance instComplexAMSpaceWithUnit :
    ComplexAMSpaceWithUnit C(K, ℂ) where
  norm_add_eq_max_of_inf_eq_zero {x y} hxy := by
    let e := selfAdjointBanachLatEquiv (K := K)
    rw [← e.norm_map (x + y), map_add, ← e.norm_map x, ← e.norm_map y]
    apply AMSpace.norm_add_eq_max_of_inf_eq_zero
    exact e.toVecLatEquiv.toVecLatHom.map_disjoint hxy
  unit := (selfAdjointBanachLatEquiv (K := K)).toLinearIsometryEquiv.symm
    (1 : C(K, ℝ))
  strongOrderUnit_unit := selfAdjointRealEquiv_symm_one_strongOrderUnit
  norm_eq_gaugeNorm x := by
    let e := selfAdjointBanachLatEquiv (K := K)
    calc
      ‖x‖ = ‖e x‖ := (e.norm_map x).symm
      _ = OrderIdeal.gaugeNorm (1 : C(K, ℝ)) (e x) := by
        change ‖e x‖ =
          OrderIdeal.gaugeNorm (AMSpaceWithUnit.unit : C(K, ℝ)) (e x)
        exact AMSpaceWithUnit.norm_eq_gaugeNorm (e x)
      _ = OrderIdeal.gaugeNorm (e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))) x :=
        (gaugeNorm_selfAdjointRealEquiv_symm_one x).symm

/-- The distinguished unit of `C(K, ℂ)` is the constant-one function. -/
@[simp]
theorem complexAMSpaceWithUnit_unit_apply (t : K) :
    ((ComplexAMSpaceWithUnit.unit : selfAdjoint C(K, ℂ)) : C(K, ℂ)) t = 1 := by
  rfl

/-- The lattice-valued modulus of a complex-valued continuous function is its
pointwise norm. -/
@[simp]
theorem modulus_apply
    (f : C(K, ℂ)) (t : K) :
    ((ComplexBanachLattice.modulus f :
        selfAdjoint C(K, ℂ)) : C(K, ℂ)) t =
      (‖f t‖ : ℂ) := by
  apply Complex.ext
  · exact selfAdjointRealEquiv_modulus_apply f t
  · have hf := (ComplexBanachLattice.modulus f).2.star_eq
    have h := congrArg (fun g : C(K, ℂ) => g t) hf
    apply Complex.conj_eq_iff_im.mp
    change star ((ComplexBanachLattice.modulus f).1 t) =
      (ComplexBanachLattice.modulus f).1 t at h
    exact h

/-! ### Identification with the complexification -/

/-- The complexification of `C(K, ℝ)` is complex-Banach-lattice isometrically
equivalent to the `C(K, ℂ)`. -/
noncomputable def complexificationEquiv :
    ComplexBanachLatEquiv
      (Complexification C(K, ℝ))
      C(K, ℂ) := by
  exact ComplexBanachLatEquiv.ofSelfAdjointBanachLatEquiv
    (Complexification.selfAdjointBanachLatEquiv.trans
      selfAdjointBanachLatEquiv.symm)

/-- The complexification equivalence combines the real and imaginary
coordinates pointwise. -/
@[simp]
theorem complexificationEquiv_apply_apply
    (z : Complexification C(K, ℝ)) (t : K) :
    complexificationEquiv z t =
      (z.re t : ℂ) + Complex.I * z.im t := by
  rw [complexificationEquiv,
    ComplexBanachLatEquiv.ofSelfAdjointBanachLatEquiv_apply,
    ContinuousMap.add_apply, ContinuousMap.smul_apply]
  have hre :
      (Complexification.selfAdjointBanachLatEquiv.trans
        selfAdjointBanachLatEquiv.symm) (ℜ z) =
        selfAdjointRealEquiv.symm z.re := by
    apply (selfAdjointRealEquiv (K := K)).injective
    change Complexification.selfAdjointEquiv (ℜ z) = z.re
    exact Complexification.selfAdjointEquiv_realPart z
  have him :
      (Complexification.selfAdjointBanachLatEquiv.trans
        selfAdjointBanachLatEquiv.symm) (ℑ z) =
        selfAdjointRealEquiv.symm z.im := by
    apply (selfAdjointRealEquiv (K := K)).injective
    change Complexification.selfAdjointEquiv (ℑ z) = z.im
    exact Complexification.selfAdjointEquiv_imaginaryPart z
  rw [hre, him, selfAdjointRealEquiv_symm_apply_apply,
    selfAdjointRealEquiv_symm_apply_apply]
  simp

/-- The real coordinate of the inverse complexification equivalence is the
pointwise real part. -/
@[simp]
theorem complexificationEquiv_symm_re_apply
    (f : C(K, ℂ)) (t : K) :
    (complexificationEquiv.symm f).re t = (f t).re := by
  have h := complexificationEquiv_apply_apply (complexificationEquiv.symm f) t
  have hinv := congrArg (fun g : C(K, ℂ) => g t)
    (complexificationEquiv.apply_symm_apply f)
  have h' : f t =
      ((complexificationEquiv.symm f).re t : ℂ) +
        Complex.I * (complexificationEquiv.symm f).im t := by
    exact hinv.symm.trans h
  have hre := congrArg Complex.re h'
  simpa using hre.symm

/-- The imaginary coordinate of the inverse complexification equivalence is the
pointwise imaginary part. -/
@[simp]
theorem complexificationEquiv_symm_im_apply
    (f : C(K, ℂ)) (t : K) :
    (complexificationEquiv.symm f).im t = (f t).im := by
  have h := complexificationEquiv_apply_apply (complexificationEquiv.symm f) t
  have hinv := congrArg (fun g : C(K, ℂ) => g t)
    (complexificationEquiv.apply_symm_apply f)
  have h' : f t =
      ((complexificationEquiv.symm f).re t : ℂ) +
        Complex.I * (complexificationEquiv.symm f).im t := by
    exact hinv.symm.trans h
  have him := congrArg Complex.im h'
  simpa using him.symm

end ContinuousMap

/-
Authors: Jesús Illescas-Fiorito
-/

import Mathlib.Order.ModularLattice
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.SymmDiff
import Mathlib.Tactic.Order

/-!
# Boolean algebras

This file add some basic constructions for Boolean algebras that are missing in mathlib:
* principal intervals `Set.Iic a = {b ∈ B, b ≤ a}`, `a ∈ B`, become Boolean algebras with
the induced structure.
* the increasing union over a (non-empty) linearly ordered set `{A i, i ∈ ι}` of Boolean
subalgebras becomes as well a Boolean subalgebra.
-/

universe u

open scoped symmDiff

variable {B : Type u} [BooleanAlgebra B]

/-- Let `a, x, y ∈ B`. If `a ⊓ x = a ⊓ y` and `aᶜ ⊓ x = aᶜ ⊓ y`, then `x=y`. -/
theorem eq_of_inf_eq_inf_compl {a x y : B}
    (ha : a ⊓ x = a ⊓ y) (hac : aᶜ ⊓ x = aᶜ ⊓ y) : x = y := by
  calc
    x = (a ⊔ aᶜ) ⊓ x := by simp
    _ = (a ⊓ x) ⊔ (aᶜ ⊓ x) := inf_sup_right ..
    _ = (a ⊓ y) ⊔ (aᶜ ⊓ y) := by rw [ha, hac]
    _ = (a ⊔ aᶜ) ⊓ y := (inf_sup_right ..).symm
    _ = y := by simp

/-- Let `a, b, c ∈ B`. Then `a ⊓ ((a ⊓ b) ⊔ (aᶜ ⊓ c)) = a ⊓ b`. -/
theorem inf_conditional (a b c : B) :
    a ⊓ ((a ⊓ b) ⊔ (aᶜ ⊓ c)) = a ⊓ b := by
  rw [inf_sup_left]
  have h : a ⊓ (aᶜ ⊓ c) = ⊥ := eq_bot_iff.2 <| calc
    a ⊓ (aᶜ ⊓ c) ≤ a ⊓ aᶜ := inf_le_inf_left a inf_le_left
    _ = ⊥ := inf_compl_eq_bot
  rw [h]
  simp

/-- Let `a, b, c ∈ B`. Then `aᶜ ⊓ ((a ⊓ b) ⊔ (aᶜ ⊓ c)) = aᶜ ⊓ c`. -/
theorem compl_inf_conditional (a b c : B) :
    aᶜ ⊓ ((a ⊓ b) ⊔ (aᶜ ⊓ c)) = aᶜ ⊓ c := by
  rw [inf_sup_left]
  have h : aᶜ ⊓ (a ⊓ b) = ⊥ := eq_bot_iff.2 <| calc
    aᶜ ⊓ (a ⊓ b) ≤ aᶜ ⊓ a := inf_le_inf_left aᶜ inf_le_left
    _ = ⊥ := compl_inf_eq_bot
  rw [h]
  simp

/-- Let `a, b, c ∈ B`. Then `(a ⊓ bᶜ) ⊔ (aᶜ ⊓ cᶜ) = ((a ⊓ b) ⊔ (aᶜ ⊓ c))ᶜ`. -/
theorem conditional_compl (a b c : B) :
    (a ⊓ bᶜ) ⊔ (aᶜ ⊓ cᶜ) = ((a ⊓ b) ⊔ (aᶜ ⊓ c))ᶜ := by
  apply eq_of_inf_eq_inf_compl (a := a)
  · rw [inf_conditional, compl_sup, compl_inf, compl_inf, compl_compl]
    symm
    calc
      a ⊓ ((aᶜ ⊔ bᶜ) ⊓ (a ⊔ cᶜ)) =
          (a ⊓ (aᶜ ⊔ bᶜ)) ⊓ (a ⊔ cᶜ) := (inf_assoc ..).symm
      _ = ((a ⊓ aᶜ) ⊔ (a ⊓ bᶜ)) ⊓ (a ⊔ cᶜ) :=
        congrArg (fun x ↦ x ⊓ (a ⊔ cᶜ)) (inf_sup_left ..)
      _ = (a ⊓ bᶜ) ⊓ (a ⊔ cᶜ) := by simp
      _ = a ⊓ bᶜ := inf_eq_left.2 (le_trans inf_le_left le_sup_left)
  · rw [compl_inf_conditional, compl_sup, compl_inf, compl_inf, compl_compl]
    symm
    calc
      aᶜ ⊓ ((aᶜ ⊔ bᶜ) ⊓ (a ⊔ cᶜ)) =
          (aᶜ ⊓ (aᶜ ⊔ bᶜ)) ⊓ (a ⊔ cᶜ) := (inf_assoc ..).symm
      _ = aᶜ ⊓ (a ⊔ cᶜ) := congrArg (fun x ↦ x ⊓ (a ⊔ cᶜ))
        (inf_eq_left.2 le_sup_left)
      _ = (aᶜ ⊓ a) ⊔ (aᶜ ⊓ cᶜ) := inf_sup_left ..
      _ = aᶜ ⊓ cᶜ := by simp

/-- Taking suprema is Lipschitz with respect to the order-valued symmetric difference. -/
theorem symmDiff_sup_le_sup (a b c d : B) :
    (a ⊔ b) ∆ (c ⊔ d) ≤ (a ∆ c) ⊔ (b ∆ d) := by
  apply symmDiff_le
  · have ha := le_symmDiff_sup_right a c
    have hb := le_symmDiff_sup_right b d
    order
  · have hc := le_symmDiff_sup_right c a
    have hd := le_symmDiff_sup_right d b
    rw [symmDiff_comm c a] at hc
    rw [symmDiff_comm d b] at hd
    order

namespace Set.Iic

noncomputable instance instDistribLattice {a : B} : DistribLattice (Set.Iic a) :=
  Subtype.distribLattice
    (fun _ _ hx hy ↦ sup_le hx hy)
    (fun _ _ hx _ ↦ inf_le_left.trans hx)

noncomputable instance instBooleanAlgebra {a : B} : BooleanAlgebra (Set.Iic a) :=
  DistribLattice.booleanAlgebraOfComplemented (Set.Iic a)

/-- In the principal interval below `a`, the complement of `b` is `a \ b`. -/
@[simp]
theorem coe_compl {a : B} (b : Set.Iic a) :
    ((bᶜ : Set.Iic a) : B) = a \ (b : B) := by
  have hb := Set.Iic.isCompl_iff.mp (isCompl_compl (x := b))
  exact (hb.1.sdiff_eq_of_sup_eq hb.2).symm

/-- Boolean difference in a principal interval agrees with Boolean difference
in the ambient algebra. -/
@[simp]
theorem coe_sdiff {a : B} (b c : Set.Iic a) :
    ((b \ c : Set.Iic a) : B) = (b : B) \ (c : B) := by
  rw [show b \ c = b ⊓ cᶜ from _root_.sdiff_eq]
  change (b : B) ⊓ ((cᶜ : Set.Iic a) : B) = (b : B) \ (c : B)
  rw [coe_compl, ← inf_sdiff_assoc, inf_eq_left.mpr b.property]

/-- Symmetric difference in a principal interval agrees with symmetric
difference in the ambient algebra. -/
@[simp]
theorem coe_symmDiff {a : B} (b c : Set.Iic a) :
    ((symmDiff b c : Set.Iic a) : B) = symmDiff (b : B) (c : B) := by
  simp [symmDiff_def]

end Set.Iic

namespace BooleanSubalgebra

/-- Let `(A i)_{i ∈ ι}` be an increasing family of Boolean subalgebras of `B`, indexed
by a nonempty linear order `ι`. Then `increasingUnion A hA` is the Boolean subalgebra
of `B` whose underlying set is `⋃ i, A i`. -/
noncomputable def increasingUnion {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (A : ι → BooleanSubalgebra B) (hA : Monotone A) : BooleanSubalgebra B where
  carrier := ⋃ i, (A i : Set B)
  bot_mem' := Set.mem_iUnion.2
    ⟨Classical.choice inferInstance, (A _).bot_mem⟩
  compl_mem' := by
    rintro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨i, (A i).compl_mem hi⟩
  supClosed' := by
    rintro x hx y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
    exact Set.mem_iUnion.2 ⟨max i j, (A (max i j)).sup_mem
      (hA (le_max_left i j) hi) (hA (le_max_right i j) hj)⟩
  infClosed' := by
    rintro x hx y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
    exact Set.mem_iUnion.2 ⟨max i j, (A (max i j)).inf_mem
      (hA (le_max_left i j) hi) (hA (le_max_right i j) hj)⟩

end BooleanSubalgebra

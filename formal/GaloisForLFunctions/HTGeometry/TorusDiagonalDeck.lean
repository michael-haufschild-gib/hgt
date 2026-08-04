import GaloisForLFunctions.HTGeometry.TorusDiagonal
import GaloisForLFunctions.HTGeometry.MultiplicativeProtocolAlgClosed
import GaloisForLFunctions.HTGeometry.DeckDegreeUpperBound

/-!
# The deck group of a diagonal torus isogeny

The constant torus acts on a freely generated differential field by coordinatewise scaling; the
kernel of a diagonal integer matrix is the product of the groups of roots of unity of its exponents,
of order the product of their absolute values when the constants are algebraically closed.

That order matches the degree bound of the diagonal substitution, so Artin's theorem identifies the
prefix image of a diagonal torus isogeny with the fixed field of its deck group -- the rank-`r`
form of the multiplicative deck identity.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

section Kernel

variable {C : Type*} [Field C] {r : ℕ}

/-- The coordinatewise power map of the constant torus. -/
def torusPowerHom (C : Type*) [Field C] {r : ℕ} (d : Fin r → ℤ) :
    (Fin r → Cˣ) →* (Fin r → Cˣ) where
  toFun u := fun i ↦ (u i) ^ (d i)
  map_one' := by
    funext i
    simp
  map_mul' u v := by
    funext i
    simp [mul_zpow]

theorem mem_ker_torusPowerHom_iff (d : Fin r → ℤ) (u : Fin r → Cˣ) :
    u ∈ (torusPowerHom C d).ker ↔ ∀ i, (u i) ^ (d i) = 1 := by
  constructor
  · intro hu i
    exact congrFun hu i
  · intro hu
    funext i
    exact hu i

/-- Membership in the deck kernel is a root-of-unity condition in each coordinate. -/
theorem mem_ker_torusPowerHom_iff_natAbs {d : Fin r → ℤ} (u : Fin r → Cˣ) :
    u ∈ (torusPowerHom C d).ker ↔ ∀ i, (u i) ∈ rootsOfUnity ((d i).natAbs) C := by
  rw [mem_ker_torusPowerHom_iff]
  refine forall_congr' fun i ↦ ?_
  rw [mem_rootsOfUnity]
  rcases le_or_gt 0 (d i) with hpos | hneg
  · rw [← zpow_natCast, show (((d i).natAbs : ℕ) : ℤ) = d i by omega]
  · rw [← zpow_natCast, show (((d i).natAbs : ℕ) : ℤ) = -(d i) by omega, zpow_neg,
      inv_eq_one]

/-- The deck kernel of a diagonal isogeny is the product of the root-of-unity groups. -/
def kerTorusPowerHomEquiv {d : Fin r → ℤ} :
    ↥((torusPowerHom C d).ker) ≃ (∀ i, ↥(rootsOfUnity ((d i).natAbs) C)) where
  toFun u := fun i ↦ ⟨(u : Fin r → Cˣ) i,
    ((mem_ker_torusPowerHom_iff_natAbs _).mp u.2) i⟩
  invFun v := ⟨fun i ↦ ((v i : Cˣ)),
    (mem_ker_torusPowerHom_iff_natAbs _).mpr fun i ↦ (v i).2⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    rfl
  right_inv v := by
    funext i
    apply Subtype.ext
    rfl

/-- **The order of the deck group of a diagonal isogeny.** -/
theorem card_ker_torusPowerHom [IsAlgClosed C] [CharZero C] {d : Fin r → ℤ}
    (hd : ∀ i, d i ≠ 0) :
    Nat.card ((torusPowerHom C d).ker) = ∏ i, (d i).natAbs := by
  classical
  have hcard : ∀ i, Nat.card (↥(rootsOfUnity ((d i).natAbs) C)) = (d i).natAbs := by
    intro i
    have hpos : 0 < (d i).natAbs := Int.natAbs_pos.mpr (hd i)
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosed C hpos
    haveI : NeZero ((d i).natAbs) := ⟨hpos.ne'⟩
    simpa [Nat.card_eq_fintype_card] using hζ.card_rootsOfUnity
  rw [Nat.card_congr (kerTorusPowerHomEquiv (C := C) (d := d)), Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ ↦ hcard i

instance finite_ker_torusPowerHom [IsAlgClosed C] [CharZero C] {d : Fin r → ℤ}
    [∀ i, NeZero ((d i).natAbs)] : Finite ((torusPowerHom C d).ker) := by
  classical
  exact Finite.of_equiv _ (kerTorusPowerHomEquiv (C := C) (d := d)).symm

end Kernel

section Deck

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E] [CharZero C] [IsAlgClosed C]

variable {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

include hx hgen in
/-- **The prefix image of a diagonal torus isogeny is the fixed field of its deck group.**  The
degree bound of the diagonal substitution matches the order of the kernel of the matrix on the
constant torus, so Artin's theorem turns the estimate into an identity. -/
theorem differentialAdjoin_diagonal_eq_fixedField {d : Fin r → ℤ} (hd : ∀ i, d i ≠ 0) :
    differentialAdjoin C (Set.range (monomialFamily (Matrix.diagonal d) x))
      = IntermediateField.fixedField
          (((torusPowerHom C d).ker).map (torusScaleRep hx hgen)) := by
  classical
  haveI : ∀ i, NeZero ((d i).natAbs) := fun i ↦ ⟨(Int.natAbs_pos.mpr (hd i)).ne'⟩
  haveI hfinker : Finite ((torusPowerHom C d).ker) := finite_ker_torusPowerHom
  haveI hfin : Finite (((torusPowerHom C d).ker).map (torusScaleRep hx hgen)) :=
    Finite.of_equiv _ (Subgroup.equivMapOfInjective _ _ (torusScaleRep_injective hx hgen)).toEquiv
  haveI : Fintype (((torusPowerHom C d).ker).map (torusScaleRep hx hgen)) := Fintype.ofFinite _
  have hx0 : ∀ i, x i ≠ 0 := torus_palette_ne_zero hx
  -- the prefix image is finite dimensional in the ambient field
  have hpowmem : ∀ i, x i ^ d i
      ∈ differentialAdjoin C (Set.range (monomialFamily (Matrix.diagonal d) x)) := by
    intro i
    rw [← monomialFamily_diagonal_apply d i]
    exact subset_differentialAdjoin C _ (Set.mem_range_self i)
  have hint : ∀ z ∈ Set.range x, IsIntegral
      (↥(differentialAdjoin C (Set.range (monomialFamily (Matrix.diagonal d) x)))) z := by
    rintro _ ⟨i, rfl⟩
    have hz : x i ^ ((d i).natAbs)
        ∈ differentialAdjoin C (Set.range (monomialFamily (Matrix.diagonal d) x)) := by
      have hzz : x i ^ (((d i).natAbs : ℕ) : ℤ)
          ∈ differentialAdjoin C (Set.range (monomialFamily (Matrix.diagonal d) x)) := by
        rcases le_or_gt 0 (d i) with hpos | hneg
        · rw [show ((((d i).natAbs : ℕ)) : ℤ) = d i by omega]
          exact hpowmem i
        · rw [show ((((d i).natAbs : ℕ)) : ℤ) = -(d i) by omega, zpow_neg]
          exact inv_mem (hpowmem i)
      rwa [zpow_natCast] at hzz
    exact isIntegral_of_pow_mem (α := x i)
      (c := (⟨x i ^ ((d i).natAbs), hz⟩ :
        ↥(differentialAdjoin C (Set.range (monomialFamily (Matrix.diagonal d) x)))))
      (Int.natAbs_pos.mpr (hd i)) rfl
  haveI : Finite (Set.range x) := Set.finite_range x
  haveI hfd0 : FiniteDimensional
      (↥(differentialAdjoin C (Set.range (monomialFamily (Matrix.diagonal d) x))))
      ↥(IntermediateField.adjoin
        (↥(differentialAdjoin C (Set.range (monomialFamily (Matrix.diagonal d) x))))
        (Set.range x)) := IntermediateField.finiteDimensional_adjoin hint
  rw [adjoin_diagonal_eq_top hx hgen hd] at hfd0
  haveI hfd : FiniteDimensional
      (↥(differentialAdjoin C (Set.range (monomialFamily (Matrix.diagonal d) x)))) E :=
    (IntermediateField.topEquiv.toLinearEquiv).finiteDimensional
  -- the deck group fixes the prefix image
  have hfix := differentialAdjoin_monomialFamily_le_fixedField hx hgen (Matrix.diagonal d)
    ((torusPowerHom C d).ker) (fun u hu i ↦ by
      rw [monomialFamily_diagonal_apply]
      have hz := (mem_ker_torusPowerHom_iff d u).mp hu i
      have hcoe := congrArg (fun w : Cˣ ↦ (w : C)) hz
      simpa using hcoe)
  -- the degree matches the order
  have hle : Module.finrank
      (↥(differentialAdjoin C (Set.range (monomialFamily (Matrix.diagonal d) x)))) E
      ≤ Nat.card (((torusPowerHom C d).ker).map (torusScaleRep hx hgen)) := by
    have hcard : Nat.card (((torusPowerHom C d).ker).map (torusScaleRep hx hgen))
        = ∏ i, (d i).natAbs := by
      rw [← Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ (torusScaleRep_injective hx hgen)).toEquiv]
      exact card_ker_torusPowerHom hd
    rw [hcard]
    exact finrank_diagonal_le_prod hx hgen hd
  exact eq_fixedField_of_finrank_le _ _ hfix hle

end Deck

end

end GaloisForLFunctions.HTGeometry

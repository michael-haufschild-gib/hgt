import GaloisForLFunctions.HTGeometry.TorusGeneralDegree
import GaloisForLFunctions.HTGeometry.TorusDiagonalDeck

/-!
# The deck group of an arbitrary torus isogeny

An integer matrix acts on the constant torus by monomial substitution.  Smith normal form conjugates
that action into a diagonal one, so the kernel has order the absolute determinant when the constants
are algebraically closed.

Matching that order against the degree bound of the substitution identifies the prefix image of an
arbitrary torus isogeny with the fixed field of its deck group.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

section Group

variable {C : Type*} [Field C] {r : ℕ}

/-- The monomial substitution action of an integer matrix on the constant torus. -/
def torusMonomialHom (C : Type*) [Field C] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) :
    (Fin r → Cˣ) →* (Fin r → Cˣ) where
  toFun u := fun i ↦ ∏ j, (u j) ^ (M i j)
  map_one' := by
    funext i
    simp
  map_mul' u v := by
    funext i
    simp [mul_zpow, Finset.prod_mul_distrib]

theorem coe_torusMonomialHom (M : Matrix (Fin r) (Fin r) ℤ) (u : Fin r → Cˣ) (i : Fin r) :
    ((torusMonomialHom C M u i : Cˣ) : C) = monomialFamily M (fun j ↦ ((u j : C))) i := by
  rw [monomialFamily_apply]
  change ((∏ j, (u j) ^ (M i j) : Cˣ) : C) = _
  push_cast
  rfl

theorem torusMonomialHom_diagonal (d : Fin r → ℤ) :
    torusMonomialHom C (Matrix.diagonal d) = torusPowerHom C d := by
  refine MonoidHom.ext fun u ↦ ?_
  funext i
  apply Units.ext
  have h := coe_torusMonomialHom (C := C) (Matrix.diagonal d) u i
  rw [monomialFamily_diagonal_apply] at h
  rw [h]
  change _ = (((u i) ^ (d i) : Cˣ) : C)
  push_cast
  rfl

theorem torusMonomialHom_mul (M N : Matrix (Fin r) (Fin r) ℤ) :
    torusMonomialHom C (M * N) = (torusMonomialHom C M).comp (torusMonomialHom C N) := by
  refine MonoidHom.ext fun u ↦ ?_
  funext i
  apply Units.ext
  have hne : ∀ j, ((u j : C)) ≠ 0 := fun j ↦ (u j).ne_zero
  have hmid : (fun j ↦ (((torusMonomialHom C N u) j : Cˣ) : C))
      = monomialFamily N (fun j ↦ ((u j : C))) := by
    funext j
    exact coe_torusMonomialHom (C := C) N u j
  calc ((torusMonomialHom C (M * N) u i : Cˣ) : C)
      = monomialFamily (M * N) (fun j ↦ ((u j : C))) i := coe_torusMonomialHom _ _ _
    _ = monomialFamily M (monomialFamily N (fun j ↦ ((u j : C)))) i := by
        rw [monomialFamily_mul _ _ hne]
    _ = monomialFamily M (fun j ↦ (((torusMonomialHom C N u) j : Cˣ) : C)) i := by rw [hmid]
    _ = ((torusMonomialHom C M (torusMonomialHom C N u) i : Cˣ) : C) :=
        (coe_torusMonomialHom _ _ _).symm

@[simp] theorem torusMonomialHom_one :
    torusMonomialHom C (1 : Matrix (Fin r) (Fin r) ℤ) = MonoidHom.id _ := by
  refine MonoidHom.ext fun u ↦ ?_
  funext i
  apply Units.ext
  have h := coe_torusMonomialHom (C := C) (1 : Matrix (Fin r) (Fin r) ℤ) u i
  rw [show monomialFamily (1 : Matrix (Fin r) (Fin r) ℤ) (fun j ↦ ((u j : C)))
      = (fun j ↦ ((u j : C))) from monomialFamily_one _] at h
  exact h

/-- A unimodular substitution acts bijectively on the constant torus. -/
theorem torusMonomialHom_bijective_of_isUnit_det {M : Matrix (Fin r) (Fin r) ℤ}
    (hu : IsUnit M.det) : Function.Bijective (torusMonomialHom C M) := by
  obtain ⟨v, hv⟩ := (Matrix.isUnit_iff_isUnit_det M).mpr hu
  have hMN : M * (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ) = 1 := by
    rw [← hv]; exact v.mul_inv
  have hNM : (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ) * M = 1 := by
    rw [← hv]; exact v.inv_mul
  have hone : torusMonomialHom C (1 : Matrix (Fin r) (Fin r) ℤ) = MonoidHom.id _ :=
    torusMonomialHom_one
  constructor
  · intro a b hab
    have h := congrArg (torusMonomialHom C (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ)) hab
    rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← torusMonomialHom_mul, hNM,
      hone] at h
    exact h
  · intro z
    refine ⟨torusMonomialHom C (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ) z, ?_⟩
    have h : (torusMonomialHom C M).comp
        (torusMonomialHom C (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ)) = MonoidHom.id _ := by
      rw [← torusMonomialHom_mul, hMN, hone]
    have hfun : ∀ f g : (Fin r → Cˣ) →* (Fin r → Cˣ), f = g → f z = g z := by
      intro f g hfg
      rw [hfg]
    exact hfun _ _ h

/-- **The order of the deck group of a torus isogeny.** -/
theorem card_ker_torusMonomialHom [IsAlgClosed C] [CharZero C]
    {M : Matrix (Fin r) (Fin r) ℤ} (hM : M.det ≠ 0) :
    Nat.card ((torusMonomialHom C M).ker) = M.det.natAbs := by
  classical
  obtain ⟨U, V, d, hU, hV, hd, hMUDV⟩ := exists_unimodular_diagonal M hM
  have hUinj : Function.Injective (torusMonomialHom C U) :=
    (torusMonomialHom_bijective_of_isUnit_det hU).1
  have hVbij : Function.Bijective (torusMonomialHom C V) :=
    torusMonomialHom_bijective_of_isUnit_det hV
  have hker : (torusMonomialHom C M).ker
      = ((torusPowerHom C d).ker).comap (torusMonomialHom C V) := by
    ext u
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, ← torusMonomialHom_diagonal]
    constructor
    · intro h
      rw [hMUDV, torusMonomialHom_mul, torusMonomialHom_mul] at h
      have h' : torusMonomialHom C U ((torusMonomialHom C (Matrix.diagonal d))
          ((torusMonomialHom C V) u)) = 1 := h
      apply hUinj
      rw [map_one]
      exact h'
    · intro h
      rw [hMUDV, torusMonomialHom_mul, torusMonomialHom_mul]
      show torusMonomialHom C U ((torusMonomialHom C (Matrix.diagonal d))
        ((torusMonomialHom C V) u)) = 1
      rw [h, map_one]
  have hprod : (∏ i, (d i).natAbs) = M.det.natAbs := by
    have hdet : M.det = U.det * (∏ i, d i) * V.det := by
      rw [hMUDV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hUabs : U.det.natAbs = 1 := Int.isUnit_iff.mp hU |>.elim
      (fun h ↦ by rw [h]; rfl) (fun h ↦ by rw [h]; rfl)
    have hVabs : V.det.natAbs = 1 := Int.isUnit_iff.mp hV |>.elim
      (fun h ↦ by rw [h]; rfl) (fun h ↦ by rw [h]; rfl)
    rw [hdet, Int.natAbs_mul, Int.natAbs_mul, hUabs, hVabs, one_mul, mul_one]
    exact (map_prod Int.natAbsHom d Finset.univ).symm
  rw [hker, ← hprod, ← card_ker_torusPowerHom (C := C) hd]
  let ev : (Fin r → Cˣ) ≃* (Fin r → Cˣ) := MulEquiv.ofBijective (torusMonomialHom C V) hVbij
  have hcomap : ((torusPowerHom C d).ker).comap (torusMonomialHom C V)
      = ((torusPowerHom C d).ker).comap (ev : (Fin r → Cˣ) →* (Fin r → Cˣ)) := rfl
  rw [hcomap, Subgroup.comap_equiv_eq_map_symm]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (ev.symm : (Fin r → Cˣ) ≃* (Fin r → Cˣ)).injective).toEquiv).symm

end Group

section Deck

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E] [CharZero C] [IsAlgClosed C]

variable {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

include hx hgen in
/-- **The prefix image of a torus isogeny is the fixed field of its deck group.**  The degree of the
substitution and the order of the kernel on the constant torus are both the absolute determinant, so
Artin's theorem turns the degree estimate into an identity. -/
theorem differentialAdjoin_monomialFamily_eq_fixedField {M : Matrix (Fin r) (Fin r) ℤ}
    (hM : M.det ≠ 0) :
    differentialAdjoin C (Set.range (monomialFamily M x))
      = IntermediateField.fixedField
          (((torusMonomialHom C M).ker).map (torusScaleRep hx hgen)) := by
  classical
  haveI hfinker : Finite ((torusMonomialHom C M).ker) := by
    have hcard : Nat.card ((torusMonomialHom C M).ker) = M.det.natAbs :=
      card_ker_torusMonomialHom hM
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    exact Int.natAbs_ne_zero.mpr hM
  haveI hfin : Finite (((torusMonomialHom C M).ker).map (torusScaleRep hx hgen)) :=
    Finite.of_equiv _ (Subgroup.equivMapOfInjective _ _ (torusScaleRep_injective hx hgen)).toEquiv
  haveI : Fintype (((torusMonomialHom C M).ker).map (torusScaleRep hx hgen)) := Fintype.ofFinite _
  -- finite dimensionality through the Smith reduction
  obtain ⟨V, d, hV, hd, hprod, heq⟩ := exists_diagonal_differentialAdjoin_eq hx hM
  have hVne : V.det ≠ 0 := det_ne_zero_of_isUnit_det hV
  have hyindep : DifferentialIndependent C (monomialFamily V x) :=
    differentialIndependent_monomialFamily hx hVne
  have hygen : differentialAdjoin C (Set.range (monomialFamily V x)) = ⊤ :=
    differentialAdjoin_monomialFamily_eq_top_of_isUnit_det hx hgen hV
  haveI hfd : FiniteDimensional
      (↥(differentialAdjoin C (Set.range (monomialFamily M x)))) E := by
    rw [heq]
    exact finiteDimensional_diagonal hyindep hygen hd
  -- the deck group fixes the prefix image
  have hfix := differentialAdjoin_monomialFamily_le_fixedField hx hgen M
    ((torusMonomialHom C M).ker) (fun u hu i ↦ by
      have hcoe := coe_torusMonomialHom (C := C) M u i
      have hu1 : torusMonomialHom C M u = 1 := hu
      rw [hu1] at hcoe
      simpa using hcoe.symm)
  -- the degree matches the order
  have hle : Module.finrank (↥(differentialAdjoin C (Set.range (monomialFamily M x)))) E
      ≤ Nat.card (((torusMonomialHom C M).ker).map (torusScaleRep hx hgen)) := by
    have hcard : Nat.card (((torusMonomialHom C M).ker).map (torusScaleRep hx hgen))
        = M.det.natAbs := by
      rw [← Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ (torusScaleRep_injective hx hgen)).toEquiv]
      exact card_ker_torusMonomialHom hM
    rw [hcard]
    exact finrank_torus_le_natAbs_det hx hgen hM
  exact eq_fixedField_of_finrank_le _ _ hfix hle

end Deck

end

end GaloisForLFunctions.HTGeometry

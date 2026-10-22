import GaloisForLFunctions.RHTower.Schanuel.SchanuelPeriodBranchDefect
import GaloisForLFunctions.RHTower.Schanuel.SchanuelPureTranscendentalPeriod

namespace GaloisForLFunctions.RHTower

noncomputable section

open Polynomial TensorProduct

/-- A nontrivial integral affine coefficient cannot annihilate a transcendental slope. -/
theorem intCast_mul_sub_ne_zero_of_transcendental
    {C F : Type*} [Field C] [Field F] [Algebra C F] [CharZero C]
    {rho : F} (hrho : Transcendental C rho)
    (k₁ k₂ : ℤ) (hk : k₁ ≠ 0 ∨ k₂ ≠ 0) :
    (k₁ : F) * rho - (k₂ : F) ≠ 0 := by
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap C F).injective
  by_cases hk₁ : k₁ = 0
  · have hk₂ : k₂ ≠ 0 := hk.elim (fun h => (h hk₁).elim) id
    simpa [hk₁] using (Int.cast_ne_zero.mpr hk₂ : (k₂ : F) ≠ 0)
  · intro hzero
    let p : Polynomial C := Polynomial.C (k₁ : C) * X - Polynomial.C (k₂ : C)
    have hp : p ≠ 0 := by
      intro hpzero
      have hcoeff : p.coeff 1 = 0 := by rw [hpzero]; rfl
      have hk₁C : (k₁ : C) ≠ 0 := Int.cast_ne_zero.mpr hk₁
      apply hk₁C
      rw [show p.coeff 1 = (k₁ : C) by
        simp only [p, coeff_sub, coeff_C_mul_X, if_true,
          coeff_C_of_ne_zero one_ne_zero, sub_zero]] at hcoeff
      exact hcoeff
    apply hrho
    refine ⟨p, hp, ?_⟩
    simpa [p] using hzero

/-- Every nontrivial integral period shift of a rank-one defect acquires rank two after adjoining
a period transcendental over the old field, provided the defect slope is transcendental over the
constant field. -/
theorem linearIndependent_nontrivial_integral_period_shift_of_transcendental
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E] [CharZero C]
    {tau : E} (htau : Transcendental F tau)
    {rho : F} (hrho : Transcendental C rho)
    (epsilon : KaehlerDifferential C F) (hepsilon : epsilon ≠ 0)
    (k₁ k₂ : ℤ) (hk : k₁ ≠ 0 ∨ k₂ ≠ 0) :
    let x : Fin 1 → E := ![tau]
    let P := IntermediateField.adjoin F (Set.range x)
    let tauP : P :=
      ⟨tau, IntermediateField.subset_adjoin F (Set.range x) ⟨0, rfl⟩⟩
    let old := KaehlerDifferential.mapBaseChange C F P (1 ⊗ₜ[F] epsilon)
    let dtau := KaehlerDifferential.D C P tauP
    LinearIndependent P ![
      old - (k₁ : P) • dtau,
      (algebraMap F P rho) • old - (k₂ : P) • dtau] := by
  classical
  dsimp only
  let x : Fin 1 → E := ![tau]
  let P := IntermediateField.adjoin F (Set.range x)
  let tauP : P :=
    ⟨tau, IntermediateField.subset_adjoin F (Set.range x) ⟨0, rfl⟩⟩
  let old := KaehlerDifferential.mapBaseChange C F P (1 ⊗ₜ[F] epsilon)
  let dtau := KaehlerDifferential.D C P tauP
  have hbase : LinearIndependent P ![old, dtau] := by
    exact linearIndependent_mapBaseChange_and_D_adjoin_transcendental
      htau epsilon hepsilon
  have hdetF : (k₁ : F) * rho - (k₂ : F) ≠ 0 :=
    intCast_mul_sub_ne_zero_of_transcendental hrho k₁ k₂ hk
  have hdetP : (k₁ : P) * algebraMap F P rho - (k₂ : P) ≠ 0 := by
    intro hzero
    apply hdetF
    apply (algebraMap F P).injective
    simpa using hzero
  exact linearIndependent_rankOne_period_shift old dtau hbase
    (algebraMap F P rho) (k₁ : P) (k₂ : P) hdetP

end


end GaloisForLFunctions.RHTower


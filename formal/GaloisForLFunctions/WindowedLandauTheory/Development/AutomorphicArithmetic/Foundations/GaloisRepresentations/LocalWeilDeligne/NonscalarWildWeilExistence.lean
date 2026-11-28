import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinExistence
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.UnramifiedCompletionOfDegree
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ResidueArtinFrobenius
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrincipalCoefficientOfUnramifiedCompletion
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.ResidueCharacterPeriods
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WildWeilParameterOfInertiaQuotient

/-! Principal-unit reduction in the unramified extension of degree
`n` gives an irreducible Weil parameter of dimension `n ≥ 2` with
unitary determinant and nonscalar wild inertia. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField Multiplicative
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameKummer
open GlobalTheory.Reciprocity
open scoped Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.WeilDeligne

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

theorem exists_irreducible_nonscalarWild (h : IsPlaceOver A v) (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : WDRep h (Fin n → ℂ), a.ρ.IsIrreducible ∧ a.N = 0 ∧
      (∀ σ, ‖LinearMap.det (a.ρ σ)‖ = 1) ∧
      ∃ t : Ine (F := K) A, t.val ∈ wildInertia A ∧ ∀ c : ℂ, a.ρ (ineIncl h t) ≠ c • 1 := by
  have hn0 : 0 < n := by omega
  obtain ⟨T, he, hnres, -⟩ := exists_unramified_completion_of_degree K Ω h hn0
  let L := (T : IntermediateField K Ω)
  letI : FiniteDimensional K L := T.2.1
  letI : IsAbelianGalois K L := T.2.2
  letI : NumberField L := NumberField.of_module_finite K L
  letI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) L⟩
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  let hw := finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A h
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  obtain ⟨β, hβ, -⟩ := existsUnique_localArtin L Ω hw
  let κ := 𝓞 K ⧸ v.asIdeal
  let κ' := 𝓞 L ⧸ w.asIdeal
  letI := v.isMaximal
  letI := w.isMaximal
  letI : Field κ := Ideal.Quotient.field v.asIdeal
  letI : Field κ' := Ideal.Quotient.field w.asIdeal
  letI : Finite κ := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Finite κ' := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  letI : Algebra κ κ' := inferInstanceAs (Algebra (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal))
  have hd : Module.finrank κ κ' = n :=
    (Ideal.inertiaDeg_eq_of_isMaximal (R := 𝓞 K) v.asIdeal w.asIdeal).symm.trans hnres
  let φ := frob h
  let σ := AlgEquiv.restrictNormalHom L φ.val
  have hσ := restrictNormalHom_isArithFrobAt (L := L) A h (isFrob_frob (h := h))
  let s : MulAction.stabilizer Gal(L/K) w.asIdeal := ⟨σ, hσ.mem_stabilizer⟩
  obtain ⟨b, hbs, hbo, hbf⟩ :=
    exists_frobeniusEquivariant_principalCoefficient v w he s hσ
  let j := unitArtinOnBaseInertia K Ω L h hβ he
  let r := b.comp j
  have hr : Function.Surjective r := hbs.comp (unitArtinOnBaseInertia_surjective K Ω L h hβ he)
  have hop : IsOpen (r.ker : Set (Ine (F := K) A)) :=
    hbo.preimage (continuous_unitArtinOnBaseInertia K Ω L h hβ he)
  let f := residueAdditiveFrobenius κ κ'
  have hF (t t' : Ine (F := K) A) (ht : ineIncl h t' = φ * ineIncl h t * φ⁻¹) :
      r t' = f (r t) := by
    change b (j t') = residueAdditiveFrobenius κ κ' (b (j t))
    rw [residueAdditiveFrobenius_apply]
    exact hbf _ _ (unitArtinOnBaseInertia_conjugation K Ω L h hβ he φ t t' ht s.2)
  let p := ringChar κ
  letI : Fact p.Prime := ⟨CharP.char_is_prime κ p⟩
  have hpm : (p : 𝓞 K) ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_natCast]
    exact CharP.cast_eq_zero κ p
  have hp : A.valuation (p : Ω) < 1 := by
    simpa only [map_natCast] using (h (p : 𝓞 K)).mpr hpm
  obtain ⟨χ, hχ⟩ := exists_fullPeriod_additiveCharacter κ κ' n hn0 hd
  have hq : (normV v : κ') = 0 := by
    change (Nat.card κ : κ') = 0
    letI : Fintype κ := Fintype.ofFinite κ
    rw [← map_natCast (algebraMap κ κ'), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero, map_zero]
  have hpow (u : Multiplicative κ') : χ u ^ normV v = 1 := by
    have he : u ^ normV v = 1 := by
      apply toAdd.injective
      change (normV v) • toAdd u = (0 : κ')
      rw [nsmul_eq_mul, hq, zero_mul]
    rw [← map_pow, he, map_one]
  exact exists_wdRep_nonscalar_wild_of_inertia_quotient hp r hr hop φ deg_frob f hF χ hpow n hn hχ

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_irreducible_nonscalarWild

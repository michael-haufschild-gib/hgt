import GaloisForLFunctions.RHTower.DeningerQ8ActualBiquadraticOddRamification
import GaloisForLFunctions.RHTower.DeningerQ8ActualMaximalAbelianField
import GaloisForLFunctions.HTGeometry.ValuationInertiaIntermediateUnramified
import GaloisForLFunctions.HTGeometry.CriticalSchurInertiaRamificationIndex

/-!
# Odd inertia of the actual Q8 field is noncentral

The integral square roots of `5` and `41` make every corresponding prime of the maximal abelian
field ramified.  If top inertia were contained in the central C2, the valuation fixed-field orbit
law would make that maximal abelian field unramified.  The contradiction proves that actual odd
inertia is not central, attaching both Fröhlich source primes to noncentral Q8 inertia.
-/

namespace RHTower

open scoped NumberField Pointwise
open GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 800000

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField
local notation "M" => deningerQ8ActualBiquadraticField

local instance deningerQ8ActualOddInertiaLocalInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
local instance deningerQ8ActualOddInertiaLocalInst2 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective

noncomputable local instance deningerQ8ActualOddInertiaLocalInst3 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance deningerQ8ActualOddInertiaLocalInst4 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance deningerQ8ActualOddInertiaLocalInst5 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance deningerQ8ActualOddInertiaLocalInst6 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance deningerQ8ActualOddInertiaLocalInst7 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance deningerQ8ActualOddInertiaLocalInst8 : FiniteDimensional ℚ M :=
  LinearEquiv.finiteDimensional
    (IntermediateField.equivMap (⊤ : IntermediateField ℚ K2)
      (IsScalarTower.toAlgHom ℚ K2 K3)).toLinearEquiv

noncomputable local instance deningerQ8ActualOddInertiaLocalInst9 : NumberField K2 := NumberField.mk
noncomputable local instance deningerQ8ActualOddInertiaLocalInst10 : NumberField K3 := NumberField.mk
noncomputable local instance deningerQ8ActualOddInertiaLocalInst11 : NumberField M := NumberField.mk
noncomputable local instance deningerQ8ActualOddInertiaLocalInst12 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois

/-- Transport an algebraic integer of the literal biquadratic presentation into the actual
maximal abelian intermediate field inside the Q8 extension. -/
noncomputable def q8BiquadIntegralToActual (x : 𝓞 K2) : 𝓞 M := by
  let y : M := ⟨algebraMap K2 K3 (x : K2), by
    change algebraMap K2 K3 (x : K2) ∈
      IntermediateField.map (IsScalarTower.toAlgHom ℚ K2 K3) ⊤
    exact ⟨x, Set.mem_univ _, rfl⟩⟩
  have hyTop : IsIntegral ℤ ((algebraMap M K3) y) := by
    change IsIntegral ℤ (algebraMap K2 K3 (x : K2))
    exact x.property.map (IsScalarTower.toAlgHom ℤ K2 K3)
  have hy : IsIntegral ℤ y :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ M K3)
      (algebraMap M K3).injective).mp hyTop
  exact ⟨y, hy⟩

/-- Transport preserves a literal rational-prime square relation. -/
theorem q8BiquadIntegralToActual_sq
    (p : ℤ) (x : 𝓞 K2)
    (hx : x ^ 2 = algebraMap ℤ (𝓞 K2) p) :
    q8BiquadIntegralToActual x ^ 2 = algebraMap ℤ (𝓞 M) p := by
  apply Subtype.ext
  apply (algebraMap M K3).injective
  change (algebraMap K2 K3 (x : K2)) ^ 2 = algebraMap ℤ K3 p
  calc
    (algebraMap K2 K3 (x : K2)) ^ 2 =
        algebraMap K2 K3 ((x : K2) ^ 2) := by rw [map_pow]
    _ = algebraMap K2 K3 (algebraMap ℤ K2 p) := by
      have hxval : (x : K2) ^ 2 = algebraMap ℤ K2 p := congrArg Subtype.val hx
      exact congrArg (algebraMap K2 K3) hxval
    _ = algebraMap ℤ K3 p := IsScalarTower.algebraMap_apply ℤ K2 K3 p

/-- If the actual maximal abelian field contains an integral square root of `p`, then top inertia
at every prime above `p` cannot lie in the central subgroup that fixes that field. -/
theorem q8Actual_odd_inertia_not_le_center
    (p : ℤ) (hp : Prime p) (x : 𝓞 K2)
    (hx : x ^ 2 = algebraMap ℤ (𝓞 K2) p)
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {p})) :
    ¬ P.inertia Gal(K3/ℚ) ≤ deningerQ8ActualCentralSubgroup := by
  intro hle
  have hPp : algebraMap ℤ (𝓞 K3) p ∈ P := by
    exact (Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance) hp).mp hPover
  have hPne : P ≠ ⊥ := by
    intro hP
    rw [hP, Ideal.mem_bot] at hPp
    have hcast : (p : 𝓞 K3) = ((0 : ℤ) : 𝓞 K3) := by simpa using hPp
    exact hp.ne_zero (Int.cast_injective hcast)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K3) :=
    ⟨P, (inferInstance : P.IsPrime), hPne⟩
  let W : ValuationSubring K3 :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K3 v
  letI : IsLocalization P.primeCompl W := by
    exact
      IsDedekindDomain.HeightOneSpectrum.instIsLocalizationPrimeComplAsIdealSubtypeMemValuationSubringValuationSubringAtPrime
        v
  letI : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) hPne W
  have hW : W ≠ ⊤ := ValuationSubring.ne_top_of_isDiscreteValuationRing W
  have hSW : ∀ s : 𝓞 K3, algebraMap (𝓞 K3) K3 s ∈ W := by
    intro s
    exact (algebraMap (𝓞 K3) W s).property
  have hAW : ∀ a : ℤ, algebraMap ℤ K3 a ∈ W := by
    intro a
    have ha := hSW (algebraMap ℤ (𝓞 K3) a)
    simpa only [IsScalarTower.algebraMap_apply ℤ (𝓞 K3) K3] using ha
  have hcent : ∀ a : ℤ,
      (¬ IsUnit (⟨algebraMap ℤ K3 a, hAW a⟩ : W)) ↔ a ∈ Ideal.span {p} := by
    intro a
    have heq : (⟨algebraMap ℤ K3 a, hAW a⟩ : W) =
        algebraMap (𝓞 K3) W (algebraMap ℤ (𝓞 K3) a) := by
      apply Subtype.ext
      exact (IsScalarTower.algebraMap_apply ℤ (𝓞 K3) K3 a).symm
    rw [heq, IsLocalization.AtPrime.isUnit_to_map_iff W P]
    change (¬ algebraMap ℤ (𝓞 K3) a ∉ P) ↔ a ∈ Ideal.span {p}
    rw [not_not]
    change a ∈ P.comap (algebraMap ℤ (𝓞 K3)) ↔ a ∈ Ideal.span {p}
    have hover : Ideal.span {p} = P.comap (algebraMap ℤ (𝓞 K3)) := hPover.over
    rw [← hover]
  letI : (Ideal.span {p}).IsMaximal := hp.isMaximal_span_singleton
  have hact : ∀ (g : Gal(K3/ℚ)) (s : 𝓞 K3),
      algebraMap (𝓞 K3) K3 (g • s) = g • algebraMap (𝓞 K3) K3 s := by
    intro g s
    rfl
  have hcenterPrime :
      ValuationInertia.centerPrime W hSW = P := by
    apply Ideal.ext
    intro s
    change ValuationInertia.toValuationSubring W hSW s ∈
        IsLocalRing.maximalIdeal W ↔ s ∈ P
    have heq : ValuationInertia.toValuationSubring W hSW s =
        algebraMap (𝓞 K3) W s := Subtype.ext rfl
    rw [heq, IsLocalization.AtPrime.to_map_mem_maximal_iff W P s]
  have hI : ∀ g : W.inertiaSubgroup ℚ,
      ((g : W.decompositionSubgroup ℚ) : K3 ≃ₐ[ℚ] K3) ∈
        deningerQ8ActualCentralSubgroup := by
    intro g
    apply hle
    rw [← hcenterPrime]
    exact ValuationInertia.coe_mem_inertia_of_mem_inertiaSubgroup W hSW hact g.2
  haveI q8OddGal : IsGalois ℚ K3 := deningerQ8RootNumberNegOne_isGalois
  have _hGalAudit : IsGalois ℚ K3 := q8OddGal
  have hpbot : Ideal.span {p} ≠ (⊥ : Ideal ℤ) := by
    intro hbot
    have hmem : p ∈ (⊥ : Ideal ℤ) := by
      rw [← hbot]
      exact Ideal.subset_span (Set.mem_singleton p)
    exact hp.ne_zero (Ideal.mem_bot.mp hmem)
  letI q8FixedNumberField :
      NumberField (IntermediateField.fixedField deningerQ8ActualCentralSubgroup) := by
    rw [← deningerQ8ActualBiquadraticField_eq_fixedField_centralSubgroup]
    infer_instance
  let Q0 : Ideal
      (𝓞 (IntermediateField.fixedField deningerQ8ActualCentralSubgroup)) :=
    ValuationInertia.intermediateCentre
      (IntermediateField.fixedField deningerQ8ActualCentralSubgroup) W hAW
  letI : Q0.IsPrime :=
    ValuationInertia.intermediateCentre_isPrime
      (IntermediateField.fixedField deningerQ8ActualCentralSubgroup) W hAW
  have hQ0ne : Q0 ≠ ⊥ :=
    ValuationInertia.intermediateCentre_ne_bot
      (IntermediateField.fixedField deningerQ8ActualCentralSubgroup) W hAW
      (Ideal.span {p}) hpbot hcent
  letI : Q0.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0ne
  letI : Finite
      (𝓞 (IntermediateField.fixedField deningerQ8ActualCentralSubgroup) ⧸ Q0) :=
    inferInstance
  letI : Finite Q0.ResidueField := inferInstance
  letI : PerfectField Q0.ResidueField := inferInstance
  have hQ0perfect : PerfectField
      (ValuationInertia.intermediateCentre
        (IntermediateField.fixedField deningerQ8ActualCentralSubgroup) W hAW).ResidueField := by
    change PerfectField Q0.ResidueField
    infer_instance
  have hram :
      (ValuationInertia.intermediateCentre
          (IntermediateField.fixedField deningerQ8ActualCentralSubgroup) W hAW).ramificationIdx
        ℤ = 1 := by
    exact @ValuationInertia.ramificationIdx_fixedField_eq_one_of_inertia_le
      ℚ K3 _ _ _ W ℤ _ _ _ _ _ _ _ q8OddGal
      deningerQ8ActualCentralSubgroup hAW hW (Ideal.span {p}) hpbot _ _ hcent hQ0perfect hI
  rw [← deningerQ8ActualBiquadraticField_eq_fixedField_centralSubgroup] at hram
  let Q : Ideal (𝓞 M) := ValuationInertia.intermediateCentre M W hAW
  letI : Q.IsPrime := ValuationInertia.intermediateCentre_isPrime M W hAW
  have hQover : Q.LiesOver (Ideal.span {p}) :=
    ValuationInertia.liesOver_intermediateCentre M W hAW (Ideal.span {p}) hcent
  have hnot : ¬ Algebra.IsUnramifiedAt ℤ Q :=
    prime_not_isUnramifiedAt_of_integral_square p hp
      (q8BiquadIntegralToActual x) (q8BiquadIntegralToActual_sq p x hx) Q hQover
  apply hnot
  exact Ideal.ramificationIdx_eq_one_iff.mp hram

/-- At every top prime above `5`, actual inertia is not the central order-two subgroup. -/
theorem q8Actual_five_inertia_not_le_center
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    ¬ P.inertia Gal(K3/ℚ) ≤ deningerQ8ActualCentralSubgroup :=
  q8Actual_odd_inertia_not_le_center 5 (by norm_num)
    q8BiquadFiveRoot q8BiquadFiveRoot_sq P hPover

/-- At every top prime above `41`, actual inertia is not the central order-two subgroup. -/
theorem q8Actual_fortyOne_inertia_not_le_center
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    ¬ P.inertia Gal(K3/ℚ) ≤ deningerQ8ActualCentralSubgroup :=
  q8Actual_odd_inertia_not_le_center 41 (by norm_num)
    q8BiquadFortyOneRoot q8BiquadFortyOneRoot_sq P hPover

end

end RHTower

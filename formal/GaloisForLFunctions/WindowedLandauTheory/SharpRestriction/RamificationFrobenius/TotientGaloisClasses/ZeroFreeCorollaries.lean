import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import GaloisForLFunctions.WindowedLandauTheory.ArchiveStatements
import GaloisForLFunctions.WindowedLandauTheory.NonvanishingRightOfTheCriticalLine
import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveEulerProduct
import GaloisForLFunctions.RHTower.EulerUnitTangent
import GaloisForLFunctions.RHTower.TwistedOrderLawExact
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-! Transfer nonvanishing of primitive characters to the headline zero statements. -/

namespace WindowedLandauTheory.HC

open DirichletCharacter

private theorem zeta_nonvanishing_of_zeroFreeAll (h : ZeroFreeAll) (s : ℂ)
    (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  have hz : LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 := h PChar.one trivial s hs
  simpa only [LFunction_modOne_eq] using hz

/-- Modulus one gives the zeta case of primitive nonvanishing. -/
theorem riemannHypothesis_of_zeroFreeAll (h : ZeroFreeAll) : RiemannHypothesis :=
  RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mpr
    (zeta_nonvanishing_of_zeroFreeAll h)

/-- Omitted Euler factors preserve right-half-plane nonvanishing for every level. -/
theorem allChi_of_zeroFreeAll (h : ZeroFreeAll) : DirichletLNonvanishingRightOfHalf := by
  intro N _ χ s hs hpole
  exact LFunction_ne_zero_of_primitive (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (zeta_nonvanishing_of_zeroFreeAll h)
    (fun M _ ψ hψ _ z hz => h ⟨M, ψ, hψ⟩ trivial z hz) χ hs hpole

/-- A left-half-strip zero of any character yields a reflected primitive or zeta zero. -/
theorem dirichletLZerosOnLine_of_zeroFreeAll (h : ZeroFreeAll) : DirichletLZerosOnLine := by
  intro N _ χ s hs₀ hs₁ hz
  have hs_ne : s ≠ 1 := by
    rintro rfl
    simp at hs₁
  rcases lt_trichotomy s.re (1 / 2) with hleft | hon | hright
  · exfalso
    cases N with
    | zero => exact NeZero.ne (0 : ℕ) rfl
    | succ n =>
      by_cases hχ : χ = 1
      · subst χ
        change LFunctionTrivChar (n + 1) s = 0 at hz
        rw [LFunctionTrivChar_eq_mul_riemannZeta hs_ne] at hz
        have hEuler : (∏ p ∈ (n + 1).primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun p hp =>
            RHTower.one_sub_prime_cpow_neg_ne_zero (Nat.prime_of_mem_primeFactors hp).two_le hs₀
        have hzeta := (mul_eq_zero.mp hz).resolve_left hEuler
        have hreflect : 1 / 2 < (1 - s).re := by
          rw [Complex.sub_re, Complex.one_re]
          linarith only [hleft]
        exact zeta_nonvanishing_of_zeroFreeAll h _ hreflect
          (RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hzeta hs₀ hs₁)
      · let χ₀ : RHTower.NonprincipalDirichletCharacter n := ⟨χ, hχ⟩
        let P := RHTower.cglPrimitiveCharacterReduction n χ₀
        letI : NeZero P.conductor := ⟨P.conductor_pos.ne'⟩
        have hpz : LFunction P.primitiveCharacter s = 0 :=
          (RHTower.cglPrimitiveLFunction_zero_iff_input n χ₀ ⟨s, hs₀⟩).mpr hz
        have hreflect : 1 / 2 < ((starRingEnd ℂ) (1 - s)).re := by
          simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
          linarith only [hleft]
        exact h ⟨P.conductor, P.primitiveCharacter, P.primitive⟩ trivial _ hreflect
          (RHTower.LFunction_eq_zero_conj_one_sub P.nonprincipal P.primitive hpz hs₀ hs₁)
  · exact hon
  · exact (allChi_of_zeroFreeAll h N χ s hright (Or.inr hs_ne) hz).elim

end WindowedLandauTheory.HC

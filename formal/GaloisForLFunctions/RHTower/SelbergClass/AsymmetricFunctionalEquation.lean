import GaloisForLFunctions.RHTower.SelbergClass.FunctionalEquationLocal
import GaloisForLFunctions.RHTower.SelbergClass.InvariantRootNumber
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Pole-safe asymmetric Selberg functional equation

Kaczorowski--Perelli write the functional equation of an extended Selberg-class
carrier in the asymmetric invariant form
`F(s) = ω_F S_F(s) h_F(s) \overline{F}(1 - s)` (their (2.2)).

Mathlib represents the complex Gamma function by a totalized function which is
zero at its poles.  Therefore, Euler reflection cannot legitimately produce a
global pointwise version of that formula.  This file states and proves the
source formula only where both completed sides are analytic and every Gamma
factor needed by the reflection rewrite is nonzero.
-/

open Complex Filter Set
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- Kaczorowski--Perelli's sine factor `S_F(s)`. -/
def SelbergGammaData.asymmetricS (G : SelbergGammaData) (s : ℂ) : ℂ :=
  (2 : ℂ) ^ G.rank * ∏ j, Complex.sin (Real.pi * ((G.lambda j : ℂ) * s + G.mu j))

/-- Kaczorowski--Perelli's archimedean factor `h_F(s)`, with
`(2π)^(-r)` represented as the inverse of its natural power. -/
def SelbergGammaData.asymmetricH (G : SelbergGammaData) (s : ℂ) : ℂ :=
  ((2 * Real.pi : ℂ) ^ G.rank)⁻¹ *
    (∏ j, (G.lambda j : ℂ) ^ ((2 : ℂ) * Complex.I * ((G.mu j).im : ℂ))) *
    (G.Q : ℂ) ^ (1 - 2 * s) *
    ∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - s) + star (G.mu j)) *
      Complex.Gamma (1 - (G.lambda j : ℂ) * s - G.mu j)

/-- The Gamma-pole-free condition needed to turn Euler reflection into a
pointwise identity for Mathlib's totalized Gamma function. -/
def SelbergGammaData.asymmetricPoleFreeSet (G : SelbergGammaData) : Set ℂ :=
  {s | ∀ j,
    Complex.Gamma ((G.lambda j : ℂ) * s + G.mu j) ≠ 0 ∧
      Complex.Gamma (1 - (G.lambda j : ℂ) * s - G.mu j) ≠ 0}

/-- Pointwise reciprocal-Gamma form of Euler reflection away from both
totalized Gamma zero sets. -/
theorem gamma_inv_eq_sin_mul_gamma_one_sub {z : ℂ}
    (hz : Complex.Gamma z ≠ 0) (h1z : Complex.Gamma (1 - z) ≠ 0) :
    (Complex.Gamma z)⁻¹ =
      Complex.sin (Real.pi * z) * Complex.Gamma (1 - z) / Real.pi := by
  have hmul := Complex.Gamma_mul_Gamma_one_sub z
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsin : Complex.sin (Real.pi * z) ≠ 0 := by
    intro hs
    rw [hs, div_zero] at hmul
    exact (mul_ne_zero hz h1z) hmul
  have hprod : Complex.Gamma z * Complex.Gamma (1 - z) *
      Complex.sin (Real.pi * z) = Real.pi := by
    rw [hmul, div_mul_cancel₀ _ hsin]
  field_simp [hz, hpi]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hprod.symm

theorem SelbergGammaData.star_Q_cpow_one_sub (G : SelbergGammaData) (s : ℂ) :
    star ((G.Q : ℂ) ^ (1 - star s)) = (G.Q : ℂ) ^ (1 - s) := by
  have harg : (G.Q : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg G.Q_pos.le]
    exact ne_of_lt Real.pi_pos
  have h := Complex.conj_cpow (G.Q : ℂ) (1 - s) harg
  simpa using h.symm

theorem SelbergGammaData.star_gammaFactor_one_sub (G : SelbergGammaData) (s : ℂ) :
    star (G.gammaFactor (1 - star s)) =
      (G.Q : ℂ) ^ (1 - s) *
        ∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - s) + star (G.mu j)) := by
  rw [SelbergGammaData.gammaFactor]
  simp only [Pi.mul_apply, Finset.prod_apply]
  change star (((G.Q : ℂ) ^ (1 - star s) *
    ∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - star s) + G.mu j))) = _
  change (starRingEnd ℂ) (((G.Q : ℂ) ^ (1 - star s)) *
    ∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - star s) + G.mu j)) = _
  rw [(starRingEnd ℂ).map_mul, map_prod (starRingEnd ℂ)]
  change star ((G.Q : ℂ) ^ (1 - star s)) *
    ∏ j, star (Complex.Gamma ((G.lambda j : ℂ) * (1 - star s) + G.mu j)) = _
  rw [G.star_Q_cpow_one_sub]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  change (starRingEnd ℂ)
    (Complex.Gamma ((G.lambda j : ℂ) * (1 - star s) + G.mu j)) = _
  rw [← Complex.Gamma_conj]
  congr 1
  simp [map_add, map_sub, map_mul]

theorem SelbergGammaData.gammaFactor_ne_zero_of_mem_asymmetricPoleFreeSet
    (G : SelbergGammaData) {s : ℂ} (hs : s ∈ G.asymmetricPoleFreeSet) :
    G.gammaFactor s ≠ 0 := by
  rw [SelbergGammaData.gammaFactor]
  simp only [Pi.mul_apply, Finset.prod_apply]
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr G.Q_pos.ne'))
  · exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ (hs j).1

theorem selbergConjugateReflection_completedValue (G : SelbergGammaData)
    (A : SelbergAnalyticContinuation) (s : ℂ) :
    selbergConjugateReflection (selbergCompletedValue G A) s =
      star (G.gammaFactor (1 - star s)) *
        selbergConjugateReflection A.value s := by
  unfold selbergConjugateReflection selbergCompletedValue
  change (starRingEnd ℂ) (G.gammaFactor (1 - star s) * A.value (1 - star s)) = _
  rw [(starRingEnd ℂ).map_mul]
  rfl

theorem ExtendedSelbergClass.rawFunctionalEquation_on_analytic_pair
    (F : ExtendedSelbergClass) {s : ℂ}
    (hs : AnalyticAt ℂ (selbergCompletedValue F.gammaData F.continuation) s)
    (hreflection : AnalyticAt ℂ
      (selbergCompletedValue F.gammaData F.continuation) (1 - star s)) :
    F.gammaData.gammaFactor s * F s =
      F.gammaData.rootNumber *
        ((F.gammaData.Q : ℂ) ^ (1 - s) *
          ∏ j, Complex.Gamma ((F.gammaData.lambda j : ℂ) * (1 - s) +
            star (F.gammaData.mu j))) *
        selbergConjugateReflection F s := by
  have hfe := F.completedFE_eq_of_analytic_pair hs hreflection
  rw [selbergConjugateReflection_completedValue,
    F.gammaData.star_gammaFactor_one_sub] at hfe
  simpa [selbergCompletedValue, ExtendedSelbergClass.value, mul_assoc] using hfe

theorem SelbergGammaData.gammaFactor_inv_expansion (G : SelbergGammaData) (s : ℂ) :
    (G.gammaFactor s)⁻¹ =
      (G.Q : ℂ) ^ (-s) *
        ∏ j, (Complex.Gamma ((G.lambda j : ℂ) * s + G.mu j))⁻¹ := by
  rw [SelbergGammaData.gammaFactor]
  simp only [Pi.mul_apply, Finset.prod_apply, mul_inv, Finset.prod_inv_distrib]
  rw [← Complex.cpow_neg]

theorem ExtendedSelbergClass.value_eq_raw_asymmetric_factor
    (F : ExtendedSelbergClass) {s : ℂ}
    (hs : AnalyticAt ℂ (selbergCompletedValue F.gammaData F.continuation) s)
    (hreflection : AnalyticAt ℂ
      (selbergCompletedValue F.gammaData F.continuation) (1 - star s))
    (hpoleFree : s ∈ F.gammaData.asymmetricPoleFreeSet) :
    F s =
      F.gammaData.rootNumber *
        ((F.gammaData.Q : ℂ) ^ (1 - s) *
          ∏ j, Complex.Gamma ((F.gammaData.lambda j : ℂ) * (1 - s) +
            star (F.gammaData.mu j))) *
        (F.gammaData.gammaFactor s)⁻¹ *
        selbergConjugateReflection F s := by
  have hgamma := F.gammaData.gammaFactor_ne_zero_of_mem_asymmetricPoleFreeSet hpoleFree
  calc
    F s = (F.gammaData.gammaFactor s)⁻¹ * (F.gammaData.gammaFactor s * F s) := by
      simpa using (inv_mul_cancel_left₀ hgamma (F s)).symm
    _ = (F.gammaData.gammaFactor s)⁻¹ *
        (F.gammaData.rootNumber *
          ((F.gammaData.Q : ℂ) ^ (1 - s) *
            ∏ j, Complex.Gamma ((F.gammaData.lambda j : ℂ) * (1 - s) +
              star (F.gammaData.mu j))) *
          selbergConjugateReflection F s) := by
      rw [F.rawFunctionalEquation_on_analytic_pair hs hreflection]
    _ = _ := by ring

theorem SelbergGammaData.invariantRootNumber_mul_phaseProduct
    (G : SelbergGammaData) :
    G.invariantRootNumber *
      (∏ j, (G.lambda j : ℂ) ^ ((2 : ℂ) * Complex.I * ((G.mu j).im : ℂ))) =
      G.rootNumber := by
  unfold SelbergGammaData.invariantRootNumber
  rw [mul_assoc]
  have hprod :
      (∏ j, (G.lambda j : ℂ) ^ (-(2 : ℂ) * Complex.I * ((G.mu j).im : ℂ))) *
        ∏ j, (G.lambda j : ℂ) ^ ((2 : ℂ) * Complex.I * ((G.mu j).im : ℂ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j _
    have hneg : (-(2 : ℂ) * Complex.I * ((G.mu j).im : ℂ)) =
        -((2 : ℂ) * Complex.I * ((G.mu j).im : ℂ)) := by ring
    rw [hneg]
    rw [Complex.cpow_neg]
    exact inv_mul_cancel₀ (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (G.lambda_pos j).ne')))
  rw [hprod, mul_one]

theorem two_pow_mul_inv_two_pi_pow (r : ℕ) :
    (2 : ℂ) ^ r * ((2 * Real.pi : ℂ) ^ r)⁻¹ = ((Real.pi : ℂ) ^ r)⁻¹ := by
  rw [mul_pow, mul_inv]
  have htwo : (2 : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

theorem SelbergGammaData.gammaInv_product_eq_sourceSine
    (G : SelbergGammaData) {s : ℂ} (hs : s ∈ G.asymmetricPoleFreeSet) :
    (∏ j, (Complex.Gamma ((G.lambda j : ℂ) * s + G.mu j))⁻¹) =
      (∏ j, Complex.sin (Real.pi * ((G.lambda j : ℂ) * s + G.mu j))) *
        (∏ j, Complex.Gamma (1 - (G.lambda j : ℂ) * s - G.mu j)) *
          ((Real.pi : ℂ) ^ G.rank)⁻¹ := by
  calc
    (∏ j, (Complex.Gamma ((G.lambda j : ℂ) * s + G.mu j))⁻¹) =
        ∏ j, (Complex.sin (Real.pi * ((G.lambda j : ℂ) * s + G.mu j)) *
          Complex.Gamma (1 - ((G.lambda j : ℂ) * s + G.mu j)) / Real.pi) := by
      apply Finset.prod_congr rfl
      intro j _
      simpa [sub_sub] using gamma_inv_eq_sin_mul_gamma_one_sub (hs j).1 (by
        simpa [sub_sub] using (hs j).2)
    _ = ∏ j, (Complex.sin (Real.pi * ((G.lambda j : ℂ) * s + G.mu j)) *
          Complex.Gamma (1 - ((G.lambda j : ℂ) * s + G.mu j)) * (Real.pi : ℂ)⁻¹) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [div_eq_mul_inv]
    _ = (∏ j, Complex.sin (Real.pi * ((G.lambda j : ℂ) * s + G.mu j)) *
          Complex.Gamma (1 - ((G.lambda j : ℂ) * s + G.mu j))) *
        ∏ _j : Fin G.rank, (Real.pi : ℂ)⁻¹ := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
      congr 2
      apply Finset.prod_congr rfl
      intro j _
      ring_nf

theorem SelbergGammaData.Q_cpow_one_sub_mul_neg (G : SelbergGammaData) (s : ℂ) :
    (G.Q : ℂ) ^ (1 - s) * (G.Q : ℂ) ^ (-s) =
      (G.Q : ℂ) ^ (1 - 2 * s) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr G.Q_pos.ne')]
  congr 1
  ring

theorem SelbergGammaData.asymmetricFactors_eq_rawFactor
    (G : SelbergGammaData) {s : ℂ} (hs : s ∈ G.asymmetricPoleFreeSet) :
    G.invariantRootNumber * G.asymmetricS s * G.asymmetricH s =
      G.rootNumber *
        ((G.Q : ℂ) ^ (1 - s) *
          ∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - s) + star (G.mu j))) *
        (G.gammaFactor s)⁻¹ := by
  calc
    G.invariantRootNumber * G.asymmetricS s * G.asymmetricH s =
        (G.invariantRootNumber *
          ∏ j, (G.lambda j : ℂ) ^ ((2 : ℂ) * Complex.I * ((G.mu j).im : ℂ))) *
        ((2 : ℂ) ^ G.rank * ((2 * Real.pi : ℂ) ^ G.rank)⁻¹) *
        (∏ j, Complex.sin (Real.pi * ((G.lambda j : ℂ) * s + G.mu j))) *
        (G.Q : ℂ) ^ (1 - 2 * s) *
        (∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - s) + star (G.mu j))) *
        ∏ j, Complex.Gamma (1 - (G.lambda j : ℂ) * s - G.mu j) := by
      unfold SelbergGammaData.asymmetricS SelbergGammaData.asymmetricH
      rw [Finset.prod_mul_distrib]
      ring
    _ = G.rootNumber * ((Real.pi : ℂ) ^ G.rank)⁻¹ *
        (∏ j, Complex.sin (Real.pi * ((G.lambda j : ℂ) * s + G.mu j))) *
        (G.Q : ℂ) ^ (1 - 2 * s) *
        (∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - s) + star (G.mu j))) *
        ∏ j, Complex.Gamma (1 - (G.lambda j : ℂ) * s - G.mu j) := by
      rw [G.invariantRootNumber_mul_phaseProduct, two_pow_mul_inv_two_pi_pow]
    _ = G.rootNumber *
        ((G.Q : ℂ) ^ (1 - s) *
          ∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - s) + star (G.mu j))) *
        ((G.Q : ℂ) ^ (-s) *
          ((∏ j, Complex.sin (Real.pi * ((G.lambda j : ℂ) * s + G.mu j))) *
            (∏ j, Complex.Gamma (1 - (G.lambda j : ℂ) * s - G.mu j)) *
              ((Real.pi : ℂ) ^ G.rank)⁻¹)) := by
      rw [← G.Q_cpow_one_sub_mul_neg]
      ring
    _ = G.rootNumber *
        ((G.Q : ℂ) ^ (1 - s) *
          ∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - s) + star (G.mu j))) *
        (G.gammaFactor s)⁻¹ := by
      rw [← G.gammaInv_product_eq_sourceSine hs, ← G.gammaFactor_inv_expansion]

/-- Pair-analytic and Gamma-pole-free locus for Kaczorowski--Perelli's
asymmetric functional equation. -/
def ExtendedSelbergClass.asymmetricFERegularSet (F : ExtendedSelbergClass) : Set ℂ :=
  F.completedFEContourSafeSet ∩ F.gammaData.asymmetricPoleFreeSet

/-- Kaczorowski--Perelli (2.2), derived from the raw completed functional
equation on its explicitly stated analytic/pole-free locus. -/
theorem ExtendedSelbergClass.asymmetricFunctionalEquation_eq_of_mem_regularSet
    (F : ExtendedSelbergClass) {s : ℂ} (hs : s ∈ F.asymmetricFERegularSet) :
    F s = F.gammaData.invariantRootNumber * F.gammaData.asymmetricS s *
      F.gammaData.asymmetricH s * selbergConjugateReflection F s := by
  have hraw := F.value_eq_raw_asymmetric_factor hs.1.1 hs.1.2 hs.2
  have hfactor := F.gammaData.asymmetricFactors_eq_rawFactor hs.2
  calc
    F s = F.gammaData.rootNumber *
        ((F.gammaData.Q : ℂ) ^ (1 - s) *
          ∏ j, Complex.Gamma ((F.gammaData.lambda j : ℂ) * (1 - s) +
            star (F.gammaData.mu j))) *
        (F.gammaData.gammaFactor s)⁻¹ * selbergConjugateReflection F s := hraw
    _ = F.gammaData.invariantRootNumber * F.gammaData.asymmetricS s *
        F.gammaData.asymmetricH s * selbergConjugateReflection F s := by
      rw [← hfactor]

theorem ExtendedSelbergClass.asymmetricFunctionalEquation_eqOn_regularSet
    (F : ExtendedSelbergClass) :
    Set.EqOn F
      (fun s ↦ F.gammaData.invariantRootNumber * F.gammaData.asymmetricS s *
        F.gammaData.asymmetricH s * selbergConjugateReflection F s)
      F.asymmetricFERegularSet := by
  intro s hs
  exact F.asymmetricFunctionalEquation_eq_of_mem_regularSet hs

end

end RHTower

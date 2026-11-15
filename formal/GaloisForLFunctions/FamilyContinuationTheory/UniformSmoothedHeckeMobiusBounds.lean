import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfTheGaussianKernelIsALogNormalWindow
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.EveryRayClassFunctionOfTheEisensteinFieldCarriesTheSeed
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane

/-!
# Uniform smoothed Möbius bounds for the Eisenstein Hecke family

The log-normal sum with Gaussian centre `5/6` over all squarefree ideals has size
`O(Q^ε X^a)`, uniformly over
ray class characters of the Eisenstein field, for `20999/24000 < a ≤ 2` and `ε > 0`.
Here `Q = 1 + 18 N(rad 𝔪) N(𝔪)` records the presented modulus, including deleted Euler factors.
The coefficients retain the Möbius signs. The proof moves the reciprocal Gaussian contour
into the unconditional zero-free half-plane and integrates the uniform reciprocal bound.
For `Q ≤ X^A`, every fixed `A ≥ 0` permits the bound `O_{A,δ}(X^(7/8+δ))` for every `δ > 0`.
-/

noncomputable section

open Complex MeasureTheory NumberField IsDedekindDomain
open scoped Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
open HeckeFamily HeckeReciprocalGrowth
open ExponentDynamicsOfTheCriticalStrip HeckeLFunctions

/-- The modulus and deleted Euler factors, measured at height zero. -/
def signedConductorScale (χ : Character) : ℝ := 1 + presentationComplexity χ 0

theorem signedConductorScale_ge_one (χ : Character) : 1 ≤ signedConductorScale χ := by
  unfold signedConductorScale presentationComplexity HeckeLogarithmic.complexity
  exact le_add_of_nonneg_right (by positivity)

theorem signedConductorScale_eq (χ : Character) :
    signedConductorScale χ = 1 + 18 * ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) *
      (χ.modulus.absNorm : ℝ) := by
  unfold signedConductorScale presentationComplexity HeckeLogarithmic.complexity
  norm_num
  ring

theorem presentationComplexity_le (χ : Character) (t : ℝ) :
    presentationComplexity χ t ≤ 2 * signedConductorScale χ * (1 + |t| ^ 2) := by
  have ht : (3 + |t|) ^ 2 ≤ 18 * (1 + |t| ^ 2) := by
    nlinarith only [sq_nonneg (|t| - 1), sq_nonneg |t|]
  have h := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) *
      (2 * (χ.modulus.absNorm : ℝ)) by positivity)
  dsimp [signedConductorScale, presentationComplexity, HeckeLogarithmic.complexity]
  simp only [abs_zero, add_zero] at *
  nlinarith only [h, sq_nonneg |t|]

/-- Uniform reciprocal growth with arbitrarily small modulus exponent and quadratic height cost. -/
theorem exists_uniform_signed_reciprocal_bound (a ε : ℝ)
    (ha : 20999 / 24000 < a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character) (s : ℂ), a ≤ s.re →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤
        C * (signedConductorScale χ) ^ ε * (1 + |s.im| ^ 2) := by
  have hβ : HeckeZeroSupremum.beta < a :=
    SubSevenEighthsZeroFree.hecke_beta_le_sub_seven_eighths.trans_lt ha
  let e : ℝ := min (1 / 2000) ((a - HeckeZeroSupremum.beta) / 16)
  have he : 0 < e := lt_min (by norm_num) (by linarith)
  have he' : e < 1 / 1000 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hmargin : HeckeZeroSupremum.beta + 8 * e ≤ a := by
    have h := min_le_right (1 / 2000 : ℝ) ((a - HeckeZeroSupremum.beta) / 16)
    change e ≤ (a - HeckeZeroSupremum.beta) / 16 at h
    linarith
  let η : ℝ := min ε 1
  have hη : 0 < η := lt_min hε zero_lt_one
  obtain ⟨D, hD, hb⟩ := reciprocal_subpower e η he he' hη
  refine ⟨D * (2 : ℝ) ^ η, by positivity, ?_⟩
  intro χ s hs
  have hQ : 0 ≤ signedConductorScale χ := (signedConductorScale_ge_one χ).trans' zero_le_one
  have hheight : (1 + |s.im| ^ 2) ^ η ≤ 1 + |s.im| ^ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg |s.im|))
        (show η ≤ 1 from min_le_right _ _)
  have hmod : (signedConductorScale χ) ^ η ≤ (signedConductorScale χ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le (signedConductorScale_ge_one χ) (min_le_left _ _)
  calc
    _ ≤ D * (presentationComplexity χ s.im) ^ η := hb χ s (hmargin.trans hs)
    _ ≤ D * (2 * signedConductorScale χ * (1 + |s.im| ^ 2)) ^ η := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by unfold presentationComplexity HeckeLogarithmic.complexity; positivity)
          (presentationComplexity_le χ s.im) hη.le) hD.le
    _ = D * ((2 : ℝ) ^ η * (signedConductorScale χ) ^ η *
        (1 + |s.im| ^ 2) ^ η) := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hQ]
    _ ≤ D * ((2 : ℝ) ^ η * (signedConductorScale χ) ^ ε * (1 + |s.im| ^ 2)) := by
      gcongr
    _ = _ := by ring

/-- The full reciprocal signal, with a constant independent of the character and modulus. -/
theorem exists_uniform_signed_signal_bound (a ε : ℝ)
    (ha : 20999 / 24000 < a) (ha2 : a ≤ 2) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character) (X : ℝ), 1 ≤ X →
      ‖HeckeSignal.signal χ (fun _ => 1) 0 X‖ ≤
        C * (signedConductorScale χ) ^ ε * X ^ a := by
  obtain ⟨D, hD, hb⟩ := exists_uniform_signed_reciprocal_bound a ε ha hε
  let B : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖ * Real.exp ((a - 5 / 6) ^ 2) * D *
    ∫ y : ℝ, Continuation.polynomialGaussian 2 y
  have hB : 0 ≤ B := by
    unfold B
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun y => by unfold Continuation.polynomialGaussian; positivity
  refine ⟨B + 1, by positivity, ?_⟩
  intro χ X hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hQ0 : 0 ≤ signedConductorScale χ := zero_le_one.trans (signedConductorScale_ge_one χ)
  have hβ : HeckeZeroSupremum.beta < a :=
    SubSevenEighthsZeroFree.hecke_beta_le_sub_seven_eighths.trans_lt ha
  rw [HeckeSignalShift.sub_contour_shift_left χ (fun _ => 1) (differentiableOn_const (1 : ℂ))
    (by intro s hs; norm_num) 0 a (by linarith) ha2 hβ hX, norm_mul]
  have hint := norm_integral_le_of_norm_le
    ((Continuation.polynomialGaussian_integrable 2).const_mul
      (X ^ a * Real.exp ((a - 5 / 6) ^ 2) * (D * (signedConductorScale χ) ^ ε)))
    (f := fun y : ℝ => Continuation.gaussianContourIntegrand
      (HeckeSignal.quotient χ (fun _ => 1)) 0 X ((a : ℂ) + y * I))
    (ae_of_all _ (fun y => by
      rw [Continuation.norm_gaussianContourIntegrand _ _ _ _ hX0]
      have h := hb χ ((a : ℂ) + y * I) (by simp)
      simp only [add_im, ofReal_im, mul_im, I_im, ofReal_re, mul_one, I_re,
        mul_zero, add_zero, zero_add] at h
      simp only [HeckeSignal.quotient, one_mul, add_zero]
      calc
        _ ≤ X ^ a * Real.exp ((a - 5 / 6) ^ 2) *
            (D * (signedConductorScale χ) ^ ε * (1 + |y| ^ 2)) * Real.exp (-(y ^ 2)) := by
          gcongr
        _ = _ := by unfold Continuation.polynomialGaussian; ring))
  have h := mul_le_mul_of_nonneg_left hint (norm_nonneg (1 / (2 * Real.pi) : ℂ))
  rw [integral_const_mul] at h
  calc
    _ ≤ B * (signedConductorScale χ) ^ ε * X ^ a := by
      convert h using 1 <;> first | rfl | (dsimp only [B]; ring)
    _ ≤ _ := by gcongr; linarith

/-- The analytic signal is the actual Möbius-signed sum over all squarefree ideals. -/
theorem signed_squarefree_sum_eq_signal (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {X : ℝ} (hX : 0 < X) :
    (∑' S : Finset (HeightOneSpectrum O), squarefreeCoeff 𝔪 ψ S *
      logNormalWindow (5 / 6) (X / squarefreeNorm S)) =
        HeckeSignal.signal (heckeFamilyOfRay 𝔪 ψ) (fun _ => 1) 0 X := by
  rw [← signal_heckeKernel_eq_tsum_logNormal 𝔪 ψ (5 / 6) hX,
    signal_two_eq_integral, HeckeSignal.signal_eq_contour _ _ _ hX]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  congr 1
  rw [← integral_neg_eq_self (fun y : ℝ => (X : ℂ) ^ linePoint y •
    heckeKernel 𝔪 ψ (5 / 6) (linePoint y))]
  apply integral_congr_ae
  filter_upwards [] with y
  have hre : 1 < (linePoint (-y)).re := by rw [linePoint_re]; norm_num
  have h0 : linePoint (-y) ≠ 0 := by intro h; norm_num [h] at hre
  have h1 : linePoint (-y) ≠ 1 := by intro h; norm_num [h] at hre
  rw [heckeKernel, heckeLFunction_eq_heckeL 𝔪 ψ hre,
    ← LFunction_heckeFamilyOfRay_eq_heckeL 𝔪 ψ hre]
  simp only [Continuation.gaussianContourIntegrand, HeckeSignal.quotient,
    ofReal_zero, add_zero, one_mul, smul_eq_mul]
  rw [show (2 : ℂ) + (y : ℂ) * I = linePoint (-y) by unfold linePoint; push_cast; ring,
    HeckeReciprocal.reciprocal_eq_inv _ h0 h1]
  push_cast
  ring

/-- Global signed cancellation, uniform in every ray class character of the Eisenstein field.
The constant depends only on `a` and `ε`; principal and imprimitive characters are included. -/
theorem exists_uniform_signed_squarefree_bound (a ε : ℝ)
    (ha : 20999 / 24000 < a) (ha2 : a ≤ 2) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (X : ℝ), 1 ≤ X →
      ‖∑' S : Finset (HeightOneSpectrum O), squarefreeCoeff 𝔪 ψ S *
        logNormalWindow (5 / 6) (X / squarefreeNorm S)‖ ≤
          C * (signedConductorScale (heckeFamilyOfRay 𝔪 ψ)) ^ ε * X ^ a := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_signed_signal_bound a ε ha ha2 hε
  refine ⟨C, hC, fun 𝔪 ψ X hX => ?_⟩
  rw [signed_squarefree_sum_eq_signal 𝔪 ψ (lt_of_lt_of_le zero_lt_one hX)]
  exact hb _ X hX

/-- The exponent `7/8` is attained with an arbitrarily small conductor cost. -/
theorem exists_uniform_signed_squarefree_seven_eighths (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (X : ℝ), 1 ≤ X →
      ‖∑' S : Finset (HeightOneSpectrum O), squarefreeCoeff 𝔪 ψ S *
        logNormalWindow (5 / 6) (X / squarefreeNorm S)‖ ≤
          C * (signedConductorScale (heckeFamilyOfRay 𝔪 ψ)) ^ ε * X ^ (7 / 8 : ℝ) :=
  exists_uniform_signed_squarefree_bound (7 / 8) ε (by norm_num) (by norm_num) hε

/-- Cancellation remains uniform when the presented modulus scale grows by any fixed power
of the summation scale. The constant may depend on that power and on the exponent loss. -/
theorem exists_uniform_signed_squarefree_growing_modulus (A δ : ℝ)
    (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (X : ℝ), 1 ≤ X →
      signedConductorScale (heckeFamilyOfRay 𝔪 ψ) ≤ X ^ A →
      ‖∑' S : Finset (HeightOneSpectrum O), squarefreeCoeff 𝔪 ψ S *
        logNormalWindow (5 / 6) (X / squarefreeNorm S)‖ ≤ C * X ^ (7 / 8 + δ) := by
  have hε : 0 < δ / (A + 1) := div_pos hδ (by linarith)
  obtain ⟨C, hC, hb⟩ := exists_uniform_signed_squarefree_seven_eighths (δ / (A + 1)) hε
  refine ⟨C, hC, fun 𝔪 ψ X hX hQ => ?_⟩
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hAε : A * (δ / (A + 1)) ≤ δ := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < A + 1)).mpr
    nlinarith only [hδ]
  have hp : (signedConductorScale (heckeFamilyOfRay 𝔪 ψ)) ^ (δ / (A + 1)) ≤ X ^ δ := by
    calc
      _ ≤ (X ^ A) ^ (δ / (A + 1)) := Real.rpow_le_rpow
        (zero_le_one.trans (signedConductorScale_ge_one _)) hQ hε.le
      _ = X ^ (A * (δ / (A + 1))) := (Real.rpow_mul hX0.le _ _).symm
      _ ≤ X ^ δ := Real.rpow_le_rpow_of_exponent_le hX hAε
  calc
    _ ≤ C * (signedConductorScale (heckeFamilyOfRay 𝔪 ψ)) ^ (δ / (A + 1)) *
        X ^ (7 / 8 : ℝ) := hb 𝔪 ψ X hX
    _ ≤ C * X ^ δ * X ^ (7 / 8 : ℝ) := by gcongr
    _ = C * X ^ (7 / 8 + δ) := by
      rw [mul_assoc, ← Real.rpow_add hX0, add_comm δ]

end GaloisForLFunctions.FamilyContinuationTheory

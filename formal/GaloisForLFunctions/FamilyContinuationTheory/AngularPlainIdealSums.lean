import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.AngularPeriodicSums
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.ActiveSupports
import GaloisForLFunctions.FamilyContinuationTheory.TheSexticGrossencharacterFactorizesTheProbeCorrection

/-! # Smooth plain ideal sums with nonzero infinity type

Unit-orbit summation transfers angular periodic cancellation to the actual ideal
coefficients of the sextic Grössencharacter family. Every finite character has the
same rapid long-sum bound; there is no exceptional principal finite twist.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
namespace GaloisForLFunctions.FamilyContinuationTheory
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open SchwartzPlanePoisson HeckeFamily HeckeRowClosure HeckeInverseAmplification
local notation "O" => Eisenstein.O

/-- The smooth ideal sum with sextic infinity type `k` and a finite character. -/
def grossenPlainIdealSum (χ : Character) (k : ℕ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : NonzeroIdeal, idealCoeff χ I.val * idealPsiSix I.val ^ k *
    W ((Ideal.absNorm I.val : ℝ) / X)

private theorem summable_angular_plain_elements (χ : Character) (k : ℕ)
    (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun z : O => elementCoeff χ z * elemPsiSix z ^ k *
      W (‖ringComplex z‖ ^ 2 / X)) := by
  have hs : Summable (fun z : O => ‖W (‖ringComplex z‖ ^ 2 / X)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W X hX)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro z
  rw [norm_mul, norm_mul, norm_pow]
  have he : ‖elementCoeff χ z‖ ≤ 1 := elementHom_norm χ z
  have ha := pow_le_one₀ (norm_nonneg (elemPsiSix z)) (norm_elemPsiSix_le_one z) (n := k)
  exact mul_le_of_le_one_left (norm_nonneg _)
    (by simpa only [one_mul] using mul_le_mul he ha (pow_nonneg (norm_nonneg _) _) zero_le_one)

/-- The six units give the exact conversion between the angular lattice sum and ideal sum. -/
theorem angular_plain_lattice_eq (χ : Character) (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (X : ℝ) (hX : 0 < X) :
    (∑' z : O, elementCoeff χ z * elemPsiSix z ^ (k + 1) *
      W (‖ringComplex z‖ ^ 2 / X)) = 6 * grossenPlainIdealSum χ (k + 1) W X := by
  let f : O → ℂ := fun z => elementCoeff χ z * elemPsiSix z ^ (k + 1) *
    W (‖ringComplex z‖ ^ 2 / X)
  have h0 : f 0 = 0 := by
    simp only [f, map_zero, zero_pow (Nat.succ_ne_zero k), mul_zero, zero_mul]
  have hu (u : Oˣ) (z : O) : f ((u : O) * z) = f z := by
    simp only [f, elementCoeff_unit_mul, map_mul, elemPsiSix_unit, one_mul,
      norm_mul, norm_ringComplex_unit]
  have heq := tsum_unit_invariant_ideals f (summable_angular_plain_elements χ (k + 1) W X hX) h0 hu
  have hterm (I : NonzeroIdeal) : f (cubicIdealGenerator I.val) =
      idealCoeff χ I.val * idealPsiSix I.val ^ (k + 1) *
        W ((Ideal.absNorm I.val : ℝ) / X) := by
    dsimp only [f]
    rw [← idealCoeff_span χ (cubicIdealGenerator_ne_zero I.val I.property),
      ← idealPsiSix_span_singleton, ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator]
  simp_rw [hterm] at heq
  have hcard : Nat.card Oˣ = 6 := card_units_thirdCyclotomic K
  simpa only [hcard, Nat.cast_ofNat, grossenPlainIdealSum] using heq

/-- For each fixed positive infinity type, every finite twist has arbitrarily rapid
smooth cancellation once the norm scale exceeds its modulus norm. -/
theorem grossenPlainIdealSum_bound (k A : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (W : 𝓢(ℝ, ℂ)),
      Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2 →
      ∀ (χ : Character) (X : ℝ), 0 < X →
      ‖grossenPlainIdealSum χ (k + 1) W X‖ ≤
        (C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
          (Ideal.absNorm χ.modulus : ℝ) /
            (1 + X / (Ideal.absNorm χ.modulus : ℝ)) ^ A := by
  obtain ⟨S, C, hC, hb⟩ := conjugate_angular_periodic_sum_bound (6 * k + 5) A
  refine ⟨S, C / 6, by positivity, ?_⟩
  intro W hW χ X hX
  let c := HeckePresentation.generator χ
  have hc : c ≠ 0 := NeZero.ne _
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  have hP : ∀ r, ‖HeckePresentation.principalResidue χ r‖ ≤ 1 :=
    FiniteRayExpansion.norm_char_le_one _
  have h := hb W hW c hc (HeckePresentation.principalResidue χ) 1 X zero_le_one hP hX
  have hn : ‖ringComplex c‖ ^ 2 = (Ideal.absNorm χ.modulus : ℝ) := by
    rw [ringComplex_norm_sq_eq_absNorm_span, HeckePresentation.span_generator]
  have hexp : 6 * k + 5 + 1 = 6 * (k + 1) := by omega
  have heq : (∑' z : O, HeckePresentation.principalResidue χ
      (Ideal.Quotient.mk (Ideal.span {c}) z) *
      (((starRingEnd ℂ) (ringComplex z) / (‖ringComplex z‖ : ℂ)) ^ (6 * k + 5 + 1) *
        W (‖ringComplex z‖ ^ 2 / X))) = 6 * grossenPlainIdealSum χ (k + 1) W X := by
    rw [← angular_plain_lattice_eq χ k W X hX]
    apply tsum_congr
    intro z
    rw [HeckePresentation.principalResidue_mk, hexp, pow_mul]
    simp only [elemPsiSix_apply, complexUnitConj_apply, mul_assoc]
  have hsix : ‖(6 : ℂ)‖ = 6 := by norm_num
  rw [heq, norm_mul, hsix, hn, mul_one] at h
  calc
    _ = (6 * ‖grossenPlainIdealSum χ (k + 1) W X‖) / 6 := by ring
    _ ≤ ((C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (Ideal.absNorm χ.modulus : ℝ) / (1 + X / (Ideal.absNorm χ.modulus : ℝ)) ^ A) / 6 :=
      div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by ring

/-- Radial Mellin twists cost only a polynomial in height, uniformly in the finite character. -/
theorem grossenPlainIdealSum_height_bound (k A : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    ∃ (J : ℕ) (C : ℝ), 0 < C ∧ ∀ (χ : Character) (X : ℝ), 0 < X →
      ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖grossenPlainIdealSum χ (k + 1) (HeckeInverseAmplification.twistProfile W σ t) X‖ ≤
        (C * (1 + ‖t‖) ^ J) * (Ideal.absNorm χ.modulus : ℝ) /
          (1 + X / (Ideal.absNorm χ.modulus : ℝ)) ^ A := by
  obtain ⟨S, C, hC, hb⟩ := grossenPlainIdealSum_bound k A
  have hsmooth : ContDiff ℝ ∞ (W : ℝ → ℂ) := W.smooth ⊤
  obtain ⟨J, D, hD, hheight⟩ := CenteredMomentDetectorDictionary.interpolatedProfile_uniform
    W (1 / 2) 2 (by norm_num) hW hsmooth S
  refine ⟨J, C * D, mul_pos hC hD, ?_⟩
  intro χ X hX σ hσ t
  let V := CenteredMomentDetectorDictionary.interpolatedProfile
    W (1 / 2) 2 (by norm_num) hW hsmooth σ t
  have hV : (V : ℝ → ℂ) = HeckeInverseAmplification.twistProfile W σ t :=
    funext (CenteredMomentDetectorDictionary.interpolatedProfile_apply
      W (1 / 2) 2 (by norm_num) hW hsmooth σ t)
  have hs : Function.support (V : ℝ → ℂ) ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
    rw [hV]
    exact (HeckeInverseAmplification.twistProfile_support W σ t).trans hW
  have h := hb V hs χ X hX
  rw [hV] at h
  refine h.trans ?_
  calc
    _ ≤ (C * (D * (1 + ‖t‖) ^ J)) * (Ideal.absNorm χ.modulus : ℝ) /
        (1 + X / (Ideal.absNorm χ.modulus : ℝ)) ^ A := by
      gcongr
      exact hheight σ hσ t
    _ = _ := by ring

end GaloisForLFunctions.FamilyContinuationTheory

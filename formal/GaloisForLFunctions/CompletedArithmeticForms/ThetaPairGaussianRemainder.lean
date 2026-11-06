import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairApertureCurrent
import GaloisForLFunctions.RHTower.GaussianWindowHankelPositiveDefinite

/-!
# Rank-uniform Gaussian Hankel remainder for ordinary theta pairs

The uniform error in the actual Hedenmalm current bounds its action on
every polynomial square by the same error constant times the Gaussian
square norm. The resulting relative bound holds at every finite Hankel
rank, with no rank or degree in the error constant.
-/

open MeasureTheory Set Complex Filter Polynomial
open scoped BigOperators ENNReal
namespace GaloisForLFunctions.CompletedArithmeticForms
open _root_.RHTower
noncomputable section

/-- The rectangular ordinary-pair approximation to the actual Hedenmalm current. -/
def thetaPairApertureCurrentHead (M : ℕ) (a b : ℝ) : ℝ :=
  2 * ∑ p ∈ (Finset.range M ×ˢ Finset.range M),
    thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b

/-- Frequency-uniform error constant for the rectangular current approximation. -/
def thetaPairCurrentRemainderBound (a : ℝ) (M : ℕ) : ℝ :=
  288 * a * besselFirstAtomTailCost 0 * Real.exp (-Real.pi * ((M : ℝ) + 1)) /
    ((9 - a ^ 2) ^ 2 * (1 - Real.exp (-Real.pi)) ^ 2)

private theorem abs_pairCurrentError_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (M : ℕ) (b : ℝ) :
    |thetaCuspCenterMixedFourierCurrent a (by rw [abs_of_nonneg ha0]; linarith) b -
      thetaPairApertureCurrentHead M a b| ≤ thetaPairCurrentRemainderBound a M := by
  exact thetaCuspCenterMixedFourierCurrent_pair_remainder_le ha0 ha b M

/-- Frequency measurability follows by translating the moving tail to a fixed half-line. -/
private theorem stronglyMeasurable_pairApertureSpectrum (n m : ℕ) (a : ℝ) :
    StronglyMeasurable (thetaPairApertureSpectrum n m a) := by
  let K : (ℝ × ℝ) × ℝ → ℂ := fun p =>
    (thetaCuspSourceTerm (p.1.1 / 2 + p.2) n *
      thetaCuspSourceTerm (p.1.1 / 2 - p.2) m : ℂ) *
        thetaWignerDifferencePhase p.1.2 p.2
  have hK : Continuous K := by
    unfold K thetaCuspSourceTerm thetaCuspSeed thetaWignerDifferencePhase
    fun_prop
  let g : ℝ × ℝ → ℝ := fun p => (thetaCuspSourcePairWigner n m (p.1 / 2) p.2).re
  have hg : StronglyMeasurable g := by
    have hC := hK.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
    simpa only [g, K, thetaCuspSourcePairWigner] using
      Complex.continuous_re.comp_stronglyMeasurable hC
  have hshift : Measurable (fun p : (ℝ × ℝ) × ℝ => (p.1.1 + p.2, p.1.2)) := by
    fun_prop
  have ht := (hg.comp_measurable hshift).integral_prod_right'
    (ν := volume.restrict (Ioi (0 : ℝ)))
  have he : (fun p : ℝ × ℝ => thetaPairCenterTailSpectrum n m p.1 p.2) =
      fun p => ∫ s in Ioi (0 : ℝ), g (p.1 + s, p.2) := by
    funext p
    have h := GaloisForLFunctions.RHTower.setIntegral_Ioi_comp_add_right
      (fun s => g (s, p.2)) p.1 p.1
    rw [sub_self] at h
    change (∫ s in Ioi p.1, g (s, p.2)) = _
    apply h.symm.trans
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    change g (s + p.1, p.2) = g (p.1 + s, p.2)
    rw [add_comm s p.1]
  have htail : StronglyMeasurable (fun p : ℝ × ℝ =>
      thetaPairCenterTailSpectrum n m p.1 p.2) := by
    rw [he]
    exact ht
  have hw : Continuous (thetaCuspCenterTailWeight a) := by
    unfold thetaCuspCenterTailWeight
    fun_prop
  have hp : StronglyMeasurable (fun p : ℝ × ℝ =>
      thetaCuspCenterTailWeight a p.2 * thetaPairCenterTailSpectrum n m p.2 p.1) :=
    (hw.stronglyMeasurable.comp_measurable measurable_snd).mul
      (htail.comp_measurable (by fun_prop : Measurable (fun p : ℝ × ℝ => (p.2, p.1))))
  change StronglyMeasurable (fun b : ℝ => ∫ r in Ioi (0 : ℝ),
    thetaCuspCenterTailWeight a r * thetaPairCenterTailSpectrum n m r b)
  exact hp.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))

private theorem stronglyMeasurable_pairApertureCurrentHead (M : ℕ) (a : ℝ) :
    StronglyMeasurable (thetaPairApertureCurrentHead M a) := by
  classical
  have hs (S : Finset (ℕ × ℕ)) : StronglyMeasurable (fun b : ℝ =>
      ∑ p ∈ S, thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b) := by
    induction S using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (stronglyMeasurable_const : StronglyMeasurable (fun _ : ℝ => (0 : ℝ)))
    | @insert p S hp ih =>
      have hsum := (stronglyMeasurable_pairApertureSpectrum (p.1 + 1) (p.2 + 1) a).add ih
      change StronglyMeasurable (fun b : ℝ =>
        thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b +
          ∑ q ∈ S, thetaPairApertureSpectrum (q.1 + 1) (q.2 + 1) a b) at hsum
      simpa only [Finset.sum_insert hp] using hsum
  exact stronglyMeasurable_const.mul (hs _)

private theorem pairCurrentError_memLp_top (tau : ℝ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (M : ℕ) :
    MemLp (fun b => thetaCuspCenterMixedFourierCurrent a
      (by rw [abs_of_nonneg ha0]; linarith) b - thetaPairApertureCurrentHead M a b)
      ∞ (gaussianWindowMeasure tau) := by
  apply memLp_top_of_bound
    ((continuous_thetaCuspCenterMixedFourierCurrent a
      (by rw [abs_of_nonneg ha0]; linarith)).stronglyMeasurable.sub
        (stronglyMeasurable_pairApertureCurrentHead M a)).aestronglyMeasurable
    (thetaPairCurrentRemainderBound a M)
  filter_upwards with b
  change ‖thetaCuspCenterMixedFourierCurrent a _ b - thetaPairApertureCurrentHead M a b‖ ≤ _
  rw [Real.norm_eq_abs]
  exact abs_pairCurrentError_le ha0 ha M b


private theorem pairCurrentHead_memLp_top (tau : ℝ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (M : ℕ) :
    MemLp (thetaPairApertureCurrentHead M a) ∞ (gaussianWindowMeasure tau) := by
  have hA : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith
  have hJ := thetaCuspCenterMixedFourierCurrent_memLp_top tau a hA
  have hd := pairCurrentError_memLp_top tau ha0 ha M
  have he : thetaPairApertureCurrentHead M a =
      thetaCuspCenterMixedFourierCurrent a hA -
        (fun b => thetaCuspCenterMixedFourierCurrent a hA b -
          thetaPairApertureCurrentHead M a b) := by
    funext b
    change thetaPairApertureCurrentHead M a b =
      thetaCuspCenterMixedFourierCurrent a hA b -
        (thetaCuspCenterMixedFourierCurrent a hA b - thetaPairApertureCurrentHead M a b)
    ring
  rw [he]
  exact hJ.sub hd

private theorem pairCurrentError_weightedMoment_eq {a tau : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (htau : 0 < tau) (M k : ℕ) :
    weightedMoment (gaussianWindowMeasure tau)
      (fun b => thetaCuspCenterMixedFourierCurrent a
        (by rw [abs_of_nonneg ha0]; linarith) b - thetaPairApertureCurrentHead M a b) k =
      weightedMoment (gaussianWindowMeasure tau)
        (thetaCuspCenterMixedFourierCurrent a (by rw [abs_of_nonneg ha0]; linarith)) k -
      weightedMoment (gaussianWindowMeasure tau) (thetaPairApertureCurrentHead M a) k := by
  letI := gaussianWindowMeasure_finite htau
  have hmu := gaussianWindowMeasure_hasEntireExponentialMoments htau
  have hJ := thetaCuspCenterMixedFourierCurrent_memLp_top tau a
    (by rw [abs_of_nonneg ha0]; linarith)
  have hH := pairCurrentHead_memLp_top tau ha0 ha M
  unfold weightedMoment
  simp_rw [mul_sub]
  exact integral_sub
    (integrable_monomial_mul_of_entireExponentialMoments hmu _ hJ k)
    (integrable_monomial_mul_of_entireExponentialMoments hmu _ hH k)

/-- Every polynomial square sees the same relative Gaussian truncation error, regardless of degree. -/
theorem thetaPairCurrent_gaussian_polynomial_remainder_le {a tau : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (htau : 0 < tau) (M : ℕ) (p : Polynomial ℝ) :
    |∫ b, (p.eval b) ^ 2 *
      (thetaCuspCenterMixedFourierCurrent a (by rw [abs_of_nonneg ha0]; linarith) b -
        thetaPairApertureCurrentHead M a b) ∂gaussianWindowMeasure tau| ≤
      thetaPairCurrentRemainderBound a M *
        ∫ b, (p.eval b) ^ 2 ∂gaussianWindowMeasure tau := by
  letI := gaussianWindowMeasure_finite htau
  have hd := pairCurrentError_memLp_top tau ha0 ha M
  have hi := gaussianWindow_integrable_sq_mul htau hd p
  have hOne : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (gaussianWindowMeasure tau) := memLp_const 1
  have hp : Integrable (fun b : ℝ => (p.eval b) ^ 2) (gaussianWindowMeasure tau) := by
    simpa only [mul_one] using gaussianWindow_integrable_sq_mul htau hOne p
  calc
    _ ≤ ∫ b, ‖(p.eval b) ^ 2 *
        (thetaCuspCenterMixedFourierCurrent a (by rw [abs_of_nonneg ha0]; linarith) b -
          thetaPairApertureCurrentHead M a b)‖ ∂gaussianWindowMeasure tau := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := gaussianWindowMeasure tau) (fun b : ℝ => (p.eval b) ^ 2 *
          (thetaCuspCenterMixedFourierCurrent a (by rw [abs_of_nonneg ha0]; linarith) b -
            thetaPairApertureCurrentHead M a b))
    _ ≤ ∫ b, thetaPairCurrentRemainderBound a M * (p.eval b) ^ 2
        ∂gaussianWindowMeasure tau := by
      apply integral_mono_ae hi.norm (hp.const_mul _)
      filter_upwards with b
      change ‖(p.eval b) ^ 2 *
        (thetaCuspCenterMixedFourierCurrent a _ b - thetaPairApertureCurrentHead M a b)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (p.eval b))]
      calc
        _ ≤ (p.eval b) ^ 2 * thetaPairCurrentRemainderBound a M :=
          mul_le_mul_of_nonneg_left (abs_pairCurrentError_le ha0 ha M b) (sq_nonneg _)
        _ = _ := mul_comm _ _
    _ = _ := integral_const_mul _ _

/-- The error Hankel form is bounded relative to the Gaussian moment form at every finite rank. -/
theorem thetaPairCurrent_gaussian_hankel_remainder_le {a tau : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (htau : 0 < tau) (M N : ℕ) (v : Fin N → ℝ) :
    |∑ i : Fin N, ∑ j : Fin N, v i * v j *
      (weightedMoment (gaussianWindowMeasure tau)
          (thetaCuspCenterMixedFourierCurrent a (by rw [abs_of_nonneg ha0]; linarith))
          (i.val + j.val) -
        weightedMoment (gaussianWindowMeasure tau) (thetaPairApertureCurrentHead M a)
          (i.val + j.val))| ≤
      thetaPairCurrentRemainderBound a M *
        (∑ i : Fin N, ∑ j : Fin N, v i * v j *
          weightedMoment (gaussianWindowMeasure tau) (fun _ => 1) (i.val + j.val)) := by
  simp_rw [← pairCurrentError_weightedMoment_eq ha0 ha htau M]
  letI := gaussianWindowMeasure_finite htau
  have hmu := gaussianWindowMeasure_hasEntireExponentialMoments htau
  have hd := pairCurrentError_memLp_top tau ha0 ha M
  have hOne : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (gaussianWindowMeasure tau) := memLp_const 1
  have hform (J : ℝ → ℝ) (hJ : MemLp J ∞ (gaussianWindowMeasure tau)) :
      (∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) J (i.val + j.val)) =
      ∫ b, ((finCoefficientPolynomial v).eval b) ^ 2 * J b
        ∂gaussianWindowMeasure tau := by
    rw [← _root_.HTGeometry.momentFunctional_sq_eq_hankelForm]
    exact momentFunctional_weightedMoment_sq_eq_integral hmu J hJ (finCoefficientPolynomial v)
  rw [hform _ hd, hform _ hOne]
  simpa only [mul_one] using
    thetaPairCurrent_gaussian_polynomial_remainder_le ha0 ha htau M (finCoefficientPolynomial v)

end
end GaloisForLFunctions.CompletedArithmeticForms

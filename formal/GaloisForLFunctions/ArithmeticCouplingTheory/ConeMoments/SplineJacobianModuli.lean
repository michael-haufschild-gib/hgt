import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineJacobianPairings
import GaloisForLFunctions.HTGeometry.RiemannSumCell

/-!
# Quantitative continuity of spline moment Jacobians

Finite Fourier sums give a quadratic frequency bound for the second derivative.
The reciprocal-spline primitive has a uniform derivative bound. Together these
control both real Jacobian pairings on every translated grid, and give the
nonlinear increment estimate needed to move nodes while preserving distinctness.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- The second derivative of a modulated spline numerator. -/
def shiftedSplineSecond (δ t x : ℝ) : ℂ :=
  ∑ j : Fin 9, -((splineCoefficient δ j*(t+splineShift j)^2 : ℝ) : ℂ)*
    phase (t+splineShift j) x

def splineSecondBound (δ t : ℝ) : ℝ :=
  ∑ j : Fin 9, |splineCoefficient δ j*(t+splineShift j)^2|

def inverseSplineBound (δ : ℝ) : ℝ := splineInvScale δ*(1/(1-splineRatio δ)^8)

def splineDualBound (δ s : ℝ) : ℝ :=
  (splineInvScale δ/(s+8))*(1/(1-splineRatio δ)^8)

lemma hasDerivAt_shiftedSplineSlope (δ t x : ℝ) :
    HasDerivAt (shiftedSplineSlope δ t) (shiftedSplineSecond δ t x) x := by
  have h := HasDerivAt.fun_sum fun j (_ : j ∈ (univ : Finset (Fin 9))) =>
    (hasDerivAt_phase (t+splineShift j) x).const_mul
      (Complex.I*((splineCoefficient δ j*(t+splineShift j) : ℝ) : ℂ))
  have he : (∑ j : Fin 9, (Complex.I*((splineCoefficient δ j*(t+splineShift j) : ℝ) : ℂ))*
      (phase (t+splineShift j) x*((((t+splineShift j) : ℝ) : ℂ)*Complex.I))) =
      shiftedSplineSecond δ t x := by
    apply sum_congr rfl
    intro j _
    simp only [Complex.ofReal_mul, Complex.ofReal_pow]
    calc
      _ = (Complex.I*Complex.I)*(splineCoefficient δ j : ℂ)*
          (((t+splineShift j : ℝ) : ℂ)^2)*phase (t+splineShift j) x := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he] at h
  exact h

lemma norm_shiftedSplineSecond_le (δ t x : ℝ) :
    ‖shiftedSplineSecond δ t x‖ ≤ splineSecondBound δ t := by
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro j _
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, phase_norm, mul_one]

lemma norm_inverseSplineNumerator_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ‖inverseSplineNumerator δ x‖ ≤ inverseSplineBound δ := by
  have h := tsum_of_norm_bounded ((hasSum_splineBinomialMass hδ).mul_left (splineInvScale δ))
    (fun k : ℕ => show ‖-((splineInvScale δ*splineBinomialMass δ k : ℝ) : ℂ)*
        phase (-(0+8+2*k)) x‖ ≤ splineInvScale δ*splineBinomialMass δ k by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (splineInvScale_pos δ).le (splineBinomialMass_nonneg δ k)),
        phase_norm, mul_one])
  rw [(hasSum_splineDual_derivative hδ 0 x).tsum_eq] at h
  simpa only [inverseSplineBound, neg_zero, phase_zero, neg_mul, one_mul, norm_neg] using h

lemma norm_shiftedSplineSlope_sub_le (δ t x y : ℝ) :
    ‖shiftedSplineSlope δ t y-shiftedSplineSlope δ t x‖ ≤ splineSecondBound δ t*|y-x| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.univ) (fun u _ => (hasDerivAt_shiftedSplineSlope δ t u).hasDerivWithinAt)
      (fun u _ => norm_shiftedSplineSecond_le δ t u) convex_univ (Set.mem_univ x) (Set.mem_univ y)

lemma norm_splineDual_sub_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (x y : ℝ) :
    ‖splineDual δ s y-splineDual δ s x‖ ≤ inverseSplineBound δ*|y-x| := by
  have hd (u : ℝ) := hasDerivAt_splineDual (s := s) hδ (by linarith only [hs]) u
  have hb (u : ℝ) : ‖-phase (-s) u*inverseSplineNumerator δ u‖ ≤ inverseSplineBound δ := by
    rw [norm_mul, norm_neg, phase_norm, one_mul]
    exact norm_inverseSplineNumerator_le hδ u
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.univ) (fun u _ => (hd u).hasDerivWithinAt) (fun u _ => hb u)
      convex_univ (Set.mem_univ x) (Set.mem_univ y)

/-- A translated numerator has a quadratic, polynomial-frequency remainder. -/
theorem norm_spline_increment_remainder_le (δ t x : ℝ) {R a b : ℝ}
    (ha : |a| ≤ R) (hb : |b| ≤ R) :
    ‖shiftedSplineNumerator δ t (x+b)-shiftedSplineNumerator δ t (x+a)-
      shiftedSplineSlope δ t x*((b-a : ℝ) : ℂ)‖ ≤ splineSecondBound δ t*R*|b-a| := by
  let f : ℝ → ℂ := fun y => shiftedSplineNumerator δ t y-
    shiftedSplineSlope δ t x*(y : ℂ)
  have hd (y : ℝ) : HasDerivAt f (shiftedSplineSlope δ t y-shiftedSplineSlope δ t x) y := by
    have hlin := Complex.ofRealCLM.hasDerivAt (x := y)
    have h := (hasDerivAt_shiftedSplineNumerator δ t y).sub
      (hlin.const_mul (shiftedSplineSlope δ t x))
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using! h
  have hC : 0 ≤ splineSecondBound δ t := sum_nonneg fun _ _ => abs_nonneg _
  have hbound (y : ℝ) (hy : y ∈ Set.Icc (x-R) (x+R)) :
      ‖shiftedSplineSlope δ t y-shiftedSplineSlope δ t x‖ ≤ splineSecondBound δ t*R := by
    apply (norm_shiftedSplineSlope_sub_le δ t x y).trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact abs_le.mpr ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
  have hxa : x+a ∈ Set.Icc (x-R) (x+R) := by
    obtain ⟨ha1,ha2⟩ := abs_le.mp ha
    exact ⟨by linarith only [ha1], by linarith only [ha2]⟩
  have hxb : x+b ∈ Set.Icc (x-R) (x+R) := by
    obtain ⟨hb1,hb2⟩ := abs_le.mp hb
    exact ⟨by linarith only [hb1], by linarith only [hb2]⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y (_ : y ∈ Set.Icc (x-R) (x+R)) => (hd y).hasDerivWithinAt)
    hbound (convex_Icc _ _) hxa hxb
  have he : f (x+b)-f (x+a)=shiftedSplineNumerator δ t (x+b)-shiftedSplineNumerator δ t (x+a)-
      shiftedSplineSlope δ t x*((b-a : ℝ) : ℂ) := by
    dsimp only [f]
    push_cast
    ring
  rw [he, Real.norm_eq_abs, show x+b-(x+a)=b-a by ring] at h
  exact h

lemma abs_splineShift_le (j : Fin 9) : |splineShift j| ≤ 8 := by
  have hj : j.val ≤ 8 := by omega
  have hjR : (j.val : ℝ) ≤ 8 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  unfold splineShift
  exact abs_le.mpr ⟨by linarith only [hjR], by linarith only [hj0]⟩

lemma splineSlopeBound_le {t L : ℝ} (ht : |t| ≤ L) (δ : ℝ) :
    splineSlopeBound δ t ≤ (L+8)*splineNumeratorBound δ := by
  unfold splineSlopeBound splineNumeratorBound
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  rw [abs_mul]
  have ha : |t+splineShift j| ≤ |t|+|splineShift j| := by
    simpa only [Real.norm_eq_abs] using norm_add_le t (splineShift j)
  have hfreq := ha.trans (add_le_add ht (abs_splineShift_le j))
  calc
    _ ≤ |splineCoefficient δ j| *(L+8) := mul_le_mul_of_nonneg_left hfreq (abs_nonneg _)
    _ = _ := by ring

lemma splineSecondBound_le {t L : ℝ} (ht : |t| ≤ L) (δ : ℝ) :
    splineSecondBound δ t ≤ (L+8)^2*splineNumeratorBound δ := by
  unfold splineSecondBound splineNumeratorBound
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  rw [abs_mul, abs_pow]
  have ha : |t+splineShift j| ≤ |t|+|splineShift j| := by
    simpa only [Real.norm_eq_abs] using norm_add_le t (splineShift j)
  have hfreq := ha.trans (add_le_add ht (abs_splineShift_le j))
  calc
    _ ≤ |splineCoefficient δ j| *(L+8)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) hfreq 2) (abs_nonneg _)
    _ = _ := by ring

def splinePairLipschitzBound (δ t s : ℝ) : ℝ :=
  splineSecondBound δ t*splineDualBound δ s+splineSlopeBound δ t*inverseSplineBound δ

private lemma norm_mul_sub_mul_le_bounds {a b c d : ℂ} {A B C D : ℝ}
    (hab : ‖a-b‖ ≤ A) (hc : ‖c‖ ≤ B) (hb : ‖b‖ ≤ C) (hcd : ‖c-d‖ ≤ D) :
    ‖a*c-b*d‖ ≤ A*B+C*D := by
  have he : a*c-b*d=(a-b)*c+b*(c-d) := by ring
  rw [he]
  calc
    _ ≤ ‖a-b‖*‖c‖+‖b‖*‖c-d‖ := by
      simpa only [norm_mul] using norm_add_le ((a-b)*c) (b*(c-d))
    _ ≤ _ := add_le_add
      (mul_le_mul hab hc (norm_nonneg _) ((norm_nonneg _).trans hab))
      (mul_le_mul hb hcd (norm_nonneg _) ((norm_nonneg _).trans hb))

lemma norm_spline_pair_integrand_sub_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (t x y : ℝ) :
    ‖shiftedSplineSlope δ t y*splineDual δ s y-shiftedSplineSlope δ t x*splineDual δ s x‖ ≤
      splinePairLipschitzBound δ t s*|y-x| := by
  have h := norm_mul_sub_mul_le_bounds (norm_shiftedSplineSlope_sub_le δ t x y)
    (norm_splineDual_le (s := s) hδ (by linarith only [hs]) y) (norm_shiftedSplineSlope_le δ t x)
    (norm_splineDual_sub_le hδ hs x y)
  refine h.trans_eq ?_
  change splineSecondBound δ t*|y-x| *splineDualBound δ s+
    splineSlopeBound δ t*(inverseSplineBound δ*|y-x|)=_
  unfold splinePairLipschitzBound
  ring

lemma norm_spline_conj_pair_integrand_sub_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (t x y : ℝ) :
    ‖shiftedSplineSlope δ t y*(starRingEnd ℂ) (splineDual δ s y)-
      shiftedSplineSlope δ t x*(starRingEnd ℂ) (splineDual δ s x)‖ ≤
      splinePairLipschitzBound δ t s*|y-x| := by
  have hnorm : ‖(starRingEnd ℂ) (splineDual δ s y)‖ ≤ splineDualBound δ s := by
    rw [Complex.norm_conj]
    exact norm_splineDual_le (s := s) hδ (by linarith only [hs]) y
  have hdiff : ‖(starRingEnd ℂ) (splineDual δ s y)-(starRingEnd ℂ) (splineDual δ s x)‖ ≤
      inverseSplineBound δ*|y-x| := by
    rw [← map_sub, Complex.norm_conj]
    exact norm_splineDual_sub_le hδ hs x y
  refine (norm_mul_sub_mul_le_bounds (norm_shiftedSplineSlope_sub_le δ t x y)
    hnorm (norm_shiftedSplineSlope_le δ t x) hdiff).trans_eq ?_
  unfold splinePairLipschitzBound
  ring

/-- Grid quadrature error is independent of the grid's translation. -/
theorem norm_spline_pair_grid_error_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (t a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, h • (shiftedSplineSlope δ t (a+k*h)*splineDual δ s (a+k*h)))-
      ∫ x in a..(a+n*h), shiftedSplineSlope δ t x*splineDual δ s x‖ ≤
      n*splinePairLipschitzBound δ t s*h^2/2 := by
  apply HTGeometry.norm_sum_smul_sub_integral_le hh
    (((continuous_shiftedSplineSlope δ t).mul (continuous_splineDual hδ hs)).intervalIntegrable _ _)
  intro k hk x hx
  have he := norm_spline_pair_integrand_sub_le hδ hs t (a+k*h) x
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at he
  exact he

theorem norm_spline_conj_pair_grid_error_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (t a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, h • (shiftedSplineSlope δ t (a+k*h)*
      (starRingEnd ℂ) (splineDual δ s (a+k*h))))-
      ∫ x in a..(a+n*h), shiftedSplineSlope δ t x*(starRingEnd ℂ) (splineDual δ s x)‖ ≤
      n*splinePairLipschitzBound δ t s*h^2/2 := by
  apply HTGeometry.norm_sum_smul_sub_integral_le hh
    (((continuous_shiftedSplineSlope δ t).mul
      (continuous_conj_splineDual hδ hs)).intervalIntegrable _ _)
  intro k hk x hx
  have he := norm_spline_conj_pair_integrand_sub_le hδ hs t (a+k*h) x
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at he
  exact he

#print axioms norm_spline_increment_remainder_le
#print axioms norm_spline_pair_grid_error_le
#print axioms norm_spline_conj_pair_grid_error_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

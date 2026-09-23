import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelSmoothProbeSummability
import GaloisForLFunctions.RHTower.CCMWeightedXiLandau

/-!
# Physical theta--Abel Landau rigidity without a rightmost zero

A squared generic smooth aperture supplies reciprocal-square decay on every multiplicity copy.
The exact physical log-window multiplier, restored theta--Abel factor, and compact aperture
Laplace amplitude are uniformly bounded and nonzero throughout the open theta--Abel strip.
Consequently they define a coefficient system for Xi pole tomography.

Landau's theorem then replaces finite dominant-layer asymptotics: if any strict-right Xi divisor
exists, the complete log-sampled physical scalar carrier is cofinally unbounded below. This does
not require the supremum of real parts to be attained, isolated, or supported on a finite layer.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Theta--Abel coordinate `rho - 1`, expressed on a multiplicity-exact right-Xi copy. -/
def xiRightThetaAbelExponent (q : XiRightZeroCopy) : ℂ :=
  xiRightCenteredZero q - 1 / 2

theorem xiRightThetaAbelExponent_re_neg (q : XiRightZeroCopy) :
    (xiRightThetaAbelExponent q).re < 0 := by
  have h := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  norm_num [xiRightThetaAbelExponent, Complex.sub_re]
  linarith

theorem xiRightThetaAbelExponent_re_gt_neg_half (q : XiRightZeroCopy) :
    -(1 / 2 : ℝ) < (xiRightThetaAbelExponent q).re := by
  have h := xiRightCenteredZero_re_pos q
  norm_num [xiRightThetaAbelExponent, Complex.sub_re]
  linarith

theorem xiRightThetaAbelExponent_ne_zero (q : XiRightZeroCopy) :
    xiRightThetaAbelExponent q ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have hn := xiRightThetaAbelExponent_re_neg q
  simp at hre
  linarith

theorem xiRightThetaAbelExponent_ne_neg_one (q : XiRightZeroCopy) :
    xiRightThetaAbelExponent q ≠ -1 := by
  intro h
  have hre := congrArg Complex.re h
  have hp := xiRightThetaAbelExponent_re_gt_neg_half q
  simp at hre
  linarith

theorem xiRightThetaAbelExponent_conj (q : XiRightZeroCopy) :
    xiRightThetaAbelExponent (xiRightZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (xiRightThetaAbelExponent q) := by
  unfold xiRightThetaAbelExponent
  rw [xiRightCenteredZero_conj, map_sub, map_div₀, map_one, map_ofNat]

theorem xiRightThetaAbelExponent_eq_of_support_eq {q r : XiRightZeroCopy}
    (h : q.1.1 = r.1.1) :
    xiRightThetaAbelExponent q = xiRightThetaAbelExponent r := by
  rw [xiRightThetaAbelExponent, xiRightThetaAbelExponent,
    xiRightCenteredZero_eq_of_support_eq h]

theorem rectangularWindowAmplitude_ne_zero_of_re_neg
    {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : z.re < 0) :
    rectangularWindowAmplitude A z ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hrev : rectangularWindowAmplitude A (-z) ≠ 0 :=
    rectangularWindowAmplitude_ne_zero hA (by simpa using neg_pos.mpr hz)
  rw [rectangularWindowAmplitude_neg hz0] at hrev
  exact fun h => hrev (by rw [h, mul_zero])

theorem norm_rectangularWindowAmplitude_xiRightThetaAbel_le
    {A : ℝ} (hA : 0 < A) (q : XiRightZeroCopy) :
    ‖rectangularWindowAmplitude A (xiRightThetaAbelExponent q)‖ ≤
      1 + Real.exp (A / 2) := by
  let z := xiRightThetaAbelExponent q
  have hz0 : z ≠ 0 := xiRightThetaAbelExponent_ne_zero q
  have hzNorm : 1 < ‖z‖ := by
    have him : z.im = (q.1.1 : ℂ).im := by
      simp [z, xiRightThetaAbelExponent, xiRightCenteredZero, xiSpectralPoint]
    have hheight : 1 < |z.im| := by
      rw [him]
      exact xiDivisorSupport_one_lt_abs_im q.1.1
    exact hheight.trans_le (Complex.abs_im_le_norm z)
  rw [rectangularWindowAmplitude_eq_div hz0, norm_div]
  have hnum : ‖1 - Complex.exp (-(A : ℂ) * z)‖ ≤
      1 + Real.exp (A / 2) := by
    calc
      ‖1 - Complex.exp (-(A : ℂ) * z)‖ ≤
          ‖(1 : ℂ)‖ + ‖Complex.exp (-(A : ℂ) * z)‖ := norm_sub_le _ _
      _ = 1 + Real.exp ((-(A : ℂ) * z).re) := by
        rw [Complex.norm_exp]
        norm_num
      _ ≤ 1 + Real.exp (A / 2) := by
        gcongr
        have hz := xiRightThetaAbelExponent_re_gt_neg_half q
        have hre : (-(A : ℂ) * z).re = -A * z.re := by
          simp [Complex.mul_re]
        rw [hre]
        change -(1 / 2 : ℝ) < z.re at hz
        nlinarith
  have hden : 1 ≤ ‖z‖ := hzNorm.le
  calc
    ‖1 - Complex.exp (-(A : ℂ) * z)‖ / ‖z‖ ≤
        (1 + Real.exp (A / 2)) / ‖z‖ := by gcongr
    _ ≤ 1 + Real.exp (A / 2) := by
      apply div_le_self
      · positivity
      · exact hden

theorem norm_xiRightThetaAbel_restoredFactor_le_two (q : XiRightZeroCopy) :
    ‖(xiRightThetaAbelExponent q + 1) / xiRightThetaAbelExponent q‖ ≤ 2 := by
  let z := xiRightThetaAbelExponent q
  have him : z.im = (q.1.1 : ℂ).im := by
    simp [z, xiRightThetaAbelExponent, xiRightCenteredZero, xiSpectralPoint]
  have hheight : 1 < |z.im| := by
    rw [him]
    exact xiDivisorSupport_one_lt_abs_im q.1.1
  have hnorm : 1 < ‖z‖ := hheight.trans_le (Complex.abs_im_le_norm z)
  have hnorm0 : 0 < ‖z‖ := zero_lt_one.trans hnorm
  rw [norm_div]
  calc
    ‖z + 1‖ / ‖z‖ ≤ (‖z‖ + 1) / ‖z‖ := by
      gcongr
      simpa using norm_add_le z (1 : ℂ)
    _ ≤ 2 := by
      rw [div_le_iff₀ hnorm0]
      linarith

/-- Exact scalar coefficient obtained after smooth probing, physical log-window differencing,
theta--Abel restoration, and integration over one compact physical aperture. -/
def xiPhysicalThetaAbelLandauCoefficient
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (A c : ℝ)
    (q : XiRightZeroCopy) : ℂ :=
  smoothProfileLaplaceAmplitude f (xiRightCenteredZero q) ^ (2 : ℕ) *
    xiPhysicalLogWindowModeMultiplier c (xiRightThetaAbelExponent q) *
    ((xiRightThetaAbelExponent q + 1) / xiRightThetaAbelExponent q) *
    rectangularWindowAmplitude A (xiRightThetaAbelExponent q)

theorem xiPhysicalThetaAbelLandauCoefficient_conj
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (A c : ℝ)
    (q : XiRightZeroCopy) :
    xiPhysicalThetaAbelLandauCoefficient f A c
        (xiRightZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (xiPhysicalThetaAbelLandauCoefficient f A c q) := by
  have hmult : xiPhysicalLogWindowModeMultiplier c
        ((starRingEnd ℂ) (xiRightThetaAbelExponent q)) =
      (starRingEnd ℂ) (xiPhysicalLogWindowModeMultiplier c
        (xiRightThetaAbelExponent q)) := by
    simp only [xiPhysicalLogWindowModeMultiplier, map_sub, map_one]
    congr 1
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  simp only [xiPhysicalThetaAbelLandauCoefficient,
    xiRightCenteredZero_conj, xiRightThetaAbelExponent_conj,
    hmult, map_mul, map_pow, map_div₀, map_add,
    map_one, rectangularWindowAmplitude_conj, ← smoothProfileLaplaceAmplitude_conj]

theorem xiPhysicalThetaAbelLandauCoefficient_eq_of_support_eq
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (A c : ℝ)
    {q r : XiRightZeroCopy} (h : q.1.1 = r.1.1) :
    xiPhysicalThetaAbelLandauCoefficient f A c q =
      xiPhysicalThetaAbelLandauCoefficient f A c r := by
  rw [xiPhysicalThetaAbelLandauCoefficient,
    xiPhysicalThetaAbelLandauCoefficient,
    xiRightCenteredZero_eq_of_support_eq h,
    xiRightThetaAbelExponent_eq_of_support_eq h]

theorem xiPhysicalThetaAbelLandauCoefficient_ne_zero
    {eta L : ℝ} (hA : 0 < A) (hc : 0 < c)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L)
    (q : XiRightZeroCopy) :
    xiPhysicalThetaAbelLandauCoefficient f A c q ≠ 0 := by
  unfold xiPhysicalThetaAbelLandauCoefficient
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (hf q)) ?_) ?_) ?_
  · exact xiPhysicalLogWindowModeMultiplier_ne_zero hc
      (xiRightThetaAbelExponent_re_neg q)
  · exact div_ne_zero
      (by
        intro hsum
        apply xiRightThetaAbelExponent_ne_neg_one q
        linear_combination hsum)
      (xiRightThetaAbelExponent_ne_zero q)
  · exact rectangularWindowAmplitude_ne_zero_of_re_neg hA
      (xiRightThetaAbelExponent_re_neg q)

/-- Physical theta--Abel coefficients meet the exact generic hypotheses of Xi pole tomography. -/
def xiPhysicalThetaAbelCoefficientSystem
    {eta L A c : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (hA : 0 < A) (hc : 0 < c)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L) :
    XiRightCoefficientSystem where
  coefficient := xiPhysicalThetaAbelLandauCoefficient f A c
  normBound := 4 * (1 + Real.exp (A / 2)) *
    (Real.exp (L / 2) * smoothProfileDerivativeMass f) ^ (2 : ℕ)
  normBound_nonneg := by positivity
  norm_le q := by
    have hsmooth := norm_smoothProfileLaplaceAmplitude_sq_xiRight_le
      heta hwindow f q
    have hwindowBound := norm_xiPhysicalLogWindowModeMultiplier_le_two_of_re_neg
      hc (xiRightThetaAbelExponent_re_neg q)
    have hfactorBound := norm_xiRightThetaAbel_restoredFactor_le_two q
    have hapertureBound := norm_rectangularWindowAmplitude_xiRightThetaAbel_le hA q
    rw [xiPhysicalThetaAbelLandauCoefficient, norm_mul, norm_mul, norm_mul]
    calc
      ‖smoothProfileLaplaceAmplitude f (xiRightCenteredZero q) ^ (2 : ℕ)‖ *
            ‖xiPhysicalLogWindowModeMultiplier c (xiRightThetaAbelExponent q)‖ *
          ‖(xiRightThetaAbelExponent q + 1) / xiRightThetaAbelExponent q‖ *
          ‖rectangularWindowAmplitude A (xiRightThetaAbelExponent q)‖
          ≤ ((Real.exp (L / 2) * smoothProfileDerivativeMass f) ^ (2 : ℕ) /
              ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) * 2 * 2 *
              (1 + Real.exp (A / 2)) := by
            gcongr
      _ = (4 * (1 + Real.exp (A / 2)) *
            (Real.exp (L / 2) * smoothProfileDerivativeMass f) ^ (2 : ℕ)) /
              ‖xiSpectralPoint q.1‖ ^ (2 : ℕ) := by ring
  conjugate q := xiPhysicalThetaAbelLandauCoefficient_conj f A c q
  support_eq {q r} h :=
    xiPhysicalThetaAbelLandauCoefficient_eq_of_support_eq f A c h
  nonzero q := xiPhysicalThetaAbelLandauCoefficient_ne_zero hA hc f hf q

/-- Log-sampled scalar physical theta--Abel carrier. The exponent in the generic Landau sum is
`rho - 1/2`; its coefficient contains the exact `rho - 1` theta--Abel factors. -/
def xiPhysicalThetaAbelLandauResponse
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (A c : ℝ) (n : ℕ) : ℝ :=
  (2 * ∑' q : XiRightZeroCopy,
    xiPhysicalThetaAbelLandauCoefficient f A c q *
      (n : ℂ) ^ xiRightCenteredZero q).re

theorem xiPhysicalThetaAbelLandauResponse_eq_weighted
    {eta L A c : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (hA : 0 < A) (hc : 0 < c)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L)
    (n : ℕ) :
    xiPhysicalThetaAbelLandauResponse f A c n =
      xiWeightedRightDirichletCoefficientReal
        (xiPhysicalThetaAbelCoefficientSystem heta hwindow hA hc f hf) n := by
  rfl

/-- No maximal real-part zero is required: every nonempty right-Xi divisor makes the exact
physical theta--Abel scalar carrier cross every lower level arbitrarily late. -/
theorem xiPhysicalThetaAbelLandauResponse_cofinally_unbounded_below
    {eta L A c : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (hA : 0 < A) (hc : 0 < c)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L)
    (hne : Nonempty XiRightZeroCopy) :
    ∀ B : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      xiPhysicalThetaAbelLandauResponse f A c n < B := by
  simpa only [xiPhysicalThetaAbelLandauResponse_eq_weighted
    heta hwindow hA hc f hf] using
    xiWeightedRightDirichletCoefficientReal_cofinally_unbounded_below
    (xiPhysicalThetaAbelCoefficientSystem heta hwindow hA hc f hf) hne

/-- Cofinal lower divergence rules out convergence of the scalar carrier to zero. -/
theorem not_tendsto_xiPhysicalThetaAbelLandauResponse_zero
    {eta L A c : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (hA : 0 < A) (hc : 0 < c)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L)
    (hne : Nonempty XiRightZeroCopy) :
    ¬ Tendsto
      (xiPhysicalThetaAbelLandauResponse f A c)
      atTop (nhds 0) := by
  intro htend
  have hIoi : Set.Ioi (-1 : ℝ) ∈ nhds (0 : ℝ) := Ioi_mem_nhds (by norm_num)
  have hevent := htend hIoi
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  obtain ⟨n, hn, hlt⟩ :=
    xiPhysicalThetaAbelLandauResponse_cofinally_unbounded_below
      heta hwindow hA hc f hf hne (-1) N
  exact (not_lt_of_ge (le_of_lt (hN n hn))) hlt

/-- Under RH the positive-transverse multiplicity-copy type is empty. -/
theorem isEmpty_xiRightZeroCopy_of_riemannHypothesis_physicalThetaAbel
    (hRH : RiemannHypothesis) : IsEmpty XiRightZeroCopy := by
  constructor
  intro q
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q.1
  have hpos := q.2
  rw [ht] at hpos
  simp at hpos

/-- Exact RH criterion with no rightmost-zero or support-attainment premise: one generic smooth
physical theta--Abel probe has an eventual lower bound exactly when RH holds. -/
theorem riemannHypothesis_iff_exists_smoothProbe_eventually_lowerBound_physicalThetaAbelLandau
    {eta L A c : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (hA : 0 < A) (hc : 0 < c) :
    RiemannHypothesis ↔
      ∃ f : SmoothBoundaryProfile eta L,
        f ∈ xiSmoothProfileGenericSet eta L ∧
        ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          0 ≤ xiPhysicalThetaAbelLandauResponse f A c n + C := by
  constructor
  · intro hRH
    obtain ⟨f, hf⟩ : (xiSmoothProfileGenericSet eta L).Nonempty :=
      (xiSmoothProfileGenericSet_dense_residual hwindow).1.nonempty
    refine ⟨f, hf, 0, 0, fun n _ => ?_⟩
    letI := isEmpty_xiRightZeroCopy_of_riemannHypothesis_physicalThetaAbel hRH
    simp [xiPhysicalThetaAbelLandauResponse]
  · rintro ⟨f, hf, C, N, hlower⟩
    by_contra hRH
    exact no_eventual_lower_bound_xiWeightedRightDirichletCoefficientReal
      (xiPhysicalThetaAbelCoefficientSystem heta hwindow hA hc f hf)
      (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH)
      ⟨C, N, fun n hn => by
        rw [← xiPhysicalThetaAbelLandauResponse_eq_weighted
          heta hwindow hA hc f hf n]
        exact hlower n hn⟩

end

end RHTower

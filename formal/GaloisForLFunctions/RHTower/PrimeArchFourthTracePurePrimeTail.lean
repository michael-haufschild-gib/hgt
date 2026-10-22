import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmStokesCurvatureTailFiniteCeiling

/-!
# Fourth-trace pure prime tail

The countable completed prime--Gamma endpoint above `233 / 20` still packages a known
archimedean logarithmic derivative with the prime source.  Unconditional vertical digamma
bounds show that this term differs by at most four from its explicit Stirling main term
throughout the relevant half-strip.  Hence RH is equivalent to a lower bound on the pure
continued prime flux after subtracting only that elementary logarithmic main term.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Explicit Stirling main term for the real archimedean logarithmic derivative. -/
def primeArchHighFrequencyMainTerm (s : ℂ) : ℝ :=
  -Real.log Real.pi / 2 +
    (1 / 4) * Real.log ((s.re / 2) ^ (2 : ℕ) + (s.im / 2) ^ (2 : ℕ))

/-- On the fourth-trace tail, the real archimedean logarithmic derivative stays within four
of its explicit Stirling main term, uniformly across the open left critical half-strip. -/
theorem abs_re_logDeriv_archFactor_sub_primeArchHighFrequencyMainTerm_le_four
    {s : ℂ} (hsRe : 0 < s.re) (hsHalf : s.re < 1 / 2)
    (hsIm : 233 / 20 < s.im) :
    |(logDeriv archFactor s).re - primeArchHighFrequencyMainTerm s| ≤ 4 := by
  let σ : ℝ := s.re / 2
  let t : ℝ := s.im / 2
  have hσ : 0 ≤ σ := by dsimp [σ]; linarith
  have ht : 0 < t := by dsimp [t]; linarith
  have ht1 : 1 ≤ t := by dsimp [t]; linarith
  have hcoord : s / 2 = (σ : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;>
      simp [σ, t, Complex.mul_re, Complex.mul_im]
  have hdig := re_digamma_vertical_bound_uncond hσ ht
  rw [← hcoord] at hdig
  have htSq : 1 ≤ t ^ (2 : ℕ) := one_le_pow₀ ht1
  have htTerm : 1 / t ^ (2 : ℕ) ≤ 1 :=
    (div_le_one (sq_pos_of_pos ht)).2 htSq
  have hpiTerm : Real.pi / (2 * t) ≤ 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) ht)).2
    nlinarith [Real.pi_lt_four]
  have hdigThree :
      |(Complex.digamma (s / 2)).re -
          (1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ))| ≤ 3 :=
    hdig.trans (by linarith)
  have hsImOne : 1 ≤ s.im := by linarith
  have hsNorm : 1 ≤ ‖s‖ := by
    calc
      1 ≤ s.im := hsImOne
      _ ≤ |s.im| := le_abs_self _
      _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hs0 : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [Complex.zero_im] at him
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    rw [Complex.one_im] at him
    linarith
  have hsinv : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one, one_div]
    exact (inv_le_one₀ (zero_lt_one.trans_le hsNorm)).2 hsNorm
  have hsm1Norm : 1 ≤ ‖s - 1‖ := by
    calc
      1 ≤ s.im := hsImOne
      _ = (s - 1).im := by simp
      _ ≤ |(s - 1).im| := le_abs_self _
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
  have hsm1inv : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, one_div]
    exact (inv_le_one₀ (zero_lt_one.trans_le hsm1Norm)).2 hsm1Norm
  have hformula :
      (logDeriv archFactor s).re - primeArchHighFrequencyMainTerm s =
        (1 / s).re + (1 / (s - 1)).re +
          (1 / 2) * ((Complex.digamma (s / 2)).re -
            (1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ))) := by
    rw [logDeriv_archFactor_closed hsRe hs0 hs1]
    rw [GaloisForLFunctions.gammaRealLogConnection]
    dsimp [primeArchHighFrequencyMainTerm, σ, t]
    simp only [Complex.ofReal_re, Complex.div_re, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im]
    norm_num
    ring
  rw [hformula]
  calc
    |(1 / s).re + (1 / (s - 1)).re +
        (1 / 2) * ((Complex.digamma (s / 2)).re -
          (1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ)))| ≤
        |(1 / s).re| + |(1 / (s - 1)).re| +
          |(1 / 2) * ((Complex.digamma (s / 2)).re -
            (1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ)))| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |(1 / s).re| + |(1 / (s - 1)).re| +
        (1 / 2) * |(Complex.digamma (s / 2)).re -
          (1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ))| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ 1 + 1 + (1 / 2) * 3 := by
      gcongr
      · exact (Complex.abs_re_le_norm _).trans hsinv
      · exact (Complex.abs_re_le_norm _).trans hsm1inv
    _ ≤ 4 := by norm_num

/-- Pure-prime countable tail condition: continued prime flux must dominate the explicit
archimedean main term up to one common additive constant. -/
def InfinitePrimeFluxGaussianRatPositiveFrequencyAboveArchMainBoundedBelow
    (R : ℝ) : Prop :=
  ∃ L : ℝ, ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 → R < (gaussianRatPoint q).im →
    riemannZeta (gaussianRatPoint q) ≠ 0 →
      L + primeArchHighFrequencyMainTerm (gaussianRatPoint q) ≤
        (infinitePrimeFlux (gaussianRatPoint q)).re

/-- Removing the uniformly controlled archimedean remainder changes only the common lower-bound
constant, so pure-prime and completed countable tails are equivalent. -/
theorem infinitePrimeFluxGaussianRatPositiveFrequencyAboveArchMainBoundedBelow_iff_completed
    :
    InfinitePrimeFluxGaussianRatPositiveFrequencyAboveArchMainBoundedBelow (233 / 20) ↔
      CompletedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow (233 / 20) := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L - 4, ?_⟩
    intro q hqpos hqhalf hqhigh hqzeta
    have hprime := hL q hqpos hqhalf hqhigh hqzeta
    have harch := abs_re_logDeriv_archFactor_sub_primeArchHighFrequencyMainTerm_le_four
      hqpos hqhalf hqhigh
    rw [abs_le] at harch
    change L - 4 ≤
      (infinitePrimeFlux (gaussianRatPoint q) -
        logDeriv archFactor (gaussianRatPoint q)).re
    simp only [Complex.sub_re]
    linarith
  · rintro ⟨L, hL⟩
    refine ⟨L - 4, ?_⟩
    intro q hqpos hqhalf hqhigh hqzeta
    have hcompleted := hL q hqpos hqhalf hqhigh hqzeta
    have harch := abs_re_logDeriv_archFactor_sub_primeArchHighFrequencyMainTerm_le_four
      hqpos hqhalf hqhigh
    rw [abs_le] at harch
    change L ≤
      (infinitePrimeFlux (gaussianRatPoint q) -
        logDeriv archFactor (gaussianRatPoint q)).re at hcompleted
    simp only [Complex.sub_re] at hcompleted
    linarith

/-- Canonical pure-prime countable endpoint after fourth-trace and archimedean discharge. -/
theorem infinitePrimeFluxGaussianRatPositiveFrequencyAboveArchMainBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh :
    InfinitePrimeFluxGaussianRatPositiveFrequencyAboveArchMainBoundedBelow (233 / 20) ↔
      RiemannHypothesis :=
  infinitePrimeFluxGaussianRatPositiveFrequencyAboveArchMainBoundedBelow_iff_completed.trans
    completedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh

/-- False RH defeats every additive pure-prime lower bound beyond the fourth-trace threshold. -/
theorem exists_gaussianRat_infinitePrimeFlux_re_lt_archMain_add_of_not_rh
    (hnot : ¬ RiemannHypothesis) :
    ∀ L : ℝ, ∃ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re ∧
      (gaussianRatPoint q).re < 1 / 2 ∧ 233 / 20 < (gaussianRatPoint q).im ∧
      riemannZeta (gaussianRatPoint q) ≠ 0 ∧
        (infinitePrimeFlux (gaussianRatPoint q)).re <
          L + primeArchHighFrequencyMainTerm (gaussianRatPoint q) := by
  intro L
  by_contra hescape
  push Not at hescape
  apply hnot
  exact
    infinitePrimeFluxGaussianRatPositiveFrequencyAboveArchMainBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mp
      ⟨L, fun q hqpos hqhalf hqhigh hqzeta =>
        hescape q hqpos hqhalf hqhigh hqzeta⟩

/-- Height-only Stirling allowance.  Dependence on the horizontal coordinate is uniformly
bounded on the fourth-trace tail and is therefore unnecessary in the canonical endpoint. -/
def primeArchHighFrequencyHeightMainTerm (t : ℝ) : ℝ :=
  -Real.log Real.pi / 2 + (1 / 4) * Real.log ((t / 2) ^ (2 : ℕ))

/-- The full two-variable Stirling term exceeds its height-only part by at most one throughout
the relevant strip. -/
theorem primeArchHighFrequencyMainTerm_sub_heightMainTerm_nonneg_le_one
    {s : ℂ} (hsRe : 0 < s.re) (hsHalf : s.re < 1 / 2)
    (hsIm : 233 / 20 < s.im) :
    0 ≤ primeArchHighFrequencyMainTerm s -
        primeArchHighFrequencyHeightMainTerm s.im ∧
      primeArchHighFrequencyMainTerm s -
        primeArchHighFrequencyHeightMainTerm s.im ≤ 1 := by
  let x : ℝ := s.re / 2
  let y : ℝ := s.im / 2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 < y := by dsimp [y]; linarith
  have hxy : x ≤ y := by dsimp [x, y]; linarith
  have hsq : x ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx hy.le)]
  have hySq : 0 < y ^ (2 : ℕ) := sq_pos_of_pos hy
  have hsumPos : 0 < x ^ (2 : ℕ) + y ^ (2 : ℕ) := by positivity
  have hlower : y ^ (2 : ℕ) ≤ x ^ (2 : ℕ) + y ^ (2 : ℕ) := by nlinarith [sq_nonneg x]
  have hupper : x ^ (2 : ℕ) + y ^ (2 : ℕ) ≤ 2 * y ^ (2 : ℕ) := by linarith
  have hlogLower : Real.log (y ^ (2 : ℕ)) ≤ Real.log (x ^ (2 : ℕ) + y ^ (2 : ℕ)) :=
    Real.strictMonoOn_log.monotoneOn hySq hsumPos hlower
  have hlogUpper : Real.log (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ≤ Real.log (2 * y ^ (2 : ℕ)) :=
    Real.strictMonoOn_log.monotoneOn hsumPos (mul_pos (by norm_num) hySq) hupper
  rw [Real.log_mul (by norm_num) (ne_of_gt hySq)] at hlogUpper
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  dsimp [primeArchHighFrequencyMainTerm,
    primeArchHighFrequencyHeightMainTerm, x, y]
  constructor <;> linarith

/-- Canonical height-only pure-prime tail condition. -/
def InfinitePrimeFluxGaussianRatPositiveFrequencyAboveHeightMainBoundedBelow
    (R : ℝ) : Prop :=
  ∃ L : ℝ, ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 → R < (gaussianRatPoint q).im →
    riemannZeta (gaussianRatPoint q) ≠ 0 →
      L + primeArchHighFrequencyHeightMainTerm (gaussianRatPoint q).im ≤
        (infinitePrimeFlux (gaussianRatPoint q)).re

/-- Horizontal dependence in the Stirling allowance changes only the common additive constant. -/
theorem infinitePrimeFluxGaussianRatPositiveFrequencyAboveHeightMainBoundedBelow_iff_archMain
    :
    InfinitePrimeFluxGaussianRatPositiveFrequencyAboveHeightMainBoundedBelow (233 / 20) ↔
      InfinitePrimeFluxGaussianRatPositiveFrequencyAboveArchMainBoundedBelow (233 / 20) := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L - 1, ?_⟩
    intro q hqpos hqhalf hqhigh hqzeta
    have hprime := hL q hqpos hqhalf hqhigh hqzeta
    have hmain := primeArchHighFrequencyMainTerm_sub_heightMainTerm_nonneg_le_one
      hqpos hqhalf hqhigh
    linarith
  · rintro ⟨L, hL⟩
    refine ⟨L, ?_⟩
    intro q hqpos hqhalf hqhigh hqzeta
    have hprime := hL q hqpos hqhalf hqhigh hqzeta
    have hmain := primeArchHighFrequencyMainTerm_sub_heightMainTerm_nonneg_le_one
      hqpos hqhalf hqhigh
    linarith

/-- Simplified pure-prime endpoint: only the height-dependent logarithmic allowance remains. -/
theorem infinitePrimeFluxGaussianRatPositiveFrequencyAboveHeightMainBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh :
    InfinitePrimeFluxGaussianRatPositiveFrequencyAboveHeightMainBoundedBelow (233 / 20) ↔
      RiemannHypothesis :=
  infinitePrimeFluxGaussianRatPositiveFrequencyAboveHeightMainBoundedBelow_iff_archMain.trans
    infinitePrimeFluxGaussianRatPositiveFrequencyAboveArchMainBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh

/-- False RH violates every height-only additive pure-prime lower bound. -/
theorem exists_gaussianRat_infinitePrimeFlux_re_lt_heightMain_add_of_not_rh
    (hnot : ¬ RiemannHypothesis) :
    ∀ L : ℝ, ∃ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re ∧
      (gaussianRatPoint q).re < 1 / 2 ∧ 233 / 20 < (gaussianRatPoint q).im ∧
      riemannZeta (gaussianRatPoint q) ≠ 0 ∧
        (infinitePrimeFlux (gaussianRatPoint q)).re <
          L + primeArchHighFrequencyHeightMainTerm (gaussianRatPoint q).im := by
  intro L
  by_contra hescape
  push Not at hescape
  apply hnot
  exact
    infinitePrimeFluxGaussianRatPositiveFrequencyAboveHeightMainBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mp
      ⟨L, fun q hqpos hqhalf hqhigh hqzeta =>
        hescape q hqpos hqhalf hqhigh hqzeta⟩

/-- The height-only Stirling allowance is one half-logarithm plus a fixed constant. -/
theorem primeArchHighFrequencyHeightMainTerm_eq_half_log_sub_constant
    {t : ℝ} (ht : 0 < t) :
    primeArchHighFrequencyHeightMainTerm t =
      Real.log t / 2 - (Real.log Real.pi + Real.log 2) / 2 := by
  rw [primeArchHighFrequencyHeightMainTerm, Real.log_pow,
    Real.log_div (ne_of_gt ht) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- Bare logarithmic pure-prime tail condition after absorbing every fixed archimedean
normalization into the common lower-bound constant. -/
def InfinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelow
    (R : ℝ) : Prop :=
  ∃ L : ℝ, ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 → R < (gaussianRatPoint q).im →
    riemannZeta (gaussianRatPoint q) ≠ 0 →
      L + Real.log (gaussianRatPoint q).im / 2 ≤
        (infinitePrimeFlux (gaussianRatPoint q)).re

/-- Fixed constants in the height allowance are immaterial to a common additive lower bound. -/
theorem infinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelow_iff_heightMain
    :
    InfinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelow (233 / 20) ↔
      InfinitePrimeFluxGaussianRatPositiveFrequencyAboveHeightMainBoundedBelow (233 / 20) := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L + (Real.log Real.pi + Real.log 2) / 2, ?_⟩
    intro q hqpos hqhalf hqhigh hqzeta
    have hmain := primeArchHighFrequencyHeightMainTerm_eq_half_log_sub_constant
      (t := (gaussianRatPoint q).im) (by linarith)
    have hprime := hL q hqpos hqhalf hqhigh hqzeta
    rw [hmain]
    linarith
  · rintro ⟨L, hL⟩
    refine ⟨L - (Real.log Real.pi + Real.log 2) / 2, ?_⟩
    intro q hqpos hqhalf hqhigh hqzeta
    have hmain := primeArchHighFrequencyHeightMainTerm_eq_half_log_sub_constant
      (t := (gaussianRatPoint q).im) (by linarith)
    have hprime := hL q hqpos hqhalf hqhigh hqzeta
    rw [hmain] at hprime
    linarith

/-- Canonical pure-prime endpoint: only half the logarithm of height remains. -/
theorem infinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh :
    InfinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelow (233 / 20) ↔
      RiemannHypothesis :=
  infinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelow_iff_heightMain.trans
    infinitePrimeFluxGaussianRatPositiveFrequencyAboveHeightMainBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh

/-- False RH violates every half-logarithmic pure-prime lower bound. -/
theorem exists_gaussianRat_infinitePrimeFlux_re_lt_half_log_height_add_of_not_rh
    (hnot : ¬ RiemannHypothesis) :
    ∀ L : ℝ, ∃ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re ∧
      (gaussianRatPoint q).re < 1 / 2 ∧ 233 / 20 < (gaussianRatPoint q).im ∧
      riemannZeta (gaussianRatPoint q) ≠ 0 ∧
        (infinitePrimeFlux (gaussianRatPoint q)).re <
          L + Real.log (gaussianRatPoint q).im / 2 := by
  intro L
  by_contra hescape
  push Not at hescape
  apply hnot
  exact
    infinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mp
      ⟨L, fun q hqpos hqhalf hqhigh hqzeta =>
        hescape q hqpos hqhalf hqhigh hqzeta⟩

/-- Unguarded half-logarithmic pure-prime tail condition.  The zeta-nonzero clause is absent. -/
def InfinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelowUnguarded
    (R : ℝ) : Prop :=
  ∃ L : ℝ, ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 → R < (gaussianRatPoint q).im →
      L + Real.log (gaussianRatPoint q).im / 2 ≤
        (infinitePrimeFlux (gaussianRatPoint q)).re

/-- At the canonical threshold, RH forced by the guarded bound makes its nonzero guard automatic. -/
theorem infinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelowUnguarded_iff_guarded
    :
    InfinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelowUnguarded
        (233 / 20) ↔
      InfinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelow
        (233 / 20) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, fun q hqpos hqhalf hqhigh _ => hL q hqpos hqhalf hqhigh⟩
  · intro hguarded
    have hRH :=
      infinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mp
        hguarded
    obtain ⟨L, hL⟩ := hguarded
    refine ⟨L, ?_⟩
    intro q hqpos hqhalf hqhigh
    exact hL q hqpos hqhalf hqhigh
      (riemannHypothesis_iff_riemannZeta_ne_zero_of_re_lt_half.mp hRH
        (gaussianRatPoint q) hqpos hqhalf)

/-- Canonical unguarded pure-prime endpoint. -/
theorem infinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelowUnguarded_twoHundredThirtyThree_twentieths_iff_rh :
    InfinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelowUnguarded
        (233 / 20) ↔ RiemannHypothesis :=
  infinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelowUnguarded_iff_guarded.trans
    infinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh

/-- False RH violates every unguarded half-logarithmic lower bound. -/
theorem exists_gaussianRat_infinitePrimeFlux_re_lt_half_log_height_add_unguarded_of_not_rh
    (hnot : ¬ RiemannHypothesis) :
    ∀ L : ℝ, ∃ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re ∧
      (gaussianRatPoint q).re < 1 / 2 ∧ 233 / 20 < (gaussianRatPoint q).im ∧
        (infinitePrimeFlux (gaussianRatPoint q)).re <
          L + Real.log (gaussianRatPoint q).im / 2 := by
  intro L
  obtain ⟨q, hqpos, hqhalf, hqhigh, _, hbad⟩ :=
    exists_gaussianRat_infinitePrimeFlux_re_lt_half_log_height_add_of_not_rh hnot L
  exact ⟨q, hqpos, hqhalf, hqhigh, hbad⟩

/-- Scalar prime-source defect after every archimedean term and fixed normalization is removed. -/
def primeArchLogHeightDefect (s : ℂ) : ℝ :=
  2 * (infinitePrimeFlux s).re - Real.log s.im

/-- The canonical scalar defect is bounded below on the countable fourth-trace tail. -/
def PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow
    (R : ℝ) : Prop :=
  ∃ L : ℝ, ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 → R < (gaussianRatPoint q).im →
      L ≤ primeArchLogHeightDefect (gaussianRatPoint q)

/-- Scaling by two identifies the scalar defect bound with the unguarded half-log bound. -/
theorem primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_iff_unguarded
    :
    PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow (233 / 20) ↔
      InfinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelowUnguarded
        (233 / 20) := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L / 2, ?_⟩
    intro q hqpos hqhalf hqhigh
    have hdefect := hL q hqpos hqhalf hqhigh
    dsimp [primeArchLogHeightDefect] at hdefect
    linarith
  · rintro ⟨L, hL⟩
    refine ⟨2 * L, ?_⟩
    intro q hqpos hqhalf hqhigh
    have hprime := hL q hqpos hqhalf hqhigh
    dsimp [primeArchLogHeightDefect]
    linarith

/-- Final scalar pure-prime endpoint after fourth-trace and archimedean discharge. -/
theorem primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh :
    PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow (233 / 20) ↔
      RiemannHypothesis :=
  primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_iff_unguarded.trans
    infinitePrimeFluxGaussianRatPositiveFrequencyAboveLogHeightBoundedBelowUnguarded_twoHundredThirtyThree_twentieths_iff_rh

/-- False RH drives the scalar pure-prime defect below every proposed floor. -/
theorem exists_gaussianRat_primeArchLogHeightDefect_lt_of_not_rh
    (hnot : ¬ RiemannHypothesis) :
    ∀ L : ℝ, ∃ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re ∧
      (gaussianRatPoint q).re < 1 / 2 ∧ 233 / 20 < (gaussianRatPoint q).im ∧
        primeArchLogHeightDefect (gaussianRatPoint q) < L := by
  intro L
  obtain ⟨q, hqpos, hqhalf, hqhigh, hbad⟩ :=
    exists_gaussianRat_infinitePrimeFlux_re_lt_half_log_height_add_unguarded_of_not_rh
      hnot (L / 2)
  refine ⟨q, hqpos, hqhalf, hqhigh, ?_⟩
  dsimp [primeArchLogHeightDefect]
  linarith

end

end RHTower

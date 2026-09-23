import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualHardyPolarization
import GaloisForLFunctions.RHTower.XiHeatCassiniPrimeGapMomentThreshold
import GaloisForLFunctions.RHTower.PerronPolyExpAbsorb

/-!
# Exact upper abscissa of the Route-T residual Hardy source

Lower-half-plane holomorphy and every real-boundary derivative follow from the unconditional
square-root-exponential Wold residual estimate.  They do not cross the real boundary.  At a
positive imaginary height `a`, one residual prime-log edge has the exact mass

`|R_N| exp(a h_N) (exp(a Δh_N) - 1)`.

For `0 < a ≤ 1`, Bertrand's bound gives `0 ≤ a Δh_N ≤ 1`, so this mass is uniformly comparable
to `a |R_N| Δh_N exp(a h_N)`.  Hence absolute convergence at height `a` is equivalent to one
explicit exponentially weighted residual-variation series.  This is the sharp source-side
quantity hidden by all polynomial/Gevrey boundary jets.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

@[simp]
theorem xiHeatCassiniOrderedPrimeComplexNegativePhase_mul_I
    (N : ℕ) (a : ℝ) :
    xiHeatCassiniOrderedPrimeComplexNegativePhase N
        (Complex.I * (a : ℂ)) =
      (Real.exp (a * xiMassNthPrimeLogHeight N) : ℂ) := by
  rw [xiHeatCassiniOrderedPrimeComplexNegativePhase, Complex.ofReal_exp]
  congr 1
  calc
    -(Complex.I * (xiMassNthPrimeLogHeight N : ℂ) *
        (Complex.I * (a : ℂ))) =
        -(Complex.I * Complex.I) *
          ((xiMassNthPrimeLogHeight N : ℂ) * (a : ℂ)) := by ring
    _ = (a * xiMassNthPrimeLogHeight N : ℝ) := by
      rw [Complex.I_mul_I]
      push_cast
      ring

/-- Exact mass of one residual edge at positive imaginary height. -/
theorem norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_mul_I
    {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖ =
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        Real.exp (a * xiMassNthPrimeLogHeight N) *
          (Real.exp (a * xiHeatCassiniOrderedPrimeLogGap N) - 1) := by
  rw [xiHeatCassiniWoldResidualComplexPhaseConnectionAtom, norm_mul,
    xiHeatCassiniOrderedPrimeComplexNegativePhase_mul_I,
    xiHeatCassiniOrderedPrimeComplexNegativePhase_mul_I,
    Complex.norm_real, Real.norm_eq_abs]
  have hheight :
      xiMassNthPrimeLogHeight (N + 1) =
        xiMassNthPrimeLogHeight N + xiHeatCassiniOrderedPrimeLogGap N := by
    dsimp only [xiHeatCassiniOrderedPrimeLogGap]
    ring
  rw [hheight, mul_add, Real.exp_add]
  have hgap : 0 ≤ a * xiHeatCassiniOrderedPrimeLogGap N :=
    mul_nonneg ha (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
  rw [show (Real.exp (a * xiMassNthPrimeLogHeight N) : ℂ) -
        (Real.exp (a * xiMassNthPrimeLogHeight N) *
          Real.exp (a * xiHeatCassiniOrderedPrimeLogGap N) : ℝ) =
      ((Real.exp (a * xiMassNthPrimeLogHeight N) *
        (1 - Real.exp (a * xiHeatCassiniOrderedPrimeLogGap N)) : ℝ) : ℂ) by
        push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.exp_nonneg _)]
  have hone : 1 - Real.exp (a * xiHeatCassiniOrderedPrimeLogGap N) ≤ 0 :=
    sub_nonpos.mpr ((Real.exp_zero).symm.trans_le (Real.exp_le_exp.mpr hgap))
  rw [abs_of_nonpos hone]
  ring

/-- Exact phase growth at an arbitrary complex source coordinate. -/
theorem norm_xiHeatCassiniOrderedPrimeComplexNegativePhase
    (N : ℕ) (z : ℂ) :
    ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z‖ =
      Real.exp (xiMassNthPrimeLogHeight N * z.im) := by
  rw [xiHeatCassiniOrderedPrimeComplexNegativePhase, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- A complex prime-log chord retains its cell length on either side of the boundary; upper growth
is isolated in the first phase. -/
theorem norm_xiHeatCassiniOrderedPrimeComplexNegativePhase_sub_succ_le_global
    (z : ℂ) (N : ℕ) :
    ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z -
        xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z‖ ≤
      xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
        Real.exp (xiMassNthPrimeLogHeight N * z.im) := by
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let w : ℂ := -(Complex.I * (delta : ℂ) * z)
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hdelta1 : delta ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have hphase :
      xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z =
        xiHeatCassiniOrderedPrimeComplexNegativePhase N z * Complex.exp w := by
    rw [xiHeatCassiniOrderedPrimeComplexNegativePhase,
      xiHeatCassiniOrderedPrimeComplexNegativePhase, ← Complex.exp_add]
    dsimp only [delta, w, xiHeatCassiniOrderedPrimeLogGap]
    congr 1
    push_cast
    ring
  have hwnorm : ‖w‖ = delta * ‖z‖ := by
    dsimp only [w]
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdelta]
  have hchord : ‖1 - Complex.exp w‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
    have h := Complex.norm_exp_sub_sum_le_norm_mul_exp w 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one] at h
    calc
      ‖1 - Complex.exp w‖ = ‖Complex.exp w - 1‖ := by
        rw [← norm_neg (Complex.exp w - 1), neg_sub]
      _ ≤ ‖w‖ * Real.exp ‖w‖ := h
  have hexp : Real.exp ‖w‖ ≤ Real.exp ‖z‖ := by
    apply Real.exp_le_exp.mpr
    rw [hwnorm]
    exact mul_le_of_le_one_left (norm_nonneg z) hdelta1
  have hchord' : ‖1 - Complex.exp w‖ ≤
      delta * ‖z‖ * Real.exp ‖z‖ := by
    calc
      ‖1 - Complex.exp w‖ ≤ ‖w‖ * Real.exp ‖w‖ := hchord
      _ = delta * ‖z‖ * Real.exp ‖w‖ := by rw [hwnorm]
      _ ≤ delta * ‖z‖ * Real.exp ‖z‖ :=
        mul_le_mul_of_nonneg_left hexp
          (mul_nonneg hdelta (norm_nonneg z))
  rw [hphase]
  calc
    ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z -
        xiHeatCassiniOrderedPrimeComplexNegativePhase N z * Complex.exp w‖ =
      ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z‖ *
        ‖1 - Complex.exp w‖ := by
          rw [show xiHeatCassiniOrderedPrimeComplexNegativePhase N z -
              xiHeatCassiniOrderedPrimeComplexNegativePhase N z * Complex.exp w =
            xiHeatCassiniOrderedPrimeComplexNegativePhase N z *
              (1 - Complex.exp w) by ring, norm_mul]
    _ ≤ ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z‖ *
        (delta * ‖z‖ * Real.exp ‖z‖) := by
      exact mul_le_mul_of_nonneg_left hchord' (norm_nonneg _)
    _ = xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
        Real.exp (xiMassNthPrimeLogHeight N * z.im) := by
      rw [norm_xiHeatCassiniOrderedPrimeComplexNegativePhase]
      dsimp only [delta]
      ring

/-- Derivative edges retain the prime-log cell on every horizontal substrip. -/
theorem norm_xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom_le_global
    {z : ℂ} {b : ℝ} (hb : 0 ≤ b) (hzb : z.im ≤ b) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom z N‖ ≤
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (xiMassNthPrimeLogHeight N * b) *
            (xiMassNthPrimeLogHeight N * ‖z‖ * Real.exp ‖z‖ + Real.exp b) := by
  let h : ℝ := xiMassNthPrimeLogHeight N
  let y : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let A : ℂ := -Complex.I * (h : ℂ)
  let Bc : ℂ := -Complex.I * (y : ℂ)
  let pn : ℂ := xiHeatCassiniOrderedPrimeComplexNegativePhase N z
  let ps : ℂ := xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z
  have hh : 0 < h := xiMassNthPrimeLogHeight_pos N
  have hy : 0 < y := xiMassNthPrimeLogHeight_pos (N + 1)
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hdelta1 : delta ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have hy_eq : y = h + delta := by
    dsimp only [y, h, delta, xiHeatCassiniOrderedPrimeLogGap]
    ring
  have hpn : ‖pn‖ ≤ Real.exp (h * b) := by
    dsimp only [pn]
    rw [norm_xiHeatCassiniOrderedPrimeComplexNegativePhase]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hzb hh.le
  have hps : ‖ps‖ ≤ Real.exp (h * b) * Real.exp b := by
    dsimp only [ps]
    rw [norm_xiHeatCassiniOrderedPrimeComplexNegativePhase]
    calc
      Real.exp (y * z.im) ≤ Real.exp (y * b) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hzb hy.le
      _ = Real.exp (h * b) * Real.exp (delta * b) := by
        rw [hy_eq, add_mul, Real.exp_add]
      _ ≤ Real.exp (h * b) * Real.exp b := by
        gcongr
        exact mul_le_of_le_one_left hb hdelta1
  have hchord : ‖pn - ps‖ ≤
      delta * ‖z‖ * Real.exp ‖z‖ * Real.exp (h * b) := by
    have hraw :=
      norm_xiHeatCassiniOrderedPrimeComplexNegativePhase_sub_succ_le_global z N
    dsimp only [pn, ps, delta, h]
    calc
      ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z -
          xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z‖ ≤
        xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
          Real.exp (xiMassNthPrimeLogHeight N * z.im) := hraw
      _ ≤ xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
          Real.exp (xiMassNthPrimeLogHeight N * b) := by
        gcongr
  have hAnorm : ‖A‖ = h := by simp [A, abs_of_nonneg hh.le]
  have hABnorm : ‖A - Bc‖ = delta := by
    calc
      ‖A - Bc‖ = ‖Complex.I * ((y - h : ℝ) : ℂ)‖ := by
        congr 1
        dsimp only [A, Bc]
        push_cast
        ring
      _ = |y - h| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ = delta := by rw [hy_eq, add_sub_cancel_left, abs_of_nonneg hdelta]
  have hAnorm_mul : ‖A * (pn - ps)‖ = h * ‖pn - ps‖ := by
    calc
      ‖A * (pn - ps)‖ = ‖A‖ * ‖pn - ps‖ := norm_mul _ _
      _ = h * ‖pn - ps‖ := by rw [hAnorm]
  have hABnorm_mul : ‖(A - Bc) * ps‖ = delta * ‖ps‖ := by
    calc
      ‖(A - Bc) * ps‖ = ‖A - Bc‖ * ‖ps‖ := norm_mul _ _
      _ = delta * ‖ps‖ := by rw [hABnorm]
  rw [xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  change |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      ‖A * pn - Bc * ps‖ ≤ _
  have hinner : ‖A * pn - Bc * ps‖ ≤
      delta * Real.exp (h * b) *
        (h * ‖z‖ * Real.exp ‖z‖ + Real.exp b) := by
    calc
      ‖A * pn - Bc * ps‖ = ‖A * (pn - ps) + (A - Bc) * ps‖ := by
        congr 1
        ring
      _ ≤ ‖A * (pn - ps)‖ + ‖(A - Bc) * ps‖ := norm_add_le _ _
      _ = h * ‖pn - ps‖ + delta * ‖ps‖ := by rw [hAnorm_mul, hABnorm_mul]
      _ ≤ h * (delta * ‖z‖ * Real.exp ‖z‖ * Real.exp (h * b)) +
          delta * (Real.exp (h * b) * Real.exp b) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hchord hh.le)
          (mul_le_mul_of_nonneg_left hps hdelta)
      _ = delta * Real.exp (h * b) *
          (h * ‖z‖ * Real.exp ‖z‖ + Real.exp b) := by ring
  calc
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| * ‖A * pn - Bc * ps‖ ≤
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          (delta * Real.exp (h * b) *
            (h * ‖z‖ * Real.exp ‖z‖ + Real.exp b)) :=
      mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
    _ = _ := by
      dsimp only [delta, h]
      ring

/-- One exponentially damped prime-log cell remains summable after one log-height loss. -/
theorem summable_primeLogGap_mul_height_mul_exp_neg_height
    {e : ℝ} (he : 0 < e) :
    Summable (fun N : ℕ =>
      xiHeatCassiniOrderedPrimeLogGap N * xiMassNthPrimeLogHeight N *
        Real.exp (-e * xiMassNthPrimeLogHeight N)) := by
  have hbase :=
    (summable_primeLogGap_mul_exp_neg_height (show 0 < e / 2 by linarith)).mul_left
      (2 / e)
  refine Summable.of_nonneg_of_le (fun N => mul_nonneg
      (mul_nonneg (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
        (xiMassNthPrimeLogHeight_pos N).le) (Real.exp_nonneg _)) (fun N => ?_) hbase
  have habsorb := pow_mul_exp_neg_le_absorb_half he
    (xiMassNthPrimeLogHeight_pos N).le 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at habsorb
  calc
    xiHeatCassiniOrderedPrimeLogGap N * xiMassNthPrimeLogHeight N *
          Real.exp (-e * xiMassNthPrimeLogHeight N) =
        xiHeatCassiniOrderedPrimeLogGap N *
          (xiMassNthPrimeLogHeight N *
            Real.exp (-(e * xiMassNthPrimeLogHeight N))) := by ring
    _ ≤ xiHeatCassiniOrderedPrimeLogGap N *
          ((2 / e) * Real.exp (-(e * xiMassNthPrimeLogHeight N / 2))) :=
      mul_le_mul_of_nonneg_left habsorb
        (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
    _ = (2 / e) * (xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (-(e / 2) * xiMassNthPrimeLogHeight N)) := by
      have hexp : Real.exp (-(e * xiMassNthPrimeLogHeight N / 2)) =
          Real.exp (-(e / 2) * xiMassNthPrimeLogHeight N) := by
        congr 1
        ring
      rw [hexp]
      ring

/-- Exponentially weighted residual variation at upper height `a`. -/
def xiHeatCassiniWoldResidualUpperVariationAtom (a : ℝ) (N : ℕ) : ℝ :=
  |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
    xiHeatCassiniOrderedPrimeLogGap N *
      Real.exp (a * xiMassNthPrimeLogHeight N)

/-- Upper edge mass is bounded below by the weighted residual variation. -/
theorem residualUpperVariationAtom_mul_le_norm
    {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    a * xiHeatCassiniWoldResidualUpperVariationAtom a N ≤
      ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖ := by
  rw [norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_mul_I ha]
  have hgap : 0 ≤ a * xiHeatCassiniOrderedPrimeLogGap N :=
    mul_nonneg ha (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
  have hexp := Real.add_one_le_exp (a * xiHeatCassiniOrderedPrimeLogGap N)
  dsimp only [xiHeatCassiniWoldResidualUpperVariationAtom]
  have hscale : 0 ≤ |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      Real.exp (a * xiMassNthPrimeLogHeight N) :=
    mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hexp hscale]

/-- For `0 ≤ a ≤ 1`, upper edge mass costs at most twice the weighted residual variation. -/
theorem norm_le_two_mul_residualUpperVariationAtom
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖ ≤
      2 * a * xiHeatCassiniWoldResidualUpperVariationAtom a N := by
  rw [norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_mul_I ha]
  let d : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hd0 : 0 ≤ d := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hd1 : d ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have had0 : 0 ≤ a * d := mul_nonneg ha hd0
  have had1 : |a * d| ≤ 1 := by
    rw [abs_of_nonneg had0]
    nlinarith
  have hexp := Real.abs_exp_sub_one_le had1
  have hexp0 : 0 ≤ Real.exp (a * d) - 1 := by
    exact sub_nonneg.mpr <| by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr had0
  rw [abs_of_nonneg hexp0, abs_of_nonneg had0] at hexp
  dsimp only [xiHeatCassiniWoldResidualUpperVariationAtom]
  dsimp only [d] at hexp
  have hscale : 0 ≤ |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      Real.exp (a * xiMassNthPrimeLogHeight N) :=
    mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hexp hscale]

/-- **Exact upper-abscissa law.**  For `0 < a ≤ 1`, absolute convergence of the raw residual
Hardy series at height `a` is equivalent to summability of its exponentially weighted residual
variation. -/
theorem summable_norm_residualAtom_mul_I_iff_upperVariation
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖) ↔
    Summable (xiHeatCassiniWoldResidualUpperVariationAtom a) := by
  constructor
  · intro hnorm
    have hscaled : Summable (fun N : ℕ =>
        a * xiHeatCassiniWoldResidualUpperVariationAtom a N) := by
      exact Summable.of_nonneg_of_le
        (fun N => mul_nonneg ha.le <| mul_nonneg
          (mul_nonneg (abs_nonneg _)
            (xiHeatCassiniOrderedPrimeLogGap_nonneg N))
          (Real.exp_nonneg _))
        (fun N => residualUpperVariationAtom_mul_le_norm ha.le N) hnorm
    have := hscaled.mul_left a⁻¹
    simpa [ha.ne'] using this
  · intro hvariation
    have hmajor := hvariation.mul_left (2 * a)
    exact Summable.of_nonneg_of_le
      (fun N => norm_nonneg _)
      (fun N => norm_le_two_mul_residualUpperVariationAtom ha.le ha1 N)
      hmajor

/-- Any exponential bound on prime-log cells with rate strictly beyond `1/2` forces the critical
additive prime-gap energy.  One logarithmic cell is retained for the exact exponential-potential
telescope; only the other is spent on the pointwise rate. -/
theorem summable_primeGapCriticalEnergy_of_primeLogGap_exp_rate
    {d C : ℝ} (hd : 1 / 2 < d)
    (hgapRate : ∀ᶠ N : ℕ in atTop,
      xiHeatCassiniOrderedPrimeLogGap N ≤
        C * Real.exp (-d * xiMassNthPrimeLogHeight N)) :
    Summable xiHeatCassiniPrimeGapCriticalEnergy := by
  have hrate : 0 < d - 1 / 2 := sub_pos.mpr hd
  have hmajor :=
    (summable_primeLogGap_mul_exp_neg_height hrate).mul_left (4 * C)
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hgapRate] with N hN
  let p : ℝ := nthPrimeSubtype N
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hgap : 0 ≤ xiHeatCassiniOrderedPrimeGap N :=
    xiHeatCassiniOrderedPrimeGap_nonneg N
  have hnormalized :
      xiHeatCassiniOrderedPrimeGap N / p ≤ 2 * delta := by
    have hbase := primeGap_div_two_prime_le_primeLogGap N
    dsimp only [p, delta] at hbase ⊢
    calc
      xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ) =
          2 * (xiHeatCassiniOrderedPrimeGap N /
            (2 * (nthPrimeSubtype N : ℝ))) := by
        field_simp [hp.ne']
      _ ≤ 2 * xiHeatCassiniOrderedPrimeLogGap N :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
  have hsqrt : Real.sqrt p =
      Real.exp (xiMassNthPrimeLogHeight N / 2) := by
    rw [xiMassNthPrimeLogHeight]
    rw [← Real.exp_log (Real.sqrt_pos.mpr hp)]
    congr 1
    exact Real.log_sqrt hp.le
  rw [Real.norm_eq_abs, abs_of_nonneg
    (xiHeatCassiniPrimeGapCriticalEnergy_nonneg N)]
  unfold xiHeatCassiniPrimeGapCriticalEnergy
  change (xiHeatCassiniOrderedPrimeGap N / p) ^ (2 : ℕ) * Real.sqrt p ≤ _
  rw [hsqrt]
  calc
    (xiHeatCassiniOrderedPrimeGap N / p) ^ (2 : ℕ) *
          Real.exp (xiMassNthPrimeLogHeight N / 2) ≤
        (2 * delta) ^ (2 : ℕ) *
          Real.exp (xiMassNthPrimeLogHeight N / 2) := by
      gcongr
    _ = 4 * delta * delta *
          Real.exp (xiMassNthPrimeLogHeight N / 2) := by ring
    _ ≤ 4 * (C * Real.exp (-d * xiMassNthPrimeLogHeight N)) * delta *
          Real.exp (xiMassNthPrimeLogHeight N / 2) := by
      gcongr
    _ = (4 * C) * (delta *
          Real.exp (-(d - 1 / 2) * xiMassNthPrimeLogHeight N)) := by
      have heq : Real.exp (-d * xiMassNthPrimeLogHeight N) *
            Real.exp (xiMassNthPrimeLogHeight N / 2) =
          Real.exp (-(d - 1 / 2) * xiMassNthPrimeLogHeight N) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show 4 * (C * Real.exp (-d * xiMassNthPrimeLogHeight N)) * delta *
            Real.exp (xiMassNthPrimeLogHeight N / 2) =
          (4 * C) * delta *
            (Real.exp (-d * xiMassNthPrimeLogHeight N) *
              Real.exp (xiMassNthPrimeLogHeight N / 2)) by ring,
        heq]
      ring

/-- Exponential decay of the centered Wold primitive transfers to the prime-log mesh at every
slightly smaller rate below one.  This is the exact local increment law: Wold mass itself has
rate one, while the two adjacent residual endpoints have the assumed rate. -/
theorem exists_primeLogGap_exp_rate_of_residual_exp_height_rate
    {c d B : ℝ} (hd : 0 < d) (hdc : d < c) (hd1 : d < 1) (hB : 0 ≤ B)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      xiHeatCassiniOrderedPrimeLogGap N ≤
        C * Real.exp (-d * xiMassNthPrimeLogHeight N) := by
  let b : ℝ := 1 - d
  let Cw : ℝ := Real.exp (-1) / b
  let C : ℝ := Cw + 2 * B
  have hb : 0 < b := by dsimp only [b]; linarith
  have hCw : 0 ≤ Cw := by dsimp only [Cw]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hrateSucc : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1)| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight (N + 1)) :=
    (tendsto_add_atTop_nat 1).eventually hrate
  filter_upwards [hrate, hrateSucc] with N hRN hRsucc
  let h : ℝ := xiMassNthPrimeLogHeight N
  let y : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let R : ℝ := xiHeatCassiniOrderedWoldResidualLogDiscrepancy N
  let S : ℝ := xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1)
  have hh : 0 < h := xiMassNthPrimeLogHeight_pos N
  have hy : 0 < y := xiMassNthPrimeLogHeight_pos (N + 1)
  have hhy : h ≤ y := nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
  have hc : 0 < c := hd.trans hdc
  have hRN' : |R| ≤ B * Real.exp (-d * h) := by
    calc
      |R| ≤ B * Real.exp (-c * h) := by simpa only [R, h] using hRN
      _ ≤ B * Real.exp (-d * h) := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply Real.exp_le_exp.mpr
        have hprod := mul_le_mul_of_nonneg_right hdc.le hh.le
        linarith
  have hRsucc' : |S| ≤ B * Real.exp (-d * h) := by
    calc
      |S| ≤ B * Real.exp (-c * y) := by simpa only [S, y] using hRsucc
      _ ≤ B * Real.exp (-d * h) := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply Real.exp_le_exp.mpr
        have : d * h ≤ c * y := by
          calc
            d * h ≤ c * h := mul_le_mul_of_nonneg_right hdc.le hh.le
            _ ≤ c * y := mul_le_mul_of_nonneg_left hhy hc.le
        linarith
  have hscaled : y * Real.exp (-(b * y)) ≤ Cw := by
    rw [show y * Real.exp (-(b * y)) =
        (b * y * Real.exp (-(b * y))) / b by field_simp [hb.ne'],
      div_le_iff₀ hb]
    simpa only [Cw, div_mul_cancel₀ _ hb.ne'] using
      Real.mul_exp_neg_le_exp_neg_one (b * y)
  have hWold : woldCoeff 1 (nthPrimeSubtype (N + 1)) ≤
      Cw * Real.exp (-d * h) := by
    have hwold :=
      (woldCoeff_one_le_harmonic_le_eight_mul_woldCoeff_one
        (nthPrimeSubtype (N + 1))).1
    have hharmonic :
        xiMassPrimeHarmonicRealCoefficient (nthPrimeSubtype (N + 1)) =
          y * Real.exp (-y) := by
      unfold xiMassPrimeHarmonicRealCoefficient
      dsimp only [y, xiMassNthPrimeLogHeight]
      rw [Real.exp_neg, Real.exp_log (nthPrimeSubtype_pos (N + 1))]
      ring
    rw [hharmonic] at hwold
    calc
      woldCoeff 1 (nthPrimeSubtype (N + 1)) ≤ y * Real.exp (-y) := hwold
      _ = (y * Real.exp (-(b * y))) * Real.exp (-d * y) := by
        rw [show Real.exp (-y) =
            Real.exp (-(b * y)) * Real.exp (-d * y) by
          rw [← Real.exp_add]
          congr 1
          dsimp only [b]
          ring]
        ring
      _ ≤ Cw * Real.exp (-d * y) :=
        mul_le_mul_of_nonneg_right hscaled (Real.exp_nonneg _)
      _ ≤ Cw * Real.exp (-d * h) := by
        apply mul_le_mul_of_nonneg_left _ hCw
        apply Real.exp_le_exp.mpr
        have hprod := mul_le_mul_of_nonneg_left hhy hd.le
        linarith
  have hincrement := xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub N
  have hidentity : xiHeatCassiniOrderedPrimeLogGap N =
      woldCoeff 1 (nthPrimeSubtype (N + 1)) - S + R := by
    dsimp only [S, R]
    dsimp only [xiHeatCassiniOrderedPrimeLogGap]
    linarith
  rw [hidentity]
  calc
    woldCoeff 1 (nthPrimeSubtype (N + 1)) - S + R ≤
        woldCoeff 1 (nthPrimeSubtype (N + 1)) + |S| + |R| := by
      linarith [neg_le_abs S, le_abs_self R]
    _ ≤ Cw * Real.exp (-d * h) +
          B * Real.exp (-d * h) + B * Real.exp (-d * h) := by
      gcongr
    _ = C * Real.exp (-d * xiMassNthPrimeLogHeight N) := by
      dsimp only [C, h]
      ring

/-- **Half-threshold coupling.**  Residual exponential decay at any rate strictly above `1/2`
simultaneously supplies the critical prime-gap energy, so mesh and residual continuation are not
independent obstacles beyond that threshold. -/
theorem summable_primeGapCriticalEnergy_of_residual_exp_height_rate
    {c B : ℝ} (hc : 1 / 2 < c) (hB : 0 ≤ B)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) :
    Summable xiHeatCassiniPrimeGapCriticalEnergy := by
  by_cases hc1 : c < 1
  · let d : ℝ := (c + 1 / 2) / 2
    have hd : 1 / 2 < d := by dsimp only [d]; linarith
    have hdc : d < c := by dsimp only [d]; linarith
    have hd1 : d < 1 := by dsimp only [d]; linarith
    obtain ⟨C, hC, hgap⟩ :=
      exists_primeLogGap_exp_rate_of_residual_exp_height_rate
        (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hd) hdc hd1 hB hrate
    exact summable_primeGapCriticalEnergy_of_primeLogGap_exp_rate hd hgap
  · let d : ℝ := 3 / 4
    have hd : 1 / 2 < d := by dsimp only [d]; norm_num
    have hdc : d < c := by dsimp only [d]; linarith
    have hd1 : d < 1 := by dsimp only [d]; norm_num
    obtain ⟨C, hC, hgap⟩ :=
      exists_primeLogGap_exp_rate_of_residual_exp_height_rate
        (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hd) hdc hd1 hB hrate
    exact summable_primeGapCriticalEnergy_of_primeLogGap_exp_rate hd hgap

/-- A genuine exponential residual estimate of rate `c` opens every upper height `a < c`.
Unlike the unconditional square-root-exponential estimate, it defeats the factor `exp(a h_N)`
exactly. -/
theorem summable_residualUpperVariationAtom_of_exp_height_rate
    {a c B : ℝ} (hac : a < c)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) :
    Summable (xiHeatCassiniWoldResidualUpperVariationAtom a) := by
  have hca : 0 < c - a := sub_pos.mpr hac
  have hmajor :=
    (summable_primeLogGap_mul_exp_neg_height hca).mul_left B
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hrate] with N hN
  have hgap : 0 ≤ xiHeatCassiniOrderedPrimeLogGap N :=
    xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hexp : 0 ≤ Real.exp (a * xiMassNthPrimeLogHeight N) :=
    Real.exp_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · dsimp only [xiHeatCassiniWoldResidualUpperVariationAtom]
    calc
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
            xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (a * xiMassNthPrimeLogHeight N) ≤
        (B * Real.exp (-c * xiMassNthPrimeLogHeight N)) *
            xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (a * xiMassNthPrimeLogHeight N) := by gcongr
      _ = B * xiHeatCassiniOrderedPrimeLogGap N *
          (Real.exp (-c * xiMassNthPrimeLogHeight N) *
            Real.exp (a * xiMassNthPrimeLogHeight N)) := by ring
      _ = B * (xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (-(c - a) * xiMassNthPrimeLogHeight N)) := by
        have heq : Real.exp (-c * xiMassNthPrimeLogHeight N) *
              Real.exp (a * xiMassNthPrimeLogHeight N) =
            Real.exp (-(c - a) * xiMassNthPrimeLogHeight N) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [heq]
        ring
  · exact mul_nonneg
      (mul_nonneg (abs_nonneg _) hgap) hexp

/-- Hence an exponential height estimate opens absolute convergence of the raw residual Hardy
series at every legal upper height below its rate. -/
theorem summable_norm_residualAtom_mul_I_of_exp_height_rate
    {a c B : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hac : a < c)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖) := by
  exact (summable_norm_residualAtom_mul_I_iff_upperVariation ha ha1).2
    (summable_residualUpperVariationAtom_of_exp_height_rate hac hrate)

/-- Global atom estimate exposing all upper growth in `exp(h_N im z)`. -/
theorem norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_le_global
    (z : ℂ) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z N‖ ≤
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
          Real.exp (xiMassNthPrimeLogHeight N * z.im) := by
  rw [xiHeatCassiniWoldResidualComplexPhaseConnectionAtom, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have hchord :=
    norm_xiHeatCassiniOrderedPrimeComplexNegativePhase_sub_succ_le_global z N
  exact (mul_le_mul_of_nonneg_left hchord (abs_nonneg _)).trans_eq (by ring)

/-- An eventual exponential estimate can be enlarged across its finite exceptional prefix without
changing its rate.  This is the finite-prefix closure needed by locally uniform series arguments. -/
theorem exists_global_residual_exp_height_bound
    {c B : ℝ} (hB : 0 ≤ B)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) :
    ∃ C : ℝ, 0 ≤ C ∧ B ≤ C ∧ ∀ N : ℕ,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        C * Real.exp (-c * xiMassNthPrimeLogHeight N) := by
  obtain ⟨N₀, htail⟩ := eventually_atTop.1 hrate
  let S : ℝ := ∑ N ∈ Finset.range N₀,
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      Real.exp (c * xiMassNthPrimeLogHeight N)
  let C : ℝ := B + S
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun N _ =>
      mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  have hC : 0 ≤ C := by dsimp only [C]; linarith
  have hBC : B ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, hBC, fun N => ?_⟩
  by_cases hN : N₀ ≤ N
  · calc
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
          B * Real.exp (-c * xiMassNthPrimeLogHeight N) := htail N hN
      _ ≤ C * Real.exp (-c * xiMassNthPrimeLogHeight N) :=
        mul_le_mul_of_nonneg_right hBC (Real.exp_nonneg _)
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr (Nat.lt_of_not_ge hN)
    have hterm :
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
            Real.exp (c * xiMassNthPrimeLogHeight N) ≤ S := by
      dsimp only [S]
      exact Finset.single_le_sum
        (f := fun i : ℕ =>
          |xiHeatCassiniOrderedWoldResidualLogDiscrepancy i| *
            Real.exp (c * xiMassNthPrimeLogHeight i))
        (fun i _ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)) hmem
    have hSC : S ≤ C := by dsimp only [C]; linarith
    calc
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| =
          (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
              Real.exp (c * xiMassNthPrimeLogHeight N)) *
            Real.exp (-c * xiMassNthPrimeLogHeight N) := by
        rw [mul_assoc, ← Real.exp_add]
        simp
      _ ≤ S * Real.exp (-c * xiMassNthPrimeLogHeight N) :=
        mul_le_mul_of_nonneg_right hterm (Real.exp_nonneg _)
      _ ≤ C * Real.exp (-c * xiMassNthPrimeLogHeight N) :=
        mul_le_mul_of_nonneg_right hSC (Real.exp_nonneg _)

/-- Exponential residual decay of rate `c` makes the raw residual atom series absolutely
convergent at every point strictly below height `c`. -/
theorem summable_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_of_exp_height_rate
    {z : ℂ} {c B : ℝ} (hzc : z.im < c) (hB : 0 ≤ B)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) :
    Summable (xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z) := by
  have he : 0 < c - z.im := sub_pos.mpr hzc
  have hmajor :=
    (summable_primeLogGap_mul_exp_neg_height he).mul_left
      (B * ‖z‖ * Real.exp ‖z‖)
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hrate] with N hN
  have hraw :=
    norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_le_global z N
  calc
    ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z N‖ ≤
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
            Real.exp (xiMassNthPrimeLogHeight N * z.im) := hraw
    _ ≤ (B * Real.exp (-c * xiMassNthPrimeLogHeight N)) *
          xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
            Real.exp (xiMassNthPrimeLogHeight N * z.im) := by
      gcongr
      exact xiHeatCassiniOrderedPrimeLogGap_nonneg N
    _ = (B * ‖z‖ * Real.exp ‖z‖) *
          (xiHeatCassiniOrderedPrimeLogGap N *
            Real.exp (-(c - z.im) * xiMassNthPrimeLogHeight N)) := by
      have heq : Real.exp (-c * xiMassNthPrimeLogHeight N) *
            Real.exp (xiMassNthPrimeLogHeight N * z.im) =
          Real.exp (-(c - z.im) * xiMassNthPrimeLogHeight N) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (B * Real.exp (-c * xiMassNthPrimeLogHeight N)) *
              xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
                Real.exp (xiMassNthPrimeLogHeight N * z.im) =
            B * ‖z‖ * Real.exp ‖z‖ * xiHeatCassiniOrderedPrimeLogGap N *
              (Real.exp (-c * xiMassNthPrimeLogHeight N) *
                Real.exp (xiMassNthPrimeLogHeight N * z.im)) := by ring
        _ = (B * ‖z‖ * Real.exp ‖z‖) *
              (xiHeatCassiniOrderedPrimeLogGap N *
                Real.exp (-(c - z.im) * xiMassNthPrimeLogHeight N)) := by
          rw [heq]
          ring

/-- Summability of upper variation at height `a` controls every raw atom at lower imaginary
height.  No pointwise residual rate is needed. -/
theorem summable_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_of_upperVariation
    {z : ℂ} {a : ℝ} (hza : z.im ≤ a)
    (hvariation : Summable (xiHeatCassiniWoldResidualUpperVariationAtom a)) :
    Summable (xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z) := by
  have hmajor := hvariation.mul_left (‖z‖ * Real.exp ‖z‖)
  apply hmajor.of_norm_bounded
  intro N
  have hh : 0 ≤ xiMassNthPrimeLogHeight N :=
    (xiMassNthPrimeLogHeight_pos N).le
  have hexp :
      Real.exp (xiMassNthPrimeLogHeight N * z.im) ≤
        Real.exp (a * xiMassNthPrimeLogHeight N) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hraw :=
    norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_le_global z N
  calc
    ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z N‖ ≤
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
            Real.exp (xiMassNthPrimeLogHeight N * z.im) := hraw
    _ ≤ |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ * Real.exp ‖z‖ *
            Real.exp (a * xiMassNthPrimeLogHeight N) := by
      exact mul_le_mul_of_nonneg_left hexp <| mul_nonneg
        (mul_nonneg
          (mul_nonneg (abs_nonneg _)
            (xiHeatCassiniOrderedPrimeLogGap_nonneg N))
          (norm_nonneg z))
        (Real.exp_nonneg _)
    _ = (‖z‖ * Real.exp ‖z‖) *
          xiHeatCassiniWoldResidualUpperVariationAtom a N := by
      dsimp only [xiHeatCassiniWoldResidualUpperVariationAtom]
      ring

/-- **Sharp residual Abel principle.**  Summability of weighted residual variation at one positive
height `a` makes the canonical residual Hardy source holomorphic at every strictly lower point.
The derivative's extra log height is absorbed solely by the local margin to `a`. -/
theorem hasDerivAt_xiHeatCassiniWoldResidualLowerHardyKernel_of_upperVariation
    {z : ℂ} {a : ℝ} (ha : 0 < a) (hza : z.im < a)
    (hvariation : Summable (xiHeatCassiniWoldResidualUpperVariationAtom a)) :
    HasDerivAt xiHeatCassiniWoldResidualLowerHardyKernel
      (∑' N : ℕ, xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom z N) z := by
  let r : ℝ := (a - z.im) / 2
  let b : ℝ := max 0 (z.im + r)
  let K : ℝ := ‖z‖ + r
  let e : ℝ := a - b
  let C : ℝ := (2 / e) * K * Real.exp K + Real.exp b
  let M : ℕ → ℝ := fun N =>
    C * xiHeatCassiniWoldResidualUpperVariationAtom a N
  have hr : 0 < r := by dsimp only [r]; linarith
  have hmid : z.im + r < a := by dsimp only [r]; linarith
  have hb0 : 0 ≤ b := by dsimp only [b]; exact le_max_left _ _
  have hba : b < a := by
    dsimp only [b]
    simpa only [max_lt_iff] using And.intro ha hmid
  have he : 0 < e := by dsimp only [e]; linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hM : Summable M := by
    exact hvariation.mul_left C
  have hzball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := M) (t := Metric.ball z r)
    (g := fun N w => xiHeatCassiniWoldResidualComplexPhaseConnectionAtom w N)
    (g' := fun N w => xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom w N)
    (y₀ := z) (y := z) hM Metric.isOpen_ball (convex_ball z r).isPreconnected
    (fun N w _ => hasDerivAt_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom N w)
    (fun N w hw => by
      have hwsub : ‖w - z‖ < r := by simpa [Metric.mem_ball, dist_eq] using hw
      have hwim : w.im ≤ b := by
        have him : |w.im - z.im| ≤ ‖w - z‖ := by
          rw [← Complex.sub_im]
          exact Complex.abs_im_le_norm _
        have hwlt : w.im < z.im + r := by
          have : w.im - z.im < r :=
            lt_of_le_of_lt (le_abs_self _) (him.trans_lt hwsub)
          linarith
        exact hwlt.le.trans (le_max_right 0 (z.im + r))
      have hwnorm : ‖w‖ ≤ K := by
        dsimp only [K]
        calc
          ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
            simpa only [sub_add_cancel] using norm_add_le (w - z) z
          _ ≤ ‖z‖ + r := by linarith
      have hnormexp : ‖w‖ * Real.exp ‖w‖ ≤ K * Real.exp K := by
        exact mul_le_mul hwnorm (Real.exp_le_exp.mpr hwnorm)
          (Real.exp_nonneg _) hK
      have hshape :
          xiMassNthPrimeLogHeight N * ‖w‖ * Real.exp ‖w‖ + Real.exp b ≤
            xiMassNthPrimeLogHeight N * K * Real.exp K + Real.exp b := by
        have := mul_le_mul_of_nonneg_left hnormexp
          (xiMassNthPrimeLogHeight_pos N).le
        linarith
      let h : ℝ := xiMassNthPrimeLogHeight N
      have hh : 0 ≤ h := by
        dsimp only [h]
        exact (xiMassNthPrimeLogHeight_pos N).le
      have hgap0 : 0 ≤ xiHeatCassiniOrderedPrimeLogGap N :=
        xiHeatCassiniOrderedPrimeLogGap_nonneg N
      have hshape0 : 0 ≤ h * ‖w‖ * Real.exp ‖w‖ + Real.exp b :=
        add_nonneg
          (mul_nonneg (mul_nonneg hh (norm_nonneg w)) (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      have habsorb := pow_mul_exp_neg_le_absorb_half he hh 1
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at habsorb
      have hexpHalf : Real.exp (-(e * h / 2)) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have : 0 ≤ e * h := mul_nonneg he.le hh
        linarith
      have hheightDamped : h * Real.exp (-e * h) ≤ 2 / e := by
        calc
          h * Real.exp (-e * h) = h * Real.exp (-(e * h)) := by ring
          _ ≤ (2 / e) * Real.exp (-(e * h / 2)) := habsorb
          _ ≤ (2 / e) * 1 :=
            mul_le_mul_of_nonneg_left hexpHalf (by positivity)
          _ = 2 / e := by ring
      have hexpDamped : Real.exp (-e * h) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have : 0 ≤ e * h := mul_nonneg he.le hh
        linarith
      have hdampedShape :
          Real.exp (-e * h) *
              (h * K * Real.exp K + Real.exp b) ≤ C := by
        dsimp only [C]
        calc
          Real.exp (-e * h) * (h * K * Real.exp K + Real.exp b) =
              (h * Real.exp (-e * h)) * K * Real.exp K +
                Real.exp (-e * h) * Real.exp b := by ring
          _ ≤ (2 / e) * K * Real.exp K + 1 * Real.exp b := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hheightDamped hK)
                (Real.exp_nonneg _))
              (mul_le_mul_of_nonneg_right hexpDamped (Real.exp_nonneg _))
          _ = (2 / e) * K * Real.exp K + Real.exp b := by ring
      have hraw :=
        norm_xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom_le_global
          hb0 hwim N
      have heq : Real.exp (h * b) = Real.exp (a * h) * Real.exp (-e * h) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [e]
        ring
      calc
        ‖xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom w N‖ ≤
            |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
              xiHeatCassiniOrderedPrimeLogGap N * Real.exp (h * b) *
                (h * ‖w‖ * Real.exp ‖w‖ + Real.exp b) := by
          simpa only [h] using hraw
        _ ≤ |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
              xiHeatCassiniOrderedPrimeLogGap N * Real.exp (h * b) *
                (h * K * Real.exp K + Real.exp b) :=
          mul_le_mul_of_nonneg_left hshape <| mul_nonneg
            (mul_nonneg (abs_nonneg _) hgap0) (Real.exp_nonneg _)
        _ = xiHeatCassiniWoldResidualUpperVariationAtom a N *
              (Real.exp (-e * h) *
                (h * K * Real.exp K + Real.exp b)) := by
          rw [heq]
          dsimp only [xiHeatCassiniWoldResidualUpperVariationAtom]
          ring
        _ ≤ xiHeatCassiniWoldResidualUpperVariationAtom a N * C :=
          mul_le_mul_of_nonneg_left hdampedShape <| mul_nonneg
            (mul_nonneg (abs_nonneg _) hgap0) (Real.exp_nonneg _)
        _ = M N := by dsimp only [M]; ring)
    hzball
    (summable_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_of_upperVariation
      hza.le hvariation)
    hzball
  change HasDerivAt
    (fun w : ℂ => ∑' N : ℕ,
      xiHeatCassiniWoldResidualComplexPhaseConnectionAtom w N)
    (∑' N : ℕ, xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom z N) z
  exact hmain

/-- One summable upper-variation slice opens a canonical holomorphic half-plane below it. -/
theorem analyticOnNhd_xiHeatCassiniWoldResidualLowerHardyKernel_of_upperVariation
    {a : ℝ} (ha : 0 < a)
    (hvariation : Summable (xiHeatCassiniWoldResidualUpperVariationAtom a)) :
    AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < a} := by
  have hopen : IsOpen {z : ℂ | z.im < a} :=
    isOpen_lt Complex.continuous_im continuous_const
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro z hz
  exact
    (hasDerivAt_xiHeatCassiniWoldResidualLowerHardyKernel_of_upperVariation
      ha hz hvariation).differentiableAt.differentiableWithinAt

/-- Absolute convergence at the single boundary point `i a` opens the full half-plane below it. -/
theorem analyticOnNhd_xiHeatCassiniWoldResidualLowerHardyKernel_of_summable_norm_mul_I
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hnorm : Summable (fun N : ℕ =>
      ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖)) :
    AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < a} := by
  exact analyticOnNhd_xiHeatCassiniWoldResidualLowerHardyKernel_of_upperVariation ha
    ((summable_norm_residualAtom_mul_I_iff_upperVariation ha ha1).1 hnorm)

/-- Cofinal absolute convergence below height `1/2` opens the entire critical source half-strip.
This is the exact non-rate formulation compatible with critical-line oscillation. -/
theorem analyticOnNhd_xiHeatCassiniWoldResidualLowerHardyKernel_of_subhalf_absoluteConvergence
    (hconv : ∀ a : ℝ, 0 < a → a < 1 / 2 →
      Summable (fun N : ℕ =>
        ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
          (Complex.I * (a : ℂ)) N‖)) :
    AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < 1 / 2} := by
  have hopen : IsOpen {z : ℂ | z.im < 1 / 2} :=
    isOpen_lt Complex.continuous_im continuous_const
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro z hz
  change z.im < 1 / 2 at hz
  let a : ℝ := (max 0 z.im + 1 / 2) / 2
  have hmax0 : 0 ≤ max 0 z.im := le_max_left _ _
  have hmaxhalf : max 0 z.im < 1 / 2 := by
    simpa only [max_lt_iff] using And.intro (by norm_num : (0 : ℝ) < 1 / 2) hz
  have ha : 0 < a := by dsimp only [a]; linarith
  have hahalf : a < 1 / 2 := by dsimp only [a]; linarith
  have hza : z.im < a := by
    have hzmax : z.im ≤ max 0 z.im := le_max_right _ _
    dsimp only [a]
    linarith
  have ha1 : a ≤ 1 := by linarith
  have hvariation : Summable (xiHeatCassiniWoldResidualUpperVariationAtom a) :=
    (summable_norm_residualAtom_mul_I_iff_upperVariation ha ha1).1
      (hconv a ha hahalf)
  exact
    (hasDerivAt_xiHeatCassiniWoldResidualLowerHardyKernel_of_upperVariation
      ha hza hvariation).differentiableAt.differentiableWithinAt

/-- A genuine exponential residual estimate opens the full source kernel, not merely its values on
the imaginary axis: below the rate abscissa, atom and derivative series converge locally uniformly. -/
theorem hasDerivAt_xiHeatCassiniWoldResidualLowerHardyKernel_of_exp_height_rate
    {z : ℂ} {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (hzc : z.im < c)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) :
    HasDerivAt xiHeatCassiniWoldResidualLowerHardyKernel
      (∑' N : ℕ, xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom z N) z := by
  obtain ⟨C, hC, hBC, hglobal⟩ :=
    exists_global_residual_exp_height_bound hB hrate
  let r : ℝ := (c - z.im) / 2
  let b : ℝ := max 0 (z.im + r)
  let K : ℝ := ‖z‖ + r
  let e : ℝ := c - b
  let M : ℕ → ℝ := fun N =>
    C * xiHeatCassiniOrderedPrimeLogGap N *
      Real.exp (-e * xiMassNthPrimeLogHeight N) *
        (xiMassNthPrimeLogHeight N * K * Real.exp K + Real.exp b)
  have hr : 0 < r := by dsimp only [r]; linarith
  have hmid : z.im + r < c := by dsimp only [r]; linarith
  have hb0 : 0 ≤ b := by dsimp only [b]; exact le_max_left _ _
  have hbc : b < c := by
    dsimp only [b]
    simpa only [max_lt_iff] using And.intro hc hmid
  have he : 0 < e := by dsimp only [e]; linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hM : Summable M := by
    have hheight :=
      (summable_primeLogGap_mul_height_mul_exp_neg_height he).mul_left
        (C * K * Real.exp K)
    have hplain :=
      (summable_primeLogGap_mul_exp_neg_height he).mul_left
        (C * Real.exp b)
    exact (hheight.add hplain).congr fun N => by
      dsimp only [M]
      ring
  have hzball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := M) (t := Metric.ball z r)
    (g := fun N w => xiHeatCassiniWoldResidualComplexPhaseConnectionAtom w N)
    (g' := fun N w => xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom w N)
    (y₀ := z) (y := z) hM Metric.isOpen_ball (convex_ball z r).isPreconnected
    (fun N w _ => hasDerivAt_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom N w)
    (fun N w hw => by
      have hwsub : ‖w - z‖ < r := by simpa [Metric.mem_ball, dist_eq] using hw
      have hwim : w.im ≤ b := by
        have him : |w.im - z.im| ≤ ‖w - z‖ := by
          rw [← Complex.sub_im]
          exact Complex.abs_im_le_norm _
        have hwlt : w.im < z.im + r := by
          have : w.im - z.im < r :=
            lt_of_le_of_lt (le_abs_self _) (him.trans_lt hwsub)
          linarith
        exact hwlt.le.trans (le_max_right 0 (z.im + r))
      have hwnorm : ‖w‖ ≤ K := by
        dsimp only [K]
        calc
          ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
            simpa only [sub_add_cancel] using norm_add_le (w - z) z
          _ ≤ ‖z‖ + r := by linarith
      have hnormexp : ‖w‖ * Real.exp ‖w‖ ≤ K * Real.exp K := by
        exact mul_le_mul hwnorm (Real.exp_le_exp.mpr hwnorm)
          (Real.exp_nonneg _) hK
      have hshape :
          xiMassNthPrimeLogHeight N * ‖w‖ * Real.exp ‖w‖ + Real.exp b ≤
            xiMassNthPrimeLogHeight N * K * Real.exp K + Real.exp b := by
        have := mul_le_mul_of_nonneg_left hnormexp
          (xiMassNthPrimeLogHeight_pos N).le
        linarith
      have hraw :=
        norm_xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom_le_global
          hb0 hwim N
      let h : ℝ := xiMassNthPrimeLogHeight N
      have hh : 0 ≤ h := by
        dsimp only [h]
        exact (xiMassNthPrimeLogHeight_pos N).le
      have hgap0 : 0 ≤ xiHeatCassiniOrderedPrimeLogGap N :=
        xiHeatCassiniOrderedPrimeLogGap_nonneg N
      have hshape0 : 0 ≤ h * ‖w‖ * Real.exp ‖w‖ + Real.exp b :=
        add_nonneg
          (mul_nonneg (mul_nonneg hh (norm_nonneg w)) (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      have heq : Real.exp (-c * h) * Real.exp (h * b) =
          Real.exp (-e * h) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [e]
        ring
      calc
        ‖xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom w N‖ ≤
            |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
              xiHeatCassiniOrderedPrimeLogGap N * Real.exp (h * b) *
                (h * ‖w‖ * Real.exp ‖w‖ + Real.exp b) := by
          simpa only [h] using hraw
        _ = |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
              (xiHeatCassiniOrderedPrimeLogGap N * Real.exp (h * b) *
                (h * ‖w‖ * Real.exp ‖w‖ + Real.exp b)) := by ring
        _ ≤ (C * Real.exp (-c * h)) *
              (xiHeatCassiniOrderedPrimeLogGap N * Real.exp (h * b) *
                (h * ‖w‖ * Real.exp ‖w‖ + Real.exp b)) :=
          mul_le_mul_of_nonneg_right (by simpa only [h] using hglobal N)
            (mul_nonneg
              (mul_nonneg hgap0 (Real.exp_nonneg _)) hshape0)
        _ ≤ (C * Real.exp (-c * h)) *
              (xiHeatCassiniOrderedPrimeLogGap N * Real.exp (h * b) *
                (h * K * Real.exp K + Real.exp b)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hshape
              (mul_nonneg hgap0 (Real.exp_nonneg _)))
            (mul_nonneg hC (Real.exp_nonneg _))
        _ = M N := by
          dsimp only [M]
          rw [show (C * Real.exp (-c * h)) *
                (xiHeatCassiniOrderedPrimeLogGap N * Real.exp (h * b) *
                  (h * K * Real.exp K + Real.exp b)) =
              C * xiHeatCassiniOrderedPrimeLogGap N *
                (Real.exp (-c * h) * Real.exp (h * b)) *
                  (h * K * Real.exp K + Real.exp b) by ring,
            heq])
    hzball
    (summable_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_of_exp_height_rate
      hzc hB hrate)
    hzball
  change HasDerivAt
    (fun w : ℂ => ∑' N : ℕ,
      xiHeatCassiniWoldResidualComplexPhaseConnectionAtom w N)
    (∑' N : ℕ, xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom z N) z
  exact hmain

/-- **Residual upper-strip theorem.**  Exponential residual rate `c > 0` extends the canonical
Hardy source holomorphically to the entire half-plane `im z < c`. -/
theorem analyticOnNhd_xiHeatCassiniWoldResidualLowerHardyKernel_of_exp_height_rate
    {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) :
    AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel
      {z : ℂ | z.im < c} := by
  have hopen : IsOpen {z : ℂ | z.im < c} :=
    isOpen_lt Complex.continuous_im continuous_const
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro z hz
  exact
    (hasDerivAt_xiHeatCassiniWoldResidualLowerHardyKernel_of_exp_height_rate
      hc hB hz hrate).differentiableAt.differentiableWithinAt

end

end RHTower

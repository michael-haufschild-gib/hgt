import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileCosinePhaseNormalForm

/-!
# Outgoing-quantile characteristic transport law

The consecutive CCM mass-quantile cells aggregate to one exact discrepancy between continuous
polar cosine data on `[0, b_N]` and atomic prime cosine data at `log n`, with equal mass built into
each cell. Its global second derivative at zero is the corresponding signed second-moment defect.

Equal mass supplies more than a generic Lipschitz estimate: the cosine discrepancy has quadratic
contact at zero. A sharp elementary cosine square bound controls the whole finite symbol by literal
absolute second-moment transport work. Thus signed work governs curvature while absolute work
governs magnitude. No sign assumption or RH-equivalent premise enters these identities.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

theorem sum_intervalIntegral_quantileCells_eq_zero_to_boundary
    (F : ℝ → ℝ) (hF : Continuous F) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1), F h) =
      ∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N, F h := by
  induction N with
  | zero => simp [ccmOutgoingPrimeQuantileBoundary_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hF.intervalIntegrable (μ := volume) 0
          (ccmOutgoingPrimeQuantileBoundary N))
        (hF.intervalIntegrable (μ := volume)
          (ccmOutgoingPrimeQuantileBoundary N)
          (ccmOutgoingPrimeQuantileBoundary (N + 1)))

theorem ccmActualHeadOutgoingQuantileCosinePhaseProfile_eq_polar_sub_atom
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi =
      (∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      criticalMellinAtomWeight n *
        Real.cos (2 * Real.pi * Real.log n * xi) := by
  let lo := ccmOutgoingPrimeQuantileBoundary n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let C : ℝ := Real.cos (2 * Real.pi * Real.log n * xi)
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi))
      volume lo hi := (by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)).intervalIntegrable _ _
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * C)
      volume lo hi := (by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2) * C).intervalIntegrable _ _
  have hmass := integral_exp_half_quantileCell_eq_atomWeight n
  unfold ccmActualHeadOutgoingQuantileCosinePhaseProfile
  change (∫ h in lo..hi,
      Real.exp (h / 2) *
        (Real.cos (2 * Real.pi * h * xi) - C)) = _
  calc
    (∫ h in lo..hi,
      Real.exp (h / 2) *
        (Real.cos (2 * Real.pi * h * xi) - C)) =
      (∫ h in lo..hi,
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      (∫ h in lo..hi, Real.exp (h / 2) * C) := by
        rw [← intervalIntegral.integral_sub hvar hconst]
        apply intervalIntegral.integral_congr
        intro h hh
        ring
    _ = (∫ h in lo..hi,
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      (∫ h in lo..hi, Real.exp (h / 2)) * C := by
        rw [intervalIntegral.integral_mul_const]
    _ = (∫ h in lo..hi,
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      criticalMellinAtomWeight n * C := by
        rw [hmass]

/-- The finite quantile phase symbol is one cosine-characteristic discrepancy of equal-mass
continuous polar and atomic prime measures. -/
theorem ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_eq_characteristicDiscrepancy
    (N : ℕ) (xi : ℝ) :
    ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi =
      (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      ∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n *
          Real.cos (2 * Real.pi * Real.log n * xi) := by
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol
  simp_rw [ccmActualHeadOutgoingQuantileCosinePhaseProfile_eq_polar_sub_atom]
  rw [Finset.sum_sub_distrib]
  rw [sum_intervalIntegral_quantileCells_eq_zero_to_boundary
    (fun h : ℝ => Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi))
    (by fun_prop)]

def ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet
    (N : ℕ) (xi : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    ccmActualHeadOutgoingQuantileCosinePhaseFirstJet n xi

def ccmActualHeadOutgoingQuantileCosinePhaseFiniteSecondJet
    (N : ℕ) (xi : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    ccmActualHeadOutgoingQuantileCosinePhaseSecondJet n xi

theorem hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol
    (N : ℕ) (xi : ℝ) :
    HasDerivAt (ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N)
      (ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet N xi) xi := by
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet
  have hsum := HasDerivAt.sum (u := Finset.range N) fun n hn =>
    hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi
  exact hsum.congr_of_eventuallyEq
    (Eventually.of_forall fun _ => by simp only [Finset.sum_apply])

theorem hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet
    (N : ℕ) (xi : ℝ) :
    HasDerivAt (ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet N)
      (ccmActualHeadOutgoingQuantileCosinePhaseFiniteSecondJet N xi) xi := by
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteSecondJet
  have hsum := HasDerivAt.sum (u := Finset.range N) fun n hn =>
    hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFirstJet n xi
  exact hsum.congr_of_eventuallyEq
    (Eventually.of_forall fun _ => by simp only [Finset.sum_apply])

/-- Global low-frequency curvature is exactly the second-moment discrepancy of the two equal-mass
measures in the characteristic transport law. -/
theorem ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_secondDeriv_zero
    (N : ℕ) :
    deriv (deriv (ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N)) 0 =
      4 * Real.pi ^ 2 *
        ((∑ n ∈ Finset.range N,
          criticalMellinAtomWeight n * (Real.log n) ^ 2) -
        ∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * h ^ 2) := by
  have hfirst :
      deriv (ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N) =
        ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet N := by
    funext xi
    exact (hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi).deriv
  rw [hfirst]
  rw [(hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet N 0).deriv]
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteSecondJet
  simp_rw [ccmActualHeadOutgoingQuantileCosinePhaseSecondJet_zero_eq_momentError]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib]
  rw [sum_intervalIntegral_quantileCells_eq_zero_to_boundary
    (fun h : ℝ => Real.exp (h / 2) * h ^ 2) (by fun_prop)]

theorem abs_cos_sub_cos_le_half_abs_sq_sub_sq (x y : ℝ) :
    |Real.cos x - Real.cos y| ≤ |x ^ 2 - y ^ 2| / 2 := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg]
  norm_num
  have hsum : |Real.sin ((x + y) / 2)| ≤ |(x + y) / 2| :=
    Real.abs_sin_le_abs
  have hdiff : |Real.sin ((x - y) / 2)| ≤ |(x - y) / 2| :=
    Real.abs_sin_le_abs
  calc
    2 * |Real.sin ((x + y) / 2)| * |Real.sin ((x - y) / 2)| ≤
        2 * |(x + y) / 2| * |(x - y) / 2| := by
      gcongr
    _ = |x ^ 2 - y ^ 2| / 2 := by
      rw [show 2 * |(x + y) / 2| * |(x - y) / 2| =
        2 * |((x + y) / 2) * ((x - y) / 2)| by rw [abs_mul]; ring]
      rw [show (x + y) / 2 * ((x - y) / 2) = (x ^ 2 - y ^ 2) / 4 by ring,
        abs_div]
      norm_num
      ring

/-- Absolute second-moment work of one mass-quantile cell. Unlike the signed curvature work,
this quantity is nonnegative and controls the full characteristic discrepancy. -/
def ccmActualHeadOutgoingQuantileQuadraticTransportCellCost (n : ℕ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n + 1),
    Real.exp (h / 2) * |h ^ 2 - (Real.log n) ^ 2|

def ccmActualHeadOutgoingQuantileQuadraticTransportFiniteCost (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    ccmActualHeadOutgoingQuantileQuadraticTransportCellCost n

theorem ccmActualHeadOutgoingQuantileCosinePhaseProfile_abs_le_quadraticTransport
    (n : ℕ) (xi : ℝ) :
    |ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi| ≤
      (2 * Real.pi * xi) ^ 2 / 2 *
        ccmActualHeadOutgoingQuantileQuadraticTransportCellCost n := by
  let lo := ccmOutgoingPrimeQuantileBoundary n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let k := 2 * Real.pi * xi
  have hlohi : lo ≤ hi := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hleft : Continuous fun h : ℝ =>
      Real.exp (h / 2) *
        (Real.cos (k * h) - Real.cos (k * Real.log n)) := by fun_prop
  have hright : Continuous fun h : ℝ =>
      k ^ 2 / 2 * (Real.exp (h / 2) * |h ^ 2 - (Real.log n) ^ 2|) := by fun_prop
  have hphase (h : ℝ) : 2 * Real.pi * h * xi = k * h := by
    dsimp only [k]
    ring
  unfold ccmActualHeadOutgoingQuantileCosinePhaseProfile
    ccmActualHeadOutgoingQuantileQuadraticTransportCellCost
  change |∫ h in lo..hi,
      Real.exp (h / 2) *
        (Real.cos (2 * Real.pi * h * xi) -
          Real.cos (2 * Real.pi * Real.log n * xi))| ≤
    k ^ 2 / 2 *
      ∫ h in lo..hi, Real.exp (h / 2) * |h ^ 2 - (Real.log n) ^ 2|
  simp_rw [hphase]
  refine (intervalIntegral.abs_integral_le_integral_abs hlohi).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hlohi (hleft.abs.intervalIntegrable lo hi)
    (hright.intervalIntegrable lo hi) fun h hh => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hcos := abs_cos_sub_cos_le_half_abs_sq_sub_sq (k * h) (k * Real.log n)
  calc
    Real.exp (h / 2) * |Real.cos (k * h) - Real.cos (k * Real.log n)| ≤
        Real.exp (h / 2) * |(k * h) ^ 2 - (k * Real.log n) ^ 2| / 2 := by
      exact (mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le).trans_eq (by ring)
    _ = k ^ 2 / 2 * (Real.exp (h / 2) * |h ^ 2 - (Real.log n) ^ 2|) := by
      rw [show (k * h) ^ 2 - (k * Real.log n) ^ 2 =
        k ^ 2 * (h ^ 2 - (Real.log n) ^ 2) by ring,
        abs_mul, abs_of_nonneg (sq_nonneg k)]
      ring

/-- Equal-mass quantile matching upgrades the finite characteristic discrepancy from a generic
Lipschitz estimate to quadratic contact at frequency zero. The control is literal absolute
second-moment transport work; no sign premise is used. -/
theorem ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_abs_le_quadraticTransport
    (N : ℕ) (xi : ℝ) :
    |ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi| ≤
      (2 * Real.pi * xi) ^ 2 / 2 *
        ccmActualHeadOutgoingQuantileQuadraticTransportFiniteCost N := by
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol
  unfold ccmActualHeadOutgoingQuantileQuadraticTransportFiniteCost
  calc
    |∑ n ∈ Finset.range N,
        ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi| ≤
      ∑ n ∈ Finset.range N,
        |ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N,
        (2 * Real.pi * xi) ^ 2 / 2 *
          ccmActualHeadOutgoingQuantileQuadraticTransportCellCost n := by
      exact Finset.sum_le_sum fun n hn =>
        ccmActualHeadOutgoingQuantileCosinePhaseProfile_abs_le_quadraticTransport n xi
    _ = (2 * Real.pi * xi) ^ 2 / 2 *
        ∑ n ∈ Finset.range N,
          ccmActualHeadOutgoingQuantileQuadraticTransportCellCost n := by
      rw [Finset.mul_sum]

end RHTower

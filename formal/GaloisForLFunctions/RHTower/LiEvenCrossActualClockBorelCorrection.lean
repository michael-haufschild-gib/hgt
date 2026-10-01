import GaloisForLFunctions.RHTower.PrimeArchThetaRawMomentRatioVanishing
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelSource
import GaloisForLFunctions.RHTower.LiClockPositiveEvenSeriesRatio
import GaloisForLFunctions.HTGeometry.EntireSeriesEulerJet
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual theta-source Borel correction

The literal correction `(B' + t B'')''` has a positive complete odd series.
The adjacent actual raw-moment ratio implies that this correction divided by
`B'` tends to zero at positive infinity. Compact factorial bounds admit every
ordinary derivative before the series identities or origin values are used.
-/

open Filter Topology Set
namespace RHTower
noncomputable section

/-- The second derivative of the literal weighted Borel derivative. -/
def liEvenCrossActualClockBorelCorrection (t : ℝ) : ℝ :=
  iteratedDeriv 2 (fun x : ℝ =>
    deriv liEvenCrossActualClockBorelKernel x +
      x * iteratedDeriv 2 liEvenCrossActualClockBorelKernel x) t

private def bcTerm (m j : ℕ) (t : ℝ) : ℝ :=
  liEvenCrossActualClockBorelCoefficient j * ((2*j).descFactorial m : ℝ) *
    t^(2*j-m)

private def bcSeries (m : ℕ) (t : ℝ) : ℝ := ∑' j, bcTerm m j t

private theorem bc_coefficient_le_inverse_factorial (j : ℕ) :
    liEvenCrossActualClockBorelCoefficient j ≤ ((j.factorial : ℝ))⁻¹ := by
  have hp : (32/303 : ℝ)^j ≤ 1 := by
    simpa using pow_le_pow_left₀ (by norm_num : 0 ≤ (32/303 : ℝ))
      (by norm_num : (32/303 : ℝ) ≤ 1) j
  calc
    liEvenCrossActualClockBorelCoefficient j ≤
        (32/303 : ℝ)^j/(j.factorial : ℝ) := liEvenCrossActualClockBorelCoefficient_le j
    _ ≤ 1/(j.factorial : ℝ) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ = _ := one_div _

private theorem bc_term_bound (m j : ℕ) {t T : ℝ}
    (hT : 1 ≤ T) (ht : |t| ≤ T) :
    ‖bcTerm m j t‖ ≤ (2:ℝ)^m*(j:ℝ)^m*
      liEvenCrossActualClockBorelCoefficient j*T^(2*j) := by
  have hd : ((2*j).descFactorial m : ℝ) ≤ (2:ℝ)^m*(j:ℝ)^m := by
    calc
      ((2*j).descFactorial m : ℝ) ≤ (((2*j : ℕ) : ℝ))^m := by
        exact_mod_cast Nat.descFactorial_le_pow (2*j) m
      _ = _ := by push_cast; rw [mul_pow]
  have hp : |t|^(2*j-m) ≤ T^(2*j) :=
    (pow_le_pow_left₀ (abs_nonneg t) ht _).trans
      (pow_le_pow_right₀ hT (Nat.sub_le _ _))
  have hc := (liEvenCrossActualClockBorelCoefficient_pos j).le
  rw [bcTerm, norm_mul, norm_mul, Real.norm_eq_abs,
    abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j),
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), norm_pow, Real.norm_eq_abs]
  calc
    liEvenCrossActualClockBorelCoefficient j * ((2*j).descFactorial m : ℝ) *
        |t|^(2*j-m) ≤
      (liEvenCrossActualClockBorelCoefficient j*((2:ℝ)^m*(j:ℝ)^m))*T^(2*j) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd
        (liEvenCrossActualClockBorelCoefficient_pos j).le) hp
        (by positivity) (by positivity)
    _ = _ := by ring

private theorem bc_envelope_summable (m : ℕ) {T : ℝ} (_hT : 0 ≤ T) :
    Summable (fun j : ℕ => (2:ℝ)^m*(j:ℝ)^m*
      liEvenCrossActualClockBorelCoefficient j*T^(2*j)) := by
  have hc (j : ℕ) : ‖(liEvenCrossActualClockBorelCoefficient j : ℂ)‖ ≤
      ((j.factorial : ℝ))⁻¹ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j)]
      using bc_coefficient_le_inverse_factorial j
  have hs := GaloisForLFunctions.HTGeometry.summable_pow_mul_of_factorial_decay
    hc m (sq_nonneg T)
  have he : (fun j : ℕ => (2:ℝ)^m*((j:ℝ)^m*
        (‖(liEvenCrossActualClockBorelCoefficient j : ℂ)‖*(T^2)^j))) =
      (fun j : ℕ => (2:ℝ)^m*(j:ℝ)^m*
        liEvenCrossActualClockBorelCoefficient j*T^(2*j)) := by
    funext j
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j), ← pow_mul]
    ring
  rw [← he]
  exact hs.mul_left _

private theorem bc_norm_summable (m : ℕ) (t : ℝ) :
    Summable (fun j => ‖bcTerm m j t‖) := by
  let T := |t|+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => bc_term_bound m j hT (by dsimp [T]; linarith))
    (bc_envelope_summable m (by linarith))

private theorem bc_summable (m : ℕ) (t : ℝ) : Summable (fun j => bcTerm m j t) :=
  (bc_norm_summable m t).of_norm

private theorem bc_term_hasDerivAt (m j : ℕ) (t : ℝ) :
    HasDerivAt (bcTerm m j) (bcTerm (m+1) j t) t := by
  have he : 2*j-(m+1) = 2*j-m-1 := by omega
  convert (((hasDerivAt_id t).pow (2*j-m)).const_mul
    (liEvenCrossActualClockBorelCoefficient j*((2*j).descFactorial m : ℝ))) using 1 <;>
    first | rfl | (simp only [bcTerm, Nat.descFactorial_succ, Nat.cast_mul,
      id_eq, mul_one, he]; ring)

private theorem bc_series_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (bcSeries m) (bcSeries (m+1) t) t := by
  let T := |t|+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  exact hasDerivAt_tsum_of_isPreconnected
    (bc_envelope_summable (m+1) (by linarith)) Metric.isOpen_ball
    (convex_ball (0:ℝ) T).isPreconnected
    (fun j y _ => bc_term_hasDerivAt m j y)
    (fun j y hy => bc_term_bound (m+1) j hT
      (le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hy)))
    (by simp [Metric.mem_ball, T]; positivity) (bc_summable m 0)
    (by simp [Metric.mem_ball, T])

private theorem bc_series_zero : bcSeries 0 = liEvenCrossActualClockBorelKernel := by
  funext t
  unfold bcSeries liEvenCrossActualClockBorelKernel
  apply tsum_congr
  intro j
  simp [bcTerm, liEvenCrossActualClockBorelTerm_eq_coefficient_mul]

private theorem bc_iteratedDeriv (m : ℕ) :
    iteratedDeriv m liEvenCrossActualClockBorelKernel = bcSeries m := by
  induction m with
  | zero => simpa using bc_series_zero.symm
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (bc_series_hasDerivAt m t).deriv

private theorem bc_first_deriv : deriv liEvenCrossActualClockBorelKernel = bcSeries 1 := by
  rw [← iteratedDeriv_one, bc_iteratedDeriv]

private theorem bc_inner_deriv :
    deriv (fun t : ℝ => bcSeries 1 t+t*bcSeries 2 t) =
      (fun t : ℝ => 2*bcSeries 2 t+t*bcSeries 3 t) := by
  funext t
  have h := (bc_series_hasDerivAt 1 t).add
    ((hasDerivAt_id t).mul (bc_series_hasDerivAt 2 t))
  convert h.deriv using 1 <;>
    solve | rfl | congr 1 | (simp only [id_eq]; ring)

private theorem bc_literal (t : ℝ) :
    liEvenCrossActualClockBorelCorrection t = 3*bcSeries 3 t+t*bcSeries 4 t := by
  rw [liEvenCrossActualClockBorelCorrection, bc_first_deriv, bc_iteratedDeriv 2,
    iteratedDeriv_succ (n := 1), iteratedDeriv_one, bc_inner_deriv]
  have h := ((bc_series_hasDerivAt 2 t).const_mul 2).add
    ((hasDerivAt_id t).mul (bc_series_hasDerivAt 3 t))
  convert h.deriv using 1 <;>
    solve | rfl | congr 1 | (simp only [id_eq]; ring)

/-- The literal correction preserves both terms in the ordinary derivative identity. -/
theorem liEvenCrossActualClockBorelCorrection_eq_derivatives (t : ℝ) :
    liEvenCrossActualClockBorelCorrection t =
      3*iteratedDeriv 3 liEvenCrossActualClockBorelKernel t+
        t*iteratedDeriv 4 liEvenCrossActualClockBorelKernel t := by
  rw [bc_iteratedDeriv, bc_iteratedDeriv]
  exact bc_literal t

private theorem bc_shifted_hasSum {f : ℕ → ℝ} (hf : Summable f) (k : ℕ)
    (hz : ∀ j, j < k → f j = 0) : HasSum (fun r => f (r+k)) (∑' j, f j) := by
  have hh : ∑ j ∈ Finset.range k, f j = 0 :=
    Finset.sum_eq_zero (fun j hj => hz j (Finset.mem_range.mp hj))
  have he := hf.sum_add_tsum_nat_add k
  rw [hh, zero_add] at he
  rw [← he]
  exact ((summable_nat_add_iff k).mpr hf).hasSum

/-- The derivative has its complete norm-summable source series at every real clock. -/
theorem liEvenCrossActualClockBorel_deriv_series (t : ℝ) :
    Summable (fun r : ℕ => ‖(2*(r+1) : ℝ)*
      liEvenCrossActualClockBorelCoefficient (r+1)*t^(2*r+1)‖) ∧
    HasSum (fun r : ℕ => (2*(r+1) : ℝ)*
      liEvenCrossActualClockBorelCoefficient (r+1)*t^(2*r+1))
      (deriv liEvenCrossActualClockBorelKernel t) := by
  have hs := bc_shifted_hasSum (bc_summable 1 t) 1
    (fun j hj => by
      have hj0 : j = 0 := by omega
      simp [hj0, bcTerm])
  change HasSum (fun r => bcTerm 1 (r+1) t) (bcSeries 1 t) at hs
  have he (r : ℕ) : bcTerm 1 (r+1) t =
      (2*(r+1) : ℝ)*liEvenCrossActualClockBorelCoefficient (r+1)*t^(2*r+1) := by
    have hn : 2*(r+1)-1 = 2*r+1 := by omega
    simp only [bcTerm, Nat.descFactorial_one, hn, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_add, Nat.cast_one]
    ring
  have hk := (hs.congr_fun (fun r => (he r).symm))
  rw [← bc_first_deriv] at hk
  exact ⟨hk.summable.norm, hk⟩

private def bcDelta (j : ℕ) : ℝ := thetaCuspNormalizedEvenMoment (j+1) /
  ((2*j+1 : ℝ)*thetaCuspNormalizedEvenMoment j)

private def bcB (r : ℕ) : ℝ :=
  (2*(r+1) : ℝ)*liEvenCrossActualClockBorelCoefficient (r+1)

private def bcA (r : ℕ) : ℝ := bcDelta (r+1)*bcB r

private theorem bc_a_coefficient (r : ℕ) :
    bcA r = thetaCuspNormalizedEvenMoment (r+2) /
      ((2*r+3 : ℝ)*((2*r+2).factorial : ℝ)*((2*r+1).factorial : ℝ)) := by
  have hn : 2*(r+1) = (2*r+1)+1 := by omega
  have hν := (thetaCuspNormalizedEvenMoment_pos (r+1)).ne'
  have hf : ((2*(r+1)).factorial : ℝ) =
      (2*(r+1) : ℝ)*((2*r+1).factorial : ℝ) := by
    rw [hn, Nat.factorial_succ]
    push_cast
    ring
  have hf2 : ((2*r+2).factorial : ℝ) =
      (2*r+2 : ℝ)*((2*r+1).factorial : ℝ) := by
    rw [show 2*r+2 = (2*r+1)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  unfold bcA bcDelta bcB liEvenCrossActualClockBorelCoefficient
  simp only [Nat.add_assoc]
  rw [hf, hf2]
  push_cast
  field_simp [hν]
  ring

private theorem bc_correction_shift (r : ℕ) (t : ℝ) :
    3*bcTerm 3 (r+2) t+t*bcTerm 4 (r+2) t = bcA r*t^(2*r+1) := by
  have h1 : 2*(r+2)-1 = 2*r+3 := by omega
  have h2 : 2*(r+2)-2 = 2*r+2 := by omega
  have h3 : 2*(r+2)-3 = 2*r+1 := by omega
  have h4 : 2*(r+2)-4 = 2*r := by omega
  have hf : ((2*(r+2)).factorial : ℝ) =
      (2*r+4 : ℝ)*(2*r+3 : ℝ)*(2*r+2 : ℝ)*((2*r+1).factorial : ℝ) := by
    rw [show 2*(r+2) = ((2*r+1)+1)+1+1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hf2 : ((2*r+2).factorial : ℝ) =
      (2*r+2 : ℝ)*((2*r+1).factorial : ℝ) := by
    rw [show 2*r+2 = (2*r+1)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [bc_a_coefficient]
  simp only [bcTerm, Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    h1, h2, h3, h4, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  unfold liEvenCrossActualClockBorelCoefficient
  rw [hf, hf2]
  rw [pow_succ t (2*r)]
  field_simp
  ring

private theorem bc_correction_hasSum (t : ℝ) :
    HasSum (fun r : ℕ => bcA r*t^(2*r+1))
      (liEvenCrossActualClockBorelCorrection t) := by
  have hs := ((bc_summable 3 t).mul_left 3).add ((bc_summable 4 t).mul_left t)
  have hz (j : ℕ) (hj : j < 2) : 3*bcTerm 3 j t+t*bcTerm 4 j t = 0 := by
    interval_cases j <;> norm_num [bcTerm, Nat.descFactorial_succ]
  have hshift := bc_shifted_hasSum hs 2 hz
  have hsum : (∑' j, (3*bcTerm 3 j t+t*bcTerm 4 j t)) =
      3*bcSeries 3 t+t*bcSeries 4 t := by
    rw [((bc_summable 3 t).mul_left 3).tsum_add ((bc_summable 4 t).mul_left t),
      tsum_mul_left, tsum_mul_left]
    rfl
  rw [hsum, ← bc_literal] at hshift
  exact hshift.congr_fun (fun r => (bc_correction_shift r t).symm)

/-- The complete correction series retains both consecutive factorials. -/
theorem liEvenCrossActualClockBorelCorrection_series (t : ℝ) :
    Summable (fun r : ℕ => ‖thetaCuspNormalizedEvenMoment (r+2) /
      ((2*r+3 : ℝ)*((2*r+2).factorial : ℝ)*((2*r+1).factorial : ℝ))*t^(2*r+1)‖) ∧
    HasSum (fun r : ℕ => thetaCuspNormalizedEvenMoment (r+2) /
      ((2*r+3 : ℝ)*((2*r+2).factorial : ℝ)*((2*r+1).factorial : ℝ))*t^(2*r+1))
      (liEvenCrossActualClockBorelCorrection t) := by
  have hs := (bc_correction_hasSum t).congr_fun (fun r =>
    congrArg (fun a : ℝ => a*t^(2*r+1)) (bc_a_coefficient r).symm)
  exact ⟨hs.summable.norm, hs⟩

private theorem bc_series_continuous (m : ℕ) : Continuous (bcSeries m) :=
  continuous_iff_continuousAt.mpr (fun t => (bc_series_hasDerivAt m t).continuousAt)

/-- Compact admission of the ordinary derivative ladder gives continuous correction. -/
theorem continuous_liEvenCrossActualClockBorelCorrection :
    Continuous liEvenCrossActualClockBorelCorrection := by
  have he : liEvenCrossActualClockBorelCorrection =
      (fun t => 3*bcSeries 3 t+t*bcSeries 4 t) := funext bc_literal
  rw [he]
  exact (continuous_const.mul (bc_series_continuous 3)).add
    (continuous_id.mul (bc_series_continuous 4))

private theorem bc_delta_pos (j : ℕ) : 0 < bcDelta j := by
  unfold bcDelta
  exact div_pos (thetaCuspNormalizedEvenMoment_pos (j+1))
    (mul_pos (by positivity) (thetaCuspNormalizedEvenMoment_pos j))

private theorem bc_b_pos (r : ℕ) : 0 < bcB r := by
  unfold bcB
  exact mul_pos (by positivity) (liEvenCrossActualClockBorelCoefficient_pos (r+1))

private theorem bc_a_pos (r : ℕ) : 0 < bcA r :=
  mul_pos (bc_delta_pos (r+1)) (bc_b_pos r)

/-- Strict raw moment positivity gives a positive derivative at every positive clock. -/
theorem liEvenCrossActualClockBorel_deriv_pos {t : ℝ} (ht : 0 < t) :
    0 < deriv liEvenCrossActualClockBorelKernel t := by
  have hs := (liEvenCrossActualClockBorel_deriv_series t).2
  have hn (r : ℕ) : 0 ≤ (2*(r+1) : ℝ)*
      liEvenCrossActualClockBorelCoefficient (r+1)*t^(2*r+1) := by
    have hc := (liEvenCrossActualClockBorelCoefficient_pos (r+1)).le
    positivity
  have h0 : 0 < (fun r : ℕ => (2*(r+1) : ℝ)*
      liEvenCrossActualClockBorelCoefficient (r+1)*t^(2*r+1)) 0 := by
    have hc := liEvenCrossActualClockBorelCoefficient_pos 1
    positivity
  rw [← hs.tsum_eq]
  exact h0.trans_le (hs.summable.le_tsum 0 (fun r _ => hn r))

/-- Every shifted correction coefficient is strictly positive. -/
theorem liEvenCrossActualClockBorelCorrection_pos {t : ℝ} (ht : 0 < t) :
    0 < liEvenCrossActualClockBorelCorrection t := by
  have hs := bc_correction_hasSum t
  rw [← hs.tsum_eq]
  have hn (r : ℕ) : 0 ≤ bcA r*t^(2*r+1) :=
    mul_nonneg (bc_a_pos r).le (pow_nonneg ht.le _)
  exact (mul_pos (bc_a_pos 0) (pow_pos ht _)).trans_le
    (hs.summable.le_tsum 0 (fun r _ => hn r))

private theorem bc_term_origin {m j : ℕ} (hne : 2*j ≠ m) : bcTerm m j 0 = 0 := by
  by_cases hj : 2*j < m
  · simp [bcTerm, Nat.descFactorial_of_lt hj]
  · have hp : 0 < 2*j-m := by omega
    simp [bcTerm, zero_pow (Nat.ne_of_gt hp)]

private theorem bc_series_one_origin : bcSeries 1 0 = 0 := by
  unfold bcSeries
  calc
    (∑' j, bcTerm 1 j 0) = ∑' j : ℕ, (0:ℝ) :=
      tsum_congr (fun j => bc_term_origin (by omega))
    _ = 0 := by simp

private theorem bc_series_three_origin : bcSeries 3 0 = 0 := by
  unfold bcSeries
  calc
    (∑' j, bcTerm 3 j 0) = ∑' j : ℕ, (0:ℝ) :=
      tsum_congr (fun j => bc_term_origin (by omega))
    _ = 0 := by simp

private theorem bc_series_two_origin :
    bcSeries 2 0 = 2*liEvenCrossActualClockBorelCoefficient 1 := by
  have hh := (bc_summable 2 0).sum_add_tsum_nat_add 2
  have hz : (∑' r, bcTerm 2 (r+2) 0) = 0 := by
    calc
      (∑' r, bcTerm 2 (r+2) 0) = ∑' r : ℕ, (0:ℝ) :=
        tsum_congr (fun r => bc_term_origin (by omega))
      _ = 0 := by simp
  rw [hz, add_zero] at hh
  change _ = bcSeries 2 0 at hh
  rw [← hh]
  norm_num [Finset.sum_range_succ, bcTerm, Nat.descFactorial_succ]
  ring

private theorem bc_series_four_origin :
    bcSeries 4 0 = 24*liEvenCrossActualClockBorelCoefficient 2 := by
  have hh := (bc_summable 4 0).sum_add_tsum_nat_add 3
  have hz : (∑' r, bcTerm 4 (r+3) 0) = 0 := by
    calc
      (∑' r, bcTerm 4 (r+3) 0) = ∑' r : ℕ, (0:ℝ) :=
        tsum_congr (fun r => bc_term_origin (by omega))
      _ = 0 := by simp
  rw [hz, add_zero] at hh
  change _ = bcSeries 4 0 at hh
  rw [← hh]
  norm_num [Finset.sum_range_succ, bcTerm, Nat.descFactorial_succ]
  ring

private theorem bc_correction_origin_derivative :
    deriv liEvenCrossActualClockBorelCorrection 0 = 4*bcSeries 4 0 := by
  have h := ((bc_series_hasDerivAt 3 0).const_mul 3).add
    ((hasDerivAt_id 0).mul (bc_series_hasDerivAt 4 0))
  have hD : HasDerivAt liEvenCrossActualClockBorelCorrection (4*bcSeries 4 0) 0 := by
    have he : liEvenCrossActualClockBorelCorrection =
        (fun x => 3*bcSeries 3 x+x*bcSeries 4 x) := funext bc_literal
    rw [he]
    convert h using 1 <;>
      first | rfl | (simp only [id_eq, one_mul]; ring)
  exact hD.deriv

/-- Both odd profiles vanish at zero, with their exact genuine linear coefficients. -/
theorem liEvenCrossActualClockBorelCorrection_origin :
    deriv liEvenCrossActualClockBorelKernel 0 = 0 ∧
    liEvenCrossActualClockBorelCorrection 0 = 0 ∧
    iteratedDeriv 2 liEvenCrossActualClockBorelKernel 0 =
      thetaCuspNormalizedEvenMoment 1/2 ∧
    deriv liEvenCrossActualClockBorelCorrection 0 =
      thetaCuspNormalizedEvenMoment 2/6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bc_first_deriv, bc_series_one_origin]
  · rw [bc_literal, bc_series_three_origin]
    simp
  · rw [bc_iteratedDeriv, bc_series_two_origin]
    norm_num [liEvenCrossActualClockBorelCoefficient]
    ring
  · rw [bc_correction_origin_derivative, bc_series_four_origin]
    norm_num [liEvenCrossActualClockBorelCoefficient]
    ring

private theorem bc_delta_raw (j : ℕ) :
    bcDelta j = thetaCuspRawEvenMoment (j+1) /
      (((2*j+1 : ℕ) : ℝ)*thetaCuspRawEvenMoment j) := by
  have h0 := (thetaCuspRawEvenMoment_pos 0).ne'
  have hj := (thetaCuspRawEvenMoment_pos j).ne'
  unfold bcDelta thetaCuspNormalizedEvenMoment
  push_cast
  field_simp [h0, hj]

private theorem bc_delta_limit : Tendsto bcDelta atTop (𝓝 0) := by
  have he : bcDelta = (fun j : ℕ => thetaCuspRawEvenMoment (j+1) /
      (((2*j+1 : ℕ) : ℝ)*thetaCuspRawEvenMoment j)) := funext bc_delta_raw
  rw [he]
  exact tendsto_thetaCuspRawEvenMoment_oddScaledRatio_zero

private theorem bc_delta_bound {j : ℕ} (hj : 1 ≤ j) : bcDelta j ≤ (49/909 : ℝ) := by
  have hv := thetaCuspNormalizedEvenMoment_pos j
  have hs := thetaCuspNormalizedEvenMoment_succ_le_score j
  have hjR : 1 ≤ (j:ℝ) := by exact_mod_cast hj
  have hd : 0 < (2*j+1 : ℝ)*thetaCuspNormalizedEvenMoment j := by positivity
  rw [bcDelta, div_le_iff₀ hd]
  have hp := mul_nonneg (sub_nonneg.mpr hjR) hv.le
  nlinarith

private theorem bc_b_bound (r : ℕ) :
    bcB r ≤ 2*(32/303 : ℝ)*(32/303 : ℝ)^r/(r.factorial : ℝ) := by
  unfold bcB
  calc
    (2*(r+1) : ℝ)*liEvenCrossActualClockBorelCoefficient (r+1) ≤
        (2*(r+1) : ℝ)*((32/303 : ℝ)^(r+1)/((r+1).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (liEvenCrossActualClockBorelCoefficient_le (r+1))
        (by positivity)
    _ = _ := by
      rw [pow_succ, Nat.factorial_succ]
      push_cast
      field_simp

private theorem bc_b_reduced_summable (t : ℝ) :
    Summable (fun r : ℕ => bcB r*t^(2*r)) := by
  have hp (r : ℕ) : 0 ≤ t^(2*r) := by rw [pow_mul]; positivity
  refine Summable.of_nonneg_of_le (fun r => mul_nonneg (bc_b_pos r).le (hp r))
    (fun r => ?_) ((Real.summable_pow_div_factorial ((32/303 : ℝ)*t^2)).mul_left
      (2*(32/303 : ℝ)))
  calc
    bcB r*t^(2*r) ≤ (2*(32/303 : ℝ)*(32/303 : ℝ)^r/(r.factorial : ℝ))*t^(2*r) :=
      mul_le_mul_of_nonneg_right (bc_b_bound r) (hp r)
    _ = 2*(32/303 : ℝ)*(((32/303 : ℝ)*t^2)^r/(r.factorial : ℝ)) := by
      rw [mul_pow, ← pow_mul]
      ring

private theorem bc_a_reduced_summable (t : ℝ) :
    Summable (fun r : ℕ => bcA r*t^(2*r)) := by
  have hp (r : ℕ) : 0 ≤ t^(2*r) := by rw [pow_mul]; positivity
  refine Summable.of_nonneg_of_le (fun r => mul_nonneg (bc_a_pos r).le (hp r))
    (fun r => ?_) ((bc_b_reduced_summable t).mul_left (49/909 : ℝ))
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (bc_delta_bound (show 1 ≤ r+1 by omega))
      (bc_b_pos r).le) (hp r)).trans_eq (by ring)

private theorem bc_first_odd (t : ℝ) :
    deriv liEvenCrossActualClockBorelKernel t = t*liClockPositiveEvenSeries bcB t := by
  rw [← (liEvenCrossActualClockBorel_deriv_series t).2.tsum_eq,
    liClockPositiveEvenSeries, ← tsum_mul_left]
  apply tsum_congr
  intro r
  unfold bcB
  rw [pow_succ]
  ring

private theorem bc_correction_odd (t : ℝ) :
    liEvenCrossActualClockBorelCorrection t = t*liClockPositiveEvenSeries bcA t := by
  rw [← (bc_correction_hasSum t).tsum_eq, liClockPositiveEvenSeries, ← tsum_mul_left]
  apply tsum_congr
  intro r
  rw [pow_succ]
  ring

/-- The literal correction is negligible relative to the positive Borel derivative. -/
theorem tendsto_liEvenCrossActualClockBorelCorrection_div_deriv :
    Tendsto (fun t : ℝ => liEvenCrossActualClockBorelCorrection t /
      deriv liEvenCrossActualClockBorelKernel t) atTop (𝓝 0) := by
  have hq : Tendsto (fun r : ℕ => bcA r/bcB r) atTop (𝓝 0) := by
    have h := bc_delta_limit.comp (tendsto_add_atTop_nat 1)
    convert h using 1
    funext r
    exact mul_div_cancel_right₀ _ (bc_b_pos r).ne'
  have h := liClockPositiveEvenSeries_ratio_tendsto (fun r => (bc_a_pos r).le)
    bc_b_pos bc_a_reduced_summable bc_b_reduced_summable hq
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [bc_first_odd, bc_correction_odd]
  exact (mul_div_mul_left _ _ ht.ne').symm

end
end RHTower

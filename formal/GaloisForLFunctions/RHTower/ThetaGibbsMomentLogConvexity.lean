import GaloisForLFunctions.RHTower.PrimeArchThetaGibbsEquipartition

/-!
# Log-convexity and ratio decay of the theta-Gibbs moments

The Gibbs atom is nonnegative, so Cauchy--Schwarz makes its moment sequence log-convex at every
index.  Combined with the one-sided equipartition decay this gives a two-sided consequence with no
further input.
-/

open MeasureTheory Set Polynomial

namespace RHTower

noncomputable section

theorem continuous_thetaCuspLiouvilleGibbsAtom (n : ℕ) :
    Continuous (thetaCuspLiouvilleGibbsAtom n) :=
  continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_thetaCuspLiouvilleGibbsAtom n x).continuousAt

/-- **Log-convexity of the theta-Gibbs moments at every index.** -/
theorem thetaCuspLiouvilleGibbsMoment_succ_sq_le (k : ℕ) {n : ℕ} (hn : 0 < n) :
    thetaCuspLiouvilleGibbsMoment (k + 1) n ^ 2 ≤
      thetaCuspLiouvilleGibbsMoment k n * thetaCuspLiouvilleGibbsMoment (k + 2) n := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let A : ℝ → ℝ := thetaCuspLiouvilleGibbsAtom n
  let f : ℝ → ℝ := fun x => Real.sqrt (x ^ k * A x)
  let g : ℝ → ℝ := fun x => Real.sqrt (x ^ (k + 2) * A x)
  have hA : ∀ x, 0 ≤ A x := thetaCuspLiouvilleGibbsAtom_nonneg n
  have hcontA : Continuous A := continuous_thetaCuspLiouvilleGibbsAtom n
  have hint : ∀ j : ℕ, Integrable (fun x : ℝ => x ^ j * A x) μ := fun j =>
    integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos j (X ^ 2) hn
  have hf_meas : AEStronglyMeasurable f μ :=
    ((Real.continuous_sqrt.comp
      ((continuous_id.pow k).mul hcontA)).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hg_meas : AEStronglyMeasurable g μ :=
    ((Real.continuous_sqrt.comp
      ((continuous_id.pow (k + 2)).mul hcontA)).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hf_sq : Integrable (fun x => f x ^ 2) μ := by
    apply (hint k).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [f]
    exact (Real.sq_sqrt (mul_nonneg (pow_nonneg hx.le k) (hA x))).symm
  have hg_sq : Integrable (fun x => g x ^ 2) μ := by
    apply (hint (k + 2)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [g]
    exact (Real.sq_sqrt (mul_nonneg (pow_nonneg hx.le (k + 2)) (hA x))).symm
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf_meas).2 hf_sq
  have hg : MemLp g 2 μ := (memLp_two_iff_integrable_sq hg_meas).2 hg_sq
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ)) (Real.HolderConjugate.two_two) hf' hg'
  have hfg : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) = ∫ x in Ioi 0, x ^ (k + 1) * A x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) ≤ x := hx.le
    dsimp [f, g]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
      ← Real.sqrt_mul (mul_nonneg (pow_nonneg hx0 k) (hA x)),
      show x ^ k * A x * (x ^ (k + 2) * A x) = (x ^ (k + 1) * A x) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (pow_nonneg hx0 (k + 1)) (hA x))
  have hf2 : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) = ∫ x in Ioi 0, x ^ k * A x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [f]
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs]
    exact Real.sq_sqrt (mul_nonneg (pow_nonneg hx.le k) (hA x))
  have hg2 : (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) = ∫ x in Ioi 0, x ^ (k + 2) * A x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [g]
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs]
    exact Real.sq_sqrt (mul_nonneg (pow_nonneg hx.le (k + 2)) (hA x))
  rw [hfg, hf2, hg2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  have h1 := thetaCuspLiouvilleGibbsMoment_nonneg k n
  have h2 := thetaCuspLiouvilleGibbsMoment_nonneg (k + 2) n
  have h3 := thetaCuspLiouvilleGibbsMoment_nonneg (k + 1) n
  simp only [thetaCuspLiouvilleGibbsMoment] at h1 h2 h3 ⊢
  have hsq : (Real.sqrt (∫ x in Ioi 0, x ^ k * A x) *
      Real.sqrt (∫ x in Ioi 0, x ^ (k + 2) * A x)) ^ 2 =
      (∫ x in Ioi 0, x ^ k * A x) * (∫ x in Ioi 0, x ^ (k + 2) * A x) := by
    rw [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2]
  nlinarith [hcs, h3, hsq, Real.sqrt_nonneg (∫ x in Ioi 0, x ^ k * A x),
    Real.sqrt_nonneg (∫ x in Ioi 0, x ^ (k + 2) * A x)]

/-- **Ratio decay.**  Log-convexity plus the equipartition bound give an explicit squared ratio
decay of the Gibbs moments at every index, with no further input. -/
theorem twelve_mul_thetaCuspLiouvilleGibbsMoment_succ_sq_le (k : ℕ) {n : ℕ} (hn : 0 < n) :
    12 * thetaCuspLiouvilleGibbsMoment (k + 1) n ^ 2 ≤
      ((k : ℝ) + 1) * thetaCuspLiouvilleGibbsMoment k n ^ 2 := by
  have hlog := thetaCuspLiouvilleGibbsMoment_succ_sq_le k hn
  have hequi := twelve_mul_thetaCuspLiouvilleGibbsMoment_succ_le (k + 1) (Nat.succ_pos k) hn
  simp only [Nat.add_sub_cancel] at hequi
  have hk := thetaCuspLiouvilleGibbsMoment_nonneg k n
  push_cast at hequi
  nlinarith [hlog, hequi, hk]

/-- **Factorial moment ceiling.**  Iterating the ratio decay bounds every Gibbs moment by the
zeroth one with an explicit factorial-over-twelve-power constant, at every index and with no
numerical input. -/
theorem twelve_pow_mul_thetaCuspLiouvilleGibbsMoment_sq_le
    (k : ℕ) {n : ℕ} (hn : 0 < n) :
    (12 : ℝ) ^ k * thetaCuspLiouvilleGibbsMoment k n ^ 2 ≤
      (k.factorial : ℝ) * thetaCuspLiouvilleGibbsMoment 0 n ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := twelve_mul_thetaCuspLiouvilleGibbsMoment_succ_sq_le k hn
      have h12 : (0 : ℝ) < 12 ^ k := by positivity
      have hchain :
          (12 : ℝ) ^ (k + 1) * thetaCuspLiouvilleGibbsMoment (k + 1) n ^ 2 ≤
            ((k : ℝ) + 1) * ((12 : ℝ) ^ k * thetaCuspLiouvilleGibbsMoment k n ^ 2) := by
        have := mul_le_mul_of_nonneg_left hstep h12.le
        calc
          (12 : ℝ) ^ (k + 1) * thetaCuspLiouvilleGibbsMoment (k + 1) n ^ 2 =
              (12 : ℝ) ^ k * (12 * thetaCuspLiouvilleGibbsMoment (k + 1) n ^ 2) := by ring
          _ ≤ (12 : ℝ) ^ k * (((k : ℝ) + 1) * thetaCuspLiouvilleGibbsMoment k n ^ 2) := this
          _ = ((k : ℝ) + 1) * ((12 : ℝ) ^ k * thetaCuspLiouvilleGibbsMoment k n ^ 2) := by ring
      have hpos : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
      have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      calc
        (12 : ℝ) ^ (k + 1) * thetaCuspLiouvilleGibbsMoment (k + 1) n ^ 2 ≤
            ((k : ℝ) + 1) * ((12 : ℝ) ^ k * thetaCuspLiouvilleGibbsMoment k n ^ 2) := hchain
        _ ≤ ((k : ℝ) + 1) * ((k.factorial : ℝ) * thetaCuspLiouvilleGibbsMoment 0 n ^ 2) :=
            mul_le_mul_of_nonneg_left ih hpos
        _ = ((k + 1).factorial : ℝ) * thetaCuspLiouvilleGibbsMoment 0 n ^ 2 := by
            rw [hfac]; ring

/-- The zeroth first-atom Gibbs moment is bounded by the boundary charge: this is exactly
nonnegativity of the zeroth Ward moment. -/
theorem thetaCuspLiouvilleGibbsMoment_zero_le_two_exp_neg_pi :
    thetaCuspLiouvilleGibbsMoment 0 1 ≤ 2 * Real.exp (-Real.pi) := by
  have h := thetaCuspFirstAtomWardMoment_nonneg 0
  simp only [thetaCuspFirstAtomWardMoment] at h
  linarith

/-- **Absolute factorial ceiling for the first atom.**  Every first-atom Gibbs moment is bounded
at every index by an explicit constant, with no certificate and no numerical input. -/
theorem twelve_pow_mul_thetaCuspFirstAtomGibbsMoment_sq_le (k : ℕ) :
    (12 : ℝ) ^ k * thetaCuspLiouvilleGibbsMoment k 1 ^ 2 ≤
      (k.factorial : ℝ) * (2 * Real.exp (-Real.pi)) ^ 2 := by
  have hceil := twelve_pow_mul_thetaCuspLiouvilleGibbsMoment_sq_le k (n := 1) (by norm_num)
  have hzero := thetaCuspLiouvilleGibbsMoment_zero_le_two_exp_neg_pi
  have hnn := thetaCuspLiouvilleGibbsMoment_nonneg 0 1
  have hfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hsq : thetaCuspLiouvilleGibbsMoment 0 1 ^ 2 ≤ (2 * Real.exp (-Real.pi)) ^ 2 := by
    nlinarith [hzero, hnn]
  calc
    (12 : ℝ) ^ k * thetaCuspLiouvilleGibbsMoment k 1 ^ 2 ≤
        (k.factorial : ℝ) * thetaCuspLiouvilleGibbsMoment 0 1 ^ 2 := hceil
    _ ≤ (k.factorial : ℝ) * (2 * Real.exp (-Real.pi)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hfac

/-- **Sharp ratio inequality.**  Keeping the middle term of the equipartition bound and combining
it with log-convexity gives a quadratic inequality for the consecutive moment ratio, strictly
sharper than the rounded `12`-version. -/
theorem sharp_thetaCuspLiouvilleGibbsMoment_ratio_quadratic (k : ℕ) {n : ℕ} (hn : 0 < n) :
    4 * Real.pi * (n : ℝ) ^ (2 : ℕ) * thetaCuspLiouvilleGibbsMoment (k + 1) n ^ 2 +
        (2 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 5 / 2) *
          (thetaCuspLiouvilleGibbsMoment (k + 1) n * thetaCuspLiouvilleGibbsMoment k n) ≤
      ((k : ℝ) + 1) * thetaCuspLiouvilleGibbsMoment k n ^ 2 := by
  have hequi :=
    thetaCuspLiouvilleGibbsMoment_succ_equipartition_upper (k + 1) (Nat.succ_pos k) hn
  simp only [Nat.add_sub_cancel] at hequi
  rw [show k + 1 + 1 = k + 2 from rfl] at hequi
  push_cast at hequi
  have hlog := thetaCuspLiouvilleGibbsMoment_succ_sq_le k hn
  have hk := thetaCuspLiouvilleGibbsMoment_nonneg k n
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnsq : (1 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hequi hk
  have hcoef : (0 : ℝ) < 4 * Real.pi * (n : ℝ) ^ (2 : ℕ) := by positivity
  nlinarith [hmul, hlog, hk, hpi, hnsq, hcoef,
    mul_le_mul_of_nonneg_left hlog hcoef.le]

/-- Per-step form of the sharp ratio inequality for the first atom: the exact constant `4π`
replaces the rounded `12`. -/
theorem fourPi_mul_thetaCuspFirstAtomGibbsMoment_succ_sq_le (k : ℕ) :
    4 * Real.pi * thetaCuspLiouvilleGibbsMoment (k + 1) 1 ^ 2 ≤
      ((k : ℝ) + 1) * thetaCuspLiouvilleGibbsMoment k 1 ^ 2 := by
  have hq := sharp_thetaCuspLiouvilleGibbsMoment_ratio_quadratic k (n := 1) (by norm_num)
  have hmid : (0 : ℝ) ≤ (2 * Real.pi - 5 / 2) *
      (thetaCuspLiouvilleGibbsMoment (k + 1) 1 * thetaCuspLiouvilleGibbsMoment k 1) := by
    apply mul_nonneg
    · nlinarith [Real.pi_gt_three]
    · exact mul_nonneg (thetaCuspLiouvilleGibbsMoment_nonneg (k + 1) 1)
        (thetaCuspLiouvilleGibbsMoment_nonneg k 1)
  norm_num at hq
  linarith [hq, hmid]

/-- **Relative factorial ceiling.**  Telescoping the sharp per-step bound from any base index `j`
gives a ceiling with the exact constant `4π`, so a good bound at a small index propagates upward
without paying the rounded constant at every step. -/
theorem fourPi_pow_mul_thetaCuspFirstAtomGibbsMoment_sq_le (j k : ℕ) :
    (4 * Real.pi) ^ k * (j.factorial : ℝ) * thetaCuspLiouvilleGibbsMoment (j + k) 1 ^ 2 ≤
      ((j + k).factorial : ℝ) * thetaCuspLiouvilleGibbsMoment j 1 ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := fourPi_mul_thetaCuspFirstAtomGibbsMoment_succ_sq_le (j + k)
      have hbase : (0 : ℝ) < (4 * Real.pi) ^ k * (j.factorial : ℝ) := by
        have : (0 : ℝ) < 4 * Real.pi := by positivity
        positivity
      have hidx : (0 : ℝ) ≤ ((j : ℝ) + k + 1) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hstep hbase.le
      have hfac : (((j + k + 1).factorial : ℝ)) =
          ((j : ℝ) + k + 1) * ((j + k).factorial : ℝ) := by
        rw [show j + k + 1 = (j + k) + 1 from rfl, Nat.factorial_succ]
        push_cast
        ring
      calc
        (4 * Real.pi) ^ (k + 1) * (j.factorial : ℝ) *
              thetaCuspLiouvilleGibbsMoment (j + (k + 1)) 1 ^ 2 =
            (4 * Real.pi) ^ k * (j.factorial : ℝ) *
              (4 * Real.pi * thetaCuspLiouvilleGibbsMoment (j + k + 1) 1 ^ 2) := by
          rw [show j + (k + 1) = j + k + 1 from rfl]; ring
        _ ≤ (4 * Real.pi) ^ k * (j.factorial : ℝ) *
              (((j : ℝ) + k + 1) * thetaCuspLiouvilleGibbsMoment (j + k) 1 ^ 2) := by
          push_cast at hmul ⊢
          linarith [hmul]
        _ = ((j : ℝ) + k + 1) *
              ((4 * Real.pi) ^ k * (j.factorial : ℝ) *
                thetaCuspLiouvilleGibbsMoment (j + k) 1 ^ 2) := by ring
        _ ≤ ((j : ℝ) + k + 1) * (((j + k).factorial : ℝ) *
              thetaCuspLiouvilleGibbsMoment j 1 ^ 2) := mul_le_mul_of_nonneg_left ih hidx
        _ = ((j + (k + 1)).factorial : ℝ) * thetaCuspLiouvilleGibbsMoment j 1 ^ 2 := by
          rw [show j + (k + 1) = j + k + 1 from rfl, hfac]; ring

end

end RHTower

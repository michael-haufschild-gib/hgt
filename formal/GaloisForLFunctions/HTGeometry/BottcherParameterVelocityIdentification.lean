/-
# Analytic identification of the first two Böttcher parameter velocities

The formal Mahler jets `velocityJet` and `secondJet` already carry the complete
algebraic-independence proof.  This module supplies the missing analytic bridge.
In the reciprocal coordinate `t = 1 / z`, the normalized Böttcher logarithm is
written without a singularity at `t = 0`; its normally convergent parameter
series is differentiated at the monomial fibre `c = 0`.
-/
import GaloisForLFunctions.Bottcher.BottcherCoord
import GaloisForLFunctions.U0.VelocityPairIndependence
import GaloisForLFunctions.HTGeometry.TaylorFormalBridge
import GaloisForLFunctions.HTGeometry.BottcherAllOrderJetLaw
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Complex PowerSeries Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Reciprocal quadratic orbit -/

/-- The quadratic family in the reciprocal coordinate: if `t = 1 / z`, then
`1 / (z^2 + c) = reciprocalQuadratic c t`. -/
def reciprocalQuadratic (c t : ℂ) : ℂ := t ^ 2 / (1 + c * t ^ 2)

/-- The reciprocal orbit, kept as an explicit recursion so that parameter
derivatives at `c = 0` are transparent. -/
def reciprocalOrbit (c t : ℂ) : ℕ → ℂ
  | 0 => t
  | k + 1 => reciprocalQuadratic c (reciprocalOrbit c t k)

@[simp] theorem reciprocalOrbit_zero (c t : ℂ) : reciprocalOrbit c t 0 = t := rfl

@[simp] theorem reciprocalOrbit_succ (c t : ℂ) (k : ℕ) :
    reciprocalOrbit c t (k + 1) =
      (reciprocalOrbit c t k) ^ 2 /
        (1 + c * (reciprocalOrbit c t k) ^ 2) := rfl

/-- At the monomial fibre the reciprocal orbit is literal dyadic powering. -/
theorem reciprocalOrbit_zero_parameter (t : ℂ) (k : ℕ) :
    reciprocalOrbit 0 t k = t ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [reciprocalOrbit_succ, ih]
    simp only [zero_mul, add_zero, div_one, pow_two]
    rw [← pow_add]
    congr 1
    omega

/-- The first parameter derivative of the reciprocal orbit, defined by the
linearized reciprocal recurrence. -/
def reciprocalOrbitFirstJet (t : ℂ) : ℕ → ℂ
  | 0 => 0
  | k + 1 =>
      2 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k - t ^ (2 ^ (k + 2))

@[simp] theorem reciprocalOrbitFirstJet_zero (t : ℂ) :
    reciprocalOrbitFirstJet t 0 = 0 := rfl

@[simp] theorem reciprocalOrbitFirstJet_succ (t : ℂ) (k : ℕ) :
    reciprocalOrbitFirstJet t (k + 1) =
      2 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k - t ^ (2 ^ (k + 2)) := rfl

/-- The reciprocal orbit is analytic in the parameter at the monomial fibre. -/
theorem analyticAt_reciprocalOrbit_parameter_zero (t : ℂ) (k : ℕ) :
    AnalyticAt ℂ (fun c => reciprocalOrbit c t k) 0 := by
  induction k with
  | zero => simpa [reciprocalOrbit] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => t) 0)
  | succ k ih =>
    rw [show (fun c => reciprocalOrbit c t (k + 1)) =
      fun c => (reciprocalOrbit c t k) ^ 2 /
        (1 + c * (reciprocalOrbit c t k) ^ 2) from rfl]
    apply (ih.pow 2).div (analyticAt_const.add (analyticAt_id.mul (ih.pow 2)))
    simp [reciprocalOrbit_zero_parameter]

/-- Exact first parameter derivative of the reciprocal orbit at `c = 0`. -/
theorem deriv_reciprocalOrbit_parameter_zero (t : ℂ) (k : ℕ) :
    deriv (fun c => reciprocalOrbit c t k) 0 = reciprocalOrbitFirstJet t k := by
  induction k with
  | zero => simp [reciprocalOrbit, reciprocalOrbitFirstJet]
  | succ k ih =>
    let u : ℂ → ℂ := fun c => reciprocalOrbit c t k
    have huan : AnalyticAt ℂ u 0 := analyticAt_reciprocalOrbit_parameter_zero t k
    have hu : HasDerivAt u (reciprocalOrbitFirstJet t k) 0 := by
      simpa [u, ih] using huan.differentiableAt.hasDerivAt
    have hnum : HasDerivAt (fun c => (u c) ^ 2)
        (2 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k) 0 := by
      convert hu.pow 2 using 1 <;> simp [u, reciprocalOrbit_zero_parameter] <;> ring
    have hden : HasDerivAt (fun c => 1 + c * (u c) ^ 2)
        (t ^ (2 ^ (k + 1))) 0 := by
      have hprod := (hasDerivAt_id' (0 : ℂ)).mul (hu.pow 2)
      convert (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).add hprod using 1 <;>
        simp [u, reciprocalOrbit_zero_parameter] <;>
        try { rw [← pow_mul]; congr 1 <;> omega }
    have hquot := hnum.div hden (by simp [u, reciprocalOrbit_zero_parameter] :
      1 + (0 : ℂ) * (u 0) ^ 2 ≠ 0)
    rw [show (fun c => reciprocalOrbit c t (k + 1)) =
      fun c => (u c) ^ 2 / (1 + c * (u c) ^ 2) from rfl]
    have hdq := hquot.deriv
    change deriv ((fun c => u c ^ 2) / (fun c => 1 + c * u c ^ 2)) 0 = _
    rw [hdq]
    simp only [u, reciprocalOrbit_zero_parameter, reciprocalOrbitFirstJet_succ]
    ring

/-! ## Reciprocal normalized Böttcher logarithm -/

/-- The `k`-th reciprocal-coordinate term of the normalized Böttcher logarithm. -/
def reciprocalBottcherLogTerm (c t : ℂ) (k : ℕ) : ℂ :=
  (2 ^ (k + 1) : ℂ)⁻¹ *
    Complex.log (1 + c * (reciprocalOrbit c t k) ^ 2)

/-- Every reciprocal logarithm term is analytic in the parameter at `c = 0`. -/
theorem analyticAt_reciprocalBottcherLogTerm_parameter_zero (t : ℂ) (k : ℕ) :
    AnalyticAt ℂ (fun c => reciprocalBottcherLogTerm c t k) 0 := by
  have hu := analyticAt_reciprocalOrbit_parameter_zero t k
  have harg : AnalyticAt ℂ
      (fun c => 1 + c * (reciprocalOrbit c t k) ^ 2) 0 :=
    analyticAt_const.add (analyticAt_id.mul (hu.pow 2))
  unfold reciprocalBottcherLogTerm
  exact analyticAt_const.mul (harg.clog (by simp [Complex.mem_slitPlane_iff]))

/-- First parameter derivative of one reciprocal logarithm term. -/
theorem deriv_reciprocalBottcherLogTerm_parameter_zero (t : ℂ) (k : ℕ) :
    deriv (fun c => reciprocalBottcherLogTerm c t k) 0 =
      (2 ^ (k + 1) : ℂ)⁻¹ * t ^ (2 ^ (k + 1)) := by
  let u : ℂ → ℂ := fun c => reciprocalOrbit c t k
  have huan : AnalyticAt ℂ u 0 := analyticAt_reciprocalOrbit_parameter_zero t k
  have hu : HasDerivAt u (reciprocalOrbitFirstJet t k) 0 := by
    simpa [u, deriv_reciprocalOrbit_parameter_zero] using huan.differentiableAt.hasDerivAt
  have hw : HasDerivAt (fun c => c * (u c) ^ 2) (t ^ (2 ^ (k + 1))) 0 := by
    convert (hasDerivAt_id' (0 : ℂ)).mul (hu.pow 2) using 1 <;>
      simp [u, reciprocalOrbit_zero_parameter] <;>
      try { rw [← pow_mul]; congr 1 <;> omega }
  have hlog : HasDerivAt (fun c => Complex.log (1 + c * (u c) ^ 2))
      (t ^ (2 ^ (k + 1))) 0 := by
    convert (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).add hw |>.clog using 1 <;> simp
  unfold reciprocalBottcherLogTerm
  simpa [u] using (hlog.const_mul (2 ^ (k + 1) : ℂ)⁻¹).deriv

/-- Second parameter derivative of one reciprocal logarithm term.  The
quadratic correction contains exactly the first orbit jet; no second orbit
jet survives because the orbit occurs multiplied by the parameter. -/
theorem iteratedDeriv_two_reciprocalBottcherLogTerm_parameter_zero
    (t : ℂ) (k : ℕ) :
    iteratedDeriv 2 (fun c => reciprocalBottcherLogTerm c t k) 0 =
      (2 ^ (k + 1) : ℂ)⁻¹ *
        (4 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k - t ^ (2 ^ (k + 2))) := by
  let u : ℂ → ℂ := fun c => reciprocalOrbit c t k
  let w : ℂ → ℂ := fun c => c * (u c) ^ 2
  let wd : ℂ → ℂ := fun c =>
    (u c) ^ 2 + c * (2 * u c * deriv u c)
  have huan : AnalyticAt ℂ u 0 := analyticAt_reciprocalOrbit_parameter_zero t k
  have hu : HasDerivAt u (reciprocalOrbitFirstJet t k) 0 := by
    simpa [u, deriv_reciprocalOrbit_parameter_zero] using huan.differentiableAt.hasDerivAt
  have hw : HasDerivAt w (t ^ (2 ^ (k + 1))) 0 := by
    convert (hasDerivAt_id' (0 : ℂ)).mul (hu.pow 2) using 1 <;>
      simp [w, u, reciprocalOrbit_zero_parameter] <;>
      try { rw [← pow_mul]; congr 1 <;> omega }
  have hdu : HasDerivAt (deriv u) (deriv (deriv u) 0) 0 :=
    huan.deriv.differentiableAt.hasDerivAt
  have hwd : HasDerivAt wd
      (4 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k) 0 := by
    have hv := (hu.const_mul 2).mul hdu
    convert (hu.pow 2).add ((hasDerivAt_id' (0 : ℂ)).mul hv) using 1 <;>
      simp [wd, u, reciprocalOrbit_zero_parameter,
        deriv_reciprocalOrbit_parameter_zero] <;> ring
  have hargan : AnalyticAt ℂ (fun c => 1 + w c) 0 := by
    exact analyticAt_const.add (analyticAt_id.mul (huan.pow 2))
  have hslit : ∀ᶠ c in nhds (0 : ℂ), 1 + w c ∈ Complex.slitPlane := by
    apply hargan.continuousAt
    exact Complex.isOpen_slitPlane.mem_nhds (by
      simp [w, Complex.mem_slitPlane_iff])
  have hderiv : deriv (fun c => reciprocalBottcherLogTerm c t k) =ᶠ[nhds (0 : ℂ)]
      fun c => (2 ^ (k + 1) : ℂ)⁻¹ * (wd c / (1 + w c)) := by
    filter_upwards [huan.eventually_analyticAt, hslit] with c hc hmem
    have hwc : HasDerivAt w (wd c) c := by
      convert (hasDerivAt_id' c).mul (hc.differentiableAt.hasDerivAt.pow 2) using 1 <;>
        simp [w, wd] <;> ring
    have hlog := ((hasDerivAt_const (x := c) (c := (1 : ℂ))).add hwc).clog hmem
    unfold reciprocalBottcherLogTerm
    simpa [w] using (hlog.const_mul (2 ^ (k + 1) : ℂ)⁻¹).deriv
  have hquot := hwd.div
    ((hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).add hw) (by simp [w])
  have hfinal := hquot.const_mul (2 ^ (k + 1) : ℂ)⁻¹
  have hfinal' : HasDerivAt
      (fun c => (2 ^ (k + 1) : ℂ)⁻¹ * (wd c / (1 + w c)))
      ((2 ^ (k + 1) : ℂ)⁻¹ *
        ((4 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k * (1 + w 0) -
          wd 0 * t ^ (2 ^ (k + 1))) / (1 + w 0) ^ 2)) 0 := by
    simpa only [Pi.div_apply, Pi.add_apply, Pi.one_apply, zero_add] using hfinal
  have hu0sq : (u 0) ^ 2 = t ^ (2 ^ (k + 1)) := by
    simp only [u, reciprocalOrbit_zero_parameter]
    rw [← pow_mul]
    congr 1
  have hpow : (t ^ (2 ^ (k + 1))) ^ 2 = t ^ (2 ^ (k + 2)) := by
    rw [← pow_mul]
    congr 1
  rw [show iteratedDeriv 2 (fun c => reciprocalBottcherLogTerm c t k) 0 =
    deriv (deriv (fun c => reciprocalBottcherLogTerm c t k)) 0 by
      simp only [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]]
  rw [hderiv.deriv_eq]
  rw [hfinal'.deriv]
  simp only [w, wd, zero_mul, add_zero, mul_one, div_one, one_pow]
  rw [hu0sq, ← pow_two, hpow]

/-! ## Normal convergence in the parameter -/

/-- The fixed parameter disk used for the analytic germ at the monomial fibre. -/
def bottcherParameterDisk : Set ℂ := Metric.ball 0 1

theorem isOpen_bottcherParameterDisk : IsOpen bottcherParameterDisk := Metric.isOpen_ball

theorem mem_bottcherParameterDisk_iff {c : ℂ} :
    c ∈ bottcherParameterDisk ↔ ‖c‖ < 1 := by
  simp [bottcherParameterDisk]

theorem norm_parameter_mul_reciprocalOrbit_sq_le_quarter {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ ≤ 1 / 2) (k : ℕ)
    (horbit : ‖reciprocalOrbit c t k‖ ≤ 1 / 2) :
    ‖c * (reciprocalOrbit c t k) ^ 2‖ ≤ 1 / 4 := by
  rw [norm_mul, norm_pow]
  calc
    ‖c‖ * ‖reciprocalOrbit c t k‖ ^ 2
        ≤ 1 * ‖reciprocalOrbit c t k‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hc) (sq_nonneg _)
    _ ≤ 1 * (1 / 2 : ℝ) ^ 2 := by
      gcongr
    _ = 1 / 4 := by norm_num

/-- The reciprocal orbit stays in the closed half-disk throughout the fixed
parameter disk. -/
theorem norm_reciprocalOrbit_le_half {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ ≤ 1 / 2) (k : ℕ) :
    ‖reciprocalOrbit c t k‖ ≤ 1 / 2 := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
    let u := reciprocalOrbit c t k
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
    have hu : ‖u‖ ≤ 1 / 2 := ih
    have hw : ‖c * u ^ 2‖ ≤ 1 / 4 := by
      simpa [u] using norm_parameter_mul_reciprocalOrbit_sq_le_quarter hc ht k ih
    have hlow : 1 - ‖c * u ^ 2‖ ≤ ‖1 + c * u ^ 2‖ := by
      have htri : ‖(1 : ℂ)‖ ≤ ‖1 + c * u ^ 2‖ + ‖c * u ^ 2‖ := by
        calc
          ‖(1 : ℂ)‖ = ‖(1 + c * u ^ 2) + -(c * u ^ 2)‖ := by ring_nf
          _ ≤ ‖1 + c * u ^ 2‖ + ‖-(c * u ^ 2)‖ := norm_add_le _ _
          _ = ‖1 + c * u ^ 2‖ + ‖c * u ^ 2‖ := by rw [norm_neg]
      rw [norm_one] at htri
      linarith
    have hden : 3 / 4 ≤ ‖1 + c * u ^ 2‖ := le_trans (by linarith) hlow
    have hden0 : 0 < ‖1 + c * u ^ 2‖ := by linarith
    rw [reciprocalOrbit_succ, norm_div, norm_pow]
    apply (div_le_iff₀ hden0).2
    nlinarith [sq_nonneg (‖u‖ - 1 / 2)]

/-- Every reciprocal orbit level is analytic in the parameter throughout the
fixed disk. -/
theorem analyticAt_reciprocalOrbit_parameter {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ ≤ 1 / 2) (k : ℕ) :
    AnalyticAt ℂ (fun d => reciprocalOrbit d t k) c := by
  induction k with
  | zero => simpa [reciprocalOrbit] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => t) c)
  | succ k ih =>
    have hu := norm_reciprocalOrbit_le_half hc ht k
    have hwq : ‖c * (reciprocalOrbit c t k) ^ 2‖ ≤ 1 / 4 :=
      norm_parameter_mul_reciprocalOrbit_sq_le_quarter hc ht k hu
    have hw : ‖c * (reciprocalOrbit c t k) ^ 2‖ < 1 := lt_of_le_of_lt hwq (by norm_num)
    have hden : 1 + c * (reciprocalOrbit c t k) ^ 2 ≠ 0 := by
      intro h0
      have hnorm := congrArg norm h0
      rw [norm_zero] at hnorm
      have htri : (1 : ℝ) ≤ ‖1 + c * (reciprocalOrbit c t k) ^ 2‖ +
          ‖c * (reciprocalOrbit c t k) ^ 2‖ := by
        calc
          (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
          _ = ‖(1 + c * (reciprocalOrbit c t k) ^ 2) -
              c * (reciprocalOrbit c t k) ^ 2‖ := by congr 1 <;> ring
          _ ≤ ‖1 + c * (reciprocalOrbit c t k) ^ 2‖ +
              ‖c * (reciprocalOrbit c t k) ^ 2‖ := norm_sub_le _ _
      rw [hnorm] at htri
      linarith
    rw [show (fun d => reciprocalOrbit d t (k + 1)) =
      fun d => (reciprocalOrbit d t k) ^ 2 /
        (1 + d * (reciprocalOrbit d t k) ^ 2) from rfl]
    exact (ih.pow 2).div (analyticAt_const.add (analyticAt_id.mul (ih.pow 2))) hden

/-- The logarithm argument stays in the principal slit plane on the fixed
parameter/reciprocal bidisk. -/
theorem reciprocalBottcherLog_argument_mem_slitPlane {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ ≤ 1 / 2) (k : ℕ) :
    1 + c * (reciprocalOrbit c t k) ^ 2 ∈ Complex.slitPlane := by
  have hu := norm_reciprocalOrbit_le_half hc ht k
  have hw : ‖c * (reciprocalOrbit c t k) ^ 2‖ ≤ 1 / 4 :=
    norm_parameter_mul_reciprocalOrbit_sq_le_quarter hc ht k hu
  rw [Complex.mem_slitPlane_iff]
  left
  have hre := abs_re_le_norm (c * (reciprocalOrbit c t k) ^ 2)
  rw [abs_le] at hre
  simp only [Complex.add_re, Complex.one_re]
  linarith [hre.1]

/-- Each reciprocal logarithm term is analytic in the parameter throughout
the fixed disk. -/
theorem analyticAt_reciprocalBottcherLogTerm_parameter {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ ≤ 1 / 2) (k : ℕ) :
    AnalyticAt ℂ (fun d => reciprocalBottcherLogTerm d t k) c := by
  have hu := analyticAt_reciprocalOrbit_parameter hc ht k
  have harg : AnalyticAt ℂ
      (fun d => 1 + d * (reciprocalOrbit d t k) ^ 2) c :=
    analyticAt_const.add (analyticAt_id.mul (hu.pow 2))
  unfold reciprocalBottcherLogTerm
  exact analyticAt_const.mul
    (harg.clog (reciprocalBottcherLog_argument_mem_slitPlane hc ht k))

/-- Uniform geometric majorant for the reciprocal logarithm terms. -/
theorem norm_reciprocalBottcherLogTerm_le {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ ≤ 1 / 2) (k : ℕ) :
    ‖reciprocalBottcherLogTerm c t k‖ ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  have hu := norm_reciprocalOrbit_le_half hc ht k
  have hw : ‖c * (reciprocalOrbit c t k) ^ 2‖ ≤ 1 / 2 := by
    exact (norm_parameter_mul_reciprocalOrbit_sq_le_quarter hc ht k hu).trans (by norm_num)
  have hlog := Bottcher.norm_clog_one_add_le hw
  unfold reciprocalBottcherLogTerm
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  calc
    ((2 : ℝ) ^ (k + 1))⁻¹ *
        ‖Complex.log (1 + c * (reciprocalOrbit c t k) ^ 2)‖
        ≤ ((2 : ℝ) ^ (k + 1))⁻¹ *
          (2 * ‖c * (reciprocalOrbit c t k) ^ 2‖) := by gcongr
    _ ≤ ((2 : ℝ) ^ (k + 1))⁻¹ := by
      have hpow : 0 ≤ ((2 : ℝ) ^ (k + 1))⁻¹ := by positivity
      nlinarith
    _ = (1 / 2 : ℝ) ^ (k + 1) := by simp [one_div]

/-- The reciprocal normalized Böttcher logarithm. -/
def reciprocalBottcherLog (c t : ℂ) : ℂ :=
  ∑' k, reciprocalBottcherLogTerm c t k

/-- The parameter series is holomorphic on the fixed disk. -/
theorem differentiableOn_reciprocalBottcherLog_parameter {t : ℂ}
    (ht : ‖t‖ ≤ 1 / 2) :
    DifferentiableOn ℂ (fun c => reciprocalBottcherLog c t) bottcherParameterDisk := by
  unfold reciprocalBottcherLog
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1))
  · have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa [pow_succ, mul_comm] using hs.mul_left (1 / 2 : ℝ)
  · intro k c hc
    exact (analyticAt_reciprocalBottcherLogTerm_parameter
      (mem_bottcherParameterDisk_iff.mp hc) ht k).differentiableAt.differentiableWithinAt
  · exact isOpen_bottcherParameterDisk
  · intro k c hc
    exact norm_reciprocalBottcherLogTerm_le
      (mem_bottcherParameterDisk_iff.mp hc) ht k

/-- The reciprocal normalized Böttcher logarithm is analytic at the monomial
parameter. -/
theorem analyticAt_reciprocalBottcherLog_parameter_zero {t : ℂ}
    (ht : ‖t‖ ≤ 1 / 2) :
    AnalyticAt ℂ (fun c => reciprocalBottcherLog c t) 0 := by
  exact (differentiableOn_reciprocalBottcherLog_parameter ht).analyticAt
    (isOpen_bottcherParameterDisk.mem_nhds (by simp [bottcherParameterDisk]))

/-- Normal convergence permits two parameter differentiations at the
monomial fibre.  The proof differentiates the locally uniform net of finite
partial sums twice, so it needs no separate majorant for differentiated
terms. -/
theorem hasSum_iteratedDeriv_two_reciprocalBottcherLogTerm_parameter_zero
    {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    HasSum
      (fun k => iteratedDeriv 2 (fun c => reciprocalBottcherLogTerm c t k) 0)
      (iteratedDeriv 2 (fun c => reciprocalBottcherLog c t) 0) := by
  let term : ℕ → ℂ → ℂ := fun k c => reciprocalBottcherLogTerm c t k
  let partials : Finset ℕ → ℂ → ℂ := fun s c => ∑ k ∈ s, term k c
  let total : ℂ → ℂ := fun c => ∑' k, term k c
  have htotal : total = fun c => reciprocalBottcherLog c t := by
    rfl
  have hu : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa [pow_succ, mul_comm] using hs.mul_left (1 / 2 : ℝ)
  have htermDiff (k : ℕ) :
      DifferentiableOn ℂ (term k) bottcherParameterDisk := by
    intro c hc
    exact (analyticAt_reciprocalBottcherLogTerm_parameter
      (mem_bottcherParameterDisk_iff.mp hc) ht k).differentiableAt.differentiableWithinAt
  have hpartialDiff (s : Finset ℕ) :
      DifferentiableOn ℂ (partials s) bottcherParameterDisk := by
    exact DifferentiableOn.fun_sum fun k _ => htermDiff k
  have hbound (k : ℕ) (c : ℂ) (hc : c ∈ bottcherParameterDisk) :
      ‖term k c‖ ≤ (1 / 2 : ℝ) ^ (k + 1) :=
    norm_reciprocalBottcherLogTerm_le (mem_bottcherParameterDisk_iff.mp hc) ht k
  have hconv0 : TendstoLocallyUniformlyOn partials total atTop bottcherParameterDisk := by
    exact (tendstoUniformlyOn_tsum hu hbound).tendstoLocallyUniformlyOn
  have hconv1 : TendstoLocallyUniformlyOn (deriv ∘ partials) (deriv total) atTop
      bottcherParameterDisk :=
    hconv0.deriv (Eventually.of_forall hpartialDiff) isOpen_bottcherParameterDisk
  have hpartialAnalytic (s : Finset ℕ) {c : ℂ} (hc : c ∈ bottcherParameterDisk) :
      AnalyticAt ℂ (partials s) c := by
    induction s using Finset.induction with
    | empty => simpa [partials] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) c)
    | @insert a s ha ih =>
        rw [show partials (insert a s) = term a + partials s by
          funext z
          simp [partials, ha]]
        exact (analyticAt_reciprocalBottcherLogTerm_parameter
          (mem_bottcherParameterDisk_iff.mp hc) ht a).add ih
  have hpartialDerivDiff (s : Finset ℕ) :
      DifferentiableOn ℂ (deriv (partials s)) bottcherParameterDisk := by
    intro c hc
    exact (hpartialAnalytic s hc).deriv.differentiableAt.differentiableWithinAt
  have hconv2 : TendstoLocallyUniformlyOn (deriv ∘ (deriv ∘ partials))
      (deriv (deriv total)) atTop bottcherParameterDisk :=
    hconv1.deriv (Eventually.of_forall hpartialDerivDiff) isOpen_bottcherParameterDisk
  have hzero : (0 : ℂ) ∈ bottcherParameterDisk := by simp [bottcherParameterDisk]
  have htend := hconv2.tendsto_at hzero
  have hfirst (s : Finset ℕ) :
      deriv (partials s) =ᶠ[nhds (0 : ℂ)] fun c => ∑ k ∈ s, deriv (term k) c := by
    filter_upwards [isOpen_bottcherParameterDisk.mem_nhds hzero] with c hc
    exact deriv_fun_sum fun k _ =>
      (htermDiff k c hc).differentiableAt (isOpen_bottcherParameterDisk.mem_nhds hc)
  have hsecond (s : Finset ℕ) :
      deriv (deriv (partials s)) 0 = ∑ k ∈ s, deriv (deriv (term k)) 0 := by
    rw [(hfirst s).deriv_eq]
    exact deriv_fun_sum fun k _ =>
      (analyticAt_reciprocalBottcherLogTerm_parameter_zero t k).deriv.differentiableAt
  rw [HasSum]
  convert htend using 1
  · funext s
    rw [show (deriv ∘ deriv ∘ partials) s 0 = deriv (deriv (partials s)) 0 from rfl,
      hsecond]
    apply Finset.sum_congr rfl
    intro k _
    simp only [term, show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]
  · rw [show iteratedDeriv 2 (fun c => reciprocalBottcherLog c t) 0 =
      deriv (deriv (fun c => reciprocalBottcherLog c t)) 0 by
        simp only [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]]
    rw [← htotal]

/-! ## Identification with the existing Böttcher coordinate -/

theorem reciprocal_inverse_escape_regime {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ < 1 / 2) (ht0 : t ≠ 0) :
    ‖c‖ ≤ ‖t⁻¹‖ ∧ 2 < ‖t⁻¹‖ := by
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have hinv : 2 < ‖t⁻¹‖ := by
    rw [norm_inv, inv_eq_one_div]
    exact (lt_div_iff₀ htpos).2 (by nlinarith)
  exact ⟨le_trans (le_of_lt hc) (by linarith), hinv⟩

/-- The reciprocal recursion is literally the inverse of the forward
quadratic orbit on the small reciprocal disk. -/
theorem reciprocalOrbit_eq_inv_quadratic_iterate {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ < 1 / 2) (ht0 : t ≠ 0) (k : ℕ) :
    reciprocalOrbit c t k = ((Bottcher.quadratic c)^[k] t⁻¹)⁻¹ := by
  obtain ⟨hcz, hz⟩ := reciprocal_inverse_escape_regime hc ht ht0
  induction k with
  | zero =>
    rw [reciprocalOrbit_zero, Function.iterate_zero_apply]
    exact (inv_inv t).symm
  | succ k ih =>
    let z := (Bottcher.quadratic c)^[k] t⁻¹
    have hz0 : z ≠ 0 := (Bottcher.escape_regime_stable hcz hz k).2
    have hnext0 : z ^ 2 + c ≠ 0 := by
      simpa [z, Function.iterate_succ_apply', Bottcher.quadratic_apply] using
        (Bottcher.escape_regime_stable hcz hz (k + 1)).2
    rw [reciprocalOrbit_succ, ih, Function.iterate_succ_apply', Bottcher.quadratic_apply]
    change z⁻¹ ^ 2 / (1 + c * z⁻¹ ^ 2) = (z ^ 2 + c)⁻¹
    field_simp

theorem reciprocalBottcherLogTerm_eq_bottcherLogTerm {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ < 1 / 2) (ht0 : t ≠ 0) (k : ℕ) :
    reciprocalBottcherLogTerm c t k = Bottcher.bottcherLogTerm c t⁻¹ k := by
  rw [reciprocalBottcherLogTerm, Bottcher.bottcherLogTerm,
    reciprocalOrbit_eq_inv_quadratic_iterate hc ht ht0]
  congr 3
  field_simp

theorem reciprocalBottcherLog_eq_bottcherLogSum {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ < 1 / 2) (ht0 : t ≠ 0) :
    reciprocalBottcherLog c t = ∑' k, Bottcher.bottcherLogTerm c t⁻¹ k := by
  unfold reciprocalBottcherLog
  exact tsum_congr (reciprocalBottcherLogTerm_eq_bottcherLogTerm hc ht ht0)

/-- The nonsingular reciprocal family is the normalized existing Böttcher
coordinate: `exp L(c,t) = t * φ_c(1/t)`. -/
theorem exp_reciprocalBottcherLog_eq_normalized_bottcherCoord {c t : ℂ}
    (hc : ‖c‖ < 1) (ht : ‖t‖ < 1 / 2) (ht0 : t ≠ 0) :
    Complex.exp (reciprocalBottcherLog c t) =
      t * Bottcher.bottcherCoord c t⁻¹ := by
  rw [Bottcher.bottcherCoord_eq_mul_exp (inv_ne_zero ht0),
    ← reciprocalBottcherLog_eq_bottcherLogSum hc ht ht0]
  field_simp

/-! ## First logarithmic parameter velocity -/

/-- Analytic `k`-th summand of the first logarithmic velocity. -/
def bottcherFirstLogVelocityTerm (k : ℕ) (t : ℂ) : ℂ :=
  (2 ^ (k + 1) : ℂ)⁻¹ * t ^ (2 ^ (k + 1))

/-- The convergent analytic value represented by the formal velocity jet. -/
def bottcherFirstLogVelocity (t : ℂ) : ℂ :=
  ∑' k : ℕ, bottcherFirstLogVelocityTerm k t

/-- The first parameter derivative of the actual reciprocal Böttcher
logarithm is the canonical dyadic velocity value. -/
theorem deriv_reciprocalBottcherLog_parameter_zero_eq_firstVelocity {t : ℂ}
    (ht : ‖t‖ ≤ 1 / 2) :
    deriv (fun c => reciprocalBottcherLog c t) 0 = bottcherFirstLogVelocity t := by
  have hsum := Complex.hasSum_deriv_of_summable_norm
    (F := fun k c => reciprocalBottcherLogTerm c t k)
    (U := bottcherParameterDisk)
    (u := fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1))
    (by
      have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa [pow_succ, mul_comm] using hs.mul_left (1 / 2 : ℝ))
    (fun k c hc => (analyticAt_reciprocalBottcherLogTerm_parameter
      (mem_bottcherParameterDisk_iff.mp hc) ht k).differentiableAt.differentiableWithinAt)
    isOpen_bottcherParameterDisk
    (fun k c hc => norm_reciprocalBottcherLogTerm_le
      (mem_bottcherParameterDisk_iff.mp hc) ht k)
    (by simp [bottcherParameterDisk] : (0 : ℂ) ∈ bottcherParameterDisk)
  unfold bottcherFirstLogVelocity bottcherFirstLogVelocityTerm reciprocalBottcherLog
  rw [← hsum.tsum_eq]
  exact tsum_congr (deriv_reciprocalBottcherLogTerm_parameter_zero t)

theorem contDiff_bottcherFirstLogVelocityTerm (k : ℕ) :
    ContDiff ℂ (⊤ : ℕ∞) (bottcherFirstLogVelocityTerm k) := by
  exact contDiff_const.mul (contDiff_id.pow _)

theorem norm_bottcherFirstLogVelocityTerm_le {t : ℂ}
    (ht : ‖t‖ ≤ 1 / 2) (k : ℕ) :
    ‖bottcherFirstLogVelocityTerm k t‖ ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  have ht1 : ‖t‖ ≤ 1 := ht.trans (by norm_num)
  unfold bottcherFirstLogVelocityTerm
  simp only [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  calc
    ((2 : ℝ) ^ (k + 1))⁻¹ * ‖t‖ ^ (2 ^ (k + 1))
        ≤ ((2 : ℝ) ^ (k + 1))⁻¹ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) ht1
    _ = (1 / 2 : ℝ) ^ (k + 1) := by
      rw [show (1 / 2 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1))⁻¹ by
        rw [one_div, inv_pow]]
      ring

theorem analyticAt_bottcherFirstLogVelocity :
    AnalyticAt ℂ bottcherFirstLogVelocity 0 := by
  let U : Set ℂ := Metric.ball 0 (1 / 2)
  have hu : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa [pow_succ, mul_comm] using hs.mul_left (1 / 2 : ℝ)
  have hdiff : ∀ k, DifferentiableOn ℂ (bottcherFirstLogVelocityTerm k) U :=
    fun k => (contDiff_bottcherFirstLogVelocityTerm k).differentiable
      (by simp) |>.differentiableOn
  have hopen : IsOpen U := Metric.isOpen_ball
  have hbound : ∀ k t, t ∈ U →
      ‖bottcherFirstLogVelocityTerm k t‖ ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    intro k t ht
    exact norm_bottcherFirstLogVelocityTerm_le (le_of_lt (by simpa [U] using ht)) k
  exact (Complex.differentiableOn_tsum_of_summable_norm hu hdiff hopen hbound).analyticAt
    (hopen.mem_nhds (by simp [U]))

theorem hasSum_iteratedDeriv_bottcherFirstLogVelocityTerm (n : ℕ) :
    HasSum (fun k => iteratedDeriv n (bottcherFirstLogVelocityTerm k) 0)
      (iteratedDeriv n bottcherFirstLogVelocity 0) := by
  let U : Set ℂ := Metric.ball 0 (1 / 2)
  let partials : Finset ℕ → ℂ → ℂ :=
    fun s t => ∑ k ∈ s, bottcherFirstLogVelocityTerm k t
  let total : ℂ → ℂ := fun t => ∑' k, bottcherFirstLogVelocityTerm k t
  have htotal : total = bottcherFirstLogVelocity := rfl
  have hu : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa [pow_succ, mul_comm] using hs.mul_left (1 / 2 : ℝ)
  have hopen : IsOpen U := Metric.isOpen_ball
  have htermDiff (k : ℕ) : DifferentiableOn ℂ (bottcherFirstLogVelocityTerm k) U :=
    (contDiff_bottcherFirstLogVelocityTerm k).differentiable (by simp) |>.differentiableOn
  have hpartialDiff (s : Finset ℕ) : DifferentiableOn ℂ (partials s) U :=
    DifferentiableOn.fun_sum fun k _ => htermDiff k
  have hbound : ∀ k t, t ∈ U →
      ‖bottcherFirstLogVelocityTerm k t‖ ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    intro k t ht
    exact norm_bottcherFirstLogVelocityTerm_le (le_of_lt (by simpa [U] using ht)) k
  have hconv0 : TendstoLocallyUniformlyOn partials total atTop U :=
    (tendstoUniformlyOn_tsum hu hbound).tendstoLocallyUniformlyOn
  have hzero : (0 : ℂ) ∈ U := by simp [U]
  have hpartialAnalytic (s : Finset ℕ) {t : ℂ} (ht : t ∈ U) :
      AnalyticAt ℂ (partials s) t := by
    induction s using Finset.induction with
    | empty => simpa [partials] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) t)
    | @insert k s hk ih =>
        rw [show partials (insert k s) = bottcherFirstLogVelocityTerm k + partials s by
          funext z
          simp [partials, hk]]
        exact ((contDiff_bottcherFirstLogVelocityTerm k).differentiable
          (by simp)).analyticAt t |>.add ih
  have hconv : ∀ m : ℕ,
      TendstoLocallyUniformlyOn
        (fun s => iteratedDeriv m (partials s)) (iteratedDeriv m total) atTop U := by
    intro m
    induction m with
    | zero => simpa [iteratedDeriv_zero] using hconv0
    | succ m ih =>
        have hdiffm : ∀ s : Finset ℕ,
            DifferentiableOn ℂ (iteratedDeriv m (partials s)) U := by
          intro s t ht
          have ha := (hpartialAnalytic s ht).iterated_deriv m
          simpa [iteratedDeriv_eq_iterate] using
            ha.differentiableAt.differentiableWithinAt
        simpa only [iteratedDeriv_succ] using
          ih.deriv (Eventually.of_forall hdiffm) hopen
  have hfinite : ∀ (m : ℕ) (s : Finset ℕ),
      iteratedDeriv m (partials s) 0 =
        ∑ k ∈ s, iteratedDeriv m (bottcherFirstLogVelocityTerm k) 0 := by
    intro m s
    induction s using Finset.induction with
    | empty => simp [partials]
    | @insert k s hk ih =>
        rw [show partials (insert k s) = bottcherFirstLogVelocityTerm k + partials s by
          funext z
          simp [partials, hk]]
        rw [iteratedDeriv_add
          ((contDiff_bottcherFirstLogVelocityTerm k).contDiffAt.of_le
            (by exact_mod_cast le_top))
          ((hpartialAnalytic s hzero).contDiffAt.of_le (by exact_mod_cast le_top)),
          ih, Finset.sum_insert hk]
  have htend := (hconv n).tendsto_at hzero
  rw [HasSum]
  convert htend using 1
  funext s
  exact (hfinite n s).symm

/-- Formal Taylor series of one first-velocity summand. -/
def bottcherFirstLogVelocitySeriesTerm (k : ℕ) : PowerSeries ℂ :=
  PowerSeries.C (2 ^ (k + 1) : ℂ)⁻¹ * X ^ (2 ^ (k + 1))

theorem taylorPS_bottcherFirstLogVelocityTerm (k : ℕ) :
    taylorPS (bottcherFirstLogVelocityTerm k) =
      bottcherFirstLogVelocitySeriesTerm k := by
  unfold bottcherFirstLogVelocityTerm bottcherFirstLogVelocitySeriesTerm
  calc
    taylorPS ((fun _ : ℂ => (2 ^ (k + 1) : ℂ)⁻¹) *
        (fun t : ℂ => t ^ (2 ^ (k + 1)))) =
      taylorPS (fun _ : ℂ => (2 ^ (k + 1) : ℂ)⁻¹) *
        taylorPS (fun t : ℂ => t ^ (2 ^ (k + 1))) :=
      taylorPS_mul contDiff_const (contDiff_id.pow _)
    _ = PowerSeries.C (2 ^ (k + 1) : ℂ)⁻¹ * X ^ (2 ^ (k + 1)) := by
      rw [taylorPS_const]
      congr 1
      ext n
      rw [coeff_taylorPS, coeff_X_pow, iteratedDeriv_fun_pow_zero]
      by_cases h : n = 2 ^ (k + 1)
      · subst n
        rw [if_pos rfl, if_pos rfl]
        exact div_self (by exact_mod_cast Nat.factorial_ne_zero (2 ^ (k + 1)))
      · simp [h]

def bottcherFirstLogVelocityTaylor : PowerSeries ℂ :=
  PowerSeries.mk fun n => ∑' k, (coeff n) (bottcherFirstLogVelocitySeriesTerm k)

theorem coeff_bottcherFirstLogVelocityTaylor (n : ℕ) :
    (coeff n) bottcherFirstLogVelocityTaylor =
      ∑' k, (coeff n) (bottcherFirstLogVelocitySeriesTerm k) :=
  coeff_mk n _

theorem taylorPS_bottcherFirstLogVelocity :
    taylorPS bottcherFirstLogVelocity = bottcherFirstLogVelocityTaylor := by
  ext n
  rw [coeff_bottcherFirstLogVelocityTaylor]
  have hs := (hasSum_iteratedDeriv_bottcherFirstLogVelocityTerm n).div_const
    (n.factorial : ℂ)
  rw [coeff_taylorPS, ← hs.tsum_eq]
  exact tsum_congr fun k => by
    rw [← coeff_taylorPS, taylorPS_bottcherFirstLogVelocityTerm]

/-- The actual analytic first logarithmic parameter velocity has the
canonical lacunary formal spatial Taylor jet. -/
theorem taylorPS_bottcherFirstLogVelocity_eq_velocityJet :
    taylorPS bottcherFirstLogVelocity = velocityJet := by
  rw [taylorPS_bottcherFirstLogVelocity]
  classical
  ext n
  rw [coeff_bottcherFirstLogVelocityTaylor, coeff_velocityJet, velocityCoeff]
  by_cases hdy : IsDyadicPow n
  · obtain ⟨k, rfl⟩ := hdy
    have hunique : ∀ j : ℕ, j ≠ k →
        (coeff (2 ^ (k + 1))) (bottcherFirstLogVelocitySeriesTerm j) = 0 := by
      intro j hj
      unfold bottcherFirstLogVelocitySeriesTerm
      rw [coeff_C_mul, coeff_X_pow, if_neg]
      ring
      intro hp
      apply hj
      have hexp := (Nat.pow_right_injective (by omega : 2 ≤ 2)) hp.symm
      omega
    rw [tsum_eq_single k hunique, if_pos ⟨k, rfl⟩]
    unfold bottcherFirstLogVelocitySeriesTerm
    rw [coeff_C_mul, coeff_X_pow, if_pos rfl]
    push_cast
    ring
  · have hz : (fun k : ℕ =>
        (coeff n) (bottcherFirstLogVelocitySeriesTerm k)) = fun _ => 0 := by
      funext k
      unfold bottcherFirstLogVelocitySeriesTerm
      rw [coeff_C_mul, coeff_X_pow, if_neg (fun hn => hdy ⟨k, hn⟩)]
      ring
    rw [hz, tsum_zero, if_neg hdy]

/-! ## Second logarithmic parameter velocity -/

/-- Taylor series respects subtraction for globally smooth functions.  This
local bridge complements the additive and multiplicative API already present
in `TaylorFormalBridge`. -/
theorem taylorPS_sub_of_contDiff {u v : ℂ → ℂ}
    (hu : ContDiff ℂ (⊤ : ℕ∞) u) (hv : ContDiff ℂ (⊤ : ℕ∞) v) :
    taylorPS (u - v) = taylorPS u - taylorPS v := by
  ext n
  rw [coeff_taylorPS,
    iteratedDeriv_sub (hu.contDiffAt.of_le (by exact_mod_cast le_top))
      (hv.contDiffAt.of_le (by exact_mod_cast le_top)),
    map_sub, coeff_taylorPS, coeff_taylorPS, sub_div]

/-- Taylor series of a monomial at the reciprocal origin. -/
theorem taylorPS_pow (m : ℕ) :
    taylorPS (fun t : ℂ => t ^ m) = (X ^ m : PowerSeries ℂ) := by
  ext n
  rw [coeff_taylorPS, coeff_X_pow, iteratedDeriv_fun_pow_zero]
  by_cases h : n = m
  · subst n
    rw [if_pos rfl, if_pos rfl]
    exact div_self (by exact_mod_cast Nat.factorial_ne_zero m)
  · simp [h]

/-- Formal spatial series of the first reciprocal-orbit parameter jet. -/
def reciprocalOrbitFirstJetSeries : ℕ → PowerSeries ℂ
  | 0 => 0
  | k + 1 =>
      2 * (X ^ (2 ^ k) * reciprocalOrbitFirstJetSeries k) - X ^ (2 ^ (k + 2))

theorem contDiff_reciprocalOrbitFirstJet (k : ℕ) :
    ContDiff ℂ (⊤ : ℕ∞) (fun t => reciprocalOrbitFirstJet t k) := by
  induction k with
  | zero => simpa [reciprocalOrbitFirstJet] using
      (contDiff_const : ContDiff ℂ (⊤ : ℕ∞) (fun _ : ℂ => (0 : ℂ)))
  | succ k ih =>
      rw [show (fun t => reciprocalOrbitFirstJet t (k + 1)) =
        fun t => 2 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k - t ^ (2 ^ (k + 2)) from rfl]
      exact ((contDiff_const.mul (contDiff_id.pow _)).mul ih).sub (contDiff_id.pow _)

/-- The polynomial orbit jet has exactly its recursively defined formal
Taylor series. -/
theorem taylorPS_reciprocalOrbitFirstJet (k : ℕ) :
    taylorPS (fun t => reciprocalOrbitFirstJet t k) = reciprocalOrbitFirstJetSeries k := by
  induction k with
  | zero => simp [reciprocalOrbitFirstJet, reciprocalOrbitFirstJetSeries, taylorPS_const]
  | succ k ih =>
      let p : ℂ → ℂ := fun t => t ^ (2 ^ k)
      let j : ℂ → ℂ := fun t => reciprocalOrbitFirstJet t k
      let q : ℂ → ℂ := fun t => t ^ (2 ^ (k + 2))
      have hp : ContDiff ℂ (⊤ : ℕ∞) p := contDiff_id.pow _
      have hj : ContDiff ℂ (⊤ : ℕ∞) j := contDiff_reciprocalOrbitFirstJet k
      have hq : ContDiff ℂ (⊤ : ℕ∞) q := contDiff_id.pow _
      have hmul2 : taylorPS ((fun _ : ℂ => 2) * (p * j)) =
          PowerSeries.C 2 * (taylorPS p * taylorPS j) := by
        calc
          taylorPS ((fun _ : ℂ => 2) * (p * j)) =
              taylorPS (fun _ : ℂ => 2) * taylorPS (p * j) := by
            simpa only [Pi.mul_apply] using
              (taylorPS_mul (u := fun _ : ℂ => 2) (v := p * j)
                contDiff_const (hp.mul hj))
          _ = PowerSeries.C 2 * (taylorPS p * taylorPS j) := by
            rw [taylorPS_const]
            congr 1
            simpa only [Pi.mul_apply] using (taylorPS_mul (u := p) (v := j) hp hj)
      rw [show (fun t => reciprocalOrbitFirstJet t (k + 1)) =
        (fun _ : ℂ => 2) * (p * j) - q by
          funext t
          dsimp [p, j, q]
          ring]
      calc
        taylorPS ((fun _ : ℂ => 2) * (p * j) - q) =
            taylorPS ((fun _ : ℂ => 2) * (p * j)) - taylorPS q :=
          taylorPS_sub_of_contDiff (contDiff_const.mul (hp.mul hj)) hq
        _ = (PowerSeries.C 2) *
              ((X ^ (2 ^ k) : PowerSeries ℂ) * reciprocalOrbitFirstJetSeries k) -
              X ^ (2 ^ (k + 2)) := by
          rw [hmul2, taylorPS_pow, ih, taylorPS_pow]
        _ = reciprocalOrbitFirstJetSeries (k + 1) := rfl

/-- Formal Taylor series of the `k`-th second-velocity summand. -/
def bottcherSecondLogVelocitySeriesTerm (k : ℕ) : PowerSeries ℂ :=
  PowerSeries.C (2 ^ (k + 1) : ℂ)⁻¹ *
    (4 * (X ^ (2 ^ k) * reciprocalOrbitFirstJetSeries k) - X ^ (2 ^ (k + 2)))

/-- Analytic `k`-th summand of the second logarithmic velocity. -/
def bottcherSecondLogVelocityTerm (k : ℕ) (t : ℂ) : ℂ :=
  (2 ^ (k + 1) : ℂ)⁻¹ *
    (4 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k - t ^ (2 ^ (k + 2)))

theorem contDiff_bottcherSecondLogVelocityTerm (k : ℕ) :
    ContDiff ℂ (⊤ : ℕ∞) (bottcherSecondLogVelocityTerm k) := by
  unfold bottcherSecondLogVelocityTerm
  exact contDiff_const.mul
    (((contDiff_const.mul (contDiff_id.pow _)).mul
      (contDiff_reciprocalOrbitFirstJet k)).sub (contDiff_id.pow _))

theorem taylorPS_bottcherSecondLogVelocityTerm (k : ℕ) :
    taylorPS (bottcherSecondLogVelocityTerm k) =
      bottcherSecondLogVelocitySeriesTerm k := by
  let xk : ℂ → ℂ := fun t => t ^ (2 ^ k)
  let jk : ℂ → ℂ := fun t => reciprocalOrbitFirstJet t k
  let x4k : ℂ → ℂ := fun t => t ^ (2 ^ (k + 2))
  have hxk : ContDiff ℂ (⊤ : ℕ∞) xk := contDiff_id.pow _
  have hjk : ContDiff ℂ (⊤ : ℕ∞) jk := contDiff_reciprocalOrbitFirstJet k
  have hx4k : ContDiff ℂ (⊤ : ℕ∞) x4k := contDiff_id.pow _
  have hsub : taylorPS ((fun _ : ℂ => 4) * (xk * jk) - x4k) =
      taylorPS ((fun _ : ℂ => 4) * (xk * jk)) - taylorPS x4k :=
    taylorPS_sub_of_contDiff (contDiff_const.mul (hxk.mul hjk)) hx4k
  have hmul4 : taylorPS ((fun _ : ℂ => 4) * (xk * jk)) =
      PowerSeries.C 4 * (taylorPS xk * taylorPS jk) := by
    calc
      taylorPS ((fun _ : ℂ => 4) * (xk * jk)) =
          taylorPS (fun _ : ℂ => 4) * taylorPS (xk * jk) := by
        simpa only [Pi.mul_apply] using
          (taylorPS_mul (u := fun _ : ℂ => 4) (v := xk * jk)
            contDiff_const (hxk.mul hjk))
      _ = PowerSeries.C 4 * (taylorPS xk * taylorPS jk) := by
        rw [taylorPS_const]
        congr 1
        simpa only [Pi.mul_apply] using (taylorPS_mul (u := xk) (v := jk) hxk hjk)
  rw [show bottcherSecondLogVelocityTerm k =
    (fun _ : ℂ => (2 ^ (k + 1) : ℂ)⁻¹) *
      ((fun _ : ℂ => 4) * (xk * jk) - x4k) by
        funext t
        dsimp [bottcherSecondLogVelocityTerm, xk, jk, x4k]
        ring]
  calc
    taylorPS ((fun _ : ℂ => (2 ^ (k + 1) : ℂ)⁻¹) *
        ((fun _ : ℂ => 4) * (xk * jk) - x4k)) =
      taylorPS (fun _ : ℂ => (2 ^ (k + 1) : ℂ)⁻¹) *
        taylorPS ((fun _ : ℂ => 4) * (xk * jk) - x4k) :=
      taylorPS_mul contDiff_const ((contDiff_const.mul (hxk.mul hjk)).sub hx4k)
    _ = PowerSeries.C (2 ^ (k + 1) : ℂ)⁻¹ *
        (taylorPS ((fun _ : ℂ => 4) * (xk * jk)) - taylorPS x4k) := by
      rw [taylorPS_const, hsub]
    _ = PowerSeries.C (2 ^ (k + 1) : ℂ)⁻¹ *
        ((PowerSeries.C 4) * (taylorPS xk * taylorPS jk) - taylorPS x4k) := by
      rw [hmul4]
    _ = bottcherSecondLogVelocitySeriesTerm k := by
      rw [taylorPS_pow, taylorPS_reciprocalOrbitFirstJet, taylorPS_pow]
      rfl

/-- Coarse but summable control of the orbit jet on the reciprocal half-disk. -/
theorem norm_reciprocalOrbitFirstJet_le {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) (k : ℕ) :
    ‖reciprocalOrbitFirstJet t k‖ ≤ (2 : ℝ) ^ k - 1 := by
  have ht1 : ‖t‖ ≤ 1 := ht.trans (by norm_num)
  induction k with
  | zero => simp
  | succ k ih =>
      rw [reciprocalOrbitFirstJet_succ]
      have hx : ‖t‖ ^ (2 ^ k) ≤ 1 := pow_le_one₀ (norm_nonneg _) ht1
      have hy : ‖t‖ ^ (2 ^ (k + 2)) ≤ 1 := pow_le_one₀ (norm_nonneg _) ht1
      have hM : 0 ≤ (2 : ℝ) ^ k - 1 :=
        sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      have hxJ :
          2 * ‖t‖ ^ (2 ^ k) * ‖reciprocalOrbitFirstJet t k‖ ≤
            2 * ‖t‖ ^ (2 ^ k) * ((2 : ℝ) ^ k - 1) :=
        mul_le_mul_of_nonneg_left ih
          (mul_nonneg (by norm_num) (pow_nonneg (norm_nonneg _) _))
      have hxM :
          2 * ‖t‖ ^ (2 ^ k) * ((2 : ℝ) ^ k - 1) ≤
            2 * 1 * ((2 : ℝ) ^ k - 1) := by
        nlinarith [mul_le_mul_of_nonneg_left hx
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)]
      calc
        ‖2 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k - t ^ (2 ^ (k + 2))‖
            ≤ ‖2 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k‖ +
              ‖t ^ (2 ^ (k + 2))‖ := norm_sub_le _ _
        _ = 2 * ‖t‖ ^ (2 ^ k) * ‖reciprocalOrbitFirstJet t k‖ +
              ‖t‖ ^ (2 ^ (k + 2)) := by simp [norm_mul, norm_pow]
        _ ≤ 2 * 1 * ((2 : ℝ) ^ k - 1) + 1 := by
          nlinarith
        _ = (2 : ℝ) ^ (k + 1) - 1 := by rw [pow_succ]; ring

theorem nat_succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega

/-- Uniform geometric majorant for the second-velocity summands. -/
theorem norm_bottcherSecondLogVelocityTerm_le {t : ℂ}
    (ht : ‖t‖ ≤ 1 / 2) (k : ℕ) :
    ‖bottcherSecondLogVelocityTerm k t‖ ≤
      3 * (1 / 2 : ℝ) ^ (k + 1) := by
  have ht1 : ‖t‖ ≤ 1 := ht.trans (by norm_num)
  have hdecay : ‖t‖ ^ (2 ^ k) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    calc
      ‖t‖ ^ (2 ^ k) ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by gcongr
      _ ≤ (1 / 2 : ℝ) ^ (k + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (nat_succ_le_two_pow k)
  have hinside :
      ‖4 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k - t ^ (2 ^ (k + 2))‖ ≤
        3 := by
    have hjet := norm_reciprocalOrbitFirstJet_le ht k
    have hjet' : ‖reciprocalOrbitFirstJet t k‖ ≤ (2 : ℝ) ^ k := by
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
    have hfirst :
        4 * ‖t‖ ^ (2 ^ k) * ‖reciprocalOrbitFirstJet t k‖ ≤ 2 := by
      calc
        4 * ‖t‖ ^ (2 ^ k) * ‖reciprocalOrbitFirstJet t k‖
            ≤ 4 * (1 / 2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ k := by
              gcongr
        _ = 2 := by
          have hkgeom : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by
            rw [← mul_pow]
            norm_num
          rw [pow_succ]
          nlinarith
    have hsecond : ‖t‖ ^ (2 ^ (k + 2)) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) ht1
    calc
      ‖4 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k - t ^ (2 ^ (k + 2))‖
          ≤ ‖4 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k‖ +
            ‖t ^ (2 ^ (k + 2))‖ := norm_sub_le _ _
      _ = 4 * ‖t‖ ^ (2 ^ k) * ‖reciprocalOrbitFirstJet t k‖ +
            ‖t‖ ^ (2 ^ (k + 2)) := by simp [norm_mul, norm_pow]
      _ ≤ 3 := by nlinarith
  unfold bottcherSecondLogVelocityTerm
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  calc
    ((2 : ℝ) ^ (k + 1))⁻¹ *
        ‖4 * t ^ (2 ^ k) * reciprocalOrbitFirstJet t k - t ^ (2 ^ (k + 2))‖
        ≤ ((2 : ℝ) ^ (k + 1))⁻¹ *
          3 := by gcongr
    _ = 3 * (1 / 2 : ℝ) ^ (k + 1) := by
      rw [show (1 / 2 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1))⁻¹ by
        rw [one_div, inv_pow]]
      ring

/-- The analytic value of the formal second logarithmic velocity. -/
def bottcherSecondLogVelocity (t : ℂ) : ℂ :=
  ∑' k : ℕ, bottcherSecondLogVelocityTerm k t

/-- The second logarithmic velocity is analytic at the reciprocal origin. -/
theorem analyticAt_bottcherSecondLogVelocity :
    AnalyticAt ℂ bottcherSecondLogVelocity 0 := by
  let U : Set ℂ := Metric.ball 0 (1 / 2)
  have hu : Summable (fun k : ℕ => 3 * (1 / 2 : ℝ) ^ (k + 1)) := by
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert hs.mul_left (3 / 2 : ℝ) using 1
    funext k
    rw [pow_succ]
    ring
  have hdiff : ∀ k, DifferentiableOn ℂ (bottcherSecondLogVelocityTerm k) U :=
    fun k => (contDiff_bottcherSecondLogVelocityTerm k).differentiable
      (by simp) |>.differentiableOn
  have hopen : IsOpen U := Metric.isOpen_ball
  have hbound : ∀ k t, t ∈ U →
      ‖bottcherSecondLogVelocityTerm k t‖ ≤ 3 * (1 / 2 : ℝ) ^ (k + 1) := by
    intro k t ht
    exact norm_bottcherSecondLogVelocityTerm_le (le_of_lt (by simpa [U] using ht)) k
  exact (Complex.differentiableOn_tsum_of_summable_norm hu hdiff hopen hbound).analyticAt
    (hopen.mem_nhds (by simp [U]))

/-- Every spatial Taylor derivative may be interchanged with the normally
convergent second-velocity series. -/
theorem hasSum_iteratedDeriv_bottcherSecondLogVelocityTerm (n : ℕ) :
    HasSum (fun k => iteratedDeriv n (bottcherSecondLogVelocityTerm k) 0)
      (iteratedDeriv n bottcherSecondLogVelocity 0) := by
  let U : Set ℂ := Metric.ball 0 (1 / 2)
  let partials : Finset ℕ → ℂ → ℂ :=
    fun s t => ∑ k ∈ s, bottcherSecondLogVelocityTerm k t
  let total : ℂ → ℂ := fun t => ∑' k, bottcherSecondLogVelocityTerm k t
  have htotal : total = bottcherSecondLogVelocity := rfl
  have hu : Summable (fun k : ℕ => 3 * (1 / 2 : ℝ) ^ (k + 1)) := by
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert hs.mul_left (3 / 2 : ℝ) using 1
    funext k
    rw [pow_succ]
    ring
  have hopen : IsOpen U := Metric.isOpen_ball
  have htermDiff (k : ℕ) : DifferentiableOn ℂ (bottcherSecondLogVelocityTerm k) U :=
    (contDiff_bottcherSecondLogVelocityTerm k).differentiable
      (by simp) |>.differentiableOn
  have hpartialDiff (s : Finset ℕ) : DifferentiableOn ℂ (partials s) U :=
    DifferentiableOn.fun_sum fun k _ => htermDiff k
  have hbound : ∀ k t, t ∈ U →
      ‖bottcherSecondLogVelocityTerm k t‖ ≤ 3 * (1 / 2 : ℝ) ^ (k + 1) := by
    intro k t ht
    exact norm_bottcherSecondLogVelocityTerm_le (le_of_lt (by simpa [U] using ht)) k
  have hconv0 : TendstoLocallyUniformlyOn partials total atTop U :=
    (tendstoUniformlyOn_tsum hu hbound).tendstoLocallyUniformlyOn
  have hzero : (0 : ℂ) ∈ U := by simp [U]
  have hpartialAnalytic (s : Finset ℕ) {t : ℂ} (ht : t ∈ U) :
      AnalyticAt ℂ (partials s) t := by
    induction s using Finset.induction with
    | empty => simpa [partials] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) t)
    | @insert k s hk ih =>
        rw [show partials (insert k s) = bottcherSecondLogVelocityTerm k + partials s by
          funext z
          simp [partials, hk]]
        exact ((contDiff_bottcherSecondLogVelocityTerm k).differentiable
          (by simp)).analyticAt t |>.add ih
  have hconv : ∀ m : ℕ,
      TendstoLocallyUniformlyOn
        (fun s => iteratedDeriv m (partials s)) (iteratedDeriv m total) atTop U := by
    intro m
    induction m with
    | zero => simpa [iteratedDeriv_zero] using hconv0
    | succ m ih =>
        have hdiffm : ∀ s : Finset ℕ,
            DifferentiableOn ℂ (iteratedDeriv m (partials s)) U := by
          intro s t ht
          have ha := (hpartialAnalytic s ht).iterated_deriv m
          simpa [iteratedDeriv_eq_iterate] using
            ha.differentiableAt.differentiableWithinAt
        simpa only [iteratedDeriv_succ] using
          ih.deriv (Eventually.of_forall hdiffm) hopen
  have hfinite : ∀ (m : ℕ) (s : Finset ℕ),
      iteratedDeriv m (partials s) 0 =
        ∑ k ∈ s, iteratedDeriv m (bottcherSecondLogVelocityTerm k) 0 := by
    intro m s
    induction s using Finset.induction with
    | empty => simp [partials, iteratedDeriv_const]
    | @insert k s hk ih =>
        rw [show partials (insert k s) = bottcherSecondLogVelocityTerm k + partials s by
          funext z
          simp [partials, hk]]
        rw [iteratedDeriv_add
          ((contDiff_bottcherSecondLogVelocityTerm k).contDiffAt.of_le
            (by exact_mod_cast le_top))
          ((hpartialAnalytic s hzero).contDiffAt.of_le (by exact_mod_cast le_top)),
          ih, Finset.sum_insert hk]
  have htend := (hconv n).tendsto_at hzero
  rw [HasSum]
  convert htend using 1
  · funext s
    exact (hfinite n s).symm

/-! ## Identification of the analytic spatial Taylor series -/

theorem dyadicSubst_X_pow (n : ℕ) :
    dyadicSubst (X ^ n : PowerSeries ℂ) = X ^ (2 * n) := by
  classical
  ext m
  rw [show (coeff m) (dyadicSubst (X ^ n : PowerSeries ℂ)) =
    (if 2 ∣ m then (coeff (m / 2)) (X ^ n : PowerSeries ℂ) else 0) from by
      rw [dyadicSubst, coeff_mk]]
  rw [coeff_X_pow, coeff_X_pow]
  split_ifs with h₁ h₂ h₃ <;> simp_all <;> omega

theorem dyadicSubst_C (a : ℂ) :
    dyadicSubst (PowerSeries.C a) = PowerSeries.C a := by
  classical
  ext n
  rw [show (coeff n) (dyadicSubst (PowerSeries.C a)) =
    (if 2 ∣ n then (coeff (n / 2)) (PowerSeries.C a) else 0) from by
      rw [dyadicSubst, coeff_mk]]
  rw [coeff_C, coeff_C]
  split_ifs with h₁ h₂ h₃ <;> simp_all <;> omega

/-- The orbit-jet polynomials transform triangularly under `t ↦ t²`. -/
theorem dyadicSubst_reciprocalOrbitFirstJetSeries (k : ℕ) :
    dyadicSubst (reciprocalOrbitFirstJetSeries k) =
      reciprocalOrbitFirstJetSeries (k + 1) +
        (2 ^ k : PowerSeries ℂ) * X ^ (2 ^ (k + 1) + 2) := by
  induction k with
  | zero =>
      change dyadicSubstHom 0 = _
      rw [map_zero]
      simp [reciprocalOrbitFirstJetSeries]
  | succ k ih =>
      rw [show reciprocalOrbitFirstJetSeries (k + 1) =
        2 * (X ^ (2 ^ k) * reciprocalOrbitFirstJetSeries k) -
          X ^ (2 ^ (k + 2)) from rfl]
      change dyadicSubstHom
        (2 * (X ^ (2 ^ k) * reciprocalOrbitFirstJetSeries k) -
          X ^ (2 ^ (k + 2))) = _
      rw [map_sub, map_mul, map_mul, map_ofNat]
      rw [show dyadicSubstHom (X ^ (2 ^ k)) = X ^ (2 * 2 ^ k) from
          dyadicSubst_X_pow _,
        show dyadicSubstHom (reciprocalOrbitFirstJetSeries k) =
          reciprocalOrbitFirstJetSeries (k + 1) +
            (2 ^ k : PowerSeries ℂ) * X ^ (2 ^ (k + 1) + 2) from ih,
        show dyadicSubstHom (X ^ (2 ^ (k + 2))) = X ^ (2 * 2 ^ (k + 2)) from
          dyadicSubst_X_pow _]
      rw [show reciprocalOrbitFirstJetSeries (k + 1 + 1) =
        2 * (X ^ (2 ^ (k + 1)) * reciprocalOrbitFirstJetSeries (k + 1)) -
          X ^ (2 ^ (k + 3)) from rfl]
      rw [show 2 * 2 ^ (k + 2) = 2 ^ (k + 3) by ring]
      rw [show X ^ (2 * 2 ^ k) = (X ^ (2 ^ (k + 1)) : PowerSeries ℂ) by
        congr 1 <;> omega]
      rw [show 2 ^ (k + 1 + 1) = 2 ^ (k + 2) by congr 1]
      ring_nf

/-- Each formal second-velocity summand transforms into the next summand
plus one sparse forcing monomial. -/
theorem dyadicSubst_bottcherSecondLogVelocitySeriesTerm (k : ℕ) :
    dyadicSubst (bottcherSecondLogVelocitySeriesTerm k) =
      2 * bottcherSecondLogVelocitySeriesTerm (k + 1) +
        2 * X ^ (2 ^ (k + 2) + 2) := by
  unfold bottcherSecondLogVelocitySeriesTerm
  change dyadicSubstHom
    (PowerSeries.C (2 ^ (k + 1) : ℂ)⁻¹ *
      (4 * (X ^ (2 ^ k) * reciprocalOrbitFirstJetSeries k) -
        X ^ (2 ^ (k + 2)))) = _
  rw [map_mul, map_sub, map_mul, map_mul]
  rw [show dyadicSubstHom (PowerSeries.C (2 ^ (k + 1) : ℂ)⁻¹) =
      PowerSeries.C (2 ^ (k + 1) : ℂ)⁻¹ from dyadicSubst_C _,
    map_ofNat,
    show dyadicSubstHom (X ^ (2 ^ k)) = X ^ (2 * 2 ^ k) from
      dyadicSubst_X_pow _,
    show dyadicSubstHom (reciprocalOrbitFirstJetSeries k) =
      reciprocalOrbitFirstJetSeries (k + 1) +
        (2 ^ k : PowerSeries ℂ) * X ^ (2 ^ (k + 1) + 2) from
          dyadicSubst_reciprocalOrbitFirstJetSeries _,
    show dyadicSubstHom (X ^ (2 ^ (k + 2))) = X ^ (2 * 2 ^ (k + 2)) from
      dyadicSubst_X_pow _]
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring,
    show 2 * 2 ^ (k + 2) = 2 ^ (k + 3) by ring]
  rw [show 2 ^ (k + 1 + 1) = 2 ^ (k + 2) by congr 1,
    show 2 ^ (k + 1 + 2) = 2 ^ (k + 3) by congr 1]
  rw [show PowerSeries.C (2 ^ (k + 1) : ℂ)⁻¹ =
      2 * PowerSeries.C (2 ^ (k + 2) : ℂ)⁻¹ by
        rw [two_mul]
        ext n
        rw [map_add, coeff_C, coeff_C]
        split_ifs
        · field_simp
          ring
        · ring]
  ring_nf
  have hscalar :
      PowerSeries.C (2⁻¹ ^ k * (1 / 4 : ℂ)) *
          (2 ^ k : PowerSeries ℂ) * 8 = 2 := by
    rw [show (2 ^ k : PowerSeries ℂ) = PowerSeries.C (2 ^ k : ℂ) by
      rw [map_pow, map_ofNat]]
    rw [show (8 : PowerSeries ℂ) = PowerSeries.C (8 : ℂ) by rw [map_ofNat]]
    rw [show (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) by rw [map_ofNat]]
    rw [← map_mul, ← map_mul]
    congr 1
    calc
      2⁻¹ ^ k * (1 / 4 : ℂ) * 2 ^ k * 8 =
          (2⁻¹ ^ k * 2 ^ k) * ((1 / 4 : ℂ) * 8) := by ring
      _ = 2 := by rw [← mul_pow]; norm_num
  linear_combination X ^ 2 * X ^ (2 ^ k * 4) * hscalar

/-- Coefficientwise sum of the formal Taylor series of all analytic
second-velocity summands. -/
def bottcherSecondLogVelocityTaylor : PowerSeries ℂ :=
  PowerSeries.mk fun n => ∑' k, (coeff n) (bottcherSecondLogVelocitySeriesTerm k)

theorem coeff_bottcherSecondLogVelocityTaylor (n : ℕ) :
    (coeff n) bottcherSecondLogVelocityTaylor =
      ∑' k, (coeff n) (bottcherSecondLogVelocitySeriesTerm k) :=
  coeff_mk n _

theorem summable_coeff_bottcherSecondLogVelocitySeriesTerm (n : ℕ) :
    Summable (fun k => (coeff n) (bottcherSecondLogVelocitySeriesTerm k)) := by
  have hs := (hasSum_iteratedDeriv_bottcherSecondLogVelocityTerm n).div_const
    (n.factorial : ℂ)
  have hs' : HasSum
      (fun k => (coeff n) (taylorPS (bottcherSecondLogVelocityTerm k)))
      ((coeff n) (taylorPS bottcherSecondLogVelocity)) := by
    simpa only [coeff_taylorPS] using hs
  simpa only [taylorPS_bottcherSecondLogVelocityTerm] using hs'.summable

/-- The analytic second logarithmic velocity has exactly the coefficientwise
formal series obtained from its normally convergent summands. -/
theorem taylorPS_bottcherSecondLogVelocity :
    taylorPS bottcherSecondLogVelocity = bottcherSecondLogVelocityTaylor := by
  ext n
  rw [coeff_bottcherSecondLogVelocityTaylor]
  have hs := (hasSum_iteratedDeriv_bottcherSecondLogVelocityTerm n).div_const
    (n.factorial : ℂ)
  rw [coeff_taylorPS, ← hs.tsum_eq]
  exact tsum_congr fun k => by
    rw [← coeff_taylorPS, taylorPS_bottcherSecondLogVelocityTerm]

theorem coeff_two_mul_X_pow (n m : ℕ) :
    (coeff n) (2 * X ^ m : PowerSeries ℂ) = if n = m then 2 else 0 := by
  rw [two_mul, map_add, coeff_X_pow]
  split_ifs <;> ring

open scoped Classical in
/-- Exact coefficient formula for the Euler forcing in the triangular
second-velocity equation. -/
theorem coeff_X_sq_thetaSeries_velocityJet (n : ℕ) :
    (coeff n) (X ^ 2 * thetaSeries velocityJet) =
      if 2 ≤ n ∧ IsDyadicPow (n - 2) then 1 else 0 := by
  rw [mul_comm, coeff_mul_X_pow', coeff_thetaSeries_velocityJet]
  by_cases h2 : 2 ≤ n
  · rw [if_pos h2]
    by_cases hd : IsDyadicPow (n - 2)
    · rw [if_pos hd, if_pos ⟨h2, hd⟩]
    · rw [if_neg hd, if_neg (fun hc => hd hc.2)]
  · rw [if_neg h2, if_neg (fun hc => h2 hc.1)]

/-- The sparse forcing tail starts with exponent six; equivalently it is
`2 X² θA - 2 X⁴`. -/
theorem tsum_coeff_secondVelocity_sparse_forcing (n : ℕ) :
    ∑' k : ℕ, (coeff n) (2 * X ^ (2 ^ (k + 2) + 2) : PowerSeries ℂ) =
      (coeff n) (2 * (X ^ 2 * thetaSeries velocityJet) - 2 * X ^ 4) := by
  classical
  by_cases hex : ∃ k : ℕ, n = 2 ^ (k + 2) + 2
  · obtain ⟨k, rfl⟩ := hex
    have hunique : ∀ j : ℕ, j ≠ k →
        (coeff (2 ^ (k + 2) + 2))
          (2 * X ^ (2 ^ (j + 2) + 2) : PowerSeries ℂ) = 0 := by
      intro j hj
      rw [coeff_two_mul_X_pow, if_neg]
      intro heq
      apply hj
      have hp : 2 ^ (k + 2) = 2 ^ (j + 2) := by omega
      have hexp := (Nat.pow_right_injective (by omega : 2 ≤ 2)) hp
      omega
    rw [tsum_eq_single k hunique, coeff_two_mul_X_pow, if_pos rfl]
    rw [map_sub, two_mul (X ^ 2 * thetaSeries velocityJet),
      two_mul (X ^ 4 : PowerSeries ℂ), map_add, map_add,
      coeff_X_sq_thetaSeries_velocityJet, coeff_X_pow]
    have hdy : IsDyadicPow ((2 ^ (k + 2) + 2) - 2) := by
      refine ⟨k + 1, ?_⟩
      rw [Nat.add_sub_cancel]
    have hpos := Nat.two_pow_pos (k + 2)
    have hpow4 : 4 ≤ 2 ^ (k + 2) := by
      have hp := Nat.pow_le_pow_right (by omega : 0 < 2)
        (by omega : 2 ≤ k + 2)
      norm_num at hp ⊢
      exact hp
    have hcond : 2 ≤ 2 ^ (k + 2) + 2 ∧
        IsDyadicPow ((2 ^ (k + 2) + 2) - 2) := ⟨by omega, hdy⟩
    have hne : 2 ^ (k + 2) + 2 ≠ 4 := by omega
    rw [if_pos hcond, if_neg hne]
    ring
  · have hzero : (fun k : ℕ =>
        (coeff n) (2 * X ^ (2 ^ (k + 2) + 2) : PowerSeries ℂ)) = fun _ => 0 := by
      funext k
      rw [coeff_two_mul_X_pow, if_neg]
      exact fun h => hex ⟨k, h⟩
    rw [hzero, tsum_zero]
    rw [map_sub, two_mul (X ^ 2 * thetaSeries velocityJet),
      two_mul (X ^ 4 : PowerSeries ℂ), map_add, map_add,
      coeff_X_sq_thetaSeries_velocityJet, coeff_X_pow]
    by_cases hn4 : n = 4
    · subst n
      rw [if_pos (show 2 ≤ 4 ∧ IsDyadicPow (4 - 2) by
        norm_num
        exact isDyadicPow_two), if_pos rfl]
      ring
    · have hnot : ¬(2 ≤ n ∧ IsDyadicPow (n - 2)) := by
        rintro ⟨hn2, j, hj⟩
        rcases j with _ | j
        · apply hn4
          norm_num at hj
          omega
        · apply hex
          refine ⟨j, ?_⟩
          calc
            n = (n - 2) + 2 := (Nat.sub_add_cancel hn2).symm
            _ = 2 ^ ((j + 1) + 1) + 2 := by rw [hj]
            _ = 2 ^ (j + 2) + 2 := by congr 2
      rw [if_neg hnot, if_neg hn4]
      ring

theorem summable_coeff_dyadicSubst_bottcherSecondLogVelocitySeriesTerm (n : ℕ) :
    Summable (fun k => (coeff n)
      (dyadicSubst (bottcherSecondLogVelocitySeriesTerm k))) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have hn : n = 2 * m := by omega
    subst n
    rw [show m + m = 2 * m by omega]
    simpa only [coeff_dyadicSubst_even] using
      summable_coeff_bottcherSecondLogVelocitySeriesTerm m
  · have hn : ¬2 ∣ n := by
      rw [Nat.odd_iff] at hodd
      omega
    have hz : (fun k : ℕ => (coeff n)
        (dyadicSubst (bottcherSecondLogVelocitySeriesTerm k))) = fun _ => 0 := by
      funext k
      exact coeff_dyadicSubst_odd _ hn
    rw [hz]
    exact summable_zero

theorem coeff_dyadicSubst_bottcherSecondLogVelocityTaylor (n : ℕ) :
    (coeff n) (dyadicSubst bottcherSecondLogVelocityTaylor) =
      ∑' k, (coeff n) (dyadicSubst (bottcherSecondLogVelocitySeriesTerm k)) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have hn : n = 2 * m := by omega
    subst n
    rw [show m + m = 2 * m by omega]
    rw [coeff_dyadicSubst_even, coeff_bottcherSecondLogVelocityTaylor]
    exact (tsum_congr fun k => coeff_dyadicSubst_even _ _).symm
  · have hn : ¬2 ∣ n := by
      rw [Nat.odd_iff] at hodd
      omega
    rw [coeff_dyadicSubst_odd _ hn]
    have hz : (fun k : ℕ => (coeff n)
        (dyadicSubst (bottcherSecondLogVelocitySeriesTerm k))) = fun _ => 0 := by
      funext k
      exact coeff_dyadicSubst_odd _ hn
    rw [hz, tsum_zero]

theorem bottcherSecondLogVelocitySeriesTerm_zero :
    bottcherSecondLogVelocitySeriesTerm 0 =
      PowerSeries.C (-(1 / 2 : ℂ)) * X ^ 4 := by
  simp [bottcherSecondLogVelocitySeriesTerm, reciprocalOrbitFirstJetSeries]

/-- The analytic second-velocity Taylor series satisfies the same triangular
Mahler equation as the canonical formal `secondJet`. -/
theorem dyadicSubst_bottcherSecondLogVelocityTaylor :
    dyadicSubst bottcherSecondLogVelocityTaylor =
      2 * bottcherSecondLogVelocityTaylor +
        2 * (X ^ 2 * thetaSeries velocityJet) - X ^ 4 := by
  ext n
  rw [coeff_dyadicSubst_bottcherSecondLogVelocityTaylor]
  have ha := summable_coeff_bottcherSecondLogVelocitySeriesTerm n
  have hatail : Summable (fun k =>
      (coeff n) (bottcherSecondLogVelocitySeriesTerm (k + 1))) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff 1).2 ha
  have hb := summable_coeff_dyadicSubst_bottcherSecondLogVelocitySeriesTerm n
  have heq (k : ℕ) :
      (coeff n) (dyadicSubst (bottcherSecondLogVelocitySeriesTerm k)) =
        2 * (coeff n) (bottcherSecondLogVelocitySeriesTerm (k + 1)) +
          (coeff n) (2 * X ^ (2 ^ (k + 2) + 2) : PowerSeries ℂ) := by
    have hk := congrArg (coeff n)
      (dyadicSubst_bottcherSecondLogVelocitySeriesTerm k)
    rw [map_add, show (coeff n) (2 * bottcherSecondLogVelocitySeriesTerm (k + 1)) =
      2 * (coeff n) (bottcherSecondLogVelocitySeriesTerm (k + 1)) by
        rw [two_mul, map_add, two_mul]] at hk
    exact hk
  have he : Summable (fun k =>
      (coeff n) (2 * X ^ (2 ^ (k + 2) + 2) : PowerSeries ℂ)) := by
    have hdifference := hb.sub (hatail.mul_left 2)
    convert hdifference using 1
    funext k
    linear_combination -(heq k)
  have hsum :
      (∑' k : ℕ, (coeff n)
        (dyadicSubst (bottcherSecondLogVelocitySeriesTerm k))) =
      ∑' k : ℕ, (2 * (coeff n) (bottcherSecondLogVelocitySeriesTerm (k + 1)) +
        (coeff n) (2 * X ^ (2 ^ (k + 2) + 2) : PowerSeries ℂ)) :=
    tsum_congr heq
  rw [(hatail.mul_left 2).tsum_add he, tsum_mul_left] at hsum
  rw [tsum_coeff_secondVelocity_sparse_forcing n] at hsum
  rw [map_sub,
    show (coeff n) (2 * (X ^ 2 * thetaSeries velocityJet)) =
      2 * (coeff n) (X ^ 2 * thetaSeries velocityJet) by
        rw [two_mul, map_add, two_mul],
    show (coeff n) (2 * X ^ 4 : PowerSeries ℂ) =
      2 * (coeff n) (X ^ 4 : PowerSeries ℂ) by
        rw [two_mul, map_add, two_mul]] at hsum
  rw [coeff_X_pow] at hsum
  have hshift := ha.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.zero_add] at hshift
  rw [map_sub, map_add,
    show (coeff n) (2 * bottcherSecondLogVelocityTaylor) =
      2 * (coeff n) bottcherSecondLogVelocityTaylor by
        rw [two_mul, map_add, two_mul]]
  rw [coeff_bottcherSecondLogVelocityTaylor]
  rw [show (coeff n) (2 * (X ^ 2 * thetaSeries velocityJet)) =
      2 * (coeff n) (X ^ 2 * thetaSeries velocityJet) by
        rw [two_mul, map_add, two_mul], coeff_X_pow]
  rw [bottcherSecondLogVelocitySeriesTerm_zero, coeff_C_mul, coeff_X_pow] at hshift
  linear_combination hsum + 2 * hshift

/-- The actual analytic second logarithmic parameter velocity has the
canonical formal spatial Taylor jet. -/
theorem taylorPS_bottcherSecondLogVelocity_eq_secondJet :
    taylorPS bottcherSecondLogVelocity = secondJet := by
  rw [taylorPS_bottcherSecondLogVelocity]
  let rhs : BottcherSpatialSeries :=
    2 * (X ^ 2 * thetaSeries velocityJet) - X ^ 4
  calc
    bottcherSecondLogVelocityTaylor = dyadicEquationSolution rhs :=
      dyadicEquationSolution_unique (by
        simpa [rhs, add_sub_assoc] using
          dyadicSubst_bottcherSecondLogVelocityTaylor)
    _ = secondJet := (dyadicEquationSolution_unique (by
      simpa [rhs, add_sub_assoc] using dyadicSubst_secondJet)).symm

/-- The second parameter derivative of the actual reciprocal Böttcher
logarithm is the canonical second logarithmic velocity value. -/
theorem iteratedDeriv_two_reciprocalBottcherLog_parameter_zero_eq_secondVelocity
    {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    iteratedDeriv 2 (fun c => reciprocalBottcherLog c t) 0 =
      bottcherSecondLogVelocity t := by
  have hsum := hasSum_iteratedDeriv_two_reciprocalBottcherLogTerm_parameter_zero ht
  unfold bottcherSecondLogVelocity
  rw [← hsum.tsum_eq]
  exact tsum_congr (iteratedDeriv_two_reciprocalBottcherLogTerm_parameter_zero t)

/-! ## Return from logarithmic jets to the normalized Böttcher coordinate -/

/-- The nonsingular normalized reciprocal Böttcher coordinate. -/
def reciprocalNormalizedBottcherCoordinate (c t : ℂ) : ℂ :=
  Complex.exp (reciprocalBottcherLog c t)

theorem reciprocalBottcherLog_zero_parameter (t : ℂ) :
    reciprocalBottcherLog 0 t = 0 := by
  unfold reciprocalBottcherLog
  have hz : (fun k : ℕ => reciprocalBottcherLogTerm 0 t k) = fun _ => 0 := by
    funext k
    simp [reciprocalBottcherLogTerm, reciprocalOrbit_zero_parameter]
  rw [hz, tsum_zero]

/-- First parameter derivative of the normalized reciprocal coordinate. -/
def bottcherFirstNormalizedVelocity (t : ℂ) : ℂ :=
  deriv (fun c => reciprocalNormalizedBottcherCoordinate c t) 0

/-- Second parameter derivative of the normalized reciprocal coordinate. -/
def bottcherSecondNormalizedVelocity (t : ℂ) : ℂ :=
  iteratedDeriv 2 (fun c => reciprocalNormalizedBottcherCoordinate c t) 0

theorem bottcherFirstNormalizedVelocity_eq {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    bottcherFirstNormalizedVelocity t = bottcherFirstLogVelocity t := by
  have hL := analyticAt_reciprocalBottcherLog_parameter_zero ht
  unfold bottcherFirstNormalizedVelocity reciprocalNormalizedBottcherCoordinate
  calc
    deriv (fun c => Complex.exp (reciprocalBottcherLog c t)) 0 =
        Complex.exp (reciprocalBottcherLog 0 t) *
          deriv (fun c => reciprocalBottcherLog c t) 0 :=
      hL.differentiableAt.hasDerivAt.cexp.deriv
    _ = bottcherFirstLogVelocity t := by
      rw [reciprocalBottcherLog_zero_parameter, Complex.exp_zero, one_mul,
        deriv_reciprocalBottcherLog_parameter_zero_eq_firstVelocity ht]

theorem bottcherSecondNormalizedVelocity_eq {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    bottcherSecondNormalizedVelocity t =
      bottcherSecondLogVelocity t + bottcherFirstLogVelocity t ^ 2 := by
  let L : ℂ → ℂ := fun c => reciprocalBottcherLog c t
  let E : ℂ → ℂ := fun c => Complex.exp (L c)
  have hL := analyticAt_reciprocalBottcherLog_parameter_zero ht
  have hzero : (0 : ℂ) ∈ bottcherParameterDisk := by simp [bottcherParameterDisk]
  have hderiv : deriv E =ᶠ[nhds (0 : ℂ)] fun c => E c * deriv L c := by
    filter_upwards [isOpen_bottcherParameterDisk.mem_nhds hzero] with c hc
    exact ((differentiableOn_reciprocalBottcherLog_parameter ht c hc).differentiableAt
      (isOpen_bottcherParameterDisk.mem_nhds hc)).hasDerivAt.cexp.deriv
  have hE : HasDerivAt E (bottcherFirstLogVelocity t) 0 := by
    have he := hL.differentiableAt.hasDerivAt.cexp
    simpa [E, L, reciprocalBottcherLog_zero_parameter,
      deriv_reciprocalBottcherLog_parameter_zero_eq_firstVelocity ht] using he
  have hDL : HasDerivAt (deriv L) (bottcherSecondLogVelocity t) 0 := by
    have hd := hL.deriv.differentiableAt.hasDerivAt
    rw [show deriv (deriv L) 0 = iteratedDeriv 2 L 0 by
      simp only [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]] at hd
    simpa [L, iteratedDeriv_two_reciprocalBottcherLog_parameter_zero_eq_secondVelocity ht]
      using hd
  unfold bottcherSecondNormalizedVelocity reciprocalNormalizedBottcherCoordinate
  change iteratedDeriv 2 E 0 = _
  rw [show iteratedDeriv 2 E 0 = deriv (deriv E) 0 by
    simp only [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]]
  rw [hderiv.deriv_eq]
  change deriv (E * deriv L) 0 = _
  rw [(hE.mul hDL).deriv]
  simp only [E, L, reciprocalBottcherLog_zero_parameter, Complex.exp_zero,
    deriv_reciprocalBottcherLog_parameter_zero_eq_firstVelocity ht]
  ring

theorem taylorPS_congr_of_eventuallyEq {f g : ℂ → ℂ}
    (hfg : f =ᶠ[nhds (0 : ℂ)] g) : taylorPS f = taylorPS g := by
  ext n
  rw [coeff_taylorPS, coeff_taylorPS, hfg.iteratedDeriv_eq n]

theorem taylorPS_add_of_analyticAt {u v : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hv : AnalyticAt ℂ v 0) :
    taylorPS (u + v) = taylorPS u + taylorPS v := by
  ext k
  rw [coeff_taylorPS, iteratedDeriv_add hu.contDiffAt hv.contDiffAt,
    map_add, coeff_taylorPS, coeff_taylorPS, add_div]

theorem taylorPS_mul_of_analyticAt {u v : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hv : AnalyticAt ℂ v 0) :
    taylorPS (u * v) = taylorPS u * taylorPS v := by
  ext N
  rw [coeff_taylorPS, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    iteratedDeriv_mul hu.contDiffAt hv.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [coeff_taylorPS, coeff_taylorPS]
  have hfac : (N.choose i : ℂ) * (i.factorial : ℂ) * ((N - i).factorial : ℂ) =
      (N.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hi0 : (i.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero i
  have hNi0 : ((N - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (N - i)
  have hN0 : (N.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  field_simp
  rw [← hfac]
  ring

theorem bottcherFirstNormalizedVelocity_eventuallyEq :
    bottcherFirstNormalizedVelocity =ᶠ[nhds (0 : ℂ)] bottcherFirstLogVelocity := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (show (0 : ℂ) ∈ Metric.ball 0 (1 / 2) by
    simp)] with t ht
  exact bottcherFirstNormalizedVelocity_eq (le_of_lt (by simpa using ht))

theorem bottcherSecondNormalizedVelocity_eventuallyEq :
    bottcherSecondNormalizedVelocity =ᶠ[nhds (0 : ℂ)]
      fun t => bottcherSecondLogVelocity t + bottcherFirstLogVelocity t ^ 2 := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (show (0 : ℂ) ∈ Metric.ball 0 (1 / 2) by
    simp)] with t ht
  exact bottcherSecondNormalizedVelocity_eq (le_of_lt (by simpa using ht))

theorem taylorPS_bottcherFirstNormalizedVelocity :
    taylorPS bottcherFirstNormalizedVelocity = velocityJet := by
  rw [taylorPS_congr_of_eventuallyEq bottcherFirstNormalizedVelocity_eventuallyEq,
    taylorPS_bottcherFirstLogVelocity_eq_velocityJet]

theorem taylorPS_bottcherSecondNormalizedVelocity :
    taylorPS bottcherSecondNormalizedVelocity =
      secondJet + velocityJet ^ 2 := by
  rw [taylorPS_congr_of_eventuallyEq bottcherSecondNormalizedVelocity_eventuallyEq]
  have hfun : (fun t => bottcherSecondLogVelocity t +
      bottcherFirstLogVelocity t ^ 2) =
      bottcherSecondLogVelocity +
        bottcherFirstLogVelocity * bottcherFirstLogVelocity := by
    funext t
    simp [pow_two]
  rw [hfun]
  rw [taylorPS_add_of_analyticAt analyticAt_bottcherSecondLogVelocity
      (analyticAt_bottcherFirstLogVelocity.mul analyticAt_bottcherFirstLogVelocity),
    taylorPS_mul_of_analyticAt analyticAt_bottcherFirstLogVelocity
      analyticAt_bottcherFirstLogVelocity,
    taylorPS_bottcherSecondLogVelocity_eq_secondJet,
    taylorPS_bottcherFirstLogVelocity_eq_velocityJet, pow_two]

/-- The first parameter velocity of the actual normalized Böttcher coordinate
at a finite spatial point. -/
def bottcherFirstParameterVelocity (z : ℂ) : ℂ :=
  deriv (fun c => Bottcher.bottcherCoord c z) 0

/-- The second parameter velocity of the actual normalized Böttcher coordinate
at a finite spatial point. -/
def bottcherSecondParameterVelocity (z : ℂ) : ℂ :=
  iteratedDeriv 2 (fun c => Bottcher.bottcherCoord c z) 0

theorem normalizedVelocity_eq_mul_actualVelocity {t : ℂ}
    (ht : ‖t‖ < 1 / 2) (ht0 : t ≠ 0) :
    bottcherFirstNormalizedVelocity t = t * bottcherFirstParameterVelocity t⁻¹ ∧
      bottcherSecondNormalizedVelocity t = t * bottcherSecondParameterVelocity t⁻¹ := by
  have hzero : (0 : ℂ) ∈ bottcherParameterDisk := by simp [bottcherParameterDisk]
  have heq : (fun c => reciprocalNormalizedBottcherCoordinate c t) =ᶠ[nhds (0 : ℂ)]
      fun c => t * Bottcher.bottcherCoord c t⁻¹ := by
    filter_upwards [isOpen_bottcherParameterDisk.mem_nhds hzero] with c hc
    unfold reciprocalNormalizedBottcherCoordinate
    exact exp_reciprocalBottcherLog_eq_normalized_bottcherCoord
      (mem_bottcherParameterDisk_iff.mp hc) ht ht0
  constructor
  · unfold bottcherFirstNormalizedVelocity bottcherFirstParameterVelocity
    have h := heq.iteratedDeriv_eq 1
    simpa [iteratedDeriv_one, iteratedDeriv_const_mul_field] using h
  · unfold bottcherSecondNormalizedVelocity bottcherSecondParameterVelocity
    have h := heq.iteratedDeriv_eq 2
    simpa [iteratedDeriv_const_mul_field] using h

/-! ## Algebraic independence of the actual coordinate jets -/

abbrev BottcherVelocityPolynomial := MvPolynomial (Fin 2) MahlerBase
abbrev BottcherVelocityCarrier := HahnSeries ℚ (RatFunc ℂ)

/-- Polynomial substitution implementing the triangular change
`(A,B) ↦ (A,B+A²)`. -/
def bottcherVelocityTriangularForward :
    BottcherVelocityPolynomial →+* BottcherVelocityPolynomial :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : MahlerBase →+* BottcherVelocityPolynomial)
    ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.X 0 ^ 2]

def bottcherVelocityTriangularInverse :
    BottcherVelocityPolynomial →+* BottcherVelocityPolynomial :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : MahlerBase →+* BottcherVelocityPolynomial)
    ![MvPolynomial.X 0, MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2]

theorem bottcherVelocityTriangularInverse_comp_forward :
    bottcherVelocityTriangularInverse.comp bottcherVelocityTriangularForward =
      RingHom.id BottcherVelocityPolynomial := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bottcherVelocityTriangularInverse, bottcherVelocityTriangularForward]
  · intro i
    fin_cases i <;>
      simp [bottcherVelocityTriangularInverse, bottcherVelocityTriangularForward]

theorem bottcherVelocityTriangularForward_ne_zero
    {P : BottcherVelocityPolynomial} (hP : P ≠ 0) :
    bottcherVelocityTriangularForward P ≠ 0 := by
  intro h
  apply hP
  have hz := congrArg bottcherVelocityTriangularInverse h
  rw [← RingHom.comp_apply, bottcherVelocityTriangularInverse_comp_forward,
    RingHom.id_apply, map_zero] at hz
  exact hz

def bottcherFirstLogVelocityCarrier : BottcherVelocityCarrier :=
  toMahlerCarrier velocityJet

def bottcherSecondLogVelocityCarrier : BottcherVelocityCarrier :=
  toMahlerCarrier secondJet

/-- The base-field element `t⁻¹`, evaluated in the Hahn carrier. -/
def bottcherReciprocalBaseCarrier : BottcherVelocityCarrier :=
  monoRatEval 1 one_pos (RatFunc.X⁻¹ : MahlerBase)

theorem bottcherReciprocalBaseCarrier_eq_mahlerT_inv :
    bottcherReciprocalBaseCarrier = mahlerT⁻¹ := by
  unfold bottcherReciprocalBaseCarrier
  apply mul_left_cancel₀ mahlerT_ne_zero
  rw [mul_inv_cancel₀ (G₀ := HahnSeries ℚ (RatFunc ℂ)) mahlerT_ne_zero]
  calc
    mahlerT * monoRatEval 1 one_pos (RatFunc.X⁻¹ : MahlerBase) =
        monoRatEval 1 one_pos RatFunc.X *
          monoRatEval 1 one_pos (RatFunc.X⁻¹ : MahlerBase) := by
      rw [mahlerT, monoRatEval_X]
    _ = monoRatEval 1 one_pos
        ((RatFunc.X : MahlerBase) * RatFunc.X⁻¹) := by rw [map_mul]
    _ = 1 := by rw [mul_inv_cancel₀ RatFunc.X_ne_zero, map_one]

/-- Carrier pair of the actual Böttcher jets in the reciprocal coordinate:
`(V₁(1/t),V₂(1/t)) = (t⁻¹A,t⁻¹(B+A²))`. -/
def bottcherActualVelocityCarrierPair : Fin 2 → BottcherVelocityCarrier :=
  ![bottcherReciprocalBaseCarrier * bottcherFirstLogVelocityCarrier,
    bottcherReciprocalBaseCarrier *
      (bottcherSecondLogVelocityCarrier + bottcherFirstLogVelocityCarrier ^ 2)]

/-- Evaluation of a polynomial over `ℂ(t)` at the actual pair of parameter
velocities. -/
def bottcherActualVelocityPolynomialEval :
    BottcherVelocityPolynomial →+* BottcherVelocityCarrier :=
  MvPolynomial.eval₂Hom (monoRatEval 1 one_pos) bottcherActualVelocityCarrierPair

theorem bottcherVelocityTriangular_eval :
    (MvPolynomial.eval₂Hom (monoRatEval 1 one_pos)
      ![bottcherFirstLogVelocityCarrier,
        bottcherSecondLogVelocityCarrier]).comp bottcherVelocityTriangularForward =
      MvPolynomial.eval₂Hom (monoRatEval 1 one_pos)
        ![bottcherFirstLogVelocityCarrier,
          bottcherSecondLogVelocityCarrier + bottcherFirstLogVelocityCarrier ^ 2] := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bottcherVelocityTriangularForward]
  · intro i
    fin_cases i <;> simp [bottcherVelocityTriangularForward]

/-- Polynomial substitution implementing multiplication of both variables by
the invertible base element `t⁻¹`. -/
def bottcherVelocityScaleForward :
    BottcherVelocityPolynomial →+* BottcherVelocityPolynomial :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : MahlerBase →+* BottcherVelocityPolynomial)
    ![MvPolynomial.C (RatFunc.X⁻¹ : MahlerBase) * MvPolynomial.X 0,
      MvPolynomial.C (RatFunc.X⁻¹ : MahlerBase) * MvPolynomial.X 1]

def bottcherVelocityScaleInverse :
    BottcherVelocityPolynomial →+* BottcherVelocityPolynomial :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : MahlerBase →+* BottcherVelocityPolynomial)
    ![MvPolynomial.C (RatFunc.X : MahlerBase) * MvPolynomial.X 0,
      MvPolynomial.C (RatFunc.X : MahlerBase) * MvPolynomial.X 1]

theorem bottcherVelocityScaleInverse_comp_forward :
    bottcherVelocityScaleInverse.comp bottcherVelocityScaleForward =
      RingHom.id BottcherVelocityPolynomial := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bottcherVelocityScaleInverse, bottcherVelocityScaleForward]
  · intro i
    fin_cases i <;> simp [bottcherVelocityScaleInverse, bottcherVelocityScaleForward]
    all_goals rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ RatFunc.X_ne_zero,
      map_one, one_mul]

theorem bottcherVelocityScaleForward_ne_zero
    {P : BottcherVelocityPolynomial} (hP : P ≠ 0) :
    bottcherVelocityScaleForward P ≠ 0 := by
  intro h
  apply hP
  have hz := congrArg bottcherVelocityScaleInverse h
  rw [← RingHom.comp_apply, bottcherVelocityScaleInverse_comp_forward,
    RingHom.id_apply, map_zero] at hz
  exact hz

theorem bottcherVelocityScale_eval :
    (MvPolynomial.eval₂Hom (monoRatEval 1 one_pos)
      ![bottcherFirstLogVelocityCarrier,
        bottcherSecondLogVelocityCarrier + bottcherFirstLogVelocityCarrier ^ 2]).comp
        bottcherVelocityScaleForward = bottcherActualVelocityPolynomialEval := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bottcherVelocityScaleForward, bottcherActualVelocityPolynomialEval]
  · intro i
    fin_cases i <;> simp [bottcherVelocityScaleForward,
      bottcherReciprocalBaseCarrier, bottcherActualVelocityCarrierPair,
      bottcherActualVelocityPolynomialEval]

/-- **Algebraic independence of the actual first two Böttcher parameter
velocities.** No nonzero polynomial over `ℂ(t)` vanishes on the reciprocal
germ pair `(V₁(1/t), V₂(1/t))`. -/
theorem bottcher_actual_velocity_pair_algebraicIndependent
    {P : BottcherVelocityPolynomial} (hP : P ≠ 0) :
    bottcherActualVelocityPolynomialEval P ≠ 0 := by
  let Q : BottcherVelocityPolynomial :=
    bottcherVelocityTriangularForward (bottcherVelocityScaleForward P)
  have hQ : Q ≠ 0 := by
    dsimp only [Q]
    exact bottcherVelocityTriangularForward_ne_zero
      (bottcherVelocityScaleForward_ne_zero hP)
  have hind : MvPolynomial.eval₂ (monoRatEval 1 one_pos)
      ![bottcherFirstLogVelocityCarrier, bottcherSecondLogVelocityCarrier] Q ≠ 0 := by
    simpa [bottcherFirstLogVelocityCarrier, bottcherSecondLogVelocityCarrier] using
      velocity_pair_algebraicIndependent hQ
  intro hzero
  apply hind
  change ((MvPolynomial.eval₂Hom (monoRatEval 1 one_pos)
    ![bottcherFirstLogVelocityCarrier, bottcherSecondLogVelocityCarrier]) Q) = 0
  rw [show Q = bottcherVelocityTriangularForward
    (bottcherVelocityScaleForward P) from rfl]
  change (((MvPolynomial.eval₂Hom (monoRatEval 1 one_pos)
    ![bottcherFirstLogVelocityCarrier, bottcherSecondLogVelocityCarrier]).comp
      bottcherVelocityTriangularForward) (bottcherVelocityScaleForward P)) = 0
  rw [bottcherVelocityTriangular_eval]
  have hscale :
      (MvPolynomial.eval₂Hom (monoRatEval 1 one_pos)
        ![bottcherFirstLogVelocityCarrier,
          bottcherSecondLogVelocityCarrier + bottcherFirstLogVelocityCarrier ^ 2])
          (bottcherVelocityScaleForward P) =
        bottcherActualVelocityPolynomialEval P := by
    simpa only [RingHom.comp_apply] using congrArg
      (fun h : BottcherVelocityPolynomial →+* BottcherVelocityCarrier => h P)
      bottcherVelocityScale_eval
  rw [hscale]
  exact hzero

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.XiHeatCassiniWoldLowerHalfShiftGapSummability

/-!
# Smooth source regularity of the physical Route-T residual connection

The centered Wold primitive has square-root-exponential decay, while every adjacent phase chord
contributes one prime-log gap.  Their product remains summable after multiplication by every
polynomial prime-log moment.  Thus the lower-half residual phase connection has a full derivative
jet, with locally uniform termwise differentiation.

This is stronger than pointwise convergence and different from the earlier weighted Hilbert graph
smoothness: it is literal `C^∞` regularity of the physical source kernel in its real boundary
coordinate.  Quantitative Gevrey constants are deliberately not claimed here.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff

namespace RHTower

noncomputable section

/-- Every polynomial prime-log moment of the physical residual variation is summable. -/
theorem summable_xiHeatCassiniWoldResidual_primeLogMoment_mul_gap (k : ℕ) :
    Summable (fun N : ℕ =>
      xiMassNthPrimeLogHeight (N + 1) ^ k *
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          xiHeatCassiniOrderedPrimeLogGap N) := by
  obtain ⟨B, c, hc, hB, hrate⟩ :=
    exists_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate
  obtain ⟨C, hC, hpow⟩ :=
    burnolPow_mul_exp_neg_sqrt_le (y := c / 2) (by linarith) k
  have hmajor :=
    summable_xiHeatCassiniOrderedPrimeLogGap_div_logHeight_sq.mul_left
      (B * (2 : ℝ) ^ k * C)
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hrate] with N hE
  let x : ℝ := xiMassNthPrimeLogHeight N
  let y : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hx : 0 < x := xiMassNthPrimeLogHeight_pos N
  have hy : 0 < y := xiMassNthPrimeLogHeight_pos (N + 1)
  have hy2x : y ≤ 2 * x := xiMassNthPrimeLogHeight_succ_le_two_mul N
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hBpowC : 0 ≤ B * (2 : ℝ) ^ k * C := by positivity
  have hyPow : y ^ k ≤ (2 : ℝ) ^ k * x ^ k := by
    calc
      y ^ k ≤ (2 * x) ^ k := pow_le_pow_left₀ hy.le hy2x k
      _ = (2 : ℝ) ^ k * x ^ k := by rw [mul_pow]
  have hpowx : x ^ k * Real.exp (-c * Real.sqrt x) ≤ C / x ^ 2 := by
    simpa [show 2 * (c / 2) = c by ring] using hpow x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (mul_nonneg (pow_nonneg hy.le k) (abs_nonneg _)) hdelta)]
  calc
    y ^ k * |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| * delta ≤
        y ^ k * (B * Real.exp (-c * Real.sqrt x)) * delta := by
      gcongr
      simpa [x, xiMassNthPrimeLogHeight] using hE
    _ ≤ ((2 : ℝ) ^ k * x ^ k) *
          (B * Real.exp (-c * Real.sqrt x)) * delta := by gcongr
    _ = (B * (2 : ℝ) ^ k) *
          (x ^ k * Real.exp (-c * Real.sqrt x)) * delta := by ring
    _ ≤ (B * (2 : ℝ) ^ k) * (C / x ^ 2) * delta := by gcongr
    _ = (B * (2 : ℝ) ^ k * C) * (delta / x ^ 2) := by ring

/-- `k`th formal derivative atom of one primitive phase edge. -/
def xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom
    (k : ℕ) (x : ℝ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
    (((-I * (xiMassNthPrimeLogHeight N : ℂ)) ^ k) *
        xiHeatCassiniOrderedPrimeNegativePhase N x -
      ((-I * (xiMassNthPrimeLogHeight (N + 1) : ℂ)) ^ k) *
        xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x)

@[simp]
theorem xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom_zero
    (x : ℝ) (N : ℕ) :
    xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom 0 x N =
      xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom x N := by
  simp [xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom,
    xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom]

theorem hasDerivAt_xiHeatCassiniOrderedPrimeNegativePhase
    (N : ℕ) (x : ℝ) :
    HasDerivAt (xiHeatCassiniOrderedPrimeNegativePhase N)
      ((-I * (xiMassNthPrimeLogHeight N : ℂ)) *
        xiHeatCassiniOrderedPrimeNegativePhase N x) x := by
  unfold xiHeatCassiniOrderedPrimeNegativePhase
  let c : ℂ := -I * (xiMassNthPrimeLogHeight N : ℂ)
  have hlin : HasDerivAt
      (fun y : ℝ => -(I * (xiMassNthPrimeLogHeight N : ℂ) * (y : ℂ)))
      (-I * (xiMassNthPrimeLogHeight N : ℂ)) x := by
    have hc : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
      simpa using Complex.ofRealCLM.hasDerivAt.const_mul c
    have hfun :
        (fun y : ℝ => -(I * (xiMassNthPrimeLogHeight N : ℂ) * (y : ℂ))) =
          (fun y : ℝ => c * (y : ℂ)) := by
      funext y
      dsimp only [c]
      ring
    rw [hfun]
    simpa only [c]
  simpa only [mul_comm] using hlin.cexp

/-- Derivative ladder for every individual residual phase-edge jet. -/
theorem hasDerivAt_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom
    (k : ℕ) (x : ℝ) (N : ℕ) :
    HasDerivAt
      (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k · N)
      (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom (k + 1) x N) x := by
  have hn := hasDerivAt_xiHeatCassiniOrderedPrimeNegativePhase N x
  have hs := hasDerivAt_xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x
  let An : ℂ := -I * (xiMassNthPrimeLogHeight N : ℂ)
  let As : ℂ := -I * (xiMassNthPrimeLogHeight (N + 1) : ℂ)
  have hn' : HasDerivAt
      (fun y : ℝ => An ^ k * xiHeatCassiniOrderedPrimeNegativePhase N y)
      (An ^ (k + 1) * xiHeatCassiniOrderedPrimeNegativePhase N x) x := by
    apply (hn.const_mul (An ^ k)).congr_deriv
    dsimp only [An]
    rw [pow_succ]
    ring
  have hs' : HasDerivAt
      (fun y : ℝ => As ^ k * xiHeatCassiniOrderedPrimeNegativePhase (N + 1) y)
      (As ^ (k + 1) * xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x) x := by
    apply (hs.const_mul (As ^ k)).congr_deriv
    dsimp only [As]
    rw [pow_succ]
    ring
  unfold xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom
  simpa only [An, As, Pi.sub_apply] using
    (hn'.sub hs').const_mul
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ)

/-- Adjacent imaginary frequencies retain one full mesh-gap factor after any polynomial jet. -/
theorem norm_negativeImag_primeLogHeight_pow_sub_succ_le
    (k N : ℕ) :
    ‖(-I * (xiMassNthPrimeLogHeight N : ℂ)) ^ k -
        (-I * (xiMassNthPrimeLogHeight (N + 1) : ℂ)) ^ k‖ ≤
      xiHeatCassiniOrderedPrimeLogGap N * (k : ℝ) *
        xiMassNthPrimeLogHeight (N + 1) ^ (k - 1) := by
  let h : ℝ := xiMassNthPrimeLogHeight N
  let s : ℝ := xiMassNthPrimeLogHeight (N + 1)
  have hh : 0 ≤ h := (xiMassNthPrimeLogHeight_pos N).le
  have hs : 0 ≤ s := (xiMassNthPrimeLogHeight_pos (N + 1)).le
  have hle : h ≤ s :=
    nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
  have hpow := abs_pow_sub_pow_le (a := s) (b := h) k
  rw [abs_of_nonneg hs, abs_of_nonneg hh, max_eq_left hle,
    abs_of_nonneg (sub_nonneg.mpr hle)] at hpow
  have hnorm :
      ‖(-I * (h : ℂ)) ^ k - (-I * (s : ℂ)) ^ k‖ =
        |h ^ k - s ^ k| := by
    have hcast :
        (h : ℂ) ^ k - (s : ℂ) ^ k = ((h ^ k - s ^ k : ℝ) : ℂ) := by
      push_cast
      rfl
    calc
      ‖(-I * (h : ℂ)) ^ k - (-I * (s : ℂ)) ^ k‖ =
          ‖(-I) ^ k * ((h : ℂ) ^ k - (s : ℂ) ^ k)‖ := by
        rw [mul_pow, mul_pow, mul_sub]
      _ = ‖(h : ℂ) ^ k - (s : ℂ) ^ k‖ := by
        rw [norm_mul, norm_pow]
        simp
      _ = |h ^ k - s ^ k| := by
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  change ‖(-I * (h : ℂ)) ^ k - (-I * (s : ℂ)) ^ k‖ ≤
    (s - h) * (k : ℝ) * s ^ (k - 1)
  rw [hnorm]
  simpa only [abs_sub_comm] using hpow

theorem norm_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom_le
    (k : ℕ) (x : ℝ) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x N‖ ≤
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N *
          (xiMassNthPrimeLogHeight (N + 1) ^ k * |x| +
            (k : ℝ) * xiMassNthPrimeLogHeight (N + 1) ^ (k - 1)) := by
  let h : ℝ := xiMassNthPrimeLogHeight N
  let s : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let A : ℂ := -I * (h : ℂ)
  let B : ℂ := -I * (s : ℂ)
  let pn : ℂ := xiHeatCassiniOrderedPrimeNegativePhase N x
  let ps : ℂ := xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x
  have hh : 0 ≤ h := (xiMassNthPrimeLogHeight_pos N).le
  have hs : 0 ≤ s := (xiMassNthPrimeLogHeight_pos (N + 1)).le
  have hle : h ≤ s :=
    nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
  have hphaseN : ‖pn‖ = 1 := by
    simp [pn, xiHeatCassiniOrderedPrimeNegativePhase, Complex.norm_exp,
      Complex.mul_re]
  have hphaseS : ‖ps‖ = 1 := by
    simp [ps, xiHeatCassiniOrderedPrimeNegativePhase, Complex.norm_exp,
      Complex.mul_re]
  have hAnorm : ‖A ^ k‖ = h ^ k := by
    simp [A, norm_pow, abs_of_nonneg hh]
  have hphaseChord : ‖pn - ps‖ ≤
      xiHeatCassiniOrderedPrimeLogGap N * |x| := by
    simpa only [pn, ps] using
      norm_xiHeatCassiniOrderedPrimeNegativePhase_sub_succ_le x N
  have hpowerChord : ‖A ^ k - B ^ k‖ ≤
      xiHeatCassiniOrderedPrimeLogGap N * (k : ℝ) * s ^ (k - 1) := by
    simpa only [A, B, h, s] using
      norm_negativeImag_primeLogHeight_pow_sub_succ_le k N
  rw [xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  change |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      ‖A ^ k * pn - B ^ k * ps‖ ≤ _
  have hinner : ‖A ^ k * pn - B ^ k * ps‖ ≤
      xiHeatCassiniOrderedPrimeLogGap N *
        (s ^ k * |x| + (k : ℝ) * s ^ (k - 1)) := by
    calc
      ‖A ^ k * pn - B ^ k * ps‖ =
          ‖A ^ k * (pn - ps) + (A ^ k - B ^ k) * ps‖ := by
        congr 1
        ring
      _ ≤ ‖A ^ k * (pn - ps)‖ + ‖(A ^ k - B ^ k) * ps‖ :=
        norm_add_le _ _
      _ = h ^ k * ‖pn - ps‖ + ‖A ^ k - B ^ k‖ := by
        rw [norm_mul, norm_mul, hAnorm, hphaseS, mul_one]
      _ ≤ h ^ k * (xiHeatCassiniOrderedPrimeLogGap N * |x|) +
          (xiHeatCassiniOrderedPrimeLogGap N * (k : ℝ) * s ^ (k - 1)) := by
        gcongr
      _ ≤ s ^ k * (xiHeatCassiniOrderedPrimeLogGap N * |x|) +
          (xiHeatCassiniOrderedPrimeLogGap N * (k : ℝ) * s ^ (k - 1)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh hle k)
            (mul_nonneg (xiHeatCassiniOrderedPrimeLogGap_nonneg N) (abs_nonneg x)))
          le_rfl
      _ = xiHeatCassiniOrderedPrimeLogGap N *
          (s ^ k * |x| + (k : ℝ) * s ^ (k - 1)) := by ring
  simpa only [s, mul_assoc] using
    mul_le_mul_of_nonneg_left hinner
      (abs_nonneg (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N))

/-- Every physical residual jet series converges absolutely at every real source point. -/
theorem summable_norm_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom
    (k : ℕ) (x : ℝ) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x N‖) := by
  have hmajor :=
    ((summable_xiHeatCassiniWoldResidual_primeLogMoment_mul_gap k).mul_right |x|).add
      ((summable_xiHeatCassiniWoldResidual_primeLogMoment_mul_gap (k - 1)).mul_left
        (k : ℝ))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun N => (norm_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom_le k x N).trans_eq
      (by ring)) hmajor

theorem summable_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom
    (k : ℕ) (x : ℝ) :
    Summable (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x) :=
  (summable_norm_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x).of_norm

/-- Full physical derivative jet of the lower-half residual source kernel. -/
def xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel
    (k : ℕ) (x : ℝ) : ℂ :=
  ∑' N : ℕ, xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x N

@[simp]
theorem xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel_zero
    (x : ℝ) :
    xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel 0 x =
      xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit x := by
  simp only [xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel,
    xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit,
    xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom_zero]

/-- The infinite physical residual kernel differentiates termwise through its complete jet. -/
theorem hasDerivAt_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel
    (k : ℕ) (x : ℝ) :
    HasDerivAt
      (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel k)
      (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel (k + 1) x) x := by
  let M : ℕ → ℝ := fun N =>
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      xiHeatCassiniOrderedPrimeLogGap N *
        (xiMassNthPrimeLogHeight (N + 1) ^ (k + 1) * (|x| + 1) +
          ((k + 1 : ℕ) : ℝ) * xiMassNthPrimeLogHeight (N + 1) ^ k)
  have hM : Summable M := by
    have hmajor :=
      ((summable_xiHeatCassiniWoldResidual_primeLogMoment_mul_gap (k + 1)).mul_right
        (|x| + 1)).add
      ((summable_xiHeatCassiniWoldResidual_primeLogMoment_mul_gap k).mul_left
        ((k + 1 : ℕ) : ℝ))
    exact hmajor.congr (fun N => by dsimp only [M]; ring)
  have hxmem : x ∈ Ioo (x - 1) (x + 1) := by constructor <;> linarith
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := M) (t := Ioo (x - 1) (x + 1))
    (g := fun N y =>
      xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k y N)
    (g' := fun N y =>
      xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom (k + 1) y N)
    (y₀ := x) (y := x) hM isOpen_Ioo isPreconnected_Ioo
    (fun N y _ =>
      hasDerivAt_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k y N)
    (fun N y hy => by
      have hyabs : |y| ≤ |x| + 1 := by
        rw [abs_le]
        constructor
        · have hxlower := neg_abs_le x
          linarith [hy.1]
        · have hxupper := le_abs_self x
          linarith [hy.2]
      have hraw :=
        norm_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom_le (k + 1) y N
      apply hraw.trans
      dsimp only [M]
      simp only [Nat.add_sub_cancel]
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add
          (mul_le_mul_of_nonneg_left hyabs
            (pow_nonneg (xiMassNthPrimeLogHeight_pos (N + 1)).le (k + 1)))
          le_rfl
      · exact mul_nonneg (abs_nonneg _)
          (xiHeatCassiniOrderedPrimeLogGap_nonneg N))
    hxmem
    (summable_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x)
    hxmem
  change HasDerivAt
    (fun z => ∑' N : ℕ,
      xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k z N)
    (∑' N : ℕ,
      xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom (k + 1) x N) x
  exact hmain

/-- In particular, the physical lower-half residual source is differentiable everywhere. -/
theorem differentiable_xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit :
    Differentiable ℝ xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit := by
  have hzero :
      xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit =
        xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel 0 := by
    funext x
    exact (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel_zero x).symm
  rw [hzero]
  intro x
  exact (hasDerivAt_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel 0 x).differentiableAt

/-- **Physical residual source regularity.**  The convergent lower-half phase connection is
`C^∞`; its `k`th derivative is the explicitly summable `k`th prime-log jet. -/
theorem contDiff_infty_xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit :
    ContDiff ℝ ∞ xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit := by
  have hderiv (j : ℕ) :
      deriv (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel j) =
        xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel (j + 1) := by
    funext x
    exact
      (hasDerivAt_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel j x).deriv
  have hiter (j : ℕ) :
      iteratedDeriv j
          (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel 0) =
        xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel j := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [iteratedDeriv_succ, ih, hderiv]
  have hsmooth : ContDiff ℝ ∞
      (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel 0) := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro j _
    rw [hiter]
    intro x
    exact
      (hasDerivAt_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel j x).differentiableAt
  have hzero :
      xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit =
        xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel 0 := by
    funext x
    exact (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel_zero x).symm
  rw [hzero]
  exact hsmooth

end

end RHTower

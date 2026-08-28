import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualHardyPolarization

/-!
# Exact log-mesh transport current of the centered Route-T Wold residual
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One source-marked residual molecule on an adjacent prime-log edge. -/
def xiHeatCassiniWoldResidualLogMeshCurrentAtom
    (phi : ℕ → ℂ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
    (phi N - phi (N + 1))

/-- Infinite residual edge current tested against a node observable. -/
def xiHeatCassiniWoldResidualLogMeshCurrent (phi : ℕ → ℂ) : ℂ :=
  ∑' N : ℕ, xiHeatCassiniWoldResidualLogMeshCurrentAtom phi N

/-- Adjacent Lipschitz law on the ordered prime-log mesh. -/
def XiHeatCassiniPrimeLogMeshLipschitz (K : ℝ) (phi : ℕ → ℂ) : Prop :=
  ∀ N : ℕ, ‖phi N - phi (N + 1)‖ ≤
    K * xiHeatCassiniOrderedPrimeLogGap N

theorem summable_xiHeatCassiniWoldResidualLogMeshCurrentAtom
    {K : ℝ} (_hK : 0 ≤ K) {phi : ℕ → ℂ}
    (hphi : XiHeatCassiniPrimeLogMeshLipschitz K phi) :
    Summable (xiHeatCassiniWoldResidualLogMeshCurrentAtom phi) := by
  have hmajor :=
    summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap.mul_left K
  apply hmajor.of_norm_bounded
  intro N
  rw [xiHeatCassiniWoldResidualLogMeshCurrentAtom, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        ‖phi N - phi (N + 1)‖ ≤
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        (K * xiHeatCassiniOrderedPrimeLogGap N) :=
      mul_le_mul_of_nonneg_left (hphi N) (abs_nonneg _)
    _ = K * (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N) := by ring

/-- Kantorovich upper bound for every adjacent-Lipschitz node observable. -/
theorem norm_xiHeatCassiniWoldResidualLogMeshCurrent_le
    {K : ℝ} (hK : 0 ≤ K) {phi : ℕ → ℂ}
    (hphi : XiHeatCassiniPrimeLogMeshLipschitz K phi) :
    ‖xiHeatCassiniWoldResidualLogMeshCurrent phi‖ ≤
      K * xiHeatCassiniWoldResidualPrimeLogTotalVariation := by
  have hs := summable_xiHeatCassiniWoldResidualLogMeshCurrentAtom hK hphi
  calc
    ‖xiHeatCassiniWoldResidualLogMeshCurrent phi‖ ≤
        ∑' N : ℕ, ‖xiHeatCassiniWoldResidualLogMeshCurrentAtom phi N‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' N : ℕ, K *
        (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          xiHeatCassiniOrderedPrimeLogGap N) :=
      hs.norm.tsum_le_tsum
        (fun N => by
          rw [xiHeatCassiniWoldResidualLogMeshCurrentAtom, norm_mul,
            Complex.norm_real, Real.norm_eq_abs]
          calc
            |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
                ‖phi N - phi (N + 1)‖ ≤
              |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
                (K * xiHeatCassiniOrderedPrimeLogGap N) :=
              mul_le_mul_of_nonneg_left (hphi N) (abs_nonneg _)
            _ = _ := by ring)
        (summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap.mul_left K)
    _ = K * xiHeatCassiniWoldResidualPrimeLogTotalVariation := by
      rw [xiHeatCassiniWoldResidualPrimeLogTotalVariation, tsum_mul_left]

/-- Source-selected sign potential.  Its slope on edge `N` is the sign of the exact Wold
residual coefficient on that edge. -/
def xiHeatCassiniWoldResidualLogMeshNormingPotential : ℕ → ℝ
  | 0 => 0
  | N + 1 => xiHeatCassiniWoldResidualLogMeshNormingPotential N -
      deningerFreqSign (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N) *
        xiHeatCassiniOrderedPrimeLogGap N

/-- Complex node observable associated with the real norming potential. -/
def xiHeatCassiniWoldResidualLogMeshNormingObservable (N : ℕ) : ℂ :=
  (xiHeatCassiniWoldResidualLogMeshNormingPotential N : ℂ)

theorem mul_deningerFreqSign_eq_abs (x : ℝ) :
    x * deningerFreqSign x = |x| := by
  by_cases hx : x = 0
  · simp [hx]
  · calc
      x * deningerFreqSign x = deningerFreqSign x * x := mul_comm _ _
      _ = |x| := (deningerFreqSign_abs hx).symm

@[simp]
theorem abs_xiHeatCassiniWoldResidualLogMeshNormingPotential_succ_sub
    (N : ℕ) :
    |xiHeatCassiniWoldResidualLogMeshNormingPotential (N + 1) -
        xiHeatCassiniWoldResidualLogMeshNormingPotential N| =
      xiHeatCassiniOrderedPrimeLogGap N := by
  rw [xiHeatCassiniWoldResidualLogMeshNormingPotential]
  have hsign : |deningerFreqSign
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N)| = 1 := by
    unfold deningerFreqSign
    split_ifs <;> norm_num
  rw [sub_sub_cancel_left, abs_neg, abs_mul, hsign, one_mul,
    abs_of_nonneg (xiHeatCassiniOrderedPrimeLogGap_nonneg N)]

theorem xiHeatCassiniWoldResidualLogMeshNormingPotential_lipschitz_forward
    (N M : ℕ) (hNM : N ≤ M) :
    |xiHeatCassiniWoldResidualLogMeshNormingPotential M -
        xiHeatCassiniWoldResidualLogMeshNormingPotential N| ≤
      xiMassNthPrimeLogHeight M - xiMassNthPrimeLogHeight N := by
  induction M with
  | zero =>
      have hN : N = 0 := Nat.eq_zero_of_le_zero hNM
      subst N
      simp
  | succ M ih =>
      by_cases hEq : N = M + 1
      · subst N
        simp
      · have hNM' : N ≤ M := by omega
        calc
          |xiHeatCassiniWoldResidualLogMeshNormingPotential (M + 1) -
              xiHeatCassiniWoldResidualLogMeshNormingPotential N| =
            |(xiHeatCassiniWoldResidualLogMeshNormingPotential (M + 1) -
                xiHeatCassiniWoldResidualLogMeshNormingPotential M) +
              (xiHeatCassiniWoldResidualLogMeshNormingPotential M -
                xiHeatCassiniWoldResidualLogMeshNormingPotential N)| := by
              congr 1
              ring
          _ ≤ |xiHeatCassiniWoldResidualLogMeshNormingPotential (M + 1) -
                xiHeatCassiniWoldResidualLogMeshNormingPotential M| +
              |xiHeatCassiniWoldResidualLogMeshNormingPotential M -
                xiHeatCassiniWoldResidualLogMeshNormingPotential N| :=
            abs_add_le _ _
          _ ≤ xiHeatCassiniOrderedPrimeLogGap M +
              (xiMassNthPrimeLogHeight M - xiMassNthPrimeLogHeight N) :=
            add_le_add
              (le_of_eq
                (abs_xiHeatCassiniWoldResidualLogMeshNormingPotential_succ_sub M))
              (ih hNM')
          _ = xiMassNthPrimeLogHeight (M + 1) -
              xiMassNthPrimeLogHeight N := by
            unfold xiHeatCassiniOrderedPrimeLogGap
            ring

/-- The norming potential is globally one-Lipschitz for the actual prime-log distance. -/
theorem xiHeatCassiniWoldResidualLogMeshNormingPotential_lipschitz
    (N M : ℕ) :
    |xiHeatCassiniWoldResidualLogMeshNormingPotential N -
        xiHeatCassiniWoldResidualLogMeshNormingPotential M| ≤
      |xiMassNthPrimeLogHeight N - xiMassNthPrimeLogHeight M| := by
  rcases le_total N M with hNM | hMN
  · have hheight : xiMassNthPrimeLogHeight N ≤ xiMassNthPrimeLogHeight M :=
      nthPrimeSubtype_log_strictMono.monotone hNM
    simpa [abs_sub_comm,
      abs_of_nonpos (sub_nonpos.mpr hheight)] using
      xiHeatCassiniWoldResidualLogMeshNormingPotential_lipschitz_forward N M hNM
  · have hheight : xiMassNthPrimeLogHeight M ≤ xiMassNthPrimeLogHeight N :=
      nthPrimeSubtype_log_strictMono.monotone hMN
    simpa [abs_of_nonneg (sub_nonneg.mpr hheight)] using
      xiHeatCassiniWoldResidualLogMeshNormingPotential_lipschitz_forward M N hMN

theorem xiHeatCassiniWoldResidualLogMeshNormingObservable_lipschitz :
    XiHeatCassiniPrimeLogMeshLipschitz 1
      xiHeatCassiniWoldResidualLogMeshNormingObservable := by
  intro N
  rw [xiHeatCassiniWoldResidualLogMeshNormingObservable,
    xiHeatCassiniWoldResidualLogMeshNormingObservable,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_sub_comm,
    abs_xiHeatCassiniWoldResidualLogMeshNormingPotential_succ_sub]
  simp

/-- The norming observable saturates every residual edge separately. -/
theorem xiHeatCassiniWoldResidualLogMeshCurrentAtom_normingObservable
    (N : ℕ) :
    xiHeatCassiniWoldResidualLogMeshCurrentAtom
        xiHeatCassiniWoldResidualLogMeshNormingObservable N =
      (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N : ℝ) := by
  rw [xiHeatCassiniWoldResidualLogMeshCurrentAtom,
    xiHeatCassiniWoldResidualLogMeshNormingObservable,
    xiHeatCassiniWoldResidualLogMeshNormingObservable,
    xiHeatCassiniWoldResidualLogMeshNormingPotential]
  push_cast
  norm_cast
  ring_nf
  rw [mul_deningerFreqSign_eq_abs]
  ring

/-- **Exact transport duality.**  The canonical source-sign potential attains the complete
prime-log transport cost, so the Kantorovich bound is sharp. -/
theorem xiHeatCassiniWoldResidualLogMeshCurrent_normingObservable_eq :
    xiHeatCassiniWoldResidualLogMeshCurrent
        xiHeatCassiniWoldResidualLogMeshNormingObservable =
      (xiHeatCassiniWoldResidualPrimeLogTotalVariation : ℂ) := by
  rw [xiHeatCassiniWoldResidualLogMeshCurrent,
    xiHeatCassiniWoldResidualPrimeLogTotalVariation,
    Complex.ofReal_tsum]
  apply tsum_congr
  exact xiHeatCassiniWoldResidualLogMeshCurrentAtom_normingObservable

/-- Exact norm of the source-sign witness. -/
theorem norm_xiHeatCassiniWoldResidualLogMeshCurrent_normingObservable :
    ‖xiHeatCassiniWoldResidualLogMeshCurrent
        xiHeatCassiniWoldResidualLogMeshNormingObservable‖ =
      xiHeatCassiniWoldResidualPrimeLogTotalVariation := by
  rw [xiHeatCassiniWoldResidualLogMeshCurrent_normingObservable_eq,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg xiHeatCassiniWoldResidualPrimeLogTotalVariation_nonneg]

/-- Constants carry no edge transport charge. -/
@[simp]
theorem xiHeatCassiniWoldResidualLogMeshCurrent_const (c : ℂ) :
    xiHeatCassiniWoldResidualLogMeshCurrent (fun _ => c) = 0 := by
  simp [xiHeatCassiniWoldResidualLogMeshCurrent,
    xiHeatCassiniWoldResidualLogMeshCurrentAtom]

/-- Fourier evaluation of the transport current is exactly the existing source-marked Hardy
carrier, with no divisor specialization. -/
theorem xiHeatCassiniWoldResidualLogMeshCurrent_negativePhase_eq
    (z : ℂ) :
    xiHeatCassiniWoldResidualLogMeshCurrent
        (fun N => xiHeatCassiniOrderedPrimeComplexNegativePhase N z) =
      xiHeatCassiniWoldResidualLowerHardyKernel z := by
  rfl

/-- On the real boundary the same current is the physical residual phase kernel. -/
theorem xiHeatCassiniWoldResidualLogMeshCurrent_realNegativePhase_eq
    (x : ℝ) :
    xiHeatCassiniWoldResidualLogMeshCurrent
        (fun N => xiHeatCassiniOrderedPrimeNegativePhase N x) =
      xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit x := by
  rw [← xiHeatCassiniWoldResidualLowerHardyKernel_ofReal]
  exact xiHeatCassiniWoldResidualLogMeshCurrent_negativePhase_eq (x : ℂ)

end

end RHTower

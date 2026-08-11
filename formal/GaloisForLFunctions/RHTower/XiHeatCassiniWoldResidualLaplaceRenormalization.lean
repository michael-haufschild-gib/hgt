import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualHardyPolarization
import GaloisForLFunctions.RHTower.WoldShellTangentTransfer
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodCollapse

/-!
# Laplace renormalization of the Route-T Wold residual

Rotating the lower Hardy coordinate by `z = -i s` turns every negative prime-log character into
a decaying Laplace character on `Re s > 0`.  Finite Abel transport then splits the residual into
two honest, absolutely convergent currents:

* the depth-one Wold prime current;
* the right-endpoint quadrature current of the ordered prime-log mesh.

Neither current remains finite at the wall `Re s = 0`.  Their difference does: after one explicit
holonomy counterterm it is exactly the lower Hardy kernel, hence vanishes to first order at the
wall origin.  This is the precise cancellation hidden by termwise estimates.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Decaying prime-log character in the safe Laplace half-plane. -/
def xiHeatCassiniOrderedPrimeLaplacePhase (N : ℕ) (s : ℂ) : ℂ :=
  xiHeatCassiniOrderedPrimeComplexNegativePhase N (-Complex.I * s)

theorem norm_xiHeatCassiniOrderedPrimeLaplacePhase
    (N : ℕ) (s : ℂ) :
    ‖xiHeatCassiniOrderedPrimeLaplacePhase N s‖ =
      Real.exp (-(s.re * xiMassNthPrimeLogHeight N)) := by
  rw [xiHeatCassiniOrderedPrimeLaplacePhase,
    xiHeatCassiniOrderedPrimeComplexNegativePhase, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]
  ring

theorem norm_xiHeatCassiniOrderedPrimeLaplacePhase_le_one
    (N : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖xiHeatCassiniOrderedPrimeLaplacePhase N s‖ ≤ 1 := by
  rw [norm_xiHeatCassiniOrderedPrimeLaplacePhase, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  exact neg_nonpos.mpr <| mul_nonneg hs (xiMassNthPrimeLogHeight_pos N).le

/-- One Wold atom in the safe Laplace coordinate. -/
def xiHeatCassiniWoldLaplaceAtom (s : ℂ) (N : ℕ) : ℂ :=
  (woldCoeff 1 (nthPrimeSubtype N) : ℂ) *
    xiHeatCassiniOrderedPrimeLaplacePhase N s

/-- One right-endpoint prime-log mesh cell in the safe Laplace coordinate. -/
def xiHeatCassiniLogMeshLaplaceAtom (s : ℂ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedPrimeLogGap N : ℂ) *
    xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s

/-- Complex finite Abel identity before taking the residual limit. -/
theorem xiHeatCassiniWoldResidualComplexFiniteAbel
    (N : ℕ) (z : ℂ) :
    (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
          xiHeatCassiniOrderedPrimeComplexNegativePhase N z +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z n =
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) *
          xiHeatCassiniOrderedPrimeComplexNegativePhase 0 z +
        ∑ n ∈ Finset.range N,
          ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (n + 1) -
              xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℝ) : ℂ) *
            xiHeatCassiniOrderedPrimeComplexNegativePhase (n + 1) z := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ] at ih ⊢
      rw [xiHeatCassiniWoldResidualComplexPhaseConnectionAtom]
      push_cast at ih ⊢
      calc
        (xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) : ℂ) *
              xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z +
            ((∑ n ∈ Finset.range N,
                xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z n) +
              (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
                (xiHeatCassiniOrderedPrimeComplexNegativePhase N z -
                  xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z)) =
            ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
                xiHeatCassiniOrderedPrimeComplexNegativePhase N z +
              ∑ n ∈ Finset.range N,
                xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z n) +
              ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) : ℂ) -
                xiHeatCassiniOrderedWoldResidualLogDiscrepancy N) *
                  xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z := by ring
        _ = _ := by rw [ih]; ring

/-- The residual primitive terminal vanishes throughout the closed safe Laplace half-plane. -/
theorem tendsto_xiHeatCassiniWoldResidualLaplaceTerminal
    {s : ℂ} (hs : 0 ≤ s.re) :
    Tendsto (fun N : ℕ =>
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
        xiHeatCassiniOrderedPrimeLaplacePhase N s) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hres := tendsto_xiHeatCassiniOrderedWoldResidualLogDiscrepancy.norm
  have hres' : Tendsto
      (fun N => ‖xiHeatCassiniOrderedWoldResidualLogDiscrepancy N‖)
      atTop (𝓝 0) := by simpa using hres
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) _ hres'
  filter_upwards with N
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (norm_xiHeatCassiniOrderedPrimeLaplacePhase_le_one N hs) (abs_nonneg _)

/-- Exponential damping makes ordered harmonic prime atoms summable for every positive Laplace
depth. -/
theorem summable_xiHeatCassiniOrderedHarmonicLaplaceMajor
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun N : ℕ =>
      xiMassPrimeHarmonicRealCoefficient (nthPrimeSubtype N) *
        Real.exp (-(s.re * xiMassNthPrimeLogHeight N))) := by
  have hprime := summable_logPrime_rpow (σ := 1 + s.re) (by linarith)
  have hordered := nthPrimeEquiv.summable_iff.mpr hprime
  apply hordered.congr
  intro N
  let p : ℝ := nthPrimeSubtype N
  have hp : 0 < p := nthPrimeSubtype_pos N
  symm
  change Real.log p / p * Real.exp (-(s.re * Real.log p)) =
    Real.log p * p ^ (-(1 + s.re))
  rw [Real.rpow_def_of_pos hp]
  rw [show Real.log p * -(1 + s.re) =
      -Real.log p + -(s.re * Real.log p) by ring, Real.exp_add]
  have hexpNegLog : Real.exp (-Real.log p) = 1 / p := by
    rw [Real.exp_neg, Real.exp_log hp]
    simp [one_div]
  rw [hexpNegLog]
  ring

/-- Depth-one Wold current is absolutely convergent after every positive Laplace shift. -/
theorem summable_xiHeatCassiniWoldLaplaceAtom
    {s : ℂ} (hs : 0 < s.re) :
    Summable (xiHeatCassiniWoldLaplaceAtom s) := by
  have hmajor := summable_xiHeatCassiniOrderedHarmonicLaplaceMajor hs
  apply hmajor.of_norm_bounded
  intro N
  rw [xiHeatCassiniWoldLaplaceAtom, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (woldCoeff_nonneg 1 _),
    norm_xiHeatCassiniOrderedPrimeLaplacePhase]
  exact mul_le_mul_of_nonneg_right
    (woldCoeff_one_le_harmonic_le_eight_mul_woldCoeff_one
      (nthPrimeSubtype N)).1
    (Real.exp_nonneg _)

/-- Right-endpoint ordered log-mesh quadrature is absolutely convergent for every positive
Laplace depth.  Only Bertrand and the reciprocal-height telescope are used. -/
theorem summable_xiHeatCassiniLogMeshLaplaceAtom
    {s : ℂ} (hs : 0 < s.re) :
    Summable (xiHeatCassiniLogMeshLaplaceAtom s) := by
  let C : ℝ := 4 / s.re ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hmajor :=
    summable_xiHeatCassiniOrderedPrimeLogGap_div_logHeight_sq.mul_left C
  apply hmajor.of_norm_bounded
  intro N
  let h : ℝ := xiMassNthPrimeLogHeight N
  let y : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hh : 0 < h := xiMassNthPrimeLogHeight_pos N
  have hy : 0 < y := xiMassNthPrimeLogHeight_pos (N + 1)
  have hhy : h ≤ y := nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have habsorb := Sieve.sq_mul_exp_neg_le_gen hs hh.le
  have hexp : Real.exp (-(s.re * y)) ≤ C / h ^ 2 := by
    calc
      Real.exp (-(s.re * y)) ≤ Real.exp (-(s.re * h)) := by
        apply Real.exp_le_exp.mpr
        exact neg_le_neg <| mul_le_mul_of_nonneg_left hhy hs.le
      _ ≤ C / h ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hh)]
        simpa only [C, mul_comm] using habsorb
  rw [xiHeatCassiniLogMeshLaplaceAtom, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hdelta,
    norm_xiHeatCassiniOrderedPrimeLaplacePhase]
  change delta * Real.exp (-(s.re * y)) ≤ C * (delta / h ^ 2)
  calc
    delta * Real.exp (-(s.re * y)) ≤ delta * (C / h ^ 2) :=
      mul_le_mul_of_nonneg_left hexp hdelta
    _ = C * (delta / h ^ 2) := by ring

/-- Local arithmetic increment is exactly Wold mass minus ordered log-mesh mass. -/
theorem xiHeatCassiniWoldResidualLaplaceIncrement_eq
    (s : ℂ) (N : ℕ) :
    ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℝ) : ℂ) *
        xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s =
      xiHeatCassiniWoldLaplaceAtom s (N + 1) -
        xiHeatCassiniLogMeshLaplaceAtom s N := by
  rw [xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub]
  unfold xiHeatCassiniWoldLaplaceAtom xiHeatCassiniLogMeshLaplaceAtom
    xiHeatCassiniOrderedPrimeLogGap
  push_cast
  ring

theorem summable_xiHeatCassiniWoldResidualLaplaceIncrement
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun N : ℕ =>
      ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
          xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℝ) : ℂ) *
        xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s) := by
  have hw := (summable_xiHeatCassiniWoldLaplaceAtom hs).comp_injective Nat.succ_injective
  have hm := summable_xiHeatCassiniLogMeshLaplaceAtom hs
  exact (hw.sub hm).congr fun N =>
    (xiHeatCassiniWoldResidualLaplaceIncrement_eq s N).symm

/-- Complete depth-one Wold current in the safe Laplace half-plane. -/
def xiHeatCassiniWoldLaplaceCurrent (s : ℂ) : ℂ :=
  ∑' N : ℕ, xiHeatCassiniWoldLaplaceAtom s N

/-- Complete right-endpoint ordered prime-log quadrature current. -/
def xiHeatCassiniLogMeshLaplaceCurrent (s : ℂ) : ℂ :=
  ∑' N : ℕ, xiHeatCassiniLogMeshLaplaceAtom s N

/-- Full Wold current is its first atom plus successor tail. -/
theorem xiHeatCassiniWoldLaplaceCurrent_eq_head_add_tail
    {s : ℂ} (hs : 0 < s.re) :
    xiHeatCassiniWoldLaplaceCurrent s =
      xiHeatCassiniWoldLaplaceAtom s 0 +
        ∑' N : ℕ, xiHeatCassiniWoldLaplaceAtom s (N + 1) := by
  rw [xiHeatCassiniWoldLaplaceCurrent]
  symm
  simpa using (summable_xiHeatCassiniWoldLaplaceAtom hs).sum_add_tsum_nat_add 1

/-- Residual primitive at the first prime differs from its Wold mass by exactly the log-height
base point and limiting holonomy. -/
theorem xiHeatCassiniWoldResidualLogDiscrepancy_zero_sub_woldCoeff :
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 -
        woldCoeff 1 (nthPrimeSubtype 0) =
      -(xiMassNthPrimeLogHeight 0 + xiHeatCassiniWoldLogHolonomyConstant) := by
  simp [xiHeatCassiniOrderedWoldResidualLogDiscrepancy,
    xiHeatCassiniOrderedWoldLogDiscrepancy,
    xiHeatCassiniOrderedWoldPartialMass]
  ring

/-- **Exact safe-half-plane renormalization identity.**  Wold prime current minus log-mesh
quadrature, after the canonical holonomy counterterm, is literally the rotated Hardy kernel. -/
theorem xiHeatCassiniWoldResidualLowerHardyKernel_negI_mul_eq_renormalizedLaplace
    {s : ℂ} (hs : 0 < s.re) :
    xiHeatCassiniWoldResidualLowerHardyKernel (-Complex.I * s) =
      xiHeatCassiniWoldLaplaceCurrent s -
        xiHeatCassiniLogMeshLaplaceCurrent s -
        ((xiMassNthPrimeLogHeight 0 + xiHeatCassiniWoldLogHolonomyConstant : ℝ) : ℂ) *
          xiHeatCassiniOrderedPrimeLaplacePhase 0 s := by
  have hedge := summable_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
    (z := -Complex.I * s) (by simp; linarith)
  have hterminal := tendsto_xiHeatCassiniWoldResidualLaplaceTerminal hs.le
  have hleftPartial := hedge.hasSum_iff_tendsto_nat.mp hedge.hasSum
  have hleft := hterminal.add hleftPartial
  have hleft' : Tendsto (fun N : ℕ =>
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
          xiHeatCassiniOrderedPrimeLaplacePhase N s +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniWoldResidualComplexPhaseConnectionAtom (-Complex.I * s) n)
      atTop (𝓝 (xiHeatCassiniWoldResidualLowerHardyKernel (-Complex.I * s))) := by
    simpa [xiHeatCassiniWoldResidualLowerHardyKernel] using hleft
  have hinc := summable_xiHeatCassiniWoldResidualLaplaceIncrement hs
  have hrightPartial := hinc.hasSum_iff_tendsto_nat.mp hinc.hasSum
  have hconstant : Tendsto (fun _ : ℕ =>
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) *
        xiHeatCassiniOrderedPrimeLaplacePhase 0 s) atTop
      (𝓝 ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) *
        xiHeatCassiniOrderedPrimeLaplacePhase 0 s)) := tendsto_const_nhds
  have hright := hconstant.add hrightPartial
  have hfinite : ∀ N : ℕ,
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
          xiHeatCassiniOrderedPrimeLaplacePhase N s +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniWoldResidualComplexPhaseConnectionAtom (-Complex.I * s) n =
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) *
          xiHeatCassiniOrderedPrimeLaplacePhase 0 s +
        ∑ n ∈ Finset.range N,
          ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (n + 1) -
              xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℝ) : ℂ) *
            xiHeatCassiniOrderedPrimeLaplacePhase (n + 1) s := by
    intro N
    simpa only [xiHeatCassiniOrderedPrimeLaplacePhase] using
      xiHeatCassiniWoldResidualComplexFiniteAbel N (-Complex.I * s)
  have habelfinal :
      xiHeatCassiniWoldResidualLowerHardyKernel (-Complex.I * s) =
        (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) *
            xiHeatCassiniOrderedPrimeLaplacePhase 0 s +
          ∑' N : ℕ,
            ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
                xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℝ) : ℂ) *
              xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s := by
    apply tendsto_nhds_unique hleft'
    apply hright.congr'
    filter_upwards with N
    exact (hfinite N).symm
  rw [habelfinal]
  have hw := (summable_xiHeatCassiniWoldLaplaceAtom hs).comp_injective Nat.succ_injective
  have hm := summable_xiHeatCassiniLogMeshLaplaceAtom hs
  rw [show (∑' N : ℕ,
      ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
          xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℝ) : ℂ) *
        xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s) =
      (∑' N : ℕ, xiHeatCassiniWoldLaplaceAtom s (N + 1)) -
        xiHeatCassiniLogMeshLaplaceCurrent s by
      rw [xiHeatCassiniLogMeshLaplaceCurrent]
      calc
        (∑' N : ℕ,
          ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
              xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℝ) : ℂ) *
            xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s) =
            ∑' N : ℕ, (xiHeatCassiniWoldLaplaceAtom s (N + 1) -
              xiHeatCassiniLogMeshLaplaceAtom s N) := by
                apply tsum_congr
                exact xiHeatCassiniWoldResidualLaplaceIncrement_eq s
        _ = _ := hw.tsum_sub hm]
  rw [xiHeatCassiniWoldLaplaceCurrent_eq_head_add_tail hs,
    xiHeatCassiniWoldLaplaceAtom]
  push_cast
  have hzeroC := congrArg (fun x : ℝ => (x : ℂ))
    xiHeatCassiniWoldResidualLogDiscrepancy_zero_sub_woldCoeff
  push_cast at hzeroC
  have hE : (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) =
      (woldCoeff 1 (nthPrimeSubtype 0) : ℂ) -
        ((xiMassNthPrimeLogHeight 0 : ℂ) +
          (xiHeatCassiniWoldLogHolonomyConstant : ℂ)) := by
    calc
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) =
          (woldCoeff 1 (nthPrimeSubtype 0) : ℂ) +
            ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) -
              (woldCoeff 1 (nthPrimeSubtype 0) : ℂ)) := by ring
      _ = _ := by rw [hzeroC]; ring
  rw [hE]
  ring

/-- First-order cancellation of the two wall-divergent currents is uniform throughout the safe
half-plane. -/
theorem norm_xiHeatCassiniWoldLaplace_sub_logMesh_sub_holonomy_le
    {s : ℂ} (hs : 0 < s.re) :
    ‖xiHeatCassiniWoldLaplaceCurrent s -
        xiHeatCassiniLogMeshLaplaceCurrent s -
        ((xiMassNthPrimeLogHeight 0 + xiHeatCassiniWoldLogHolonomyConstant : ℝ) : ℂ) *
          xiHeatCassiniOrderedPrimeLaplacePhase 0 s‖ ≤
      2 * xiHeatCassiniWoldResidualPrimeLogTotalVariation * ‖s‖ := by
  rw [← xiHeatCassiniWoldResidualLowerHardyKernel_negI_mul_eq_renormalizedLaplace hs]
  have h := norm_xiHeatCassiniWoldResidualLowerHardyKernel_le
    (z := -Complex.I * s) (by simp; linarith)
  simpa using h

/-- The renormalized Wold-minus-mesh symbol has a bounded divided boundary value. -/
theorem norm_xiHeatCassiniWoldLaplaceRenormalizedQuotient_le
    {s : ℂ} (hs : 0 < s.re) :
    ‖(xiHeatCassiniWoldLaplaceCurrent s -
          xiHeatCassiniLogMeshLaplaceCurrent s -
          ((xiMassNthPrimeLogHeight 0 + xiHeatCassiniWoldLogHolonomyConstant : ℝ) : ℂ) *
            xiHeatCassiniOrderedPrimeLaplacePhase 0 s) / s‖ ≤
      2 * xiHeatCassiniWoldResidualPrimeLogTotalVariation := by
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    simp at hs
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hs0)]
  exact (norm_xiHeatCassiniWoldLaplace_sub_logMesh_sub_holonomy_le hs).trans_eq (by ring)

end

end RHTower

import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSignedCurvatureMeasure
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadWallGramLightConeCovariantTransmutation
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadSignedCompletedErrorGammaProducer

/-!
# Actual-head landing and compactification of the FU signed curvature cells

The discrete signed curvature cells from CCM-FU admit a literal Route-O landing on matched actual
Gamma heads.  At prime powers, multiplication by the wall rate turns the critical Mellin atom into
the covariant wall-chord polar jet, leaving the continuous Suzuki curvature on the same matched
head.

This landing also exposes a sharp obstruction: every signed curvature cell is uniformly bounded,
while the matched Suzuki current is absolutely summable.  Their actual-head product is therefore
absolutely summable.  Thus post-matching quadratic damping compactifies the cofinal FU source and
cannot itself retain the RH-bearing Green growth.  A viable Route-O landing must occur before this
damping, in a source-faithful wall-light/Robin channel.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set
open GaloisForLFunctions.RHTower
open scoped Interval

/-- Every event cell of the signed prime--archimedean curvature measure has modulus at most two. -/
theorem abs_suzukiCheckpointSignedCurvatureCell_le_two
    {N : ℕ} (hN : 2 ≤ N) :
    |suzukiCheckpointSignedCurvatureCell N| ≤ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    (Real.log_le_log_iff hNpos hNp1pos).mpr (by exact_mod_cast Nat.le_succ N)
  have hFTC : (∫ t in Real.log (N : ℝ)..Real.log ((N + 1 : ℕ) : ℝ),
      screwRegularKernel t) =
      suzukiCheckpointReservoirDeriv (Real.log ((N + 1 : ℕ) : ℝ)) -
        suzukiCheckpointReservoirDeriv (Real.log (N : ℝ)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hlog] at ht
      exact hasDerivAt_suzukiCheckpointReservoirDeriv (hlogNpos.trans_le ht.1)
    · apply ContinuousOn.intervalIntegrable
      exact continuousOn_screwRegularKernel.mono (by
        intro t ht
        rw [Set.uIcc_of_le hlog] at ht
        exact hlogNpos.trans_le ht.1)
  have harch0 : 0 ≤
      suzukiCheckpointReservoirDeriv (Real.log ((N + 1 : ℕ) : ℝ)) -
        suzukiCheckpointReservoirDeriv (Real.log (N : ℝ)) := by
    rw [← hFTC]
    apply intervalIntegral.integral_nonneg hlog
    intro t ht
    exact (suzukiCheckpointReservoirDeriv_curvature_pos_of_log_two_le
      ((suzukiCheckpointCell_subset_Ici_log_two hN) ⟨ht.1, ht.2⟩)).le
  have hgap : Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) ≤ 1 / (N : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hNp1pos hNpos)
    rw [Real.log_div hNp1pos.ne' hNpos.ne'] at h
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) / (N : ℝ) - 1 := h
      _ = 1 / (N : ℝ) := by
        push_cast
        field_simp [hNpos.ne']
        ring
  have harchLe :
      suzukiCheckpointReservoirDeriv (Real.log ((N + 1 : ℕ) : ℝ)) -
          suzukiCheckpointReservoirDeriv (Real.log (N : ℝ)) ≤ 2 := by
    have hloglt : Real.log (N : ℝ) < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.strictMonoOn_log hNpos hNp1pos
        (by exact_mod_cast (show N < N + 1 by omega))
    have hcont : ContinuousOn suzukiCheckpointReservoirDeriv
        (Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ))) := by
      intro t ht
      exact (hasDerivAt_suzukiCheckpointReservoirDeriv
        (hlogNpos.trans_le ht.1)).continuousAt.continuousWithinAt
    have hderiv : ∀ t ∈ Ioo (Real.log (N : ℝ))
        (Real.log ((N + 1 : ℕ) : ℝ)),
        HasDerivAt suzukiCheckpointReservoirDeriv (screwRegularKernel t) t := by
      intro t ht
      exact hasDerivAt_suzukiCheckpointReservoirDeriv (hlogNpos.trans ht.1)
    obtain ⟨c, hc, hratio⟩ :=
      exists_hasDerivAt_eq_slope suzukiCheckpointReservoirDeriv
        screwRegularKernel hloglt hcont hderiv
    have hcLe : c ≤ Real.log ((N + 1 : ℕ) : ℝ) := hc.2.le
    have hKLe : screwRegularKernel c ≤ Real.exp (c / 2) := by
      rw [screwRegularKernel]
      exact sub_le_self _ (div_nonneg (Real.exp_pos _).le
        (one_sub_exp_neg_two_mul_pos (hlogNpos.trans hc.1)).le)
    have hexpLe : Real.exp (c / 2) ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) := by
      have hhalf : c / 2 ≤ Real.log ((N + 1 : ℕ) : ℝ) / 2 := by linarith
      have h := Real.exp_le_exp.mpr hhalf
      rw [← Real.log_sqrt hNp1pos.le,
        Real.exp_log (Real.sqrt_pos.mpr hNp1pos)] at h
      exact h
    have hsqrtLe : Real.sqrt ((N + 1 : ℕ) : ℝ) / (N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hNpos]
      have hsqrt : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by
            push_cast
            ring
          rw [hcast]
          have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
          nlinarith
      nlinarith
    have hgap0 : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) :=
      sub_nonneg.mpr hlog
    calc
      _ = screwRegularKernel c *
          (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) := by
            have hgapne :
                Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) ≠ 0 :=
              sub_ne_zero.mpr hloglt.ne'
            rw [hratio]
            field_simp [hgapne]
      _ ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) *
          (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) := by
            gcongr
            exact hKLe.trans hexpLe
      _ ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) * (1 / (N : ℝ)) := by
            gcongr
      _ = Real.sqrt ((N + 1 : ℕ) : ℝ) / (N : ℝ) := by ring
      _ ≤ 2 := hsqrtLe
  have hw0 := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer (N + 1)
  have hw2 := criticalMellinAtomWeight_le_two (N + 1)
  unfold suzukiCheckpointSignedCurvatureCell
  rw [hFTC, abs_le]
  constructor <;> linarith

/-- Type-level absolute summability missing from the prior signed-current declaration. -/
theorem summable_abs_ccmActualHeadMatchedSuzukiCurrent
    (f : SoninL2) :
    Summable (fun n : ℕ => |ccmActualHeadMatchedSuzukiCurrent n f|) := by
  have hbase := summable_vonMangoldt_logPow
    (σ := (3 / 2 : ℝ)) (by norm_num) 1
  have hmajor := hbase.mul_left ((1 : ℝ) / 4 * ‖f‖ ^ 2)
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hmajor
  refine (abs_ccmActualHeadMatchedSuzukiCurrent_le_quadratic n f).trans ?_
  have hmaj := criticalMellinAtomWeight_sq_div_exp_le_logMajorant n
  have hnonneg : 0 ≤ (1 / 4 : ℝ) * ‖f‖ ^ 2 := by positivity
  calc
    criticalMellinAtomWeight n ^ 2 /
          (4 * Real.exp (Real.log n / 2)) * ‖f‖ ^ 2 =
        ((1 / 4 : ℝ) * ‖f‖ ^ 2) *
          (criticalMellinAtomWeight n ^ 2 /
            Real.exp (Real.log n / 2)) := by ring
    _ ≤ ((1 / 4 : ℝ) * ‖f‖ ^ 2) *
        (((ArithmeticFunction.vonMangoldt n : ℝ) *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) * Real.log n) :=
      mul_le_mul_of_nonneg_left hmaj hnonneg
    _ = (1 / 4 * ‖f‖ ^ 2) *
        (ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) * Real.log n ^ 1) := by ring

/-- Actual-head lift of the signed Suzuki curvature cell after matched prime--polar damping. -/
def ccmFUSignedCurvatureMatchedCurrent (N : ℕ) (f : SoninL2) : ℝ :=
  suzukiCheckpointSignedCurvatureCell N *
    ccmActualHeadMatchedSuzukiCurrent (N + 1) f

/-- Quadratic matched-current damping makes the actual-head lift absolutely summable. -/
theorem summable_ccmFUSignedCurvatureMatchedCurrent (f : SoninL2) :
    Summable (ccmFUSignedCurvatureMatchedCurrent · f) := by
  have hshift : Summable (fun N : ℕ =>
      |ccmActualHeadMatchedSuzukiCurrent (N + 1) f|) :=
    (summable_nat_add_iff 1).mpr (summable_abs_ccmActualHeadMatchedSuzukiCurrent f)
  have hmajor := hshift.mul_left 2
  refine Summable.of_norm_bounded_eventually_nat hmajor ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  rw [ccmFUSignedCurvatureMatchedCurrent, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (abs_suzukiCheckpointSignedCurvatureCell_le_two hN) (abs_nonneg _)

/-- Prime-power specialization of the shared FU/O source. -/
def ccmActualHeadPrimePowerSignedCurvatureEventCurrent
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  suzukiCheckpointSignedCurvatureCell (n - 1) *
    ccmActualHeadMatchedSuzukiCurrent n f

/-- Division-free FU-to-Route-O landing. The same signed curvature cell becomes archimedean
curvature on the actual matched head minus the literal wall-chord polar jet. -/
theorem two_pi_log_mul_primePowerSignedCurvatureEventCurrent_eq_arch_sub_wallJet
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    let n := xiGammaEulerValuationNat (p, e)
    (2 * Real.pi * Real.log n) *
        ccmActualHeadPrimePowerSignedCurvatureEventCurrent p e f =
      (2 * Real.pi * Real.log n) *
          (∫ t in Real.log ((n - 1 : ℕ) : ℝ)..Real.log (n : ℝ),
            screwRegularKernel t) *
          ccmActualHeadMatchedSuzukiCurrent n f -
        ccmActualHeadWallChordPolarJetCurrent p e f := by
  let n := xiGammaEulerValuationNat (p, e)
  have hn : 2 ≤ n := one_lt_xiGammaEulerValuationNat p e
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [ccmActualHeadWallChordPolarJetCurrent_eq_rate_mul_matchedSuzukiCurrent]
  unfold ccmActualHeadPrimePowerSignedCurvatureEventCurrent
    ccmActualHeadWallPolarJetRate suzukiCheckpointSignedCurvatureCell
  dsimp only [n]
  rw [hsucc]
  ring

end RHTower

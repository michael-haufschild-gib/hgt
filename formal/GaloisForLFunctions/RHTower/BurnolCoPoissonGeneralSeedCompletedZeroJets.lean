import GaloisForLFunctions.RHTower.BurnolCoPoissonCompletedZeroJets
import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedMellin
import GaloisForLFunctions.RHTower.BurnolCoPoissonReciprocalSeedLanding
import Mathlib.Analysis.MellinTransform

/-!
# Completed zero jets for every literal Burnol co-Poisson seed

`BurnolCoPoissonCompletedZeroJets` established exact zero multiplicity for
explicit logarithmic subwindows.  A completeness argument needs the same
lower-jet annihilation for every compact seed in the literal co-Poisson source
class.  The missing analytic point is that the seed Mellin factor is
holomorphic, not merely defined pointwise.

Here compact multiplicative support gives eventual zero at both Mellin ends.
Mathlib's Mellin differentiability theorem therefore proves holomorphy on the
full open strip.  Multiplication by the exact zeta factor then kills every
lower jet at an actual right-half Xi divisor.

This is a source-level theorem.  It does not identify the *closed* span of
the jet evaluators with `P_aᗮ`; that remaining equality requires the bounded
higher-jet evaluator and aperture-completeness parts of Burnol's theorem.
-/

open Complex Real MeasureTheory Set Filter Topology Asymptotics

namespace RHTower

noncomputable section

private theorem burnolSeed_eventuallyEq_zero_atTop {b : ℝ}
    (src : BurnolCoPoissonSource b) : src.seed =ᶠ[atTop] 0 := by
  filter_upwards [eventually_gt_atTop (b⁻¹)] with t ht
  by_contra hne
  have hmem := src.seed_support (Function.mem_support.mpr hne)
  exact (not_le_of_gt ht) hmem.2

private theorem burnolSeed_eventuallyEq_zero_nhdsGT {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) : src.seed =ᶠ[𝓝[>] 0] 0 := by
  filter_upwards [Ioo_mem_nhdsGT hb] with t ht
  by_contra hne
  have hmem := src.seed_support (Function.mem_support.mpr hne)
  exact (not_le_of_gt ht.2) hmem.1

private theorem burnolSeed_isBigO_top {b : ℝ}
    (src : BurnolCoPoissonSource b) :
    src.seed =O[atTop] fun t : ℝ => t ^ (-1 : ℝ) := by
  exact (isBigO_zero (fun t : ℝ => t ^ (-1 : ℝ)) atTop).congr'
    (burnolSeed_eventuallyEq_zero_atTop src).symm EventuallyEq.rfl

private theorem burnolSeed_isBigO_bot {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) :
    src.seed =O[𝓝[>] 0] fun _t : ℝ => (1 : ℝ) := by
  exact (isBigO_zero (fun _t : ℝ => (1 : ℝ)) (𝓝[>] 0)).congr'
    (burnolSeed_eventuallyEq_zero_nhdsGT hb src).symm EventuallyEq.rfl

/-- The Mellin transform of every compact literal source seed is
holomorphic on the full critical strip. -/
theorem differentiableOn_mellin_burnolCoPoissonSeed {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) :
    DifferentiableOn ℂ (mellin src.seed) {w : ℂ | 0 < w.re ∧ w.re < 1} := by
  intro w hw
  exact (mellin_differentiableAt_of_isBigO_rpow
    (src.seed_integrable.locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (burnolSeed_isBigO_top src) hw.2 (by simpa using burnolSeed_isBigO_bot hb src) hw.1).differentiableWithinAt

/-- The factor multiplying zeta in the general co-Poisson source formula is
holomorphic at every point of the open critical strip. -/
theorem analyticAt_burnolCoPoissonSeedMellin {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    AnalyticAt ℂ (fun z : ℂ => ∫ u in Ioi (0 : ℝ),
      src.seed u * ((u : ℝ) : ℂ) ^ (-z)) w := by
  have hUopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hseed : AnalyticAt ℂ (mellin src.seed) (1 - w) := by
    apply (differentiableOn_mellin_burnolCoPoissonSeed hb src).analyticOnNhd hUopen
    constructor <;> simp only [Complex.sub_re, Complex.one_re]
    · linarith
    · linarith
  have hcomp : AnalyticAt ℂ (fun z : ℂ => mellin src.seed (1 - z)) w := by
    exact AnalyticAt.comp (g := mellin src.seed) (f := fun z : ℂ => 1 - z) (x := w)
      hseed (by fun_prop)
  have heq : (fun z : ℂ => ∫ u in Ioi (0 : ℝ),
      src.seed u * ((u : ℝ) : ℂ) ^ (-z)) =
      (fun z : ℂ => mellin src.seed (1 - z)) := by
    funext z
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change src.seed u * (u : ℂ) ^ (-z) = (u : ℂ) ^ (1 - z - 1) * src.seed u
    rw [show (1 : ℂ) - z - 1 = -z by ring]
    ring
  rw [heq]
  exact hcomp

/-- The literal completed Mellin germ of an arbitrary compact co-Poisson
source. -/
def burnolCoPoissonSourceCompletedMellinGerm {b : ℝ}
    (src : BurnolCoPoissonSource b) (w : ℂ) : ℂ :=
  mellinCompletionFactor w *
    (riemannZeta w * ∫ u in Ioi (0 : ℝ), src.seed u * ((u : ℝ) : ℂ) ^ (-w))

/-- Every lower jet of the completed Mellin germ of a literal compact
co-Poisson source vanishes at an actual right-half Xi divisor. -/
theorem iteratedDeriv_burnolCoPoissonSourceCompletedMellinGerm_eq_zero_of_lt
    {b : ℝ} (hb : 0 < b) (src : BurnolCoPoissonSource b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    iteratedDeriv j (burnolCoPoissonSourceCompletedMellinGerm src) (rho : ℂ) = 0 := by
  have hrho0 : 0 < (rho : ℂ).re := by linarith
  have hrho1 : (rho : ℂ).re < 1 := (xi_divisor_support_re_mem_open_unit rho).2
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact (ne_of_lt hrho1) hre
  have hgamma : ContDiffAt ℂ j mellinCompletionFactor (rho : ℂ) :=
    (analyticAt_mellinCompletionFactor_of_re_pos hrho0).contDiffAt
  have hzeta : ContDiffAt ℂ j riemannZeta (rho : ℂ) :=
    (analyticOn_riemannZeta (rho : ℂ) hne1).contDiffAt
  have hseed : ContDiffAt ℂ j (fun w : ℂ => ∫ u in Ioi (0 : ℝ),
      src.seed u * ((u : ℝ) : ℂ) ^ (-w)) (rho : ℂ) :=
    (analyticAt_burnolCoPoissonSeedMellin hb src hrho0 hrho1).contDiffAt
  have hrest : ContDiffAt ℂ j (riemannZeta * fun w : ℂ => ∫ u in Ioi (0 : ℝ),
      src.seed u * ((u : ℝ) : ℂ) ^ (-w)) (rho : ℂ) := hzeta.mul hseed
  change iteratedDeriv j
    (mellinCompletionFactor *
      (riemannZeta * fun w : ℂ => ∫ u in Ioi (0 : ℝ),
        src.seed u * ((u : ℝ) : ℂ) ^ (-w))) (rho : ℂ) = 0
  rw [iteratedDeriv_mul hgamma hrest]
  apply Finset.sum_eq_zero
  intro i hi
  have hile : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hinner : iteratedDeriv (j - i)
      (riemannZeta * fun w : ℂ => ∫ u in Ioi (0 : ℝ),
        src.seed u * ((u : ℝ) : ℂ) ^ (-w)) (rho : ℂ) = 0 := by
    have hzeta' : ContDiffAt ℂ (j - i) riemannZeta (rho : ℂ) :=
      hzeta.of_le (by exact tsub_le_self)
    have hseed' : ContDiffAt ℂ (j - i) (fun w : ℂ => ∫ u in Ioi (0 : ℝ),
        src.seed u * ((u : ℝ) : ℂ) ^ (-w)) (rho : ℂ) :=
      hseed.of_le (by exact tsub_le_self)
    rw [iteratedDeriv_mul hzeta' hseed']
    apply Finset.sum_eq_zero
    intro k hk
    have hkle : k ≤ j - i := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hklj : k ≤ j := le_trans hkle (Nat.sub_le _ _)
    have hklt : k < burnolCoPoissonXiConormalOrder rho := lt_of_le_of_lt hklj hj
    rw [(riemannZeta_exact_jet_at_burnolCoPoissonXiConormalOrder rho).1 k hklt]
    simp
  rw [hinner]
  ring

/-- Every lower jet of the actual completed co-Poisson evaluation vanishes
for every literal compact source at a right-half Xi divisor. -/
theorem iteratedDeriv_soninMellinEvaluation_burnolCoPoissonSource_eq_zero_of_lt
    {b : ℝ} (hb : 0 < b) (src : BurnolCoPoissonSource b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    iteratedDeriv j
      (fun w : ℂ => soninMellinEvaluation w
        (((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2)) (rho : ℂ) = 0 := by
  let U : Set ℂ := {w | 1 / 2 < w.re ∧ w.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hrhoU : (rho : ℂ) ∈ U := ⟨hright, (xi_divisor_support_re_mem_open_unit rho).2⟩
  have hEq : Set.EqOn
      (fun w : ℂ => soninMellinEvaluation w
        (((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2))
      (burnolCoPoissonSourceCompletedMellinGerm src) U := by
    intro w hw
    exact soninMellinEvaluation_burnolCoPoissonSource hb src hw.1 hw.2
  rw [hEq.iteratedDeriv_of_isOpen hUopen j hrhoU]
  exact iteratedDeriv_burnolCoPoissonSourceCompletedMellinGerm_eq_zero_of_lt
    hb src rho hright hj

/-- Both branches of every literal cosine-closed co-Poisson generator have
all lower Xi jets equal to zero. -/
theorem iteratedDeriv_soninMellinEvaluation_burnolCoPoissonGenerator_eq_zero_of_lt
    {b : ℝ} (hb : 0 < b) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonGeneratorSet b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    iteratedDeriv j (fun w : ℂ => soninMellinEvaluation w ((f : evenSubspace) : SoninL2))
      (rho : ℂ) = 0 := by
  rcases hf with ⟨src, rfl | rfl⟩
  · exact iteratedDeriv_soninMellinEvaluation_burnolCoPoissonSource_eq_zero_of_lt
      hb src rho hright hj
  · simpa only [BurnolCoPoissonSource.reciprocal_vector,
      coe_burnolExtendedSoninCosine] using
      (iteratedDeriv_soninMellinEvaluation_burnolCoPoissonSource_eq_zero_of_lt
        hb (src.reciprocal hb) rho hright hj)

end

end RHTower

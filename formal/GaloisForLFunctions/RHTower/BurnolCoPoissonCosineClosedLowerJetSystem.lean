import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedCompletedZeroJets
import GaloisForLFunctions.RHTower.BurnolSoninContinuousEvaluation

/-!
# Algebraic cosine-closed lower zero-jet system

The literal co-Poisson source class is closed under its cosine branch.  Each
generator has a completed Mellin germ analytic on the right critical strip and
all jets below the exact zeta multiplicity vanish at an actual Xi divisor.

This file packages those facts into a submodule: finite source combinations
retain both an analytic local germ and every lower-jet zero.  Thus the
cosine-closed **algebraic** source system satisfies Burnol's zero-jet
annihilation relations without any postulated evaluator.

The topological closure is deliberately not claimed here.  Passing this
statement through the closure requires a separately proved bounded higher-jet
evaluator on `L_a`; that is the remaining analytic component of the full
Burnol completeness theorem.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- On the aperture strip, completed Mellin evaluation is additive for two
actual extended Sonine vectors. -/
theorem soninMellinEvaluation_add_of_mem_extendedSonin
    {b : ℝ} (hb : 0 < b) {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {f g : evenSubspace} (hf : f ∈ soninExtendedSpace b) (hg : g ∈ soninExtendedSpace b) :
    soninMellinEvaluation w (((f + g : evenSubspace) : SoninL2) : ℝ → ℂ) =
      soninMellinEvaluation w ((f : SoninL2) : ℝ → ℂ) +
        soninMellinEvaluation w ((g : SoninL2) : ℝ → ℂ) := by
  let f' : soninExtendedSpace b := ⟨f, hf⟩
  let g' : soninExtendedSpace b := ⟨g, hg⟩
  simpa [f', g'] using soninMellinEvaluation_add_extendedSonin hlo hhi hb f' g'

/-- Scalar multiplication of an extended Sonine vector commutes with its
completed Mellin evaluation. -/
theorem soninMellinEvaluation_smul_of_mem_extendedSonin
    {b : ℝ} {w : ℂ} (c : ℂ) {f : evenSubspace} (hf : f ∈ soninExtendedSpace b) :
    soninMellinEvaluation w (((c • f : evenSubspace) : SoninL2) : ℝ → ℂ) =
      c * soninMellinEvaluation w ((f : SoninL2) : ℝ → ℂ) := by
  let f' : soninExtendedSpace b := ⟨f, hf⟩
  simpa [f'] using soninMellinEvaluation_smul_extendedSonin c f'

/-- Extended Sonine vectors whose completed Mellin evaluation has a local
analytic germ with vanishing `j`th jet at `rho`. -/
def burnolCoPoissonLowerXiJetAnnihilator (b : ℝ) (rho : XiDivisorSupport)
    (j : ℕ) (hb : 0 < b) : Submodule ℂ evenSubspace where
  carrier := {f | f ∈ soninExtendedSpace b ∧
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (rho : ℂ) ∧
      Set.EqOn (fun w : ℂ => soninMellinEvaluation w ((f : evenSubspace) : SoninL2)) F
        {w : ℂ | 1 / 2 < w.re ∧ w.re < 1} ∧
      iteratedDeriv j F (rho : ℂ) = 0}
  zero_mem' := by
    refine ⟨(soninExtendedSpace b).zero_mem, fun _ => 0, analyticAt_const, ?_, by simp⟩
    intro w hw
    simp [soninMellinEvaluation]
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨hfE, F, hFan, hFEq, hFzero⟩
    rcases hg with ⟨hgE, G, hGan, hGEq, hGzero⟩
    refine ⟨(soninExtendedSpace b).add_mem hfE hgE, F + G, hFan.add hGan, ?_, ?_⟩
    · intro w hw
      change soninMellinEvaluation w (((f + g : evenSubspace) : SoninL2) : ℝ → ℂ) =
        F w + G w
      have hFw := hFEq hw
      have hGw := hGEq hw
      change soninMellinEvaluation w ((f : SoninL2) : ℝ → ℂ) = F w at hFw
      change soninMellinEvaluation w ((g : SoninL2) : ℝ → ℂ) = G w at hGw
      rw [soninMellinEvaluation_add_of_mem_extendedSonin hb hw.1 hw.2 hfE hgE, hFw, hGw]
    · rw [iteratedDeriv_add hFan.contDiffAt hGan.contDiffAt, hFzero, hGzero, add_zero]
  smul_mem' := by
    intro c f hf
    rcases hf with ⟨hfE, F, hFan, hFEq, hFzero⟩
    refine ⟨(soninExtendedSpace b).smul_mem c hfE, c • F, hFan.const_smul, ?_, ?_⟩
    · intro w hw
      change soninMellinEvaluation w (((c • f : evenSubspace) : SoninL2) : ℝ → ℂ) =
        c * F w
      have hFw := hFEq hw
      change soninMellinEvaluation w ((f : SoninL2) : ℝ → ℂ) = F w at hFw
      rw [soninMellinEvaluation_smul_of_mem_extendedSonin c hfE, hFw]
    · rw [iteratedDeriv_const_smul hFan.contDiffAt c, hFzero, smul_zero]

/-- The literal co-Poisson completed germ is analytic at every right-half Xi
divisor. -/
theorem analyticAt_burnolCoPoissonSourceCompletedMellinGerm_of_right
    {b : ℝ} (hb : 0 < b) (src : BurnolCoPoissonSource b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    AnalyticAt ℂ (burnolCoPoissonSourceCompletedMellinGerm src) (rho : ℂ) := by
  have hrho0 : 0 < (rho : ℂ).re := by linarith
  have hrho1 : (rho : ℂ).re < 1 := (xi_divisor_support_re_mem_open_unit rho).2
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact (ne_of_lt hrho1) hre
  exact (analyticAt_mellinCompletionFactor_of_re_pos hrho0).mul
    ((analyticOn_riemannZeta (rho : ℂ) hne1).mul
      (analyticAt_burnolCoPoissonSeedMellin hb src hrho0 hrho1))

/-- Every literal co-Poisson source belongs to the lower Xi-jet
annihilator. -/
theorem burnolCoPoissonSource_mem_lowerXiJetAnnihilator
    {b : ℝ} (hb : 0 < b) (src : BurnolCoPoissonSource b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    (src.vector : evenSubspace) ∈ burnolCoPoissonLowerXiJetAnnihilator b rho j hb := by
  refine ⟨src.vector.property, burnolCoPoissonSourceCompletedMellinGerm src,
    analyticAt_burnolCoPoissonSourceCompletedMellinGerm_of_right hb src rho hright, ?_, ?_⟩
  · intro w hw
    exact soninMellinEvaluation_burnolCoPoissonSource hb src hw.1 hw.2
  · exact iteratedDeriv_burnolCoPoissonSourceCompletedMellinGerm_eq_zero_of_lt
      hb src rho hright hj

/-- Both branches of every cosine-closed generator obey every lower Xi-jet
relation. -/
theorem burnolCoPoissonGenerator_mem_lowerXiJetAnnihilator
    {b : ℝ} (hb : 0 < b) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonGeneratorSet b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    f ∈ burnolCoPoissonLowerXiJetAnnihilator b rho j hb := by
  rcases hf with ⟨src, rfl | rfl⟩
  · exact burnolCoPoissonSource_mem_lowerXiJetAnnihilator hb src rho hright hj
  · simpa only [BurnolCoPoissonSource.reciprocal_vector,
      coe_burnolExtendedSoninCosine] using
      (burnolCoPoissonSource_mem_lowerXiJetAnnihilator hb (src.reciprocal hb)
        rho hright hj)

/-- **Cosine-closed algebraic lower-jet system.**  Every finite linear
combination of literal co-Poisson sources and their cosine images has an
analytic germ whose `j`th Xi jet vanishes below the exact multiplicity. -/
theorem burnolCoPoissonAlgebraicSourceSpace_le_lowerXiJetAnnihilator
    {b : ℝ} (hb : 0 < b) (rho : XiDivisorSupport)
    (hright : 1 / 2 < (rho : ℂ).re) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    burnolCoPoissonAlgebraicSourceSpace b ≤
      burnolCoPoissonLowerXiJetAnnihilator b rho j hb := by
  rw [burnolCoPoissonAlgebraicSourceSpace, Submodule.span_le]
  intro f hf
  exact burnolCoPoissonGenerator_mem_lowerXiJetAnnihilator hb hf rho hright hj

end RHTower

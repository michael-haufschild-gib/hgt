import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Fourier--Borel transforms of compactly carried functionals

This file constructs the exact Banach-valued exponential test used in the
Euler-unit completeness proof.  A continuous functional on a compact carrier
produces an entire Fourier--Borel transform, and a sectorial lower bound for
`Re (z s)` gives the required exponential decay with the operator norm as its
only constant.
-/

noncomputable section

namespace RHTower

open Set Complex

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The continuous exponential test `s ↦ exp (-z s)` on a compact carrier. -/
def compactExponentialTest (s : C(K, ℂ)) (z : ℂ) : C(K, ℂ) :=
  NormedSpace.exp (-(z • s))

/-- Fourier--Borel transform of a continuous functional carried by `K`. -/
def compactFourierBorel (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) (z : ℂ) : ℂ :=
  L (compactExponentialTest s z)

@[simp]
theorem compactExponentialTest_apply (s : C(K, ℂ)) (z : ℂ) (k : K) :
    compactExponentialTest s z k = Complex.exp (-z * s k) := by
  let ev : C(K, ℂ) →+* ℂ :=
    (Pi.evalRingHom (fun _ : K ↦ ℂ) k).comp ContinuousMap.coeFnRingHom
  have hev : Continuous ev := by
    simpa only [RingHom.coe_comp, Function.comp_apply, ContinuousMap.coeFnRingHom_apply,
      Pi.evalRingHom_apply] using (ContinuousMap.evalCLM ℂ k).continuous
  change ev (NormedSpace.exp (-(z • s))) = _
  rw [NormedSpace.map_exp ev hev]
  rw [Complex.exp_eq_exp_ℂ]
  simp [ev]

/-- The Banach-valued exponential test is entire in its scalar parameter. -/
theorem compactExponentialTest_analyticOnNhd (s : C(K, ℂ)) :
    AnalyticOnNhd ℂ (compactExponentialTest s) Set.univ := by
  let S : ℂ →L[ℂ] C(K, ℂ) :=
    -(ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) s)
  intro z hz
  have he : AnalyticAt ℂ (NormedSpace.exp : C(K, ℂ) → C(K, ℂ)) (S z) :=
    NormedSpace.exp_analytic (S z)
  have hc := he.compContinuousLinearMap (u := S)
  simpa [compactExponentialTest, S, Function.comp_def] using hc

/-- A compactly carried Fourier--Borel transform is entire. -/
theorem compactFourierBorel_analyticOnNhd
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) :
    AnalyticOnNhd ℂ (compactFourierBorel L s) Set.univ := by
  simpa [compactFourierBorel, Function.comp_def] using
    L.comp_analyticOnNhd (compactExponentialTest_analyticOnNhd s)

/-- Pointwise sectorial positivity gives an exponential sup-norm bound on the
compact exponential test. -/
theorem norm_compactExponentialTest_le (s : C(K, ℂ)) (z : ℂ) (c : ℝ)
    (hre : ∀ k, c * ‖z‖ ≤ (z * s k).re) :
    ‖compactExponentialTest s z‖ ≤ Real.exp (-c * ‖z‖) := by
  apply (ContinuousMap.norm_le (compactExponentialTest s z) (Real.exp_nonneg _)).2
  intro k
  rw [compactExponentialTest_apply, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hk := hre k
  simp only [neg_mul, Complex.neg_re]
  linarith

/-- The corresponding Fourier--Borel decay estimate. -/
theorem norm_compactFourierBorel_le
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    (z : ℂ) (c : ℝ) (hre : ∀ k, c * ‖z‖ ≤ (z * s k).re) :
    ‖compactFourierBorel L s z‖ ≤ ‖L‖ * Real.exp (-c * ‖z‖) := by
  exact (L.le_opNorm (compactExponentialTest s z)).trans
    (mul_le_mul_of_nonneg_left (norm_compactExponentialTest_le s z c hre)
      (norm_nonneg L))

end RHTower

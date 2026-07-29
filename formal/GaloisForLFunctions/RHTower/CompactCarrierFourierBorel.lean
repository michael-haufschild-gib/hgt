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
    change Continuous (fun f : C(K, ℂ) => f k)
    exact (ContinuousMap.evalCLM ℂ k).continuous
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
  change AnalyticAt ℂ (fun w => NormedSpace.exp (-(w • s))) z
  simpa [S, Function.comp_def] using hc

/-- The first scalar derivative of the compact exponential test at zero is
the negative carrier coordinate. -/
theorem compactExponentialTest_hasDerivAt_zero (s : C(K, ℂ)) :
    HasDerivAt (compactExponentialTest s) (-s) 0 := by
  let S : ℂ →L[ℂ] C(K, ℂ) :=
    -(ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) s)
  have hexp : HasFDerivAt (NormedSpace.exp : C(K, ℂ) → C(K, ℂ))
      (ContinuousLinearMap.id ℂ C(K, ℂ)) 0 := by
    have h := (NormedSpace.exp_hasFPowerSeriesAt_zero
      (𝕂 := ℂ) (𝔸 := C(K, ℂ))).hasFDerivAt
    apply h.congr_fderiv
    ext x : 1
    rw [continuousMultilinearCurryFin1_apply]
    have hx := NormedSpace.expSeries_apply_eq
      (𝕂 := ℂ) (𝔸 := C(K, ℂ)) x 1
    have hvec : Fin.snoc (0 : Fin 0 → C(K, ℂ)) x = (fun _ : Fin 1 => x) := by
      funext i
      fin_cases i
      rfl
    rw [hvec]
    simpa using hx
  have hexpS : HasFDerivAt (NormedSpace.exp : C(K, ℂ) → C(K, ℂ))
      (ContinuousLinearMap.id ℂ C(K, ℂ)) (S 0) := by
    simpa [S] using hexp
  have hcomp := hexpS.comp 0 S.hasFDerivAt
  have hfun : compactExponentialTest s =
      (NormedSpace.exp : C(K, ℂ) → C(K, ℂ)) ∘ S := by
    funext z
    simp [compactExponentialTest, S]
  have hFD : HasFDerivAt (compactExponentialTest s) S 0 := by
    rw [hfun]
    simpa using hcomp
  have hS1 : S 1 = -s := by
    ext k
    simp [S]
  exact hFD.hasDerivAt.congr_deriv hS1

/-- A compactly carried Fourier--Borel transform is entire. -/
theorem compactFourierBorel_analyticOnNhd
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) :
    AnalyticOnNhd ℂ (compactFourierBorel L s) Set.univ := by
  change AnalyticOnNhd ℂ (fun z => L (compactExponentialTest s z)) Set.univ
  exact L.comp_analyticOnNhd (compactExponentialTest_analyticOnNhd s)

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

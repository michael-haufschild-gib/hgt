import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Heat kernels from a spectral datum

Mathlib carries no heat kernels.  This file builds them from the only data that the analysis of a
degenerating family of Laplacians actually uses: a nonnegative spectrum `λ₀ ≤ λ₁ ≤ …` together with
the corresponding eigenfunctions `φ₀, φ₁, …` on a measure space.  The kernel is the spectral sum

```text
K(t,x,y) = Σₙ e^{−tλₙ} φₙ(x) \overline{φₙ(y)} .
```

Proved here, for that kernel:

* it is Hermitian, `K(t,y,x) = \overline{K(t,x,y)}`;
* on the diagonal it is the nonnegative real number `Σₙ e^{−tλₙ}|φₙ(x)|²`;
* the pointwise Cauchy–Schwarz bound `|K(t,x,y)| ≤ K(t,x,x)^{1/2} K(t,y,y)^{1/2}`, which is the
  estimate every off-diagonal heat-kernel argument starts from;
* the trace formula `∫ K(t,x,x) dμ = Σₙ e^{−tλₙ}` for an orthonormal family;
* monotonicity of the diagonal in the time variable.

Nothing here needs a manifold: the spectral datum is the whole input.
-/

open MeasureTheory Set Filter Real

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*}

/-- The heat kernel attached to a spectrum `lam` and an eigenfunction family `φ`. -/
noncomputable def spectralHeatKernel (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) (t : ℝ) (x y : X) : ℂ :=
  ∑' n, (Real.exp (-(t * lam n)) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y))

/-- The diagonal profile of the heat kernel: a nonnegative real spectral sum. -/
noncomputable def spectralHeatDiag (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) (t : ℝ) (x : X) : ℝ :=
  ∑' n, Real.exp (-(t * lam n)) * ‖φ n x‖ ^ (2 : ℕ)

theorem spectralHeatDiag_nonneg (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) (t : ℝ) (x : X) :
    0 ≤ spectralHeatDiag lam φ t x :=
  tsum_nonneg fun n => by positivity

/-- On the diagonal the heat kernel is the real diagonal profile. -/
theorem spectralHeatKernel_diag (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) (t : ℝ) (x : X) :
    spectralHeatKernel lam φ t x x = ((spectralHeatDiag lam φ t x : ℝ) : ℂ) := by
  rw [spectralHeatKernel, spectralHeatDiag, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have hmc : φ n x * (starRingEnd ℂ) (φ n x) = ((‖φ n x‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hmc]
  push_cast
  ring

/-- **The heat kernel is Hermitian.** -/
theorem spectralHeatKernel_conj (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) (t : ℝ) (x y : X) :
    (starRingEnd ℂ) (spectralHeatKernel lam φ t x y) = spectralHeatKernel lam φ t y x := by
  rw [spectralHeatKernel, spectralHeatKernel, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rw [map_mul, map_mul, Complex.conj_conj]
  simp only [Complex.conj_ofReal]
  ring

/-- **The pointwise Cauchy–Schwarz bound for a heat kernel.**

`|K(t,x,y)| ≤ K(t,x,x)^{1/2} K(t,y,y)^{1/2}`. -/
theorem norm_spectralHeatKernel_le (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) {t : ℝ} {x y : X}
    (hx : Summable fun n => Real.exp (-(t * lam n)) * ‖φ n x‖ ^ (2 : ℕ))
    (hy : Summable fun n => Real.exp (-(t * lam n)) * ‖φ n y‖ ^ (2 : ℕ)) :
    ‖spectralHeatKernel lam φ t x y‖
      ≤ Real.sqrt (spectralHeatDiag lam φ t x) * Real.sqrt (spectralHeatDiag lam φ t y) := by
  set u : ℕ → ℝ := fun n => Real.sqrt (Real.exp (-(t * lam n))) * ‖φ n x‖ with hu
  set v : ℕ → ℝ := fun n => Real.sqrt (Real.exp (-(t * lam n))) * ‖φ n y‖ with hv
  have hsq : ∀ (z : X) (n : ℕ),
      (Real.sqrt (Real.exp (-(t * lam n))) * ‖φ n z‖) ^ (2 : ℕ)
        = Real.exp (-(t * lam n)) * ‖φ n z‖ ^ (2 : ℕ) := by
    intro z n
    rw [mul_pow, Real.sq_sqrt (Real.exp_nonneg _)]
  have hu2 : Summable fun n => u n ^ (2 : ℕ) := by
    refine hx.congr fun n => ?_
    rw [hu, hsq]
  have hv2 : Summable fun n => v n ^ (2 : ℕ) := by
    refine hy.congr fun n => ?_
    rw [hv, hsq]
  have hterm : ∀ n, ‖(Real.exp (-(t * lam n)) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y))‖
      = u n * v n := by
    intro n
    rw [norm_mul, norm_mul, Complex.norm_conj]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    rw [hu, hv]
    have : Real.sqrt (Real.exp (-(t * lam n))) * Real.sqrt (Real.exp (-(t * lam n)))
        = Real.exp (-(t * lam n)) := Real.mul_self_sqrt (Real.exp_nonneg _)
    calc Real.exp (-(t * lam n)) * (‖φ n x‖ * ‖φ n y‖)
        = (Real.sqrt (Real.exp (-(t * lam n))) * Real.sqrt (Real.exp (-(t * lam n))))
            * (‖φ n x‖ * ‖φ n y‖) := by rw [this]
      _ = (Real.sqrt (Real.exp (-(t * lam n))) * ‖φ n x‖)
            * (Real.sqrt (Real.exp (-(t * lam n))) * ‖φ n y‖) := by ring
  have hsummableNorm : Summable fun n =>
      ‖(Real.exp (-(t * lam n)) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y))‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((hu2.add hv2).mul_left (1 / 2))
    rw [hterm n]
    have := two_mul_le_add_sq (u n) (v n)
    nlinarith [this]
  refine le_trans (norm_tsum_le_tsum_norm hsummableNorm) ?_
  have hcongr : (∑' n, ‖(Real.exp (-(t * lam n)) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y))‖)
      = ∑' n, u n * v n := tsum_congr hterm
  rw [hcongr]
  refine le_trans (ContinuousLinearMap.tsum_mul_le_sqrt_mul_sqrt hu2 hv2) (le_of_eq ?_)
  congr 1
  · congr 1
    exact tsum_congr fun n => by rw [hu, hsq]
  · congr 1
    exact tsum_congr fun n => by rw [hv, hsq]

/-- **The trace formula.**  For an `L²`-orthonormal family the diagonal integrates to the heat
trace `Σₙ e^{−tλₙ}`. -/
theorem integral_spectralHeatDiag [MeasurableSpace X] {μ : Measure X}
    (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) {t : ℝ}
    (hint : ∀ n, Integrable (fun x => ‖φ n x‖ ^ (2 : ℕ)) μ)
    (hnorm : ∀ n, ∫ x, ‖φ n x‖ ^ (2 : ℕ) ∂μ = 1)
    (hsum : Summable fun n => Real.exp (-(t * lam n))) :
    ∫ x, spectralHeatDiag lam φ t x ∂μ = ∑' n, Real.exp (-(t * lam n)) := by
  have hIint : ∀ n, Integrable (fun x => Real.exp (-(t * lam n)) * ‖φ n x‖ ^ (2 : ℕ)) μ := fun n =>
    (hint n).const_mul _
  have hnormsum : Summable fun n =>
      ∫ x, ‖Real.exp (-(t * lam n)) * ‖φ n x‖ ^ (2 : ℕ)‖ ∂μ := by
    refine hsum.congr fun n => ?_
    have hcongr : ∀ x, ‖Real.exp (-(t * lam n)) * ‖φ n x‖ ^ (2 : ℕ)‖
        = Real.exp (-(t * lam n)) * ‖φ n x‖ ^ (2 : ℕ) := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [hcongr]
    rw [MeasureTheory.integral_const_mul, hnorm n, mul_one]
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun n x => Real.exp (-(t * lam n)) * ‖φ n x‖ ^ (2 : ℕ)) hIint hnormsum
  simp only [spectralHeatDiag]
  rw [show (∫ x, ∑' n, Real.exp (-(t * lam n)) * ‖φ n x‖ ^ (2 : ℕ) ∂μ) = _ from hswap.symm]
  refine tsum_congr fun n => ?_
  rw [MeasureTheory.integral_const_mul, hnorm n, mul_one]

/-- **The diagonal is antitone in the time.** -/
theorem antitoneOn_spectralHeatDiag (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) (x : X)
    (hlam : ∀ n, 0 ≤ lam n)
    (hsum : ∀ t ∈ Ioi (0 : ℝ), Summable fun n => Real.exp (-(t * lam n)) * ‖φ n x‖ ^ (2 : ℕ)) :
    AntitoneOn (fun t => spectralHeatDiag lam φ t x) (Ioi (0 : ℝ)) := by
  intro t₁ ht₁ t₂ ht₂ hle
  refine (hsum t₂ ht₂).tsum_le_tsum (fun n => ?_) (hsum t₁ ht₁)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine Real.exp_le_exp.mpr ?_
  have : t₁ * lam n ≤ t₂ * lam n := mul_le_mul_of_nonneg_right hle (hlam n)
  linarith

end GaloisForLFunctions.HTGeometry

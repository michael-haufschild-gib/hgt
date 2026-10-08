import GaloisForLFunctions.RHTower.PerronKernelIdentity

/-!
# One-sided pole cancellation for the GY certificate audit

The reflected Perron kernel has zero integral at every nonnegative Fourier
displacement. A finite arithmetic multiplier retains exactly the frequencies
strictly above that displacement, with their original complex coefficients.

This corrects the frozen-coefficient Lorentzian step in the L398 paper sketch.
It is a classical Fourier/Perron bridge, not an estimate for the complete GY
window, a zero-free theorem, or a proof of prime-blind positivity.
Paper proof: docs/reports/weil-work/results/01-pbap/GY-CAUSALITY-AUDIT.md.
-/

noncomputable section
open MeasureTheory Complex Set Filter
namespace RHTower.WeilWorkPBAP


/-- Complex second-order pole with the original Fourier orientation. -/
def poleWave (δ x t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (t*x) : ℝ) : ℂ) * I) /
    ((δ : ℂ) - 2 * Real.pi * t * I)^2

/-- Exact reflected Perron identity, including the zero endpoint. -/
theorem poleWave_integral {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    (∫ t : ℝ, poleWave δ x t) = RHTower.perronTent δ (-x) := by
  rw [← integral_neg_eq_self (fun t : ℝ => poleWave δ x t)]
  rw [← RHTower.perron_kernel_identity hδ (-x)]
  apply integral_congr_ae
  filter_upwards with t
  unfold poleWave
  rw [smul_eq_mul, mul_one_div]
  congr 2 <;> push_cast <;> ring

/-- Nonnegative displacement is causally invisible to this pole. -/
theorem poleWave_integral_nonneg {δ x : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) :
    (∫ t : ℝ, poleWave δ x t) = 0 := by
  rw [poleWave_integral hδ, RHTower.perronTent,
    Set.indicator_of_notMem (show -x ∉ Ioi (0 : ℝ) by simpa using hx)]

/-- The surviving negative-displacement response is explicit. -/
theorem poleWave_integral_neg {δ x : ℝ} (hδ : 0 < δ) (hx : x < 0) :
    (∫ t : ℝ, poleWave δ x t) = (-x : ℂ) * Complex.exp ((δ : ℂ)*x) := by
  rw [poleWave_integral hδ, RHTower.perronTent,
    Set.indicator_of_mem (show -x ∈ Ioi (0 : ℝ) by simpa using hx)]
  push_cast
  ring_nf



/-- The pole integral is absolutely convergent. -/
theorem poleWave_integrable {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    Integrable (poleWave δ x) := by
  have hk : Integrable (fun t : ℝ =>
      (1 : ℂ) / ((δ : ℂ) - 2 * Real.pi * t * I)^2) := by
    convert (RHTower.integrable_fourier_perronTent hδ).comp_neg using 1
    funext t
    rw [RHTower.fourier_perronTent hδ]
    congr 2; push_cast; ring
  have he : AEStronglyMeasurable (fun t : ℝ =>
      Complex.exp (((2 * Real.pi * (t*x) : ℝ) : ℂ) * I)) :=
    (by fun_prop : Continuous _).aestronglyMeasurable
  have hb : ∀ᵐ t : ℝ, ‖Complex.exp (((2 * Real.pi * (t*x) : ℝ) : ℂ) * I)‖ ≤ 1 := by
    filter_upwards with t
    simp [Complex.norm_exp]
  change Integrable (fun t : ℝ => Complex.exp (((2 * Real.pi * (t*x) : ℝ) : ℂ) * I) /
    ((δ : ℂ) - 2 * Real.pi * t * I)^2)
  simpa only [mul_one_div] using hk.bdd_mul he hb

/-- A finite multiplier retains its exact complex phases. -/
theorem finite_poleWave_integral {ι : Type*} (S : Finset ι)
    (b : ι → ℂ) (v : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    (∫ t : ℝ, (∑ j ∈ S, b j * Complex.exp
        (-(((2 * Real.pi * (t*v j) : ℝ) : ℂ) * I))) * poleWave δ x t) =
      ∑ j ∈ S, b j * RHTower.perronTent δ (v j-x) := by
  have hp : ∀ t : ℝ,
      (∑ j ∈ S, b j * Complex.exp
        (-(((2 * Real.pi * (t*v j) : ℝ) : ℂ) * I))) * poleWave δ x t =
      ∑ j ∈ S, b j * poleWave δ (x-v j) t := by
    intro t
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    unfold poleWave
    have he : Complex.exp (-(((2 * Real.pi * (t*v j) : ℝ) : ℂ) * I)) *
        Complex.exp (((2 * Real.pi * (t*x) : ℝ) : ℂ) * I) =
        Complex.exp (((2 * Real.pi * (t*(x-v j)) : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc _ = b j * (Complex.exp (-(((2 * Real.pi * (t*v j) : ℝ) : ℂ) * I)) *
          Complex.exp (((2 * Real.pi * (t*x) : ℝ) : ℂ) * I)) /
          ((δ : ℂ) - 2 * Real.pi * t * I)^2 := by ring
      _ = _ := by rw [he]; ring
  simp_rw [hp]
  rw [integral_finsetSum S (fun j hj => (poleWave_integrable hδ _).const_mul (b j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, poleWave_integral hδ, neg_sub]

/-- Exact surviving frequency tail; low frequencies contribute zero. -/
theorem finite_poleWave_tail {ι : Type*} (S : Finset ι)
    (b : ι → ℂ) (v : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    (∫ t : ℝ, (∑ j ∈ S, b j * Complex.exp
        (-(((2 * Real.pi * (t*v j) : ℝ) : ℂ) * I))) * poleWave δ x t) =
      ∑ j ∈ S with x < v j,
        b j * ((v j-x : ℝ) : ℂ) * Complex.exp (-((δ : ℂ)*(v j-x))) := by
  classical
  rw [finite_poleWave_integral S b v hδ, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : x < v j
  · rw [if_pos h, RHTower.perronTent,
      Set.indicator_of_mem (show v j-x ∈ Ioi (0 : ℝ) from sub_pos.mpr h)]
    push_cast
    ring_nf
  · rw [if_neg h, RHTower.perronTent,
      Set.indicator_of_notMem (show v j-x ∉ Ioi (0 : ℝ) by simpa using h), mul_zero]

/-- Every finite head below the displacement is annihilated. -/
theorem finite_poleWave_integral_eq_zero {ι : Type*} (S : Finset ι)
    (b : ι → ℂ) (v : ι → ℝ) {δ x : ℝ} (hδ : 0 < δ)
    (hv : ∀ j ∈ S, v j ≤ x) :
    (∫ t : ℝ, (∑ j ∈ S, b j * Complex.exp
        (-(((2 * Real.pi * (t*v j) : ℝ) : ℂ) * I))) * poleWave δ x t) = 0 := by
  rw [finite_poleWave_integral S b v hδ]
  apply Finset.sum_eq_zero
  intro j hj
  rw [RHTower.perronTent,
    Set.indicator_of_notMem (show v j-x ∉ Ioi (0 : ℝ) from not_lt.mpr (sub_nonpos.mpr (hv j hj))),
    mul_zero]

end RHTower.WeilWorkPBAP


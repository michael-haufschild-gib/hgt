import Mathlib

/-!
# Product receivers see depth only through their total length

A product receiver of order `k` is a measure `μ` on `ℝ^k` with a weight `Φ ∈ L¹(μ)`. Tested
against the external power `T^{⊠k}` of the explicit-formula distribution `T(x) = Σ_ρ e^{(ρ−½)x}`,
it responds to a tuple of zeros through `R(z) = ∫ Φ(x) e^{⟨z, x⟩} dμ(x)` at `z_j = ρ_j − ½`, so
the depths `Re ρ_j − ½` enter only through `e^{Σ_j (Re z_j) x_j}`.

* **Depth–length conservation** (`norm_productResponse_le`). If `μ`-almost every point of the
  support of `Φ` has total length `Σ_j |x_j| ≤ S` and every `|Re z_j| ≤ δ`, then
  `|R(z)| ≤ e^{δS} ∫ |Φ| dμ`. The order `k` does not enter.
* **The diagonal is a degree-one receiver** (`integral_cexp_diag_eq_integral_map`,
  `ae_abs_le_of_map_sum`). On a repeated zero, `z = (w, …, w)`, the response is the Laplace
  transform of the image of `μ` under `x ↦ Σ_j x_j`, a measure on `[−S, S]`.
* **Sharpness** (`exp_mul_le_re_integral_cexp_diag`). A positive receiver carried by
  `{Σ_j x_j ≥ S − ε}` has real diagonal response at least `e^{δ(S−ε)} μ(ℝ^k)`.

So a product of any order gains on a zero's depth exactly what a single receiver of the same
total length gains. A tensor power amplifies depth only when the base cost stays fixed while the
local weight is raised to the power, as for the stalks of a local system in Deligne's argument;
on the spectrum of a single source the cost is the total length itself.
-/

open MeasureTheory Complex

namespace GaloisForLFunctions.ArithmeticKunnethTheory

variable {k : ℕ}

/-- The total length `Σ_j |x_j|` of a point of `ℝ^k`. -/
def totalLength (x : Fin k → ℝ) : ℝ := ∑ j, |x j|

/-- The response `∫ Φ(x) e^{⟨z, x⟩} dμ(x)` of a product receiver to `z ∈ ℂ^k`. -/
noncomputable def productResponse (μ : Measure (Fin k → ℝ)) (Φ : (Fin k → ℝ) → ℂ)
    (z : Fin k → ℂ) : ℂ :=
  ∫ x, Φ x * cexp (∑ j, z j * (x j : ℂ)) ∂μ

/-- The exponential weight of a tuple with depths `Re z_j` is at most `e^{Σ_j |Re z_j| |x_j|}`. -/
theorem norm_cexp_sum_le (z : Fin k → ℂ) (x : Fin k → ℝ) :
    ‖cexp (∑ j, z j * (x j : ℂ))‖ ≤ Real.exp (∑ j, |(z j).re| * |x j|) := by
  rw [Complex.norm_exp, Complex.re_sum]
  refine Real.exp_le_exp.mpr (Finset.sum_le_sum fun j _ => ?_)
  rw [Complex.re_mul_ofReal, ← abs_mul]
  exact le_abs_self _

/-- With every depth at most `δ`, the exponential weight is at most `e^{δ · totalLength x}`. -/
theorem norm_cexp_sum_le_exp_totalLength {z : Fin k → ℂ} {δ : ℝ} (hz : ∀ j, |(z j).re| ≤ δ)
    (x : Fin k → ℝ) :
    ‖cexp (∑ j, z j * (x j : ℂ))‖ ≤ Real.exp (δ * totalLength x) := by
  refine (norm_cexp_sum_le z x).trans (Real.exp_le_exp.mpr ?_)
  rw [totalLength, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hz j) (abs_nonneg _)

/-- **Depth–length conservation.** A product receiver of total length `S` responds to a zero
tuple of depths at most `δ` by at most `e^{δS} ∫ |Φ| dμ`, whatever its order `k`. -/
theorem norm_productResponse_le {μ : Measure (Fin k → ℝ)} {Φ : (Fin k → ℝ) → ℂ}
    (hΦ : Integrable Φ μ) {z : Fin k → ℂ} {δ S : ℝ} (hδ : 0 ≤ δ) (hz : ∀ j, |(z j).re| ≤ δ)
    (hS : ∀ᵐ x ∂μ, Φ x ≠ 0 → totalLength x ≤ S) :
    ‖productResponse μ Φ z‖ ≤ Real.exp (δ * S) * ∫ x, ‖Φ x‖ ∂μ := by
  rw [productResponse, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hΦ.norm.const_mul _) ?_
  filter_upwards [hS] with x hx
  rw [norm_mul, mul_comm]
  by_cases h0 : Φ x = 0
  · simp [h0]
  refine mul_le_mul_of_nonneg_right ((norm_cexp_sum_le_exp_totalLength hz x).trans ?_)
    (norm_nonneg _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hx h0) hδ)

/-- **The diagonal is a degree-one receiver.** On a repeated zero `z = (w, …, w)` the response of
`μ` is the Laplace transform of its image under `x ↦ Σ_j x_j`. -/
theorem integral_cexp_diag_eq_integral_map (μ : Measure (Fin k → ℝ)) (w : ℂ) :
    ∫ x, cexp (∑ j, w * (x j : ℂ)) ∂μ =
      ∫ u : ℝ, cexp (w * (u : ℂ)) ∂(μ.map fun x : Fin k → ℝ => (∑ j, x j : ℝ)) := by
  have hm : Measurable fun x : Fin k → ℝ => ∑ j, x j := by fun_prop
  rw [integral_map hm.aemeasurable (by fun_prop)]
  congr 1
  ext x
  rw [Complex.ofReal_sum, Finset.mul_sum]

/-- The image of a receiver of total length `S` under `x ↦ Σ_j x_j` lives on `[−S, S]`. -/
theorem ae_abs_le_of_map_sum {μ : Measure (Fin k → ℝ)} {S : ℝ}
    (hS : ∀ᵐ x ∂μ, totalLength x ≤ S) :
    ∀ᵐ u ∂(μ.map fun x : Fin k → ℝ => (∑ j, x j : ℝ)), |u| ≤ S := by
  have hm : Measurable fun x : Fin k → ℝ => ∑ j, x j := by fun_prop
  rw [ae_map_iff hm.aemeasurable (measurableSet_le (by fun_prop) measurable_const)]
  filter_upwards [hS] with x hx
  exact (Finset.abs_sum_le_sum_abs _ _).trans hx

/-- **Sharpness.** A finite positive receiver of total length `S` carried by `{Σ_j x_j ≥ S − ε}`
has real diagonal response at least `e^{δ(S−ε)} μ(ℝ^k)` at depth `δ ≥ 0`. -/
theorem exp_mul_le_re_integral_cexp_diag {μ : Measure (Fin k → ℝ)} [IsFiniteMeasure μ]
    {δ S ε : ℝ} (hδ : 0 ≤ δ) (hS : ∀ᵐ x ∂μ, totalLength x ≤ S)
    (hcar : ∀ᵐ x ∂μ, S - ε ≤ ∑ j, x j) :
    Real.exp (δ * (S - ε)) * μ.real Set.univ ≤
      (∫ x, cexp (∑ j, (δ : ℂ) * (x j : ℂ)) ∂μ).re := by
  have hre : ∀ x : Fin k → ℝ,
      cexp (∑ j, (δ : ℂ) * (x j : ℂ)) = ((Real.exp (δ * ∑ j, x j) : ℝ) : ℂ) := by
    intro x
    rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  simp_rw [hre]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  have hint : Integrable (fun x : Fin k → ℝ => Real.exp (δ * ∑ j, x j)) μ := by
    refine Integrable.mono' (integrable_const (Real.exp (δ * S))) (by fun_prop) ?_
    filter_upwards [hS] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans ((Finset.abs_sum_le_sum_abs _ _).trans hx)) hδ)
  calc Real.exp (δ * (S - ε)) * μ.real Set.univ
      = ∫ _x, Real.exp (δ * (S - ε)) ∂μ := by rw [integral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ x, Real.exp (δ * ∑ j, x j) ∂μ := by
      refine integral_mono_ae (integrable_const _) hint ?_
      filter_upwards [hcar] with x hx
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx hδ)

end GaloisForLFunctions.ArithmeticKunnethTheory

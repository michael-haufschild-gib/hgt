import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorMovingBoundary
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorSpatialDefect
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorFiniteBoundary

/-! # Height rescaling and finite Poisson packets at the real boundary -/

noncomputable section

open MeasureTheory Set Complex Filter Topology Polynomial

namespace RHTower.WeilHigherDenominator

/-- The square-root and logarithmic normalizations supply the exact height factor. -/
theorem polynomialPolarMode_boundary_rescaled {α : Type*} {l : Filter α}
    {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) (P : ℂ[X])
    {x y d : α → ℝ} {x₀ d₀ : ℝ} (hx₀ : 0 < x₀) (hd₀ : 0 < d₀)
    (hx : Tendsto x l (𝓝 x₀)) (hy : Tendsto y l (𝓝[>] 0))
    (hd : Tendsto d l (𝓝 d₀)) :
    Tendsto (fun a => polynomialPolarMode ρ P ((x a : ℂ) + ((y a / d a : ℝ) : ℂ) * I) /
      ((Real.sqrt (y a) : ℂ) * (Real.log (y a) : ℂ)))
      l (𝓝 ((-2 * (x₀ : ℂ) ^ (-ρ) * P.eval (Real.log x₀ : ℂ)) / (Real.sqrt d₀ : ℂ))) := by
  have hdpos : ∀ᶠ a in l, 0 < d a := hd.eventually (eventually_gt_nhds hd₀)
  have hypos : ∀ᶠ a in l, 0 < y a := hy.eventually self_mem_nhdsWithin
  have hyone : ∀ᶠ a in l, y a < 1 := hy.eventually
    ((eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds)
  have hheight : Tendsto (fun a => y a / d a) l (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h := (tendsto_nhds_of_tendsto_nhdsWithin hy).div hd hd₀.ne'
      rw [zero_div] at h
      exact h
    · filter_upwards [hypos, hdpos] with a hya hda
      exact div_pos hya hda
  have hsmall : ∀ᶠ a in l, y a / d a < 1 := hheight.eventually
    ((eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds)
  have hm := polynomial_polarKernel_boundary_moving hρ₀ hρ₁ P hx₀ hx hheight
  have hr : Tendsto (fun a => ((Real.log (y a / d a) / Real.log (y a) : ℝ) : ℂ))
      l (𝓝 (1 : ℂ)) := by
    simpa only [ofReal_one, Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_log_div_height hd₀ hd hy)
  have hs : Tendsto (fun a => (Real.sqrt (d a) : ℂ)) l (𝓝 (Real.sqrt d₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (Real.continuous_sqrt.tendsto d₀ |>.comp hd)
  have hlim := ((hm.mul hr).div hs (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd₀).ne'))
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [hypos, hdpos, hyone, hsmall] with a hya hda hya1 hsmall
  have hsy : (Real.sqrt (y a) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hya).ne'
  have hsd : (Real.sqrt (d a) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hda).ne'
  have hly : (Real.log (y a) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.log_neg hya hya1).ne
  have hlh : (Real.log (y a / d a) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.log_neg (div_pos hya hda) hsmall).ne
  change (((∫ t : ℝ, P.eval (Real.log |t| : ℂ) *
      polarKernel ρ ((x a : ℂ) + ((y a / d a : ℝ) : ℂ) * I) t) /
      (Real.log (y a / d a) : ℂ)) *
        ((Real.log (y a / d a) / Real.log (y a) : ℝ) : ℂ)) / (Real.sqrt (d a) : ℂ) = _
  have him : ((x a : ℂ) + ((y a / d a : ℝ) : ℂ) * I).im = y a / d a := by simp
  rw [polynomialPolarMode, him, Real.sqrt_div hya.le]
  push_cast
  field_simp

/-- A finite packet's limit is its explicit boundary polynomial sum, along moving paths. -/
theorem poissonPacket_boundary_path {α : Type*} {l : Filter α}
    (Z : Finset ℂ) (R : ℂ → ℂ[X]) (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    {z : α → ℂ} {y d : α → ℝ} {x₀ d₀ : ℝ} (hx₀ : 0 < x₀) (hd₀ : 0 < d₀)
    (hx : Tendsto (fun a => (z a).re) l (𝓝 x₀))
    (hy : Tendsto y l (𝓝[>] 0)) (hd : Tendsto d l (𝓝 d₀))
    (him : ∀ᶠ a in l, (z a).im = y a / d a) :
    Tendsto (fun a => (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z a)) /
      ((Real.sqrt (y a) : ℂ) * (Real.log (y a) : ℂ)))
      l (𝓝 ((-2 * finitePoleBoundary Z id R x₀) / (Real.sqrt d₀ : ℂ))) := by
  have hlim := tendsto_finsetSum Z fun ρ hρ =>
    polynomialPolarMode_boundary_rescaled (hstrip ρ hρ).1 (hstrip ρ hρ).2 (R ρ)
      hx₀ hd₀ hx hy hd
  have he : (∑ ρ ∈ Z, (-2 * (x₀ : ℂ) ^ (-ρ) * (R ρ).eval (Real.log x₀ : ℂ)) /
      (Real.sqrt d₀ : ℂ)) = (-2 * finitePoleBoundary Z id R x₀) / (Real.sqrt d₀ : ℂ) := by
    rw [← Finset.sum_div]
    congr 1
    simp only [finitePoleBoundary, id_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx₀.ne'), ← ofReal_log hx₀.le,
      mul_comm (Real.log x₀ : ℂ) (-ρ)]
    ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [him] with a ha
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ _
  rw [← ha, Complex.re_add_im]

end RHTower.WeilHigherDenominator

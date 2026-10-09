import GaloisForLFunctions.RHTower.LaguerrePolyaFirstOrderInterlacing
import GaloisForLFunctions.HTGeometry.FirstOrderFilterVanishingIntervalBound

/-!
# Gap estimate for first-order Laguerre–Pólya preimages

Let `ψ` be in the Laguerre–Pólya class, `c > 0`, and `F = ψ − c ψ′` (not identically zero).
Normalise by a positive differentiable amplitude `A`: `s = Re ψ / A` and `Z = Re F / A` on `ℝ`.
Then `c s′ = −(Z + (c A′/A − 1) s)` on the real line, and `s` vanishes in every closed interval
between two real zeros of `F` (`exists_zero_Icc_of_laguerrePolya_sub_smul_deriv`). The
first-order filter bound therefore gives, on each such gap `[γ, γ′]` with
`2 C (γ′ − γ) ≤ c` and `|c A′/A − 1| ≤ C`:

`∫_γ^{γ′} s² ≤ (4/c²)(γ′ − γ)² ∫_γ^{γ′} Z²`
(`integral_sq_le_of_laguerrePolya_firstOrder_gap`).

This is the deterministic half of the Laguerre–Pólya maximality theorem for Ξ. Summed over the
zero gaps of Ξ, its right side is `o(T)` by the gap and moment bounds for Hardy's function, while
the left side has mean `≍ T` for the filtered Hardy function.
-/

open Set MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- **Gap estimate for a first-order Laguerre–Pólya preimage.** -/
theorem integral_sq_le_of_laguerrePolya_firstOrder_gap {ψ : ℂ → ℂ}
    (hψ : GaloisForLFunctions.HTGeometry.LaguerrePolya ψ) {c : ℝ} (hc : 0 < c)
    (hnz : ∃ z₀, ψ z₀ - (c : ℂ) * deriv ψ z₀ ≠ 0)
    {A A' : ℝ → ℝ} (hApos : ∀ x, 0 < A x) (hAd : ∀ x, HasDerivAt A (A' x) x)
    (hA'c : Continuous A') {C γ γ' : ℝ} (hC : 0 ≤ C) (hγ : γ < γ')
    (hlen : 2 * C * (γ' - γ) ≤ c) (hbound : ∀ x ∈ Icc γ γ', |c * A' x / A x - 1| ≤ C)
    (h1 : ψ γ - (c : ℂ) * deriv ψ γ = 0) (h2 : ψ γ' - (c : ℂ) * deriv ψ γ' = 0) :
    ∫ x in γ..γ', ((ψ x).re / A x) ^ 2 ≤
      4 / c ^ 2 * (γ' - γ) ^ 2 * ∫ x in γ..γ', ((ψ x - (c : ℂ) * deriv ψ x).re / A x) ^ 2 := by
  obtain ⟨x₀, hx₀, hzero⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hψ c hnz hγ h1 h2
  have hψd : Differentiable ℂ ψ := LaguerrePolya.differentiable hψ
  have hdd : Differentiable ℂ (deriv ψ) := fun z => ((hψd.analyticAt z).deriv).differentiableAt
  set f : ℝ → ℝ := fun x => (ψ x).re with hf
  set f' : ℝ → ℝ := fun x => (deriv ψ x).re with hf'
  have hfd : ∀ x, HasDerivAt f (f' x) x := fun x =>
    ((hψd (x : ℂ)).hasDerivAt).real_of_complex
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hfd x).continuousAt
  have hf'c : Continuous f' :=
    Complex.continuous_re.comp (hdd.continuous.comp Complex.continuous_ofReal)
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hAd x).continuousAt
  set s : ℝ → ℝ := fun x => f x / A x with hs
  set Z : ℝ → ℝ := fun x => (ψ x - (c : ℂ) * deriv ψ x).re / A x with hZ
  set cc : ℝ → ℝ := fun x => c * A' x / A x - 1 with hcc
  have hZeq : ∀ x, Z x = (f x - c * f' x) / A x := by
    intro x
    simp only [hZ, hf, hf', Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hderiv : ∀ x ∈ Icc γ γ', HasDerivAt s (-(Z x + cc x * s x) / c) x := by
    intro x _
    have hA0 := (hApos x).ne'
    have h := (hfd x).div (hAd x) hA0
    refine h.congr_deriv ?_
    rw [hZeq x]
    simp only [hs, hcc]
    field_simp
    ring
  have hZc : ContinuousOn Z (Icc γ γ') := by
    refine Continuous.continuousOn ?_
    have : Z = fun x => (f x - c * f' x) / A x := funext hZeq
    rw [this]
    exact (hfc.sub (continuous_const.mul hf'c)).div hAc fun x => (hApos x).ne'
  have hccc : ContinuousOn cc (Icc γ γ') :=
    (((continuous_const.mul hA'c).div hAc fun x => (hApos x).ne').sub
      continuous_const).continuousOn
  have hs0 : s x₀ = 0 := by
    simp only [hs, hf, hzero, Complex.zero_re, zero_div]
  exact integral_sq_le_of_firstOrderFilter hc hC hγ.le hlen hderiv hZc hccc hbound hx₀ hs0

end

end RHTower

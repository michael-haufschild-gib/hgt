import GaloisForLFunctions.RHTower.SuzukiWeilRaySeriesIdentity
import GaloisForLFunctions.RHTower.XiCauchyTransformCompleteness

/-!
# Bridge from the transform ray series to the corpus Cauchy transform

Step 3b(ii) of the route to Suzuki's Lemma 3.2.  The corpus already proves the fibre residue
(`RHTower.xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball` in
`XiCauchyTransformCompleteness`), so nothing here needs to be constructed — only matched.

Two points make the match:

* `xiCauchyTransform u z = sum conj(u q) (gamma_q - z)^{-1}` while the ray series is
  `sum b_q / (z - gamma_q)`, so the right vector is `u q = conj(b_q)` and the transform is *minus*
  the ray series;
* `b_q = a_q / gamma_q` is square summable because `|a_q| <= (e^{T/2}+1) ‖phi‖_1` uniformly
  (every Xi zero has `|Im gamma| < 1/2`) and `xiSpectralPoint_inv_sq_summable`.

With `suzukiPHatRaySum_eq_zero_off_divisor` supplying vanishing on the whole divisor complement —
much more than the "real part zero on one ball" the corpus theorem asks for — the fibre sums vanish,
which is `m_gamma * conj(F(-gamma)) = 0`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-- The divisor vector whose Cauchy transform is minus the ray series. -/
def suzukiRayVectorFun (φ : ℝ → ℂ) (q : XiZeroCopy) : ℂ :=
  (starRingEnd ℂ) ((∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
    * (starRingEnd ℂ) (φ t)) / xiSpectralPoint q)

theorem memℓp_suzukiRayVectorFun {φ : ℝ → ℂ} (hφ : Integrable φ) {T : ℝ}
    (hsupp : ∀ t : ℝ, T < |t| → φ t = 0) :
    Memℓp (suzukiRayVectorFun φ) 2 := by
  set M : ℝ := (Real.exp (T / 2) + 1) * ∫ t : ℝ, ‖φ t‖ with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (by positivity) (integral_nonneg fun t => norm_nonneg _)
  refine HilbertSchmidt.memℓp_of_sq ?_
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left (M ^ (2 : ℕ)))
  have hnum := norm_raySeriesNumerator_le hφ hsupp q
  have hγpos : (0 : ℝ) < ‖xiSpectralPoint q‖ :=
    norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hu : ‖suzukiRayVectorFun φ q‖
      = ‖∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
          * (starRingEnd ℂ) (φ t)‖ / ‖xiSpectralPoint q‖ := by
    rw [suzukiRayVectorFun, Complex.norm_conj, norm_div]
  rw [hu, div_pow]
  rw [div_le_iff₀ (by positivity)]
  have hsq : ‖∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
      * (starRingEnd ℂ) (φ t)‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
    have h0 : (0 : ℝ) ≤ ‖∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
        * (starRingEnd ℂ) (φ t)‖ := norm_nonneg _
    nlinarith [hnum, h0, hM0]
  calc ‖∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
        * (starRingEnd ℂ) (φ t)‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := hsq
    _ = M ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
        field_simp

theorem xiCauchyTransform_suzukiRayVector {φ : ℝ → ℂ} (hφ : Integrable φ) {T : ℝ}
    (hsupp : ∀ t : ℝ, T < |t| → φ t = 0) (z : ℂ) :
    xiCauchyTransform ⟨suzukiRayVectorFun φ, memℓp_suzukiRayVectorFun hφ hsupp⟩ z
      = -∑' q : XiZeroCopy, suzukiPHatRayTerm φ z q := by
  rw [xiCauchyTransform, ← tsum_neg]
  refine tsum_congr fun q => ?_
  have hcoe : (⟨suzukiRayVectorFun φ, memℓp_suzukiRayVectorFun hφ hsupp⟩ :
      lp (fun _ : XiZeroCopy => ℂ) 2) q = suzukiRayVectorFun φ q := rfl
  rw [hcoe, suzukiRayVectorFun, Complex.conj_conj, suzukiPHatRayTerm]
  rcases eq_or_ne (xiSpectralPoint q) 0 with h0 | h0
  · exact absurd h0 (xiSpectralPoint_ne_zero q)
  · rcases eq_or_ne (z - xiSpectralPoint q) 0 with h1 | h1
    · have h2 : xiSpectralPoint q - z = 0 := by linear_combination -h1
      rw [h1, h2]
      simp
    · have h2 : xiSpectralPoint q - z ≠ 0 := fun hc => h1 (by linear_combination -hc)
      field_simp
      ring

end
end RHTower


import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheBoxCameraPaysItsExteriorMass
import GaloisForLFunctions.MultiscaleMollifiedZetaField.BoxCameraTuranProfile

/-!
# Near-top clusters with geometric exterior loss

The finite Turán signal and the full multiplicity-weighted exterior bound
give a lower bound for the actual zero field. Without a gap assumption,
the same bound holds or a deep exterior zero lies within the prescribed
ordinate distance.
-/

noncomputable section

open Complex MeasureTheory Set
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open SquareRootThreshold (zetaZeroWidth)

def widthCenteredBoxZeroField (A h : ℝ) (n : ℕ) (r y t : ℝ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
    paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (gammaOf ρ - t)

/-- The full exterior cost, with the shallow part evaluated at the first lag. -/
def boxExteriorBound (A h : ℝ) (n : ℕ) (r g d y t : ℝ) : ℝ :=
  ((2 / h) * ((1 + g ^ 2) / g ^ 2) * (1 / (h * g)) ^ n +
    (4 * A + 4 / h) * Real.exp (-(d * (y - boxCameraRadius A h n r)))) * lorentzMass t

theorem exists_nu_widthCenteredBoxZeroField_ge_of_deep_gap
    {A h r ℓ t η g d : ℝ} (hA : 0 < A) (hh : 0 < h) (hr : 0 < r)
    (n : ℕ) (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hg : 0 < g) (hd : 0 ≤ d)
    {M N : ℕ} (hN : 1 ≤ N)
    (hy : boxCameraRadius A h n r ≤ ((M : ℝ) + 1) * ℓ)
    {s : Finset zetaZeroConfig.carrier} (hcard : s.card ≤ N)
    (hsec : ∀ ρ ∈ s, |(ρ : ℂ).im - t| * boxCameraRadius A h n r ≤ 1 / 10)
    {ρ : zetaZeroConfig.carrier} (hρ : ρ ∈ s)
    (hnear : zetaZeroWidth - η ≤ (ρ : ℂ).re - 1 / 2)
    (hgap : ∀ q : zetaZeroConfig.carrier, q ∉ s →
      zetaZeroWidth - d ≤ (q : ℂ).re - 1 / 2 → g ≤ |(q : ℂ).im - t|) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧
      A * turanConstant N M *
        Real.exp (-(η * (((M : ℝ) + N) * ℓ + boxCameraRadius A h n r))) -
          boxExteriorBound A h n r g d (((M : ℝ) + 1) * ℓ) t ≤
        ‖widthCenteredBoxZeroField A h n r ((ν : ℝ) * ℓ) t‖ := by
  obtain ⟨ν, hν1, hνN, hsignal⟩ := exists_nu_widthCenteredBox_cluster_signal
    hA hh hr n hℓ hη hN hcard hsec hρ hnear
  have hlow : ((M : ℝ) + 1) * ℓ ≤ (ν : ℝ) * ℓ := by
    apply mul_le_mul_of_nonneg_right _ hℓ.le
    exact_mod_cast hν1
  have hyν := hy.trans hlow
  have hs := summable_widthCenteredBoxCamera hA.le hh hr n hyν (t := t)
  have hmass0 : 0 ≤ lorentzMass t := by
    simpa only [Finset.sum_empty] using sum_mult_unit_le_lorentzMass t ∅ (by simp)
  have htail := norm_tsum_sub_sum_le hs s
    (c := boxExteriorBound A h n r g d (((M : ℝ) + 1) * ℓ) t) (fun F hF => by
      have hb := sum_widthCenteredBoxCamera_exterior_le_deep_gap hA.le hh hr hg n hyν hd F
        (fun q hq hdeep => hgap q (fun hqs => Finset.disjoint_left.mp hF hq hqs) hdeep)
      simp only [norm_mul, Complex.norm_natCast]
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ hmass0
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith only [hlow, hd])
  refine ⟨ν, hν1, hνN, ?_⟩
  have htri := norm_sub_norm_le
    (∑ q ∈ s, (zetaZeroConfig.mult q : ℂ) *
      paperFT (boxCenteredCamera A h n r zetaZeroWidth ((ν : ℝ) * ℓ)) (gammaOf q - t))
    (widthCenteredBoxZeroField A h n r ((ν : ℝ) * ℓ) t)
  rw [norm_sub_rev] at htri
  change ‖widthCenteredBoxZeroField A h n r ((ν : ℝ) * ℓ) t - _‖ ≤ _ at htail
  linarith only [hsignal, htail, htri]

/-- Every eligible cluster is visible at the stated level, or has a deep
exterior companion. No exterior mass or gap is assumed. -/
theorem widthCenteredBox_cluster_visible_or_deep_companion
    {A h r ℓ t η g d : ℝ} (hA : 0 < A) (hh : 0 < h) (hr : 0 < r)
    (n : ℕ) (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hg : 0 < g) (hd : 0 ≤ d)
    {M N : ℕ} (hN : 1 ≤ N)
    (hy : boxCameraRadius A h n r ≤ ((M : ℝ) + 1) * ℓ)
    {s : Finset zetaZeroConfig.carrier} (hcard : s.card ≤ N)
    (hsec : ∀ ρ ∈ s, |(ρ : ℂ).im - t| * boxCameraRadius A h n r ≤ 1 / 10)
    {ρ : zetaZeroConfig.carrier} (hρ : ρ ∈ s)
    (hnear : zetaZeroWidth - η ≤ (ρ : ℂ).re - 1 / 2) :
    (∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧
      A * turanConstant N M *
        Real.exp (-(η * (((M : ℝ) + N) * ℓ + boxCameraRadius A h n r))) -
          boxExteriorBound A h n r g d (((M : ℝ) + 1) * ℓ) t ≤
        ‖widthCenteredBoxZeroField A h n r ((ν : ℝ) * ℓ) t‖) ∨
    ∃ q : zetaZeroConfig.carrier, q ∉ s ∧
      zetaZeroWidth - d ≤ (q : ℂ).re - 1 / 2 ∧ |(q : ℂ).im - t| < g := by
  classical
  by_cases hc : ∃ q : zetaZeroConfig.carrier, q ∉ s ∧
      zetaZeroWidth - d ≤ (q : ℂ).re - 1 / 2 ∧ |(q : ℂ).im - t| < g
  · exact Or.inr hc
  · apply Or.inl
    apply exists_nu_widthCenteredBoxZeroField_ge_of_deep_gap hA hh hr n hℓ hη hg hd hN
      hy hcard hsec hρ hnear
    intro q hq hdeep
    exact le_of_not_gt fun hclose => hc ⟨q, hq, hdeep, hclose⟩

end GaloisForLFunctions.MultiscaleMollifiedZetaField

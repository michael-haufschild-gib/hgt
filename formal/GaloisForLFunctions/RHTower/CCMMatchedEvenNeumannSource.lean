import GaloisForLFunctions.RHTower.CCMFiniteNeumannFormDecay

open Filter
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Literal even pole source at the matched anchor. -/
def ccmMatchedEvenPoleSource (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  (1 / 2 : ℂ) • (ccmPolarApertureVector a (1 / 2) + ccmPolarApertureVector a (-1 / 2))

theorem norm_ccmMatchedEvenPoleSource_le (a : SuzukiPositiveAperture) :
    ‖ccmMatchedEvenPoleSource a‖ ≤ Real.exp (a.1 / 2) := by
  have he : (Real.exp (a.1 / 2)) ^ 2 = Real.exp a.1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hbound (f : suzukiApertureHilbert a) (hf : ‖f‖ ^ 2 = 2 * Real.sinh a.1) :
      ‖f‖ ≤ Real.exp (a.1 / 2) := by
    rw [Real.sinh_eq] at hf
    nlinarith [Real.exp_pos (-a.1), Real.exp_pos (a.1 / 2)]
  have hp := hbound _ (norm_sq_ccmPolarApertureVector_half a)
  have hm := hbound _ (norm_sq_ccmPolarApertureVector_neg_half a)
  unfold ccmMatchedEvenPoleSource
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [norm_smul, hhalf]
  have hs := norm_add_le (ccmPolarApertureVector a (1 / 2))
    (ccmPolarApertureVector a (-1 / 2))
  linarith

/-- The actual even pole source has the same admitted endpoint scale. -/
theorem ccmMatchedEvenPoleSource_budget (a : SuzukiPositiveAperture) :
    CCMFiniteExponentialBudget (ccmMatchedEvenPoleSource a : SoninL2) (Real.exp (a.1 / 2)) := by
  have hp : CCMFiniteExponentialBudget (ccmPolarL2Vector a (1 / 2)) (Real.exp (a.1 / 2)) := by
    convert CCMFiniteExponentialBudget.polar a (1 / 2) using 1
    norm_num
    ring
  have hm : CCMFiniteExponentialBudget (ccmPolarL2Vector a (-1 / 2)) (Real.exp (a.1 / 2)) := by
    convert CCMFiniteExponentialBudget.polar a (-1 / 2) using 1
    norm_num
    ring
  have hb := (hp.add hm).smul (1 / 2 : ℂ)
  change CCMFiniteExponentialBudget (ccmMatchedEvenPoleSource a : SoninL2) _ at hb
  convert hb using 1
  rw [norm_div, norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num
  ring

def ccmMatchedEvenNeumannVector (a : SuzukiPositiveAperture) (n : ℕ) : suzukiApertureHilbert a :=
  ccmFiniteNeumannVector a (ccmMatchedEvenPoleSource a) n

/-- An actual finite inverse for the even pole source, with all source
norm and endpoint-budget obligations discharged. -/
theorem eventually_ccmMatchedEvenPoleSource_neumann_decay :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
      ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
        let u := ccmMatchedEvenNeumannVector ⟨a, ha⟩ ⌈a⌉₊
        ‖u‖ ≤ M * Real.exp (a / 2) /
          boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ⟨a, ha⟩) ∧
        ‖ccmMatchedEvenPoleSource ⟨a, ha⟩ - ccmShiftedBoundedWeil ⟨a, ha⟩ u‖ ≤
          R * Real.exp (-7 * a / 2) := by
  obtain ⟨M, R, hM, hR, hbound⟩ := eventually_ccmFiniteExponentialSource_neumann_decay
  refine ⟨M, R, hM, hR, ?_⟩
  filter_upwards [hbound] with a haBound
  intro ha
  have h := haBound ha (ccmMatchedEvenPoleSource ⟨a, ha⟩) (Real.exp (a / 2))
    (norm_ccmMatchedEvenPoleSource_le ⟨a, ha⟩) (ccmMatchedEvenPoleSource_budget ⟨a, ha⟩)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The literal even Neumann source has an actual Gamma lift with vanishing
form energy and a decaying physical residual. No admission premise remains. -/
theorem eventually_ccmMatchedEvenNeumannVector_form_decay :
    ∃ D E : ℝ, 0 < D ∧ 0 < E ∧
      ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
        ∃ g : CCMArchimedeanFormDomain ⟨a, ha⟩,
          ccmArchimedeanFormToAperture ⟨a, ha⟩ g =
            ccmMatchedEvenNeumannVector ⟨a, ha⟩ ⌈a⌉₊ ∧
          ‖g‖ ^ 2 ≤ D * a * Real.exp (-a) ∧
          ‖ccmMatchedEvenPoleSource ⟨a, ha⟩ - ccmShiftedBoundedWeil ⟨a, ha⟩
            (ccmArchimedeanFormToAperture ⟨a, ha⟩ g)‖ ≤ E * Real.exp (-7 * a / 2) := by
  obtain ⟨D, E, hD, hE, hform⟩ := eventually_ccmFiniteExponentialSource_form_decay
  refine ⟨D, E, hD, hE, ?_⟩
  filter_upwards [hform] with a haForm
  intro ha
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  obtain ⟨g, hg, hgNorm, hrNorm⟩ := haForm ha (ccmMatchedEvenPoleSource ap)
    (Real.exp (a / 2)) (norm_ccmMatchedEvenPoleSource_le ap) (ccmMatchedEvenPoleSource_budget ap)
  refine ⟨g, hg, ?_, ?_⟩
  · have he : (Real.exp (a / 2)) ^ 2 * Real.exp (-2 * a) = Real.exp (-a) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ D * a * (Real.exp (a / 2)) ^ 2 * Real.exp (-2 * a) := hgNorm
      _ = (D * a) * ((Real.exp (a / 2)) ^ 2 * Real.exp (-2 * a)) := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ E * Real.exp (a / 2) * Real.exp (-4 * a) := hrNorm
      _ = E * Real.exp (-7 * a / 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

end RHTower
end

import GaloisForLFunctions.RHTower.ConstrainedProlateHeadDistance
import GaloisForLFunctions.RHTower.ConstrainedProlateFuchsModelTransfer

/-!
# The ground-direction metric law for the CCM Fuchs family

The sign-optimized distance between the exact constrained ground direction and the two-mode seed
is governed by a head-alignment defect and a tail fraction.  For the Connes–Consani–Moscovici
scale family `d_j(λ) = A_j λ^{8j+1} e^{−4πλ²}` those inputs are not hypotheses: the spectral
structure and the tail-ratio collapse are theorems about the family, and the nonvanishing of the
head coordinate follows from the root lying strictly inside the first gap.

Everything here is discharged from the family data `A` alone together with the coordinate limits.
-/

open Filter Set GaloisForLFunctions

noncomputable section

namespace RHTower

/-- The CCM Fuchs scale sequence at aperture `lam`. -/
def ccmFuchsScale (A : ℕ → ℝ) (lam : ℝ) : ℕ → ℝ := fun j => fuchsRate (A j) (4 * j) lam

/-- The exact constrained ground root of the CCM Fuchs family. -/
def ccmFuchsRoot (A : ℕ → ℝ) (ℓ : ℝ → ℕ → ℝ) (lam : ℝ) : ℝ :=
  infiniteSecularRoot (ccmFuchsScale A lam) (ℓ lam)

/-! ## Discharging the structural hypotheses -/

theorem ccm_struct {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2)) :
    ∀ᶠ lam : ℝ in atTop,
      (0 ≤ ccmFuchsScale A lam 0 ∧ ccmFuchsScale A lam 0 < ccmFuchsScale A lam 1 ∧
        ccmFuchsScale A lam 1 < ccmFuchsScale A lam 2) ∧
      ∀ j, ccmFuchsScale A lam 2 ≤ ccmFuchsScale A lam (j + 2) :=
  fuchsRate_radial_struct hA hC hgrow

theorem ccm_tail {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) :
    Tendsto (fun lam : ℝ =>
      lam * ccmFuchsScale A lam 1 / (ccmFuchsScale A lam 2 - ccmFuchsScale A lam 1))
      atTop (nhds 0) :=
  fuchsRate_radial_tail_ratio_tendsto_zero (hA 1) (hA 2)

/-! ## Discharging the nonvanishing hypotheses -/

theorem ccm_l0_ne_zero {ℓ : ℝ → ℕ → ℝ}
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0 :=
  hl0.eventually_ne (by positivity)

theorem ccm_l1_ne_zero {ℓ : ℝ → ℕ → ℝ}
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop, ℓ lam 1 ≠ 0 := by
  refine hl1.eventually_ne ?_
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  positivity

/-- **The head coordinate of the exact eigenvector never vanishes.**  The ground root lies
strictly above `d₀`, so the zeroth denominator `d₀ − μ` is strictly negative, and the numerator
`ℓ₀` is eventually nonzero. -/
theorem ccm_secularVector_zero_ne_zero {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop,
      secularVector (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam) 0 ≠ 0 := by
  filter_upwards [ccm_struct hA hC hgrow, hsum, ccm_l0_ne_zero hl0, ccm_l1_ne_zero hl1]
    with lam hst hsm h0 h1
  obtain ⟨⟨_, h01, h12⟩, hd2⟩ := hst
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsm h0 h1
  have hden : ccmFuchsScale A lam 0 - ccmFuchsRoot A ℓ lam ≠ 0 := by
    have : ccmFuchsScale A lam 0 < ccmFuchsRoot A ℓ lam := hrmem.1
    linarith
  rw [secularVector]
  exact div_ne_zero h0 hden

/-! ## The metric law -/

/-- **The exact constrained ground direction converges to the two-mode seed direction for the CCM
Fuchs family.**  No structural, tail, or nonvanishing hypothesis remains: all are discharged from
the family data.  What is assumed is only the coordinate data itself — square-summability, the
Bessel bound, and the two coordinate limits. -/
theorem ccm_tendsto_min_norm_secularHead_sub_twoModeSeed
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    Tendsto (fun lam => min
        (‖(‖secularHead (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)‖)⁻¹
            • secularHead (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)
          - (‖twoModeSeed (ℓ lam)‖)⁻¹ • twoModeSeed (ℓ lam)‖ ^ 2)
        (‖(‖secularHead (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)‖)⁻¹
            • secularHead (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)
          + (‖twoModeSeed (ℓ lam)‖)⁻¹ • twoModeSeed (ℓ lam)‖ ^ 2))
      atTop (nhds 0) := by
  have ha0 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by positivity
  have ha1 : (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ≠ 0 := by
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  exact tendsto_min_norm_secularHead_normalize_sub_twoModeSeed
    (ccm_secularVector_zero_ne_zero hA hC hgrow hsum hl0 hl1)
    (ccm_l0_ne_zero hl0)
    (secularVector_head_seed_defect_tendsto_zero ha0 ha1
      (ccm_struct hA hC hgrow) hsum hbessel (ccm_tail hA) hl0 hl1)

end RHTower

end

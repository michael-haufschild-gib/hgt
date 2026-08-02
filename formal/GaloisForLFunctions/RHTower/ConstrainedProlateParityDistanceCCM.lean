import GaloisForLFunctions.RHTower.ConstrainedProlateFullDistanceCCM
import GaloisForLFunctions.RHTower.ConstrainedProlateParityExactTransfer

/-!
# Full `ℓ²` metric law for the negative constrained-prolate parity sector

The negative Fourier sector uses the offset Fuchs ladder
`d_j(λ) = M_j λ^(8j+5) exp(-4πλ²)`, corresponding to prolate indices `4j+2`.
The general full-distance theorem already turns head alignment and tail collapse into convergence
of normalized `ℓ²` vectors up to sign.  This module discharges every structural, root,
summability, and tail-rate hypothesis for that offset ladder.

Only the genuine prolate coordinate inputs remain: square summability, the Bessel bound, and the
fixed-coordinate limits to the `h₂(0)` and `h₆(0)` Hermite values.
-/

open Filter Set GaloisForLFunctions

noncomputable section

namespace RHTower

/-- Negative-sector Fuchs scale, with paper modes `4j+2`. -/
def ccmNegativeFuchsScale (M : ℕ → ℝ) (lam : ℝ) : ℕ → ℝ :=
  fun j => fuchsRate (M j) (4 * j + 2) lam

/-- Exact infinite-dimensional constrained root in the negative sector. -/
def ccmNegativeFuchsRoot (M : ℕ → ℝ) (ℓ : ℝ → ℕ → ℝ) (lam : ℝ) : ℝ :=
  infiniteSecularRoot (ccmNegativeFuchsScale M lam) (ℓ lam)

theorem ccmNegative_struct {M : ℕ → ℝ} (hM : ∀ j, 0 < M j)
    {C : ℝ} (hC : 1 ≤ C) (hgrow : ∀ j, M 2 ≤ C ^ j * M (j + 2)) :
    ∀ᶠ lam : ℝ in atTop,
      (0 ≤ ccmNegativeFuchsScale M lam 0 ∧
        ccmNegativeFuchsScale M lam 0 < ccmNegativeFuchsScale M lam 1 ∧
        ccmNegativeFuchsScale M lam 1 < ccmNegativeFuchsScale M lam 2) ∧
      ∀ j, ccmNegativeFuchsScale M lam 2 ≤ ccmNegativeFuchsScale M lam (j + 2) := by
  simpa only [ccmNegativeFuchsScale] using
    fuchsRate_radial_offset2_struct hM hC hgrow

theorem ccmNegative_tail {M : ℕ → ℝ} (hM : ∀ j, 0 < M j) :
    Tendsto (fun lam : ℝ =>
      lam * ccmNegativeFuchsScale M lam 1 /
        (ccmNegativeFuchsScale M lam 2 - ccmNegativeFuchsScale M lam 1))
      atTop (nhds 0) := by
  simpa only [ccmNegativeFuchsScale] using
    fuchsRate_step4_tail_ratio_tendsto_zero (hM 1) (hM 2) 6

theorem ccmNegative_l0_ne_zero {ℓ : ℝ → ℕ → ℝ}
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop
      (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0 :=
  hl0.eventually_ne (by positivity)

theorem ccmNegative_l1_ne_zero {ℓ : ℝ → ℕ → ℝ}
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop, ℓ lam 1 ≠ 0 := by
  exact hl1.eventually_ne (by positivity)

theorem ccmNegative_memℓp {M : ℕ → ℝ} (hM : ∀ j, 0 < M j)
    {C : ℝ} (hC : 1 ≤ C) (hgrow : ∀ j, M 2 ≤ C ^ j * M (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop
      (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop,
      Memℓp (secularVector (ccmNegativeFuchsScale M lam) (ℓ lam)
        (ccmNegativeFuchsRoot M ℓ lam)) 2 := by
  filter_upwards [ccmNegative_struct hM hC hgrow, hsum,
    ccmNegative_l0_ne_zero hl0, ccmNegative_l1_ne_zero hl1]
      with lam hst hsm h0 h1
  obtain ⟨⟨_, h01, h12⟩, hd2⟩ := hst
  exact memℓp_secularVector h01 h12 hd2 hsm h0 h1

theorem ccmNegative_summable_secularVector_sq
    {M : ℕ → ℝ} (hM : ∀ j, 0 < M j)
    {C : ℝ} (hC : 1 ≤ C) (hgrow : ∀ j, M 2 ≤ C ^ j * M (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop
      (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop, Summable fun j =>
      secularVector (ccmNegativeFuchsScale M lam) (ℓ lam)
        (ccmNegativeFuchsRoot M ℓ lam) j ^ 2 := by
  filter_upwards [ccmNegative_struct hM hC hgrow, hsum,
    ccmNegative_l0_ne_zero hl0, ccmNegative_l1_ne_zero hl1]
      with lam hst hsm h0 h1
  obtain ⟨⟨_, h01, h12⟩, hd2⟩ := hst
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsm h0 h1
  have hlt : ccmNegativeFuchsRoot M ℓ lam < ccmNegativeFuchsScale M lam 2 := by
    rw [ccmNegativeFuchsRoot]
    exact hrmem.2.trans h12
  exact (summable_nat_add_iff
      (f := fun j => secularVector (ccmNegativeFuchsScale M lam) (ℓ lam)
        (ccmNegativeFuchsRoot M ℓ lam) j ^ 2) 2).mp
    (summable_secularVector_sq_tail hd2 hsm hlt)

theorem ccmNegative_secularVector_zero_ne_zero
    {M : ℕ → ℝ} (hM : ∀ j, 0 < M j)
    {C : ℝ} (hC : 1 ≤ C) (hgrow : ∀ j, M 2 ≤ C ^ j * M (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop
      (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop,
      secularVector (ccmNegativeFuchsScale M lam) (ℓ lam)
        (ccmNegativeFuchsRoot M ℓ lam) 0 ≠ 0 := by
  filter_upwards [ccmNegative_struct hM hC hgrow, hsum,
    ccmNegative_l0_ne_zero hl0, ccmNegative_l1_ne_zero hl1]
      with lam hst hsm h0 h1
  obtain ⟨⟨_, h01, h12⟩, hd2⟩ := hst
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsm h0 h1
  have hden : ccmNegativeFuchsScale M lam 0 - ccmNegativeFuchsRoot M ℓ lam ≠ 0 := by
    have hroot : ccmNegativeFuchsScale M lam 0 < ccmNegativeFuchsRoot M ℓ lam := by
      simpa only [ccmNegativeFuchsRoot] using hrmem.1
    linarith
  rw [secularVector]
  exact div_ne_zero h0 hden

/-- **The exact negative-sector constrained vector converges in normalized `ℓ²` distance,
up to sign, to its two-mode Hermite seed.**  Both vectors are literal `lp 2` values.  Every
offset-Fuchs structural and tail condition is discharged; only the true prolate coordinate inputs
remain explicit. -/
theorem ccm_tendsto_min_norm_lp_normalize_sub_negativeTwoModeSeed
    {M : ℕ → ℝ} (hM : ∀ j, 0 < M j)
    {C : ℝ} (hC : 1 ≤ C) (hgrow : ∀ j, M 2 ≤ C ^ j * M (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop
      (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    Tendsto (fun lam => min
        (‖(‖secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
              (ccmNegativeFuchsRoot M ℓ lam)‖)⁻¹ •
            secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
              (ccmNegativeFuchsRoot M ℓ lam)
          - (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ 2)
        (‖(‖secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
              (ccmNegativeFuchsRoot M ℓ lam)‖)⁻¹ •
            secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
              (ccmNegativeFuchsRoot M ℓ lam)
          + (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ 2))
      atTop (nhds 0) := by
  have ha0 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := by positivity
  have ha1 : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := by positivity
  refine tendsto_min_norm_lp_normalize_sub_twoModeSeed
    (V := fun lam => secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
      (ccmNegativeFuchsRoot M ℓ lam))
    (G := fun lam => twoModeSeedLp (ℓ lam))
    (D := fun lam => ccmNegativeFuchsScale M lam) (L := ℓ)
    (M := ccmNegativeFuchsRoot M ℓ)
    ((ccmNegative_memℓp hM hC hgrow hsum hl0 hl1).mono
      fun lam h => secularLp_coeFn h)
    (Eventually.of_forall fun lam => twoModeSeedLp_coeFn (ℓ lam))
    (ccmNegative_summable_secularVector_sq hM hC hgrow hsum hl0 hl1)
    (ccmNegative_secularVector_zero_ne_zero hM hC hgrow hsum hl0 hl1)
    (ccmNegative_l0_ne_zero hl0)
    (secularVector_head_seed_defect_tendsto_zero ha0 ha1
      (ccmNegative_struct hM hC hgrow) hsum hbessel (ccmNegative_tail hM) hl0 hl1)
    (secularVector_tail_fraction_tendsto_zero ha0 ha1
      (ccmNegative_struct hM hC hgrow) hsum hbessel (ccmNegative_tail hM) hl0 hl1)

end RHTower

end

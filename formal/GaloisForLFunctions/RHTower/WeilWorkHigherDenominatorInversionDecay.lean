import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionAmplitude

/-!
# Uniform oscillatory decay on the actual inversion path

All amplitude and phase bounds are derived on a fixed positive compact test
interval. This supplies the inverse-square majorant for the infinite moving
Fourier trace without a residue expansion or boundary regularity premise.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

/-- The actual normalized inverted mode, paired against a compact test. -/
def inversionCosinePairing (φ : ℝ → ℂ) (a b k y : ℝ) : ℂ :=
  ∫ x in a..b, (Real.cos (2 * Real.pi * k * inversionBoundaryPhase y x) : ℂ) *
    inversionAmplitude φ k y x

/-- Uniform decay, with kernel frequency and oscillatory frequency independently quantified. -/
theorem exists_inversion_exponential_decay {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : tsupport φ ⊆ Ioo a b) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ y ∈ Ioc 0 δ, Real.log y ≤ -1 →
      ∀ k : ℝ, 1 ≤ k → ∀ L : ℝ, L ≠ 0 →
        ‖∫ x in a..b, Complex.exp (I * (L : ℂ) * (inversionBoundaryPhase y x : ℂ)) *
          inversionAmplitude φ k y x‖ ≤ C / L ^ 2 := by
  obtain ⟨δ, M, G, hδ, hM, hG, hδa, hbound⟩ :=
    exists_inversionAmplitude_jets_bound (b := b) hφ ha
  let J := M * (G ^ 2 + 4 * G ^ 4 + 3 * G ^ 6)
  have hJ : 0 ≤ J := by positivity
  refine ⟨δ, (b - a) * J, hδ, mul_nonneg (sub_nonneg.mpr hab) hJ, ?_⟩
  intro y hy hlog k hk L hL
  have hk0 := lt_of_lt_of_le zero_lt_one hk
  have hy0 := hy.1
  have hyA := hy.2.trans hδa
  let A := inversionAmplitude φ k y
  let A' := inversionAmplitudeD φ k y
  let A'' := inversionAmplitudeDD φ k y
  let v := inversionBoundarySpeed y
  let vC := fun x => (v x : ℂ)
  let vD := fun x => (inversionBoundarySpeedD y x : ℂ)
  let vDD := fun x => (inversionBoundarySpeedDD y x : ℂ)
  let B₁ := phaseAmplitudeD A A' vC vD
  let B₂ := phaseAmplitudeDD A A' A'' vC vD vDD
  have hx0 : ∀ x ∈ uIcc a b, 0 < x := by
    rw [uIcc_of_le hab]
    exact fun x hx => ha.trans_le hx.1
  have hA : ∀ x ∈ uIcc a b, HasDerivAt A (A' x) x :=
    fun x hx => hasDerivAt_inversionAmplitude hφ hk0 hy0 (hx0 x hx)
  have hA' : ∀ x ∈ uIcc a b, HasDerivAt A' (A'' x) x :=
    fun x hx => hasDerivAt_inversionAmplitudeD hφ hk0 hy0 (hx0 x hx)
  have hv : ∀ x ∈ uIcc a b, HasDerivAt v (inversionBoundarySpeedD y x) x :=
    fun x hx => hasDerivAt_inversionBoundarySpeed (hx0 x hx) y
  have hv' : ∀ x ∈ uIcc a b, HasDerivAt (inversionBoundarySpeedD y)
      (inversionBoundarySpeedDD y x) x :=
    fun x hx => hasDerivAt_inversionBoundarySpeedD (hx0 x hx) y
  have hv0 : ∀ x ∈ uIcc a b, v x ≠ 0 := by
    intro x hx
    have hxa : a ≤ x := (uIcc_of_le hab ▸ hx).1
    exact (inversionBoundarySpeed_neg ha hxa hy0.le hyA).ne
  have hvc0 : ∀ x ∈ uIcc a b, vC x ≠ 0 := by
    intro x hx
    change (v x : ℂ) ≠ 0
    exact_mod_cast hv0 x hx
  have hd₁ : ∀ x ∈ uIcc a b, HasDerivAt (fun t => A t / (v t : ℂ)) (B₁ x) x :=
    fun x hx => hasDerivAt_phaseAmplitude (hA x hx) (hv x hx).ofReal_comp (hvc0 x hx)
  have hd₂ : ∀ x ∈ uIcc a b, HasDerivAt (fun t => B₁ t / (v t : ℂ)) (B₂ x) x :=
    fun x hx => hasDerivAt_phaseAmplitudeD (hA x hx) (hA' x hx)
      (hv x hx).ofReal_comp (hv' x hx).ofReal_comp (hvc0 x hx)
  have hAc : ContinuousOn A (uIcc a b) := fun x hx => (hA x hx).continuousAt.continuousWithinAt
  have hA'c : ContinuousOn A' (uIcc a b) := fun x hx => (hA' x hx).continuousAt.continuousWithinAt
  have hA''c : ContinuousOn A'' (uIcc a b) :=
    (continuousOn_inversionAmplitudeDD hφ hk0 hy0).mono hx0
  have hvr : ContinuousOn v (uIcc a b) := fun x hx => (hv x hx).continuousAt.continuousWithinAt
  have hvc : ContinuousOn vC (uIcc a b) := Complex.continuous_ofReal.comp_continuousOn hvr
  have hvDc : ContinuousOn vD (uIcc a b) :=
    fun x hx => (hv' x hx).ofReal_comp.continuousAt.continuousWithinAt
  have hvDDr : ContinuousOn (inversionBoundarySpeedDD y) (uIcc a b) := by
    have hd : ContinuousOn (fun x : ℝ => x ^ 2 + y ^ 2) (uIcc a b) := by fun_prop
    exact (by fun_prop : ContinuousOn (fun x : ℝ =>
      -6 * (x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4)) (uIcc a b)).div (hd.pow 4)
        fun x hx => pow_ne_zero 4 (inversionBoundaryDenom_pos (hx0 x hx) y).ne'
  have hvDDc : ContinuousOn vDD (uIcc a b) := Complex.continuous_ofReal.comp_continuousOn hvDDr
  have hvpow (n : ℕ) : ∀ x ∈ uIcc a b, vC x ^ n ≠ 0 :=
    fun x hx => pow_ne_zero n (hvc0 x hx)
  have hB₁ : ContinuousOn B₁ (uIcc a b) :=
    (hA'c.div hvc hvc0).sub ((hAc.mul hvDc).div (hvc.pow 2) (hvpow 2))
  have hB₂ : ContinuousOn B₂ (uIcc a b) :=
    (((hA''c.div (hvc.pow 2) (hvpow 2)).sub
      (((continuousOn_const.mul hA'c).mul hvDc).div (hvc.pow 3) (hvpow 3))).sub
      ((hAc.mul hvDDc).div (hvc.pow 3) (hvpow 3))).add
      (((continuousOn_const.mul hAc).mul (hvDc.pow 2)).div (hvc.pow 4) (hvpow 4))
  have heA := inversionAmplitude_endpoint
    (show a ∉ tsupport φ from fun h => (lt_irrefl a) (hs h).1) k y
  have heB := inversionAmplitude_endpoint
    (show b ∉ tsupport φ from fun h => (lt_irrefl b) (hs h).2) k y
  have hn := norm_nonstationary_twice_le hab hL
    (fun x hx => hasDerivAt_inversionBoundaryPhase (hx0 x hx) y) hvr hv0
    hd₁ hd₂ hB₁.intervalIntegrable hB₂.intervalIntegrable heA.1 heB.1
    (phaseAmplitudeD_eq_zero heA.1 heA.2) (phaseAmplitudeD_eq_zero heB.1 heB.2)
  have hBbound : ∀ x ∈ Icc a b, ‖B₂ x‖ ≤ J := by
    intro x hx
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hbound y hy hlog k hk x hx
    apply norm_phaseAmplitudeDD_le hM hG.le h0 h1 h2
    · simpa [vC, v, norm_inv, Complex.norm_real, Real.norm_eq_abs] using h3
    · simpa [vD, Complex.norm_real, Real.norm_eq_abs] using h4
    · simpa [vDD, Complex.norm_real, Real.norm_eq_abs] using h5
  have hi : (∫ x in a..b, ‖B₂ x‖) ≤ (b - a) * J := by
    calc
      _ ≤ ∫ _ in a..b, J := intervalIntegral.integral_mono_on hab
        hB₂.norm.intervalIntegrable intervalIntegrable_const hBbound
      _ = _ := by simp
  calc
    _ ≤ |L|⁻¹ ^ 2 * ∫ x in a..b, ‖B₂ x‖ := hn
    _ ≤ |L|⁻¹ ^ 2 * ((b - a) * J) := mul_le_mul_of_nonneg_left hi (sq_nonneg _)
    _ = (b - a) * J / L ^ 2 := by rw [inv_pow, sq_abs]; ring

/-- The full inverted cosine coefficient has one inverse-square bound for all small heights. -/
theorem exists_inversionCosinePairing_decay {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : tsupport φ ⊆ Ioo a b) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ y ∈ Ioc 0 δ, Real.log y ≤ -1 →
      ∀ k : ℝ, 1 ≤ k → ‖inversionCosinePairing φ a b k y‖ ≤ C / k ^ 2 := by
  obtain ⟨δ, C, hδ, hC, hdecay⟩ := exists_inversion_exponential_decay hφ ha hab hs
  refine ⟨δ, C / (2 * Real.pi) ^ 2, hδ, by positivity, ?_⟩
  intro y hy hlog k hk
  let L := 2 * Real.pi * k
  have hk0 := lt_of_lt_of_le zero_lt_one hk
  have hL : 0 < L := by dsimp [L]; positivity
  have hplus := hdecay y hy hlog k hk L hL.ne'
  have hminus := hdecay y hy hlog k hk (-L) (neg_ne_zero.mpr hL.ne')
  rw [neg_sq] at hminus
  have hA : ContinuousOn (inversionAmplitude φ k y) (uIcc a b) := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le (uIcc_of_le hab ▸ hx).1
    exact (hasDerivAt_inversionAmplitude hφ hk0 hy.1 hx0).continuousAt.continuousWithinAt
  have hP : ContinuousOn (inversionBoundaryPhase y) (uIcc a b) := by
    intro x hx
    exact (hasDerivAt_inversionBoundaryPhase
      (ha.trans_le (uIcc_of_le hab ▸ hx).1) y).continuousAt.continuousWithinAt
  have hi (s : ℝ) : IntervalIntegrable (fun x =>
      Complex.exp (I * (s : ℂ) * (inversionBoundaryPhase y x : ℂ)) *
        inversionAmplitude φ k y x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have heq : inversionCosinePairing φ a b k y =
      ((∫ x in a..b, Complex.exp (I * (L : ℂ) * (inversionBoundaryPhase y x : ℂ)) *
          inversionAmplitude φ k y x) +
        (∫ x in a..b, Complex.exp (I * ((-L : ℝ) : ℂ) * (inversionBoundaryPhase y x : ℂ)) *
          inversionAmplitude φ k y x)) / 2 := by
    rw [← intervalIntegral.integral_add (hi L) (hi (-L)), ← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [Complex.ofReal_cos, Complex.cos]
    have hp : ((2 * Real.pi * k * inversionBoundaryPhase y x : ℝ) : ℂ) * I =
        I * (L : ℂ) * (inversionBoundaryPhase y x : ℂ) := by dsimp [L]; push_cast; ring
    have hm : -((2 * Real.pi * k * inversionBoundaryPhase y x : ℝ) : ℂ) * I =
        I * ((-L : ℝ) : ℂ) * (inversionBoundaryPhase y x : ℂ) := by dsimp [L]; push_cast; ring
    rw [hp, hm]
    ring
  rw [heq, norm_div, Complex.norm_ofNat]
  calc
    _ ≤ ((C / L ^ 2) + (C / L ^ 2)) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact (norm_add_le _ _).trans (add_le_add hplus hminus)
    _ = (C / (2 * Real.pi) ^ 2) / k ^ 2 := by dsimp [L]; field_simp; ring

end RHTower.WeilHigherDenominator

import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilRemainderMultiplier

/-!
# One-step contraction for the literal odd remainder orbit

Exponential-band cancellation of the actual full remainder symbol controls
the low-frequency source. Its global full-line norm and the certified
finite-exponential tail control the complement. Physical compression and
the prescribed Suzuki shift retain this estimate for the actual operator.
The final recurrence applies uniformly to every natural iterate of the
actual odd pole source, with no assumed Riesz-response regularity.
-/

open MeasureTheory Set Filter
open scoped FourierTransform InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem cutoff_norm_le (s : Set ℝ) (hs : MeasurableSet s) (f : SoninL2) :
    ‖indicatorCutoff s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [indicatorCutoff_ae s hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs]
  · rw [indicator_of_notMem hxs, norm_zero]
    exact norm_nonneg _

private theorem full_remainder_low_band (a : SuzukiPositiveAperture) (R δ : ℝ)
    (hδ : 0 ≤ δ)
    (hband : ∀ ξ ∈ centralInterval R, ‖ccmArchimedeanRemainderScalar +
      (polarPrimeStieltjesSymbol a.1 (-2 * Real.pi * ξ) : ℂ)‖ ≤ δ) (f : SoninL2) :
    ‖ccmFullLineBoundedRemainder a
      (fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f)‖ ≤ δ * ‖f‖ := by
  let g := fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f
  have hcut : (fourierUnitary g : ℝ → ℂ) =ᵐ[volume]
      (centralInterval R).indicator (fun ξ => fourierUnitary f ξ) := by
    dsimp [g]
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact indicatorCutoff_ae _ _ _
  have hcmp : ∀ᵐ ξ : ℝ, ‖fourierUnitary (ccmFullLineBoundedRemainder a g) ξ‖ ≤
      ‖((δ : ℂ) • fourierUnitary f : SoninL2) ξ‖ := by
    filter_upwards [fourier_ccmFullLineBoundedRemainder_ae a g, hcut,
      Lp.coeFn_smul (δ : ℂ) (fourierUnitary f)] with ξ hB hQ hscalar
    rw [hB, hQ, hscalar, Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hδ]
    by_cases hξ : ξ ∈ centralInterval R
    · rw [indicator_of_mem hξ, norm_mul]
      exact mul_le_mul_of_nonneg_right (hband ξ hξ) (norm_nonneg _)
    · rw [indicator_of_notMem hξ, mul_zero, norm_zero]
      exact mul_nonneg hδ (norm_nonneg _)
  have h := Lp.norm_le_norm_of_ae_le hcmp
  rw [fourierUnitary.norm_map, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hδ, fourierUnitary.norm_map] at h
  exact h

private theorem source_tail_norm_le {f : SoninL2} {V R : ℝ}
    (hf : CCMFiniteExponentialBudget f V) (hR : 0 < R) :
    ‖f - fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f‖ ≤
      2 * V / (Real.pi * Real.sqrt R) := by
  have hV := hf.nonneg
  have ht := hf.fourier_tail_sq_le hR
  have hpos : 0 ≤ 2 * V / (Real.pi * Real.sqrt R) := by positivity
  have he : (2 * V / (Real.pi * Real.sqrt R)) ^ 2 = 4 * V ^ 2 / (Real.pi ^ 2 * R) := by
    simp only [div_pow, mul_pow, Real.sq_sqrt hR.le]
    ring
  have hs : ‖f - fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f‖ ^ 2 ≤
      (2 * V / (Real.pi * Real.sqrt R)) ^ 2 := by
    rw [he]
    refine ht.trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [sq_nonneg V]
  nlinarith only [hs, hpos, norm_nonneg (f - fourierCutoff (centralInterval R)
    (measurableSet_centralInterval R) f)]

/-- The literal remainder's signed Fourier symbol is small on every fixed
exponential band, including the scalar atom and Fourier normalization. -/
theorem eventually_ccmFullLineRemainder_symbol_small (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ξ : ℝ, |ξ| ≤ Real.exp (K * a) →
      ‖ccmArchimedeanRemainderScalar + (polarPrimeStieltjesSymbol a (-2 * Real.pi * ξ) : ℂ)‖ ≤
        (ε / 2) * Real.exp a := by
  filter_upwards [eventually_abs_polarPrimeStieltjesSymbol_le_exponentialFrequency
      (K + 1) (ε / 4) (by linarith) (by positivity),
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (2 * Real.pi)),
    Real.tendsto_exp_atTop.eventually
      (eventually_ge_atTop (4 * ‖ccmArchimedeanRemainderScalar‖ / ε))] with a hsymbol hpi hscalar
  intro ξ hξ
  have hfreq : |-2 * Real.pi * ξ| ≤ Real.exp ((K + 1) * a) := by
    calc
      _ = (2 * Real.pi) * |ξ| := by rw [abs_mul, abs_mul]; norm_num [abs_of_pos Real.pi_pos]
      _ ≤ (2 * Real.pi) * Real.exp (K * a) := mul_le_mul_of_nonneg_left hξ (by positivity)
      _ ≤ Real.exp a * Real.exp (K * a) := mul_le_mul_of_nonneg_right hpi (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hk : ‖ccmArchimedeanRemainderScalar‖ ≤ (ε / 4) * Real.exp a := by
    have h := (div_le_iff₀ hε).mp hscalar
    nlinarith only [h]
  calc
    _ ≤ ‖ccmArchimedeanRemainderScalar‖ + ‖(polarPrimeStieltjesSymbol a (-2 * Real.pi * ξ) : ℂ)‖ :=
      norm_add_le _ _
    _ = ‖ccmArchimedeanRemainderScalar‖ + |polarPrimeStieltjesSymbol a (-2 * Real.pi * ξ)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (ε / 4) * Real.exp a + (ε / 4) * Real.exp a := add_le_add hk (hsymbol _ hfreq)
    _ = _ := by ring

/-- Low-band cancellation and the exact Fourier tail control the complete
compressed operator on every physical aperture vector. -/
theorem norm_ccmRestrictedWeilBoundedRemainder_le_low_add_tail
    (a : SuzukiPositiveAperture) (R δ : ℝ) (hδ : 0 ≤ δ)
    (hband : ∀ ξ ∈ centralInterval R, ‖ccmArchimedeanRemainderScalar +
      (polarPrimeStieltjesSymbol a.1 (-2 * Real.pi * ξ) : ℂ)‖ ≤ δ)
    (f : suzukiApertureHilbert a) :
    ‖ccmRestrictedWeilBoundedRemainder a f‖ ≤ δ * ‖f‖ +
      (‖ccmArchimedeanRemainderScalar‖ + 46) * Real.exp a.1 *
        ‖f.1 - fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f.1‖ := by
  let q := fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f.1
  have hlow := full_remainder_low_band a R δ hδ hband f.1
  have hsplit : ccmFullLineBoundedRemainder a f.1 =
      ccmFullLineBoundedRemainder a q + ccmFullLineBoundedRemainder a (f.1 - q) := by
    rw [map_sub]
    abel
  have hcomp : ‖ccmRestrictedWeilBoundedRemainder a f‖ ≤ ‖ccmFullLineBoundedRemainder a f.1‖ := by
    rw [ccmRestrictedWeilBoundedRemainder_eq_compressed_fullLine]
    change ‖(ccmApertureCompression a (ccmFullLineBoundedRemainder a) f : SoninL2)‖ ≤ _
    rw [ccmApertureCompression_val]
    exact cutoff_norm_le _ _ _
  calc
    _ ≤ ‖ccmFullLineBoundedRemainder a f.1‖ := hcomp
    _ ≤ ‖ccmFullLineBoundedRemainder a q‖ + ‖ccmFullLineBoundedRemainder a (f.1 - q)‖ :=
      hsplit ▸ norm_add_le _ _
    _ ≤ δ * ‖f‖ + ‖ccmFullLineBoundedRemainder a‖ * ‖f.1 - q‖ :=
      add_le_add hlow ((ccmFullLineBoundedRemainder a).le_opNorm _)
    _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
      (norm_ccmFullLineBoundedRemainder_le a) (norm_nonneg _))

private theorem normalized_source_step (a : SuzukiPositiveAperture) {R ε V : ℝ}
    (hR : 0 < R) (hε : 0 < ε)
    (hband : ∀ ξ ∈ centralInterval R, ‖ccmArchimedeanRemainderScalar +
      (polarPrimeStieltjesSymbol a.1 (-2 * Real.pi * ξ) : ℂ)‖ ≤ (ε / 2) * Real.exp a.1)
    (f : suzukiApertureHilbert a) (hf : CCMFiniteExponentialBudget f.1 V) :
    ‖ccmNormalizedWeilRemainder a f‖ ≤ ε * ‖f‖ +
      (4 * (‖ccmArchimedeanRemainderScalar‖ + 46) / Real.pi) * V / Real.sqrt R := by
  let D := ‖ccmArchimedeanRemainderScalar‖ + 46
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have hV := hf.nonneg
  have hbound := norm_ccmRestrictedWeilBoundedRemainder_le_low_add_tail a R
    ((ε / 2) * Real.exp a.1) (by positivity) hband f
  have htail := source_tail_norm_le hf hR
  have hfull : ‖ccmRestrictedWeilBoundedRemainder a f‖ ≤
      ((ε / 2) * Real.exp a.1) * ‖f‖ + D * Real.exp a.1 * (2 * V / (Real.pi * Real.sqrt R)) := by
    exact hbound.trans (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left htail (by positivity)))
  have hscale : Real.exp a.1 / c ≤ 2 :=
    (div_le_iff₀ hc).2 (exp_aperture_le_twice_suzukiWeilIntervalShift a)
  change ‖(c⁻¹ : ℂ) • ccmRestrictedWeilBoundedRemainder a f‖ ≤ _
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  calc
    _ ≤ c⁻¹ * (((ε / 2) * Real.exp a.1) * ‖f‖ +
        D * Real.exp a.1 * (2 * V / (Real.pi * Real.sqrt R))) :=
      mul_le_mul_of_nonneg_left hfull (by positivity)
    _ = (Real.exp a.1 / c) * ((ε / 2) * ‖f‖ + D * (2 * V / (Real.pi * Real.sqrt R))) := by ring
    _ ≤ 2 * ((ε / 2) * ‖f‖ + D * (2 * V / (Real.pi * Real.sqrt R))) :=
      mul_le_mul_of_nonneg_right hscale (by dsimp [D]; positivity)
    _ = _ := by dsimp [D]; ring

/-- A proved source norm estimate for the actual prescribed-shift remainder. -/
theorem eventually_ccmNormalizedWeilRemainder_budget_contraction
    (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ f : suzukiApertureHilbert ⟨a, ha⟩, ∀ V : ℝ,
      CCMFiniteExponentialBudget f.1 V →
      ‖ccmNormalizedWeilRemainder ⟨a, ha⟩ f‖ ≤ ε * ‖f‖ +
        (4 * (‖ccmArchimedeanRemainderScalar‖ + 46) / Real.pi) * V /
          Real.sqrt (Real.exp (K * a)) := by
  filter_upwards [eventually_ccmFullLineRemainder_symbol_small K ε hK hε] with a hband
  intro ha f V hf
  apply normalized_source_step ⟨a, ha⟩ (Real.exp_pos _) hε _ f hf
  intro ξ hξ
  apply hband ξ
  exact abs_le.mpr hξ

/-- The literal odd source orbit obeys the required one-step recurrence,
uniformly over every natural iteration count, without a regularity premise. -/
theorem eventually_ccmNormalizedWeilRemainder_odd_norm_recurrence
    (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ n : ℕ,
      let p := (1 / 2 : ℂ) • (ccmPolarApertureVector ⟨a, ha⟩ (1 / 2) -
        ccmPolarApertureVector ⟨a, ha⟩ (-1 / 2))
      let f := ((ccmNormalizedWeilRemainder ⟨a, ha⟩)^[n]) p
      ‖ccmNormalizedWeilRemainder ⟨a, ha⟩ f‖ ≤ ε * ‖f‖ +
        (4 * (‖ccmArchimedeanRemainderScalar‖ + 46) / Real.pi) *
          ((2 * (‖ccmArchimedeanRemainderScalar‖ + 46)) ^ n * Real.exp (a / 2)) /
            Real.sqrt (Real.exp (K * a)) := by
  filter_upwards [eventually_ccmNormalizedWeilRemainder_budget_contraction K ε hK hε] with a h
  intro ha n
  exact h ha _ _ (ccmNormalizedWeilRemainder_odd_iterate_budget ⟨a, ha⟩ n)

end RHTower
end

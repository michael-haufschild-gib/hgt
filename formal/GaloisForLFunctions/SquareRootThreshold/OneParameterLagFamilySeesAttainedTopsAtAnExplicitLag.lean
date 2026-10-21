import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyHidesOnlyInCollapsedClusters

/-!
# The one-parameter lag family sees attained tops at an explicit lag

`AttainedDepthIsVisible` shows that the lag family `P_v` of one width, the window functionals of the
difference tests `κ_w(t + v/2) − κ_w(t − v/2)`, turns negative when the largest real part of the
zeros is attained, without bounding the lag. With the cluster collapse of
`OneParameterLagFamilyHidesOnlyInCollapsedClusters` the first negative lag is explicit.

**Theorem** (`one_param_attained_top_visible`, `one_param_attained_top_primeWindow_neg`). Let
`½ + z₀` be a zero of `ζ` of largest real part `½ + δ₀`, `η = |h_w(γ₀ − iδ₀)| > 0`,
`Γ₀ = Γ₀(η)` (`oneParamRecordHeight`), `P ≥ 80 log(180Γ₀)`, and let `g > 0` separate the zeros
with `|Im ρ| ≤ Γ₀ + 1`, `Re ρ ≥ ½ + δ₀/4` (such `g` exists, `exists_box_count_and_separation`). If
`2κ₀/V ≤ δ₀/16`, `Vδ₀/8 ≥ 4π(k + P)`, `V δ₀ ≥ 2 log(80 log(180Γ₀)(e^{w/2}B_w)²/(2η²))` and
`B₀(p) < (gκ₀/(2(P + 1)))^p V^{2k+p+1} (δ₀/8)^{2k+1}` for every `p ≤ P`, then `P_v < 0` for some
`v ∈ [0, V]`; for `2w < log 2` this is the prime-side window functional `lagPrimeWindowRHS`.

The positivity of the record's cluster forces its companions to the record at geometric radius
`e^{−cVδ₀/p}`, while near an attained top the zeros are finitely many and `g`-separated; the
condition holds for `k ≳ P log(P/g)` and `Vδ₀ ≍ k + P`. So the first negative lag of the
one-parameter family at an attained top is
`O_w((log(1/η) · log(log(1/η)/g) + log log(1/η))/δ₀)`,
explicit in the depth `δ₀`, the transform `η` of the bump at the top zero, and the separation `g`.
This applies to every finite set of off-line zeros, whose top is attained.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **An attained top is seen by `P_v` at an explicit lag.** Let `½ + z₀` be a zero of largest real
part `½ + δ₀`, `η = |h_w(γ₀ − iδ₀)| > 0`, `Γ₀ = Γ₀(η)`, `P ≥ 80 log(180Γ₀)`, and let the zeros in the
box `|Im ρ| ≤ Γ₀ + 1`, `Re ρ ≥ ½ + δ₀/4` keep mutual distance `≥ g > 0`. Let `k ≥ 1`, `κ₀ ≥ 1`,
`2κ₀/V ≤ δ₀/16`, `V ≥ π(k + P)`, `Vδ₀/8 ≥ 4π(k + P)`,
`V δ₀ ≥ 2 log(80 log(180Γ₀)(e^{w/2}B_w)²/(2η²))`, and for every `p ≤ P`
`B₀(p) < (g κ₀/(2(P + 1)))^p V^{2k+p+1} (δ₀/8)^{2k+1}`. Then some difference test
`κ_w(t + v/2) − κ_w(t − v/2)`, `v ∈ [0, V]`, is Weil negative. -/
theorem one_param_attained_top_visible {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re) {P : ℕ}
    (hP : 80 * Real.log (180 * oneParamRecordHeight w η) ≤ P) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ ≠ ρ' →
      |ρ.im| ≤ oneParamRecordHeight w η + 1 → |ρ'.im| ≤ oneParamRecordHeight w η + 1 →
      1 / 2 + z₀.re / 4 ≤ ρ.re → 1 / 2 + z₀.re / 4 ≤ ρ'.re → g ≤ ‖ρ - ρ'‖)
    {V κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀) (hV : 0 < V)
    (hV2 : 2 * Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2)) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + P : ℕ) ≤ V)
    (hVr : 4 * π * (k + P : ℕ) ≤ V * (z₀.re / 8))
    (hmain : ∀ p : ℕ, p ≤ P → oneParamCollapseBound w η κ₀ k p <
      (g * κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1)) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  classical
  by_contra hneg
  push Not at hneg
  set D := evenCoeff zetaZeroConfig (modScaledBump w 0) with hDdef
  set Γ := oneParamRecordHeight w η with hΓdef
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · exact h
    · have := conj_mem_zetaZeroConfig h
      have e : conj (1 / 2 + conj x) = 1 / 2 + x := by apply Complex.ext <;> simp
      rwa [e] at this
  have htop' : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V := fun ρ hρ => by
    have := htop ρ hρ; have : 0 < 1 / V := one_div_pos.mpr hV; linarith
  obtain ⟨z₁, hz₁, hre₁, hup, -, C, hz₁C, hCP, hCmem, -, hbound⟩ :=
    one_param_cluster_collapse hw hz₀ hre₀ hη hηle hV htop' hneg hP hk hκ₀ hV2 hκV hVk hVr
  set p := C.card with hp
  have hr3 : z₀.re / 8 + 2 * κ₀ / V ≤ 3 * z₀.re / 16 := by linarith
  have hz₁box : |(1 / 2 + z₁).im| ≤ Γ + 1 ∧ 1 / 2 + z₀.re / 4 ≤ (1 / 2 + z₁).re := by
    have e1 : (1 / 2 + z₁).im = z₁.im := by simp
    have e2 : (1 / 2 + z₁).re = 1 / 2 + z₁.re := by simp
    rw [e1, e2]
    exact ⟨by linarith only [hup], by linarith only [hre₁, hre₀]⟩
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1 : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hPr : g ^ p ≤ ∏ z ∈ C, ‖z - z₁‖ := by
    rw [hp, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => hg.le) fun z hz => ?_
    obtain ⟨hDz, hzr⟩ := hCmem z hz
    have hzz : ‖z - z₁‖ ≤ 3 * z₀.re / 16 := hzr.trans hr3
    have hbox : |(1 / 2 + z).im| ≤ Γ + 1 ∧ 1 / 2 + z₀.re / 4 ≤ (1 / 2 + z).re := by
      have e1 : (1 / 2 + z).im = z.im := by simp
      have e2 : (1 / 2 + z).re = 1 / 2 + z.re := by simp
      rw [e1, e2]
      have h1 := Complex.abs_im_le_norm (z - z₁)
      have h2 := Complex.abs_re_le_norm (z - z₁)
      rw [Complex.sub_im] at h1
      rw [Complex.sub_re] at h2
      have h3 := abs_sub_abs_le_abs_sub z.im z₁.im
      have h4 := neg_abs_le (z.re - z₁.re)
      constructor
      · linarith only [h1, h3, hzz, hup, hre₀1]
      · linarith only [h2, h4, hzz, hre₁, hre₀]
    have hne : (1 / 2 + z) ≠ 1 / 2 + z₁ := fun h => hz₁C (by
      have : z = z₁ := by simpa using h
      rwa [this] at hz)
    have := hsep _ (hmem z hDz) _ (hmem z₁ hz₁) hne hbox.1 hz₁box.1 hbox.2 hz₁box.2
    rwa [show (1 / 2 + z) - (1 / 2 + z₁) = z - z₁ by ring] at this
  have hcmp := hmain p hCP
  have hpos : 0 ≤ (κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1) := by
    have : 0 < κ₀ := by linarith
    positivity
  have h1 : g ^ p * ((κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1)) ≤
      (∏ z ∈ C, ‖z - z₁‖) * ((κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) *
        (z₀.re / 8) ^ (2 * k + 1)) := mul_le_mul_of_nonneg_right hPr hpos
  have e : (g * κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1) =
      g ^ p * ((κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1)) := by
    rw [mul_div_assoc, mul_pow]; ring
  have e2 : (∏ z ∈ C, ‖z - z₁‖) * ((κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) *
      (z₀.re / 8) ^ (2 * k + 1)) = (∏ z ∈ C, ‖z - z₁‖) * (κ₀ / (2 * (P + 1))) ^ p *
        V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1) := by ring
  rw [e] at hcmp
  rw [e2] at h1
  linarith only [hcmp, h1, hbound]

/-- **The prime-side form.** For `2w < log 2`, under the hypotheses of
`one_param_attained_top_visible`, some window functional `P_v`, `v ∈ [0, V]`, is negative:
`Re lagPrimeWindowRHS(v, w, ·) < 0`. -/
theorem one_param_attained_top_primeWindow_neg {w : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2)
    {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re) {P : ℕ}
    (hP : 80 * Real.log (180 * oneParamRecordHeight w η) ≤ P) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ ≠ ρ' →
      |ρ.im| ≤ oneParamRecordHeight w η + 1 → |ρ'.im| ≤ oneParamRecordHeight w η + 1 →
      1 / 2 + z₀.re / 4 ≤ ρ.re → 1 / 2 + z₀.re / 4 ≤ ρ'.re → g ≤ ‖ρ - ρ'‖)
    {V κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀) (hV : 0 < V)
    (hV2 : 2 * Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2)) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + P : ℕ) ≤ V)
    (hVr : 4 * π * (k + P : ℕ) ≤ V * (z₀.re / 8))
    (hmain : ∀ p : ℕ, p ≤ P → oneParamCollapseBound w η κ₀ k p <
      (g * κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1)) :
    ∃ v ∈ Icc (0 : ℝ) V, (lagPrimeWindowRHS v w (EF.weilTest
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re < 0 := by
  obtain ⟨v, hv, hneg⟩ := one_param_attained_top_visible hw hz₀ hre₀ hη hηle htop hP hg hsep hk hκ₀
    hV hV2 hκV hVk hVr hmain
  refine ⟨v, hv, ?_⟩
  rwa [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv.1] at hneg

end GaloisForLFunctions.SquareRootThreshold

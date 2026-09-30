import GaloisForLFunctions.RHTower.WeilDeviationFourierAnnihilation
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.RHTower.WeilFullConeSummableDeficitRigidity

/-!
# A Weil-positive system with density-zero excess over `Λ` is `Λ`

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_excessMeanVanishes`). Let `lam` be full-cone
Weil-positive with translation-bounded excess `a⁺ = (lam − Λ)⁺/√n`, and assume this excess has
vanishing mean. Then `lam(n) = Λ(n)` for every `n ≥ 2`. Nothing is assumed about the deficit.

**Special case** (`eq_vonMangoldt_of_weilPositiveFull_of_summable_excess`). The conclusion holds
when `Σ_n (lam(n) − Λ(n))⁺ / √n < ∞`.

**Proof.**
- The deviation `a = (lam − Λ)/√n` annihilates `𝓕h` for every smooth compactly supported `h`
  (`deviationPairing_fourier_eq_zero`).
- Fix `m ≥ 2` and take the modulated dilated Fejér test `Φ(ξ) = F(ξ/(m+1)) e^{2πiξ log m}`.
  Its transform is `(m+1) 𝓕F((m+1)(u − log m))`, which vanishes unless `|u − log m| ≤ 17/(25(m+1))`.
  Since `|log n − log m| ≥ 1/(m+1)` for `n ≠ m`, this isolates `log m` among all `±log n`. So the
  pairing of `Φ` is `a(m)(m+1)∫F`.
- The cut-off tests `Φ χ(·/Γ)` pair to zero, and the tails tend to zero. Hence `a(m) = 0`.

**Corollaries.**
- `riemannHypothesis_iff_exists_weilPositiveFull_summable_excess`: RH holds iff some full-cone
  Weil-positive `lam` has summable excess over `Λ`.
- `not_summable_excess_of_ne` and `not_summable_deficit_of_ne`: a full-cone Weil-positive
  `lam ≠ Λ` has infinite excess and infinite deficit.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ContDiff

namespace RHTower.WeilExcess

noncomputable section

/-! ## The modulated Fejér test -/

/-- The dilated Fejér test modulated to frequency `x`: `F(ξ/s) e^{2πiξx}`. -/
def modulatedFejer (s x ξ : ℝ) : ℂ :=
  Complex.exp (-(2 * π * ξ * -x : ℝ) * I) * dilatedFejer s ξ

theorem fourier_modulatedFejer (s x u : ℝ) :
    𝓕 (modulatedFejer s x) u = 𝓕 (dilatedFejer s) (u - x) := by
  rw [fourier_eq_integral, fourier_eq_integral]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [modulatedFejer]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

theorem contDiff_modulatedFejer (s x : ℝ) : ContDiff ℝ ∞ (modulatedFejer s x) := by
  have h1 : ContDiff ℝ ∞ fun ξ : ℝ => ((2 * π * ξ * -x : ℝ) : ℂ) :=
    ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).mul contDiff_const)
  exact (Complex.contDiff_exp.comp (h1.neg.mul contDiff_const)).mul (contDiff_dilatedFejer s)

theorem integrable_modulatedFejer {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Integrable (modulatedFejer s x) :=
  integrable_exp_mul (integrable_dilatedFejer hs) (-x)

theorem integrable_fourier_modulatedFejer {s : ℝ} (hs : 1 ≤ s) (x : ℝ) :
    Integrable (𝓕 (modulatedFejer s x)) :=
  ((integrable_fourier_dilatedFejer hs).comp_sub_right x).congr
    (Eventually.of_forall fun u => (fourier_modulatedFejer s x u).symm)

theorem fourier_modulatedFejer_eq_zero {s : ℝ} (hs : 1 ≤ s) (x : ℝ) {u : ℝ}
    (hu : |x| + 17 / 25 < |u|) : 𝓕 (modulatedFejer s x) u = 0 := by
  rw [fourier_modulatedFejer]
  apply fourier_dilatedFejer_eq_zero hs
  have := abs_sub_abs_le_abs_sub u x
  linarith

/-! ## Isolating one logarithm -/

/-- Distinct logarithms of positive integers are `1/(m+1)`-separated from `log m`. -/
theorem inv_succ_le_abs_log_sub {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m) :
    1 / ((m : ℝ) + 1) ≤ |Real.log n - Real.log m| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rcases lt_or_gt_of_ne hnm with h | h
  · have h1 : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hm' hn')
    rw [Real.log_div hm'.ne' hn'.ne', inv_div] at hlog
    have h2 : 1 / ((m : ℝ) + 1) ≤ 1 - n / m := by
      rw [show 1 - (n : ℝ) / m = (m - n) / m by field_simp,
        div_le_div_iff₀ (by positivity) hm']
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m - n - 1) (by positivity : (0 : ℝ) ≤ m + 1)]
    exact le_abs.mpr (Or.inr (by linarith))
  · have h1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hn' hm')
    rw [Real.log_div hn'.ne' hm'.ne', inv_div] at hlog
    have h2 : 1 / ((m : ℝ) + 1) ≤ 1 - m / n := by
      rw [show 1 - (m : ℝ) / n = (n - m) / n by field_simp,
        div_le_div_iff₀ (by positivity) hn']
      nlinarith [mul_nonneg hm'.le (by linarith : (0 : ℝ) ≤ n - m - 1)]
    exact le_abs.mpr (Or.inl (by linarith))

theorem fourier_modulatedFejer_log {m : ℕ} (hm : 2 ≤ m) (n : ℕ) (hn : 2 ≤ n) :
    𝓕 (modulatedFejer ((m : ℝ) + 1) (Real.log m)) (-Real.log n) = 0 ∧
      (n ≠ m → 𝓕 (modulatedFejer ((m : ℝ) + 1) (Real.log m)) (Real.log n) = 0) := by
  have hs : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hlog2 : ∀ k : ℕ, 2 ≤ k → 17 / 25 < Real.log k := fun k hk =>
    seventeen_div_twentyfive_lt_log_two.trans_le (Real.log_le_log two_pos (by exact_mod_cast hk))
  refine ⟨?_, fun hnm => ?_⟩
  · rw [fourier_modulatedFejer]
    apply fourier_dilatedFejer_eq_zero hs
    have h1 := hlog2 n hn
    have h2 := hlog2 m hm
    rw [show -Real.log n - Real.log m = -(Real.log n + Real.log m) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  · rw [fourier_modulatedFejer, fourier_dilatedFejer (by linarith), fourier_fejerTestC_eq_zero,
      mul_zero]
    have hgap := inv_succ_le_abs_log_sub (by omega) (by omega) hnm
    rw [div_le_iff₀ (by positivity)] at hgap
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < (m : ℝ) + 1)]
    linarith

theorem fourier_modulatedFejer_log_self (m : ℕ) :
    𝓕 (modulatedFejer ((m : ℝ) + 1) (Real.log m)) (Real.log m) =
      (((m : ℝ) + 1 : ℝ) : ℂ) * 𝓕 fejerTestC 0 := by
  rw [fourier_modulatedFejer, sub_self, fourier_dilatedFejer (by positivity), mul_zero]

theorem integral_fejerTest_pos : 0 < ∫ ξ, fejerTest ξ := by
  obtain ⟨c, hc0, hcF⟩ := exists_fejerTest_lower
  have hF0 : 0 < fejerTest 0 := lt_trans (by norm_num) three_eighths_lt_fejerTest_zero
  have hint : Integrable fejerTest :=
    integrable_fejerTestC.norm.congr (Eventually.of_forall fun ξ => by
      simp only [fejerTestC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerTest_nonneg ξ)])
  rw [integral_pos_iff_support_of_nonneg (fun ξ => fejerTest_nonneg ξ) hint]
  have hsub : Ioo (-c) c ⊆ Function.support fejerTest := fun x hx => by
    rw [Function.mem_support]
    have := hcF x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
    exact (by linarith : 0 < fejerTest x).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo, ENNReal.ofReal_pos]
  linarith

theorem fourier_fejerTestC_zero_ne : 𝓕 fejerTestC 0 ≠ 0 := by
  rw [fourier_zero_eq_integral]
  have : (∫ x, fejerTestC x) = ((∫ x, fejerTest x : ℝ) : ℂ) := by
    simp only [fejerTestC]; exact integral_complex_ofReal
  rw [this, Complex.ofReal_ne_zero]
  exact integral_fejerTest_pos.ne'

/-- The deviation paired with the modulated test at `log m` is `a(m)(m+1)∫F`. -/
theorem hasSum_modulatedFejer (lam : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) :
    HasSum (fun n : ℕ => (weilDeviation lam n : ℂ) *
      (𝓕 (modulatedFejer ((m : ℝ) + 1) (Real.log m)) (Real.log n) +
        𝓕 (modulatedFejer ((m : ℝ) + 1) (Real.log m)) (-Real.log n)))
      ((weilDeviation lam m : ℂ) * ((((m : ℝ) + 1 : ℝ) : ℂ) * 𝓕 fejerTestC 0)) := by
  convert hasSum_single m (fun n hn => ?_) using 1
  · rw [fourier_modulatedFejer_log_self, (fourier_modulatedFejer_log hm m hm).1, add_zero]
  · by_cases hn2 : 2 ≤ n
    · rw [(fourier_modulatedFejer_log hm n hn2).1, (fourier_modulatedFejer_log hm n hn2).2 hn,
        add_zero, mul_zero]
    · simp [weilDeviation, hn2]

/-! ## Rigidity -/

/-- **The deviation vanishes.** -/
theorem weilDeviation_eq_zero {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {Dₑ : ℝ} (hexc : CauchyBounded (deviationExcess lam) Dₑ) (hmean : ExcessMeanVanishes lam)
    (m : ℕ) : weilDeviation lam m = 0 := by
  by_cases hm : 2 ≤ m
  swap
  · simp [weilDeviation, hm]
  obtain ⟨D, -, hD'⟩ := exists_tsum_deficit_cauchyProfile_le hW hexc
  have hD : CauchyBounded (deviationDeficit lam) D := hD'
  have hs : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set Φ := modulatedFejer ((m : ℝ) + 1) (Real.log m) with hΦ
  have hΦi : Integrable Φ := integrable_modulatedFejer (by linarith) _
  have htail := tendsto_deviationPairing_tail hexc hD (Φ := Φ)
    (contDiff_modulatedFejer _ _).continuous hΦi (integrable_fourier_modulatedFejer hs _)
    (b := |Real.log m| + 17 / 25) (by positivity)
    (fun u hu => fourier_modulatedFejer_eq_zero hs _ hu)
  have hX := hasSum_modulatedFejer lam hm
  have hconst : ∀ Γ : ℝ, 0 < Γ → deviationPairing lam (tailTransform Φ Γ) =
      (weilDeviation lam m : ℂ) * ((((m : ℝ) + 1 : ℝ) : ℂ) * 𝓕 fejerTestC 0) := by
    intro Γ hΓ
    have hsm : ContDiff ℝ ∞ fun ξ => Φ ξ * packet cutoffC 0 Γ ξ :=
      (contDiff_modulatedFejer _ _).mul (contDiff_packet contDiff_cutoffC 0 Γ)
    have hcp : HasCompactSupport fun ξ => Φ ξ * packet cutoffC 0 Γ ξ :=
      hasCompactSupport_mul_cutoff hΓ
    have hY := (summable_deviation_fourier_smooth hexc hD hsm hcp).hasSum
    have h0 := deviationPairing_fourier_eq_zero hW hexc hmean hsm hcp
    unfold deviationPairing at h0
    rw [h0] at hY
    have hsub := (hX.sub hY).tsum_eq
    rw [sub_zero] at hsub
    rw [← hsub]
    unfold deviationPairing
    refine tsum_congr fun n => ?_
    rw [fourier_eq_add_tailTransform hΦi Γ (Real.log n),
      fourier_eq_add_tailTransform hΦi Γ (-Real.log n)]
    ring
  have hlim : Tendsto (fun Γ => deviationPairing lam (tailTransform Φ Γ)) atTop
      (𝓝 ((weilDeviation lam m : ℂ) * ((((m : ℝ) + 1 : ℝ) : ℂ) * 𝓕 fejerTestC 0))) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop 0] with Γ hΓ using (hconst Γ hΓ).symm)
  have h0 := tendsto_nhds_unique hlim htail
  have hne : (((m : ℝ) + 1 : ℝ) : ℂ) * 𝓕 fejerTestC 0 ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) fourier_fejerTestC_zero_ne
  exact_mod_cast (mul_eq_zero.mp h0).resolve_right hne

theorem summable_deviationExcess {lam : ℕ → ℝ}
    (hexc : Summable fun n => max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 /
      Real.sqrt n) :
    Summable (deviationExcess lam) := by
  refine Summable.of_nonneg_of_le (deviationExcess_nonneg lam) (fun n => ?_) hexc
  unfold deviationExcess weilDeviation
  split_ifs with hn
  · have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
    rw [← max_div_div_right hsq.le, zero_div]
  · rw [max_self]
    exact div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)

/-- **Density-zero excess rigidity.** A full-cone Weil-positive `lam` whose excess over `Λ` is
translation-bounded with vanishing mean equals `Λ` at every `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_excessMeanVanishes {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {Dₑ : ℝ} (hexc : CauchyBounded (deviationExcess lam) Dₑ)
    (hmean : ExcessMeanVanishes lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  intro n hn
  have h := weilDeviation_eq_zero hW hexc hmean n
  rw [weilDeviation, if_pos hn, div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))).ne'

/-- A full-cone Weil-positive `lam ≠ Λ` with translation-bounded excess has an excess of positive
upper mean. -/
theorem not_excessMeanVanishes_of_ne {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ) {n : ℕ} (hn : 2 ≤ n)
    (hne : lam n ≠ ArithmeticFunction.vonMangoldt n) : ¬ ExcessMeanVanishes lam :=
  fun hmean => hne (eq_vonMangoldt_of_weilPositiveFull_of_excessMeanVanishes hW hexc hmean n hn)

/-- **Summable excess rigidity.** A full-cone Weil-positive `lam` whose excess over `Λ` is
summable against `n^{−1/2}` equals `Λ` at every `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_summable_excess {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hexc : Summable fun n => max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 /
      Real.sqrt n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  intro n hn
  have hs := summable_deviationExcess hexc
  have h := weilDeviation_eq_zero hW (cauchyBounded_of_summable (deviationExcess_nonneg lam) hs)
    (excessMeanVanishes_of_summable hs) n
  rw [weilDeviation, if_pos hn, div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))).ne'

/-- **RH as summable excess.** RH holds iff some full-cone Weil-positive `lam` has summable excess
over `Λ` against `n^{−1/2}`. -/
theorem riemannHypothesis_iff_exists_weilPositiveFull_summable_excess :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧
      Summable fun n => max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 / Real.sqrt n := by
  constructor
  · intro hRH
    refine ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, ?_⟩
    simp only [sub_self, max_self, zero_div]
    exact summable_zero
  · rintro ⟨lam, hW, hexc⟩
    have heq := eq_vonMangoldt_of_weilPositiveFull_of_summable_excess hW hexc
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hc => ?_
    have := hW f hf hc
    rwa [weilFullFunctional_congr heq] at this

/-- A full-cone Weil-positive `lam ≠ Λ` has infinite excess over `Λ`. -/
theorem not_summable_excess_of_ne {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {n : ℕ} (hn : 2 ≤ n)
    (hne : lam n ≠ ArithmeticFunction.vonMangoldt n) :
    ¬ Summable fun n => max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 / Real.sqrt n :=
  fun hexc => hne (eq_vonMangoldt_of_weilPositiveFull_of_summable_excess hW hexc n hn)

/-- A full-cone Weil-positive `lam ≠ Λ` has infinite deficit below `Λ`. -/
theorem not_summable_deficit_of_ne {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {n : ℕ} (hn : 2 ≤ n)
    (hne : lam n ≠ ArithmeticFunction.vonMangoldt n) :
    ¬ Summable fun n => max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 / Real.sqrt n :=
  fun hdef => hne (eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit hW hdef n hn)

end

end RHTower.WeilExcess

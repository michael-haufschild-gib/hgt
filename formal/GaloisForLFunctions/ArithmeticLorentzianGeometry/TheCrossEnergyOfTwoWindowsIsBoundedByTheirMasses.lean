import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheArchimedeanCrossEnergyIsOneSided

/-!
# The cross energy of two windows is bounded by their masses

`TheArchimedeanCrossEnergyIsOneSided` bounds the Lévy cross term of two windows by
`‖G_m‖₂‖G_n‖₂` times the Lévy mass of their pair window, `2w ω(s − w)`. Integrating the correlation
first loses nothing: `∫ |c_{mn}| ≤ ‖G_m‖₁‖G_n‖₁ ≤ w ‖G_m‖₂‖G_n‖₂` by Fubini, where the pair window
charged `2w`. The cross penalty halves.

* **The correlation** (`continuous_pairCorr`, `integral_abs_pairCorr_le`): `τ ↦ c_{mn}(τ)` is
  continuous, supported in `[−w, w]`, and `∫ |c_{mn}| ≤ ‖G_m‖₁ ‖G_n‖₁`.
* **One pair** (`integral_levy_abs_pairCorr_le`, `integral_levy_abs_pairCorr_eq_zero`): at
  log-distance `s ≥ 2w` the Lévy-weighted correlation is at most `ω(s − w) ‖G_m‖₁ ‖G_n‖₁`; at
  `s ≤ −2w` it vanishes on `(0, ∞)`.
* **The Lévy energy with masses** (`levyEnergy_windowTest_ge_masses`) and **the halved cross
  penalty** (`levyEnergy_windowTest_ge_fubini`):
  `levyEnergy f ≥ Σ levyEnergy G_m − (wN/2)[(2(1 + 1/λ)/(1 − κ)) D_N(y) + L_λ,κ |y|²]`.
* **The Markov form** (`eventually_markovEnergy_windowTest_ge_fubini`): the lower bound of
  `eventually_markovEnergy_windowTest_ge_sharp` with both cross constants halved.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

variable {G : ℕ → ℝ → ℝ} {w : ℝ}

/-! ### The correlation of two windows -/

theorem pairCorr_eq_setIntegral (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) (τ : ℝ) :
    pairCorr G m n τ = ∫ v in Set.Icc 0 w, G m v * G n (v + τ) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by
    rw [hGsupp m v hv, zero_mul]).symm

theorem continuous_pairCorr (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) : Continuous (pairCorr G m n) := by
  have h : Continuous fun τ => ∫ v in Set.Icc 0 w, G m v * G n (v + τ) :=
    continuous_parametric_integral_of_continuous (f := fun τ v => G m v * G n (v + τ))
      (((hG m).continuous.comp continuous_snd).mul
        ((hG n).continuous.comp (continuous_snd.add continuous_fst))) isCompact_Icc
  exact (funext fun τ => pairCorr_eq_setIntegral hGsupp m n τ) ▸ h

theorem integrable_abs_pairCorr (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) :
    Integrable fun τ => |pairCorr G m n τ| := by
  refine (continuous_pairCorr hG hGsupp m n).abs.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-w) w) isCompact_Icc fun τ hτ => ?_
  have : w < |τ| := by
    by_contra h
    exact hτ (abs_le.mp (not_lt.mp h))
  rw [pairCorr_eq_zero hGsupp m n this, abs_zero]

/-- **Fubini**: `∫ |c_{mn}| ≤ ‖G_m‖₁ ‖G_n‖₁`. -/
theorem integral_abs_pairCorr_le (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) :
    ∫ τ, |pairCorr G m n τ| ≤ (∫ v, |G m v|) * ∫ v, |G n v| := by
  set F : ℝ → ℝ → ℝ := fun τ v => |G m v| * |G n (v + τ)|
  have hFc : Continuous (Function.uncurry F) :=
    ((hG m).continuous.comp continuous_snd).abs.mul
      ((hG n).continuous.comp (continuous_snd.add continuous_fst)).abs
  have hFs : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.intro (K := Set.Icc (-w) w ×ˢ Set.Icc 0 w)
      (isCompact_Icc.prod isCompact_Icc) fun p hp => ?_
    obtain ⟨τ, v⟩ := p
    simp only [Function.uncurry_apply_pair, F]
    by_cases hv : v ∈ Set.Icc 0 w
    · by_cases hvτ : v + τ ∈ Set.Icc 0 w
      · exfalso
        exact hp ⟨⟨by linarith [hv.2, hvτ.1], by linarith [hv.1, hvτ.2]⟩, hv⟩
      · rw [hGsupp n _ hvτ, abs_zero, mul_zero]
    · rw [hGsupp m _ hv, abs_zero, zero_mul]
  have hF : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hFc.integrable_of_hasCompactSupport hFs
  have hpt : ∀ τ, |pairCorr G m n τ| ≤ ∫ v, F τ v := fun τ => by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    simp only [F, abs_mul]
  have hleft : Integrable fun τ => ∫ v, F τ v := hF.integral_prod_left
  calc ∫ τ, |pairCorr G m n τ| ≤ ∫ τ, ∫ v, F τ v :=
        integral_mono (integrable_abs_pairCorr hG hGsupp m n) hleft hpt
    _ = ∫ v, ∫ τ, F τ v := integral_integral_swap hF
    _ = ∫ v, |G m v| * ∫ τ, |G n τ| := by
        refine integral_congr_ae (ae_of_all _ fun v => ?_)
        simp only [F]
        rw [integral_const_mul, integral_add_left_eq_self (fun τ => |G n τ|) v]
    _ = (∫ v, |G m v|) * ∫ v, |G n v| := integral_mul_const _ _

/-! ### One pair -/

theorem integrableOn_levy_abs_pairCorr (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 < w) {s : ℝ} (hs : 2 * w ≤ |s|)
    (m n : ℕ) :
    IntegrableOn (fun t => archLevyDensity t * |pairCorr G m n (t - s)|) (Set.Ioi 0) := by
  have hwin := (window_integrable_and_le hw0 hs).1
  refine Integrable.mono' (hwin.const_mul (windowNorm G m * windowNorm G n))
    ((RHTower.measurable_archLevyDensity.mul
      ((continuous_pairCorr hG hGsupp m n).comp (continuous_sub_right s)).abs.measurable)
      |>.aestronglyMeasurable) ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht => ?_))
  have hω : 0 ≤ archLevyDensity t := (archLevyDensity_pos ht).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hω (abs_nonneg _))]
  by_cases hmem : t ∈ Set.Icc (s - w) (s + w)
  · rw [Set.indicator_of_mem hmem]
    have := abs_pairCorr_le hG hGsupp m n (t - s)
    nlinarith
  · rw [Set.indicator_of_notMem hmem, mul_zero]
    have hout : w < |t - s| := by
      by_contra h
      obtain ⟨h1, h2⟩ := abs_le.mp (not_lt.mp h)
      exact hmem ⟨by linarith, by linarith⟩
    rw [pairCorr_eq_zero hGsupp m n hout, abs_zero, mul_zero]

/-- **One pair to the right**: at log-distance `s ≥ 2w`,
`∫_0^∞ ω(t) |c_{mn}(t − s)| dt ≤ ω(s − w) ‖G_m‖₁ ‖G_n‖₁`. -/
theorem integral_levy_abs_pairCorr_le (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 < w) {s : ℝ} (hs : 2 * w ≤ s)
    (m n : ℕ) :
    ∫ t in Set.Ioi 0, archLevyDensity t * |pairCorr G m n (t - s)| ≤
      archLevyDensity (s - w) * ((∫ v, |G m v|) * ∫ v, |G n v|) := by
  have hint := integrableOn_levy_abs_pairCorr hG hGsupp hw0 (s := s)
    (by rw [abs_of_nonneg (by linarith)]; exact hs) m n
  have hshift : Integrable fun t => |pairCorr G m n (t - s)| :=
    (integrable_abs_pairCorr hG hGsupp m n).comp_sub_right s
  have hle : ∀ t ∈ Set.Ioi (0 : ℝ), archLevyDensity t * |pairCorr G m n (t - s)| ≤
      archLevyDensity (s - w) * |pairCorr G m n (t - s)| := fun t ht => by
    by_cases hmem : |t - s| ≤ w
    · obtain ⟨h1, h2⟩ := abs_le.mp hmem
      exact mul_le_mul_of_nonneg_right (archLevyDensity_antitoneOn
        (show (0 : ℝ) < s - w by linarith) ht (by linarith)) (abs_nonneg _)
    · rw [pairCorr_eq_zero hGsupp m n (not_le.mp hmem), abs_zero, mul_zero, mul_zero]
  have hω : 0 ≤ archLevyDensity (s - w) := (archLevyDensity_pos (show (0 : ℝ) < s - w by linarith)).le
  calc ∫ t in Set.Ioi 0, archLevyDensity t * |pairCorr G m n (t - s)|
      ≤ ∫ t in Set.Ioi 0, archLevyDensity (s - w) * |pairCorr G m n (t - s)| :=
        setIntegral_mono_on hint (hshift.const_mul _).integrableOn measurableSet_Ioi hle
    _ ≤ ∫ t, archLevyDensity (s - w) * |pairCorr G m n (t - s)| :=
        setIntegral_le_integral (hshift.const_mul _)
          (Filter.Eventually.of_forall fun t => mul_nonneg hω (abs_nonneg _))
    _ = archLevyDensity (s - w) * ∫ τ, |pairCorr G m n τ| := by
        rw [integral_const_mul, integral_sub_right_eq_self (fun τ => |pairCorr G m n τ|) s]
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_pairCorr_le hG hGsupp m n) hω

/-- **One pair to the left**: at log-distance `s ≤ −2w` the correlation vanishes on `(0, ∞)`. -/
theorem integral_levy_abs_pairCorr_eq_zero (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hw0 : 0 < w) {s : ℝ} (hs : s ≤ -(2 * w)) (m n : ℕ) :
    ∫ t in Set.Ioi 0, archLevyDensity t * |pairCorr G m n (t - s)| = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
    have ht0 : (0 : ℝ) < t := ht
    have : w < |t - s| := by rw [abs_of_pos (by linarith)]; linarith
    rw [pairCorr_eq_zero hGsupp m n this, abs_zero, mul_zero]

/-! ### The Lévy energy with masses -/

/-- **The Lévy energy of a window test with the masses of the pairs**:
`levyEnergy f ≥ Σ_m levyEnergy G_m − 2 Σ_{m ≠ n} ∫_0^∞ ω(t) |c_{mn}(t − log(n/m))| dt`. -/
theorem levyEnergy_windowTest_ge_masses (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 2) :
    ∑ m ∈ Icc 1 N, levyEnergy (G m) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else ∫ t in Set.Ioi 0,
          archLevyDensity t * |pairCorr G m n (t - (Real.log n - Real.log m))|) ≤
      levyEnergy (windowTest N G) := by
  have hδ := atomSpacing_pos hN
  have hw' : w < atomSpacing N := by linarith
  set ω := archLevyDensity
  have hsep : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n → 2 * w ≤ |Real.log n - Real.log m| := by
    intro m hm n hn hmn
    have := atomSpacing_le_abs_logGap hm hn hmn
    simp only [logGap] at this
    linarith
  set c : ℕ → ℕ → ℝ → ℝ := fun m n t =>
    if m = n then 0 else ω t * |pairCorr G m n (t - (Real.log n - Real.log m))|
  have hcint : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, IntegrableOn (c m n) (Set.Ioi 0) := by
    intro m hm n hn
    by_cases hmn : m = n
    · simp only [c, if_pos hmn]; exact integrableOn_zero
    · simp only [c, if_neg hmn]
      exact integrableOn_levy_abs_pairCorr hG hGsupp hw0 (hsep m hm n hn hmn) m n
  have hGint : ∀ m, IntegrableOn
      (fun t => ω t * ∫ u, (G m u - G m (u + t)) ^ 2) (Set.Ioi 0) :=
    fun m => integrableOn_levyIntegrand (hG m) (hasCompactSupport_profile hGsupp m)
  have hcsum : IntegrableOn (fun t => ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n t) (Set.Ioi 0) :=
    integrable_finsetSum _ fun m hm => integrable_finsetSum _ fun n hn => hcint m hm n hn
  have hdsum : IntegrableOn
      (fun t => ∑ m ∈ Icc 1 N, ω t * ∫ u, (G m u - G m (u + t)) ^ 2) (Set.Ioi 0) :=
    integrable_finsetSum _ fun m _ => hGint m
  set ℓ : ℝ → ℝ := fun t => ∑ m ∈ Icc 1 N, ω t * (∫ u, (G m u - G m (u + t)) ^ 2) -
    2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n t
  have hℓint : IntegrableOn ℓ (Set.Ioi 0) := hdsum.sub (hcsum.const_mul _)
  have hf := contDiff_windowTest hG N
  have hfc := hasCompactSupport_windowTest hGsupp N
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      ℓ t ≤ ω t * ∫ u, (windowTest N G u - windowTest N G (u + t)) ^ 2 := by
    intro t ht
    have hω0 : 0 ≤ ω t := (archLevyDensity_pos ht).le
    rw [integral_sub_shift_sq_windowTest_eq hG hGsupp hw' t]
    have hsum : ω t * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
        pairCorr G m n (t - (Real.log n - Real.log m))) ≤
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n t := by
      rw [mul_sum]
      refine sum_le_sum fun m _ => ?_
      rw [mul_sum]
      refine sum_le_sum fun n _ => ?_
      by_cases hmn : m = n
      · simp [c, hmn]
      simp only [c, if_neg hmn]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) hω0
    simp only [ℓ]
    have e : ω t * (∑ m ∈ Icc 1 N, (∫ u, (G m u - G m (u + t)) ^ 2) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
          pairCorr G m n (t - (Real.log n - Real.log m)))) =
        ∑ m ∈ Icc 1 N, ω t * (∫ u, (G m u - G m (u + t)) ^ 2) -
          2 * (ω t * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
            pairCorr G m n (t - (Real.log n - Real.log m)))) := by
      rw [mul_sub, Finset.mul_sum]; ring
    rw [e]
    linarith [hsum]
  have hLint : IntegrableOn
      (fun t => ω t * ∫ u, (windowTest N G u - windowTest N G (u + t)) ^ 2) (Set.Ioi 0) :=
    integrableOn_levyIntegrand hf hfc
  have hmono := setIntegral_mono_on hℓint hLint measurableSet_Ioi hpt
  have hℓ : ∫ t in Set.Ioi 0, ℓ t = ∑ m ∈ Icc 1 N, levyEnergy (G m) -
      2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ∫ t in Set.Ioi 0, c m n t := by
    simp only [ℓ]
    rw [integral_sub hdsum (hcsum.const_mul _), integral_const_mul,
      integral_finsetSum _ fun m _ => hGint m, integral_finsetSum _ fun m hm =>
        integrable_finsetSum _ fun n hn => hcint m hm n hn]
    congr 2
    exact sum_congr rfl fun m hm => integral_finsetSum _ fun n hn => hcint m hm n hn
  have hcbound : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ∫ t in Set.Ioi 0, c m n t =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else ∫ t in Set.Ioi 0,
        ω t * |pairCorr G m n (t - (Real.log n - Real.log m))|) := by
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    by_cases hmn : m = n
    · simp [c, hmn]
    · simp only [c, if_neg hmn]
  rw [hℓ] at hmono
  have hL : levyEnergy (windowTest N G) = ∫ t in Set.Ioi 0,
      ω t * ∫ u, (windowTest N G u - windowTest N G (u + t)) ^ 2 := rfl
  linarith

/-! ### The cross penalty from a symmetric pair bound -/

/-- **The cross penalty from a pair bound.** If a nonnegative array `V` has
`V_mn + V_nm ≤ y_m y_n · 2w(1/(2(1 − κ)|log(n/m)|) + 1)` for `m ≠ n`, then
`2 Σ_{m ≠ n} V_mn ≤ wN [(2(1 + 1/λ)/(1 − κ)) D_N(y) + L_λ,κ |y|²]`. -/
theorem two_mul_sum_cross_le {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w) {κ : ℝ}
    (hκ : κ ≤ 1 / 2) {lam : ℝ} (hlam : 0 < lam) {y : ℕ → ℝ} (hy0 : ∀ n, 0 ≤ y n)
    (V : ℕ → ℕ → ℝ)
    (hV : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n → V m n + V n m ≤
      y m * y n * (2 * w * (1 / (2 * (1 - κ) * |Real.log n - Real.log m|) + 1))) :
    2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else V m n) ≤
      w * N * (2 * (1 + 1 / lam) / (1 - κ) * poleDefect N y +
        crossConstant lam κ * ∑ n ∈ Icc 1 N, y n ^ 2) := by
  have hκ1 : 0 < 1 - κ := by linarith
  set k : ℕ → ℕ → ℝ := fun m n =>
    2 * w * (1 / (2 * (1 - κ) * |Real.log n - Real.log m|) + 1)
  have hk0 : ∀ m n, 0 ≤ k m n := fun m n =>
    mul_nonneg (by positivity) (add_nonneg (one_div_nonneg.mpr
      (mul_nonneg (mul_nonneg two_pos.le hκ1.le) (abs_nonneg _))) zero_le_one)
  have hks : ∀ m n, k n m = k m n := fun m n => by simp only [k, abs_sub_comm]
  set S := ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else V m n)
  have hswap : S = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else V n m) := by
    simp only [S]
    rw [sum_comm]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    by_cases h : n = m
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have habs : ∀ m n, y m * y n = |y m| * |y n| := fun m n => by
    rw [abs_of_nonneg (hy0 m), abs_of_nonneg (hy0 n)]
  have hS : 2 * S ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else |y m| * |y n| * k m n) := by
    have : 2 * S = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else (V m n + V n m)) := by
      rw [two_mul]
      nth_rewrite 2 [hswap]
      simp only [S, ← sum_add_distrib]
      refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    rw [this]
    refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
    split_ifs with h
    · exact le_rfl
    · rw [← habs]; exact hV m hm n hn h
  have hschur := RenormalizedArithmeticPotentialTheory.sum_abs_mul_sym_le N y k hk0 hks
  have hrow : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n) ≤
      w / (1 - κ) * (2 * m * (1 + Real.log (N + 1)) + N) + 2 * w * N := by
    intro m hm
    have hr := sum_inv_abs_log_sub_le hm
    have e : ∀ n ∈ Icc 1 N, (if m = n then 0 else k m n) ≤
        w / (1 - κ) * (if m = n then 0 else 1 / |Real.log n - Real.log m|) + 2 * w := by
      intro n _
      split_ifs
      · positivity
      · simp only [k]
        have : 2 * w * (1 / (2 * (1 - κ) * |Real.log n - Real.log m|)) =
            w / (1 - κ) * (1 / |Real.log n - Real.log m|) := by
          field_simp
        nlinarith
    have hconst : ∑ n ∈ Icc 1 N, (2 * w) = 2 * w * N := by
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    calc ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n)
        ≤ ∑ n ∈ Icc 1 N, (w / (1 - κ) * (if m = n then 0 else 1 / |Real.log n - Real.log m|) +
            2 * w) := sum_le_sum e
      _ = w / (1 - κ) * ∑ n ∈ Icc 1 N, (if m = n then 0 else 1 / |Real.log n - Real.log m|) +
            2 * w * N := by rw [sum_add_distrib, ← mul_sum, hconst]
      _ ≤ w / (1 - κ) * (2 * m * (1 + Real.log (N + 1)) + N) + 2 * w * N := by
          gcongr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrow' : ∀ m ∈ Icc 1 N, y m ^ 2 * ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n) ≤
      w * N / (1 - κ) * (2 * ((m : ℝ) / N * Real.log m * y m ^ 2) +
        (2 * (1 + Real.log 2) + 1) * y m ^ 2) + 2 * w * N * y m ^ 2 := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have h1 := hrow m hm
    have h2 := div_mul_one_add_log_le hm1 hmN
    have hym := sq_nonneg (y m)
    have e : w / (1 - κ) * (2 * m * (1 + Real.log (N + 1)) + N) =
        w * N / (1 - κ) * (2 * ((m : ℝ) / N * (1 + Real.log (N + 1))) + 1) := by
      field_simp
    calc y m ^ 2 * ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n)
        ≤ y m ^ 2 * (w / (1 - κ) * (2 * m * (1 + Real.log (N + 1)) + N) + 2 * w * N) :=
          mul_le_mul_of_nonneg_left h1 hym
      _ = w * N / (1 - κ) * (2 * ((m : ℝ) / N * (1 + Real.log (N + 1))) + 1) * y m ^ 2 +
            2 * w * N * y m ^ 2 := by rw [e]; ring
      _ ≤ w * N / (1 - κ) * (2 * ((m : ℝ) / N * Real.log m + (1 + Real.log 2)) + 1) * y m ^ 2 +
            2 * w * N * y m ^ 2 := by gcongr
      _ = _ := by ring
  have htop := sum_top_le_poleDefect_param N y hlam
  have hsum : ∑ m ∈ Icc 1 N, y m ^ 2 * ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n) ≤
      w * N / (1 - κ) * (2 * ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * y n ^ 2 +
        (2 * (1 + Real.log 2) + 1) * ∑ n ∈ Icc 1 N, y n ^ 2) +
        2 * w * N * ∑ n ∈ Icc 1 N, y n ^ 2 := by
    refine (sum_le_sum hrow').trans (le_of_eq ?_)
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
  have hcoef : 0 ≤ w * N / (1 - κ) := by positivity
  have h1 := hS.trans hschur
  have h2 := h1.trans hsum
  have h3 : w * N / (1 - κ) * (2 * ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * y n ^ 2) ≤
      w * N / (1 - κ) * (2 * ((1 + 1 / lam) * poleDefect N y +
        (1 + lam) * psiConstant * ∑ n ∈ Icc 1 N, y n ^ 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hcoef
  have e : w * N * (2 * (1 + 1 / lam) / (1 - κ) * poleDefect N y +
      crossConstant lam κ * ∑ n ∈ Icc 1 N, y n ^ 2) =
      w * N / (1 - κ) * (2 * ((1 + 1 / lam) * poleDefect N y +
        (1 + lam) * psiConstant * ∑ n ∈ Icc 1 N, y n ^ 2)) +
      w * N / (1 - κ) * ((2 * (1 + Real.log 2) + 1) * ∑ n ∈ Icc 1 N, y n ^ 2) +
      2 * w * N * ∑ n ∈ Icc 1 N, y n ^ 2 := by
    unfold crossConstant; field_simp; ring
  rw [e]
  nlinarith

/-- **The halved cross penalty.** For a window test at `w ≤ κ δ_N`, `0 ≤ κ ≤ 1/2`, `λ > 0`,
`levyEnergy f ≥ Σ levyEnergy G_m − (wN/2)[(2(1 + 1/λ)/(1 − κ)) D_N(y) + L_λ,κ |y|²]`. -/
theorem levyEnergy_windowTest_ge_fubini (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 2) (hwκ : w ≤ κ * atomSpacing N) {lam : ℝ}
    (hlam : 0 < lam) :
    ∑ m ∈ Icc 1 N, levyEnergy (G m) -
        w * N / 2 * (2 * (1 + 1 / lam) / (1 - κ) * poleDefect N (windowNorm G) +
          crossConstant lam κ * ∑ n ∈ Icc 1 N, windowNorm G n ^ 2) ≤
      levyEnergy (windowTest N G) := by
  have hδ := atomSpacing_pos hN
  have hw2 : w ≤ atomSpacing N / 2 := by nlinarith
  have hmaster := levyEnergy_windowTest_ge_masses hG hGsupp hN hw0 hw2
  set y := windowNorm G
  have hy0 : ∀ n, 0 ≤ y n := windowNorm_nonneg G
  have hκ1 : 0 < 1 - κ := by linarith
  set W : ℕ → ℕ → ℝ := fun m n => ∫ t in Set.Ioi 0,
    archLevyDensity t * |pairCorr G m n (t - (Real.log n - Real.log m))|
  -- `‖G_m‖₁‖G_n‖₁ ≤ w y_m y_n`
  have hmass : ∀ m n, (∫ v, |G m v|) * (∫ v, |G n v|) ≤ w * (y m * y n) := fun m n => by
    have h1 := integral_abs_profile_le hG hGsupp hw0 m
    have h2 := integral_abs_profile_le hG hGsupp hw0 n
    have hsw : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw0.le
    calc (∫ v, |G m v|) * (∫ v, |G n v|) ≤ (Real.sqrt w * y m) * (Real.sqrt w * y n) :=
          mul_le_mul h1 h2 (integral_nonneg fun _ => abs_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (hy0 m))
      _ = w * (y m * y n) := by
          rw [show Real.sqrt w * y m * (Real.sqrt w * y n) =
            (Real.sqrt w * Real.sqrt w) * (y m * y n) by ring, hsw]
  -- `W_mn + W_nm ≤ y_m y_n · w(1/(2(1 − κ)|log(n/m)|) + 1)`
  have hWW : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n → 2 * W m n + 2 * W n m ≤
      y m * y n * (2 * w * (1 / (2 * (1 - κ) * |Real.log n - Real.log m|) + 1)) := by
    intro m hm n hn hmn
    have hsep := atomSpacing_le_abs_logGap hm hn hmn
    simp only [logGap] at hsep
    have hwsep : w ≤ κ * |Real.log n - Real.log m| :=
      hwκ.trans (mul_le_mul_of_nonneg_left hsep hκ0)
    have hs2 : 2 * w ≤ |Real.log n - Real.log m| := by linarith
    have hyy : 0 ≤ y m * y n := mul_nonneg (hy0 m) (hy0 n)
    -- `ω(s − w) ≤ 1/(2(1 − κ)s) + 1`
    have hω : ∀ s : ℝ, 2 * w ≤ s → w ≤ κ * s →
        archLevyDensity (s - w) ≤ 1 / (2 * (1 - κ) * s) + 1 := by
      intro s hs hws
      have hsw : 0 < s - w := by linarith
      have h1 := archLevyDensity_le_inv_add_one hsw
      have h2 : 1 / (2 * (s - w)) ≤ 1 / (2 * (1 - κ) * s) :=
        one_div_le_one_div_of_le (mul_pos (mul_pos two_pos hκ1) (by linarith)) (by nlinarith)
      linarith
    rcases le_or_gt (Real.log n - Real.log m) 0 with hneg | hpos
    · have e : |Real.log n - Real.log m| = Real.log m - Real.log n := by
        rw [abs_of_nonpos hneg]; ring
      rw [e] at hwsep hs2
      have h1 : W m n = 0 := integral_levy_abs_pairCorr_eq_zero hGsupp hw0 (by linarith) m n
      have h2 : W n m ≤ archLevyDensity (Real.log m - Real.log n - w) *
          ((∫ v, |G n v|) * ∫ v, |G m v|) := integral_levy_abs_pairCorr_le hG hGsupp hw0 hs2 n m
      have h3 := hω _ hs2 hwsep
      have hω0 : 0 ≤ archLevyDensity (Real.log m - Real.log n - w) :=
        (archLevyDensity_pos (show (0 : ℝ) < Real.log m - Real.log n - w by linarith)).le
      have h4 := mul_le_mul_of_nonneg_left (hmass n m) hω0
      rw [e, h1]
      have : archLevyDensity (Real.log m - Real.log n - w) * (w * (y n * y m)) ≤
          (1 / (2 * (1 - κ) * (Real.log m - Real.log n)) + 1) * (w * (y m * y n)) := by
        rw [mul_comm (y n)]
        exact mul_le_mul_of_nonneg_right h3 (by positivity)
      nlinarith
    · have e : |Real.log n - Real.log m| = Real.log n - Real.log m := abs_of_pos hpos
      rw [e] at hwsep hs2
      have h1 : W n m = 0 := integral_levy_abs_pairCorr_eq_zero hGsupp hw0 (by linarith) n m
      have h2 : W m n ≤ archLevyDensity (Real.log n - Real.log m - w) *
          ((∫ v, |G m v|) * ∫ v, |G n v|) := integral_levy_abs_pairCorr_le hG hGsupp hw0 hs2 m n
      have h3 := hω _ hs2 hwsep
      have hω0 : 0 ≤ archLevyDensity (Real.log n - Real.log m - w) :=
        (archLevyDensity_pos (show (0 : ℝ) < Real.log n - Real.log m - w by linarith)).le
      have h4 := mul_le_mul_of_nonneg_left (hmass m n) hω0
      rw [e, h1]
      have : archLevyDensity (Real.log n - Real.log m - w) * (w * (y m * y n)) ≤
          (1 / (2 * (1 - κ) * (Real.log n - Real.log m)) + 1) * (w * (y m * y n)) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      nlinarith
  have hcross := two_mul_sum_cross_le hN hw0 hκ hlam hy0 (fun m n => 2 * W m n) hWW
  have e : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else 2 * W m n) =
      2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else W m n) := by
    rw [mul_sum]; refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  rw [e] at hcross
  linarith

/-! ### The Markov form at the halved cross penalty -/

/-- **The Markov form of a window test at the halved cross penalty.** For `ε > 0`,
`0 ≤ κ ≤ 1/2`, `λ > 0`, eventually in `N`: every window test at `w ≤ κ δ_N` with shape term
`β(G_n) ≥ β‖G_n‖²` has `M(f) ≥ φ₀ |y|² + c₀ D_N(y)`, where
`φ₀ = 2θ′(0) + log(1/(wN)) + 2c_∞ + β + γ − ε − (e^{1/2}/2) w − (L_λ,κ/2) wN` and
`c₀ = 1 − ε − ((1 + 1/λ)/(1 − κ)) wN`. -/
theorem eventually_markovEnergy_windowTest_ge_fubini {ε : ℝ} (hε : 0 < ε) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1 / 2) {lam : ℝ} (hlam : 0 < lam) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ κ * atomSpacing N →
      ∀ G : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 2 (G n)) → (∀ n u, u ∉ Set.Icc 0 w → G n u = 0) →
      ∀ β : ℝ, (∀ n, β * ∫ u, G n u ^ 2 ≤ bumpRobin (G n) w) →
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + archRobinConstant + β +
            Real.eulerMascheroniConstant - ε - Real.exp (1 / 2) / 2 * w -
            crossConstant lam κ / 2 * (w * N)) * (∑ n ∈ Icc 1 N, windowNorm G n ^ 2) +
          (1 - ε - (1 + 1 / lam) / (1 - κ) * (w * N)) * poleDefect N (windowNorm G) ≤
          markovEnergy (fun u => (windowTest N G u : ℂ)) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atomicWeilForm_add_poleDefect_le hε
  refine ⟨max N₁ 1, fun N hN w hw0 hw G hG hGsupp β hβ => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ := atomSpacing_pos hN1
  have hδ1 := atomSpacing_le_one hN1
  have hw2 : w ≤ atomSpacing N / 2 := by nlinarith
  have hw' : w < atomSpacing N := by linarith
  have hw1 : w ≤ 1 := by linarith
  have hf := contDiff_windowTest hG N
  have hfc := hasCompactSupport_windowTest hGsupp N
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    integral_windowTest_sq hG hGsupp hw']
  have hy : ∑ n ∈ Icc 1 N, ∫ u, G n u ^ 2 = ∑ n ∈ Icc 1 N, windowNorm G n ^ 2 :=
    sum_congr rfl fun n _ => (windowNorm_sq G n).symm
  rw [hy]
  have hlevy := levyEnergy_windowTest_ge_fubini hG hGsupp hN1 hw0 hκ0 hκ hw hlam
  have hP := hN₁ N (le_trans (le_max_left _ _) hN) (windowNorm G)
  have hprime := primeSum_windowTest_le hG hGsupp hw'
  have hself : (Real.log (1 / w) + archRobinConstant + β - Real.exp (1 / 2) / 2 * w) *
      (∑ n ∈ Icc 1 N, windowNorm G n ^ 2) ≤ ∑ m ∈ Icc 1 N, levyEnergy (G m) := by
    rw [mul_sum]
    refine sum_le_sum fun n _ => ?_
    rw [windowNorm_sq]
    have h1 := levyEnergy_profile_ge_shape (hG n) (hGsupp n) hw0 hw1
    have h2 := hβ n
    nlinarith
  have hlog : Real.log (1 / (w * N)) = Real.log (1 / w) - Real.log N := by
    rw [one_div, Real.log_inv, Real.log_mul hw0.ne' hN0.ne', one_div, Real.log_inv]; ring
  have hκ1 : 0 < 1 - κ := by linarith
  have e : w * N / 2 * (2 * (1 + 1 / lam) / (1 - κ) * poleDefect N (windowNorm G) +
      crossConstant lam κ * ∑ n ∈ Icc 1 N, windowNorm G n ^ 2) =
      (1 + 1 / lam) / (1 - κ) * (w * N) * poleDefect N (windowNorm G) +
        crossConstant lam κ / 2 * (w * N) * ∑ n ∈ Icc 1 N, windowNorm G n ^ 2 := by
    field_simp
  rw [e] at hlevy
  rw [hlog]
  nlinarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry

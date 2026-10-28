import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeAtEveryRoot

/-!
# The pole is the only negative square at every root

On the pole hyperplane `m₋ = 0` the Markov form is Weil's form, so RH is the statement that the
Markov form is nonnegative there (`riemannHypothesis_iff_forall_exp_neg_half_moment_zero_markovEnergy_nonneg`).
The Euler–Maclaurin synthesis carries this to the atomic families at every root: a pole-free test
`G` and a fixed bump `h` with `m₋(h) > 0` are synthesized with the same weights, and subtracting
`t` times the synthesized bump, `t = m₋(D_G)/m₋(h + D_h)`, moves the atomic test into the pole
hyperplane at a cost proportional to the synthesis error.

* **Correction into the pole hyperplane** (`exists_pole_correction`, `comb_perturbation`): for
  `m₋(F) = 0` and small `D₁, D₂`, `F + D₁ − t(h + D₂)` lies in the pole hyperplane with
  `|t| ≤ 2e^{R′/2}‖D₁‖₁/m₋(h)`, and `D₁ − t(h + D₂)` is a small Lipschitz perturbation.
* **Smooth pole-free negative tests** (`exists_smooth_poleFree_markov_neg`).
* **The pole hyperplane at every root**
  (`riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg_of_growthPow`): for every smooth
  profile and every dilation sequence of overlap growth of some order, RH holds iff for all large
  `N` the Markov form is nonnegative on the atomic tests of width `1/κ_N` in the pole hyperplane.
  With `markov_atomicFamilies_negative_of_growthPow`: at overlap ratio `(log N)^ε` the Markov form
  has a negative square unconditionally, and RH is the statement that it has only one, the pole.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower
open scoped Real ContDiff

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### Correction into the pole hyperplane -/

section Correction

/-- A smooth bump `h ≥ 0` supported in `[−2, 2]` with `m₋(h) > 0`. -/
theorem exists_smooth_bump_poleMomentNeg_pos :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ 0 < poleMomentNeg h := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨bump, bump.contDiff, bump.hasCompactSupport, ?_⟩
  unfold poleMomentNeg
  have hint : Integrable fun u => bump u * Real.exp (-(u / 2)) :=
    (bump.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      bump.hasCompactSupport.mul_right
  rw [integral_pos_iff_support_of_nonneg (fun u => mul_nonneg bump.nonneg (Real.exp_pos _).le) hint]
  have hs : (Function.support fun u => bump u * Real.exp (-(u / 2))) = Metric.ball 0 2 := by
    ext u
    simp only [Function.mem_support, ne_eq, mul_eq_zero, Real.exp_ne_zero, or_false]
    rw [← bump.support_eq, Function.mem_support]
  rw [hs]
  exact Metric.measure_ball_pos volume 0 two_pos

/-- **The corrected perturbation** `D = D₁ − t(h + D₂)`, `|t| ≤ T`: it is `C²`, supported in
`[−R′, R′]`, with supremum `≤ e₁ + T(M_h + e₂)` and Lipschitz constant `≤ L₁ + T(L_h + L₂)`. -/
theorem comb_perturbation {h D₁ D₂ : ℝ → ℝ} {R' e₁ e₂ L₁ L₂ Mh Lh t T : ℝ}
    (hh : ContDiff ℝ 2 h) (hhR : SupportedIn R' h) (hMh : ∀ u, |h u| ≤ Mh)
    (hLh : ∀ u v, |h u - h v| ≤ Lh * |u - v|) (hD₁ : ContDiff ℝ 2 D₁) (hD₁R : SupportedIn R' D₁)
    (he₁ : ∀ u, |D₁ u| ≤ e₁) (hL₁ : ∀ u v, |D₁ u - D₁ v| ≤ L₁ * |u - v|)
    (hD₂ : ContDiff ℝ 2 D₂) (hD₂R : SupportedIn R' D₂) (he₂ : ∀ u, |D₂ u| ≤ e₂)
    (hL₂ : ∀ u v, |D₂ u - D₂ v| ≤ L₂ * |u - v|) (ht : |t| ≤ T) :
    ContDiff ℝ 2 (fun u => D₁ u - t * (h u + D₂ u)) ∧
      SupportedIn R' (fun u => D₁ u - t * (h u + D₂ u)) ∧
      (∀ u, |D₁ u - t * (h u + D₂ u)| ≤ e₁ + T * (Mh + e₂)) ∧
      ∀ u v, |(D₁ u - t * (h u + D₂ u)) - (D₁ v - t * (h v + D₂ v))| ≤
        (L₁ + T * (Lh + L₂)) * |u - v| := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hLh0 : 0 ≤ Lh := by
    have := hLh 1 0; simp only [sub_zero, abs_one, mul_one] at this
    linarith [abs_nonneg (h 1 - h 0)]
  have hL₂0 : 0 ≤ L₂ := by
    have := hL₂ 1 0; simp only [sub_zero, abs_one, mul_one] at this
    linarith [abs_nonneg (D₂ 1 - D₂ 0)]
  refine ⟨hD₁.sub (contDiff_const.mul (hh.add hD₂)), fun u hu => by
    simp only [hD₁R u hu, hhR u hu, hD₂R u hu, add_zero, mul_zero, sub_zero], fun u => ?_,
    fun u v => ?_⟩
  · have h1 : |t * (h u + D₂ u)| ≤ T * (Mh + e₂) := by
      rw [abs_mul]
      exact mul_le_mul ht ((abs_add_le _ _).trans (add_le_add (hMh u) (he₂ u))) (abs_nonneg _) hT
    exact (abs_sub _ _).trans (add_le_add (he₁ u) h1)
  · have e : (D₁ u - t * (h u + D₂ u)) - (D₁ v - t * (h v + D₂ v)) =
        (D₁ u - D₁ v) - t * ((h u - h v) + (D₂ u - D₂ v)) := by ring
    rw [e]
    have h1 : |t * ((h u - h v) + (D₂ u - D₂ v))| ≤ T * ((Lh + L₂) * |u - v|) := by
      rw [abs_mul]
      refine mul_le_mul ht ((abs_add_le _ _).trans ?_) (abs_nonneg _) hT
      have := add_le_add (hLh u v) (hL₂ u v)
      linarith
    have := (abs_sub _ _).trans (add_le_add (hL₁ u v) h1)
    linarith

/-- **Correction into the pole hyperplane**: for `m₋(F) = 0`, `m₋(h) > 0` and `D₁, D₂` supported in
`[−R′, R′]` with `e^{R′/2} 2R′ e₂ ≤ m₋(h)/2`, some `t` with `|t| ≤ 2e^{R′/2} 2R′ e₁/m₋(h)` puts
`F + D₁ − t(h + D₂)` into the pole hyperplane. -/
theorem exists_pole_correction {F h D₁ D₂ : ℝ → ℝ} {R' e₁ e₂ : ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hF0 : poleMomentNeg F = 0) (hh : Continuous h)
    (hhc : HasCompactSupport h) (hh0 : 0 < poleMomentNeg h) (hD₁ : Continuous D₁)
    (hD₁R : SupportedIn R' D₁) (he₁ : ∀ u, |D₁ u| ≤ e₁) (hD₂ : Continuous D₂)
    (hD₂R : SupportedIn R' D₂) (he₂ : ∀ u, |D₂ u| ≤ e₂) (hR' : 0 ≤ R')
    (hsmall : Real.exp (R' / 2) * (2 * R' * e₂) ≤ poleMomentNeg h / 2) :
    ∃ t : ℝ, |t| ≤ 2 * (Real.exp (R' / 2) * (2 * R' * e₁)) / poleMomentNeg h ∧
      poleMomentNeg (fun u => F u + (D₁ u - t * (h u + D₂ u))) = 0 := by
  have hD₁c := hasCompactSupport_of_vanishes hD₁R
  have hD₂c := hasCompactSupport_of_vanishes hD₂R
  have hm₁ : |poleMomentNeg D₁| ≤ Real.exp (R' / 2) * (2 * R' * e₁) :=
    (abs_poleMomentNeg_le hD₁ hD₁c hD₁R).trans (mul_le_mul_of_nonneg_left
      (integral_abs_le_of_bound hD₁ hD₁c he₁ hD₁R hR') (Real.exp_pos _).le)
  have hm₂ : |poleMomentNeg D₂| ≤ Real.exp (R' / 2) * (2 * R' * e₂) :=
    (abs_poleMomentNeg_le hD₂ hD₂c hD₂R).trans (mul_le_mul_of_nonneg_left
      (integral_abs_le_of_bound hD₂ hD₂c he₂ hD₂R hR') (Real.exp_pos _).le)
  have hden : poleMomentNeg h / 2 ≤ poleMomentNeg h + poleMomentNeg D₂ := by
    have := neg_abs_le (poleMomentNeg D₂); linarith
  have hden0 : 0 < poleMomentNeg h + poleMomentNeg D₂ := by linarith
  refine ⟨poleMomentNeg D₁ / (poleMomentNeg h + poleMomentNeg D₂), ?_, ?_⟩
  · rw [abs_div, abs_of_pos hden0, div_le_iff₀ hden0]
    have h2 : 2 * (Real.exp (R' / 2) * (2 * R' * e₁)) / poleMomentNeg h * (poleMomentNeg h / 2) =
        Real.exp (R' / 2) * (2 * R' * e₁) := by field_simp
    have h3 : 0 ≤ 2 * (Real.exp (R' / 2) * (2 * R' * e₁)) / poleMomentNeg h :=
      div_nonneg (by linarith [abs_nonneg (poleMomentNeg D₁)]) hh0.le
    nlinarith [mul_le_mul_of_nonneg_left hden h3]
  · set t := poleMomentNeg D₁ / (poleMomentNeg h + poleMomentNeg D₂)
    have e : (fun u => F u + (D₁ u - t * (h u + D₂ u))) =
        fun u => F u + (D₁ u + (-t) * (h u + D₂ u)) := by funext u; ring
    have hhD : Continuous fun u => h u + D₂ u := hh.add hD₂
    have e1 : poleMomentNeg (fun u => F u + (D₁ u + -t * (h u + D₂ u))) =
        poleMomentNeg F + poleMomentNeg (fun u => D₁ u + -t * (h u + D₂ u)) :=
      poleMomentNeg_add hF hFc (hD₁.add (continuous_const.mul hhD))
        (hD₁c.add (hhc.add hD₂c).mul_left)
    have e2 : poleMomentNeg (fun u => D₁ u + -t * (h u + D₂ u)) =
        poleMomentNeg D₁ + poleMomentNeg (fun u => -t * (h u + D₂ u)) :=
      poleMomentNeg_add hD₁ hD₁c (continuous_const.mul hhD) (hhc.add hD₂c).mul_left
    have e3 : poleMomentNeg (fun u => -t * (h u + D₂ u)) =
        -t * poleMomentNeg (fun u => h u + D₂ u) := poleMomentNeg_const_mul (-t) _
    have e4 : poleMomentNeg (fun u => h u + D₂ u) = poleMomentNeg h + poleMomentNeg D₂ :=
      poleMomentNeg_add hh hhc hD₂ hD₂c
    rw [e, e1, e2, e3, e4, hF0]
    simp only [t]
    field_simp
    ring

/-- The errors of a corrected synthesis vanish: with `e₁, e₂ → 0`, `log k · e₁² → 0` and
`ℓ_i/k` convergent, `E = e₁ + C e₁ (M_h + e₂) → 0` and its Lévy bound with Lipschitz constant
`ℓ₁ + C e₁ (L_h + ℓ₂)` tends to `0`. -/
theorem tendsto_comb {R' C Mh Lh a₁ a₂ : ℝ} {e₁ e₂ ℓ₁ ℓ₂ k : ℕ → ℝ}
    (hk : Tendsto k atTop atTop) (he₁ : Tendsto e₁ atTop (𝓝 0)) (he₂ : Tendsto e₂ atTop (𝓝 0))
    (hlog : Tendsto (fun n => Real.log (k n) * e₁ n ^ 2) atTop (𝓝 0))
    (hℓ₁ : Tendsto (fun n => ℓ₁ n * (1 / k n)) atTop (𝓝 a₁))
    (hℓ₂ : Tendsto (fun n => ℓ₂ n * (1 / k n)) atTop (𝓝 a₂)) :
    Tendsto (fun n => e₁ n + C * e₁ n * (Mh + e₂ n)) atTop (𝓝 0) ∧
      Tendsto (fun n => synthLevy R' (e₁ n + C * e₁ n * (Mh + e₂ n))
        (ℓ₁ n + C * e₁ n * (Lh + ℓ₂ n)) (k n)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => 1 / k n) atTop (𝓝 0) := by
    simp only [one_div]; exact hk.inv_tendsto_atTop
  have hE : Tendsto (fun n => e₁ n + C * e₁ n * (Mh + e₂ n)) atTop (𝓝 0) := by
    have := he₁.add ((he₁.const_mul C).mul (he₂.const_add Mh))
    simpa using this
  refine ⟨hE, ?_⟩
  have hX : Tendsto (fun n => ℓ₁ n * (1 / k n) + C * e₁ n * (Lh * (1 / k n) + ℓ₂ n * (1 / k n)))
      atTop (𝓝 (a₁ + C * 0 * (Lh * 0 + a₂))) :=
    hℓ₁.add ((he₁.const_mul C).mul ((hinv.const_mul Lh).add hℓ₂))
  have hY : Tendsto (fun n => Real.log (k n) * e₁ n ^ 2 * (1 + C * (Mh + e₂ n)) ^ 2) atTop
      (𝓝 (0 * (1 + C * (Mh + 0)) ^ 2)) :=
    hlog.mul ((((he₂.const_add Mh).const_mul C).const_add 1).pow 2)
  have hV := ((hX.mul hE).const_mul (Real.exp (1 / 2) * (2 * R'))).add
    (((hY.const_mul 2).add ((hE.pow 2).const_mul levyLipConstant)).const_mul (2 * R'))
  simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hV
  refine hV.congr fun n => ?_
  unfold synthLevy
  ring

end Correction

/-! ### The pole hyperplane at every root -/

section EveryRoot

variable {φ : ℝ → ℝ} {κ : ℕ → ℝ} {q : ℕ}

/-- Sup and Lipschitz bounds of a smooth test from its derivative bounds. -/
theorem sup_lip_of_iteratedDeriv_bounds {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {M : ℕ → ℝ}
    (hM : ∀ l t, |iteratedDeriv l G t| ≤ M l) :
    (∀ t, |G t| ≤ M 0) ∧ ∀ u v, |G u - G v| ≤ M 1 * |u - v| :=
  ⟨fun t => by simpa using hM 0 t, abs_sub_le_of_hasDerivAt
    (fun t => (hG.differentiable (by simp) t).hasDerivAt) fun t => by simpa using hM 1 t⟩

/-- **Smooth pole-free negative tests**: a `C²` test in the pole hyperplane with `M < 0` yields a
smooth one: mollify, then correct by a multiple of a smooth bump. -/
theorem exists_smooth_poleFree_markov_neg (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (hu0 : poleMomentNeg u = 0) (hneg : markovQuad u < 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ poleMomentNeg G = 0 ∧
      markovQuad G < 0 := by
  obtain ⟨h, hh, hhc, hh0⟩ := exists_smooth_bump_poleMomentNeg_pos
  have hh2 : ContDiff ℝ 2 h := hh.of_le (natCast_le_infty 2)
  obtain ⟨Ru, Mu, Lu, hRu, huR, hMu, hLu⟩ := exists_test_bounds hu huc
  obtain ⟨Rh, Mh, Lh, hRh, hhR, hMh, hLh⟩ := exists_test_bounds hh2 hhc
  set R := max Ru Rh
  have huR' : SupportedIn R u := fun v hv => huR v (lt_of_le_of_lt (le_max_left _ _) hv)
  have hhR' : SupportedIn (R + 1) h := fun v hv => hhR v (by linarith [le_max_right Ru Rh])
  have hR : 0 ≤ R := hRu.trans (le_max_left _ _)
  obtain ⟨Err, hErr, hle⟩ := stableForm_markovQuad.2 u hu huc (R + 1) (by linarith)
    (fun v hv => huR' v (by linarith))
  set C := 2 * (Real.exp ((R + 1) / 2) * (2 * (R + 1))) / poleMomentNeg h
  obtain ⟨he, -, hlog, hℓ⟩ := tendsto_mollifyErr Lu (∫ s, |φ s|) Mu (∫ s, |deriv φ s|) (R + 1)
  obtain ⟨hE, hV⟩ := tendsto_comb (R' := R + 1) (C := C) (Mh := Mh) (Lh := Lh) (e₂ := fun _ => 0)
    (ℓ₂ := fun _ => 0) (a₂ := 0) tendsto_natCast_atTop_atTop he tendsto_const_nhds hlog hℓ
    (by simp)
  obtain ⟨n, hn1, hn2⟩ := (((hErr _ _ hE hV).eventually (gt_mem_nhds
    (show (0 : ℝ) < -markovQuad u by linarith))).and (eventually_ge_atTop 1)).exists
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn2
  obtain ⟨hD2, hDR, hsup, hlip⟩ := mollify_perturbation hφ hφ1 hφint hu huR' hMu hLu hn
  have hz : ∀ v, |(fun _ : ℝ => (0 : ℝ)) v| ≤ 0 := fun v => by simp
  have hzL : ∀ v w, |(fun _ : ℝ => (0 : ℝ)) v - (fun _ : ℝ => (0 : ℝ)) w| ≤ 0 * |v - w| :=
    fun v w => by simp
  obtain ⟨t, ht, ht0⟩ := exists_pole_correction hu.continuous huc hu0 hh.continuous hhc hh0
    hD2.continuous hDR hsup continuous_const (fun _ _ => rfl) hz (by linarith)
    (by simp; positivity)
  have hT : |t| ≤ C * (Lu * (1 / (n : ℝ)) * ∫ s, |φ s|) := by
    refine ht.trans (le_of_eq ?_); simp only [C]; ring
  obtain ⟨hD2', hDR', hsup', hlip'⟩ := comb_perturbation hh2 hhR' hMh hLh hD2 hDR hsup hlip
    contDiff_const (fun _ _ => rfl) hz hzL hT
  refine ⟨fun x => mollify u φ n x - t * h x,
    (contDiff_mollify hφ hφ1 hu.continuous (by linarith)).sub (contDiff_const.mul hh),
    (hasCompactSupport_of_vanishes (mollify_supportedIn hφ1 huR' hn)).sub hhc.mul_left, ?_, ?_⟩
  · rw [← ht0]; congr 1; funext x; ring
  · have h1 := hle _ _ _ _ hD2' hDR' hsup' hlip' hn
    have e : (fun x => u x + ((mollify u φ n x - u x) - t * (h x + 0))) =
        fun x => mollify u φ n x - t * h x := by funext x; ring
    rw [e] at h1
    linarith

/-- **Pole-free negative tests reach the atomic families at every root**: a smooth test in the pole
hyperplane with `M < 0` gives, for infinitely many `N`, an atomic test of width `1/κ_N` in the pole
hyperplane with `M < 0`. -/
theorem frequently_poleHyperplane_markov_neg (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hκ : OverlapGrowthPow q κ) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hGc : HasCompactSupport G) (hG0 : poleMomentNeg G = 0) (hneg : markovQuad G < 0) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, poleMomentNeg (atomicTest N x (dilate (κ N) φ)) = 0 ∧
      markovQuad (atomicTest N x (dilate (κ N) φ)) < 0 := by
  obtain ⟨h, hh, hhc, hh0⟩ := exists_smooth_bump_poleMomentNeg_pos
  have hG2 : ContDiff ℝ 2 G := hG.of_le (natCast_le_infty 2)
  have hh2 : ContDiff ℝ 2 h := hh.of_le (natCast_le_infty 2)
  obtain ⟨RG, -, -, hRG, hGR, -, -⟩ := exists_test_bounds hG2 hGc
  obtain ⟨Rh, -, -, hRh, hhR, -, -⟩ := exists_test_bounds hh2 hhc
  set R := max RG Rh
  have hR : 0 ≤ R := hRG.trans (le_max_left _ _)
  have hGR' : SupportedIn R G := fun v hv => hGR v (lt_of_le_of_lt (le_max_left _ _) hv)
  have hhR' : SupportedIn R h := fun v hv => hhR v (lt_of_le_of_lt (le_max_right _ _) hv)
  obtain ⟨MG, hMG0, hMG⟩ := exists_iteratedDeriv_bounds hG hGc
  obtain ⟨Mh, hMh0, hMh⟩ := exists_iteratedDeriv_bounds hh hhc
  obtain ⟨hhsup, hhlip⟩ := sup_lip_of_iteratedDeriv_bounds hh hMh
  obtain ⟨Err, hErr, hle⟩ := stableForm_markovQuad.2 G hG2 hGc (R + 1) (by linarith)
    (fun v hv => hGR' v (by linarith))
  have hκ' : OverlapGrowthPow (2 * (2 * q + 2)) κ := hκ.mono (by omega)
  set B := blockSize R
  have hB : 1 ≤ B := one_le_blockSize R
  set A : ℕ → ℝ := fun j => ∫ s, |iteratedDeriv j φ s|
  obtain ⟨he₁, -, hlog, hℓ₁⟩ := tendsto_em hκ' hB (M := MG) (A := A) (R' := R + 1)
  obtain ⟨he₂, -, -, hℓ₂⟩ := tendsto_em hκ' hB (M := Mh) (A := A) (R' := R + 1)
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  set C := 2 * (Real.exp ((R + 1) / 2) * (2 * (R + 1))) / poleMomentNeg h
  obtain ⟨hE, hV⟩ := tendsto_comb (R' := R + 1) (C := C) (Mh := Mh 0) (Lh := Mh 1)
    (hκ.1.comp hNB) he₁ he₂ hlog hℓ₁ hℓ₂
  have h1 := (hErr _ _ hE hV).eventually (gt_mem_nhds (show (0 : ℝ) < -markovQuad G by linarith))
  have hc0 : 0 < poleMomentNeg h / 2 / (Real.exp ((R + 1) / 2) * (2 * (R + 1))) := by
    have := Real.exp_pos ((R + 1) / 2); positivity
  have h2 := he₂.eventually (gt_mem_nhds hc0)
  have h3 := hNB.eventually (hκ.1.eventually_ge_atTop 1)
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨n, hn1, hn2, hk, hn3, hna⟩ :=
    (h1.and (h2.and (h3.and ((eventually_ge_atTop 2).and (eventually_ge_atTop a))))).exists
  refine ⟨n * B, hna.trans (Nat.le_mul_of_pos_right n hB), ?_⟩
  obtain ⟨xG, DG, hxG, hDG2, hDGR, hDGs, hDGl⟩ :=
    exists_emSynthesis hφ hφ1 hφint hG hGR' hMG hMG0 hn3 hk q
  obtain ⟨xh, Dh, hxh, hDh2, hDhR, hDhs, hDhl⟩ :=
    exists_emSynthesis hφ hφ1 hφint hh hhR' hMh hMh0 hn3 hk q
  have hsmall : Real.exp ((R + 1) / 2) * (2 * (R + 1) * emErr Mh A q (κ (n * B)) n) ≤
      poleMomentNeg h / 2 := by
    have hpos : 0 < Real.exp ((R + 1) / 2) * (2 * (R + 1)) := by
      have := Real.exp_pos ((R + 1) / 2); positivity
    have := (lt_div_iff₀ hpos).mp hn2
    linarith
  obtain ⟨t, ht, ht0⟩ := exists_pole_correction hG2.continuous hGc hG0 hh2.continuous hhc hh0
    hDG2.continuous hDGR hDGs hDh2.continuous hDhR hDhs (by linarith) hsmall
  have hT : |t| ≤ C * emErr MG A q (κ (n * B)) n := by
    refine ht.trans (le_of_eq ?_); simp only [C]; ring
  obtain ⟨hD2, hDR, hsup, hlip⟩ := comb_perturbation hh2 (fun v hv => hhR' v (by linarith))
    hhsup hhlip hDG2 hDGR hDGs hDGl hDh2 hDhR hDhs hDhl hT
  set D : ℝ → ℝ := fun v => DG v - t * (h v + Dh v)
  set c := Real.log n + R
  refine ⟨fun j => xG j - t * xh j, ?_⟩
  have hx : atomicTest (n * B) (fun j => xG j - t * xh j) (dilate (κ (n * B)) φ) =
      fun v => (fun w => G w + D w) (v - c) := by
    rw [atomicTest_sub_const_mul, hxG, hxh]
    funext v
    simp only [D]
    ring
  have hGD2 : ContDiff ℝ 2 fun w => G w + D w := hG2.add hD2
  have hGDc : HasCompactSupport fun w => G w + D w :=
    hGc.add (hasCompactSupport_of_vanishes hDR)
  rw [hx, poleMomentNeg_comp_sub (fun w => G w + D w) c, markovQuad_comp_sub hGD2 hGDc c]
  refine ⟨by rw [ht0, mul_zero], ?_⟩
  have := hle D _ _ _ hD2 hDR hsup hlip hk
  linarith

/-- **The pole is the only negative square at every root**: for every smooth profile `φ` supported
in `[−1, 1]` with `∫ φ = 1` and every dilation sequence of overlap growth of some order, RH holds
iff for all large `N` the Markov form is nonnegative on the atomic tests of width `1/κ_N` in the
pole hyperplane `m₋ = 0`. -/
theorem riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg_of_growthPow
    (hκ : OverlapGrowthPow q κ) (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      poleMomentNeg (atomicTest N x (dilate (κ N) φ)) = 0 →
        0 ≤ markovQuad (atomicTest N x (dilate (κ N) φ)) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (natCast_le_infty 2)
  constructor
  · intro hRH
    filter_upwards [hκ.1.eventually_gt_atTop 0] with N hk x h0
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ2 hφ1 hk N x
    exact riemannHypothesis_iff_forall_exp_neg_half_moment_zero_markovEnergy_nonneg.mp hRH _ h2 hc
      h0
  intro H
  by_contra hRH
  obtain ⟨u, hu, huc, -, hpole, hneg⟩ := exists_even_poleFree_negative_of_not_riemannHypothesis hRH
  have hu0 : poleMomentNeg u = 0 := by
    rw [paperFT_ofReal_I_half] at hpole
    exact_mod_cast hpole
  have hQu : weilQuad u < 0 := by
    rw [zeta_W_eq_weilFullFunctional (f := fun x => (u x : ℂ)) (Complex.ofRealCLM.contDiff.comp hu)
      (huc.comp_left Complex.ofReal_zero)] at hneg
    exact hneg
  have hMu : markovQuad u < 0 := by
    rw [markovQuad_eq hu huc, hu0, zero_mul, mul_zero, sub_zero]
    exact hQu
  obtain ⟨G, hG, hGc, hG0, hGneg⟩ := exists_smooth_poleFree_markov_neg hφ hφ1 hφint hu huc hu0 hMu
  obtain ⟨N, ⟨x, hx0, hxM⟩, hN⟩ :=
    ((frequently_poleHyperplane_markov_neg hφ hφ1 hφint hκ hG hGc hG0 hGneg).and_eventually H).exists
  exact absurd (hN x hx0) (not_le.mpr hxM)

end EveryRoot

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis

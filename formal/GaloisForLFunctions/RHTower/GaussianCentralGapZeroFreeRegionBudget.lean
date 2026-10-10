import GaloisForLFunctions.RHTower.GaussianWeightedGapExtremalBohrSpectrum
import GaloisForLFunctions.RHTower.GaussianCentralGapExplicitCriterion
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionSharp
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovZeroFree
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay

/-!
# Unconditional central Gaussian budgets from zero-free regions

Let `G(u) = P_½(e^{-u}) − C_½(e^{-u})` be the central Gaussian prime gap.  RH is equivalent to
`G = O(1)`; unconditionally only `G = O(e^{u/4})` is trivial.

* **Transfer law** (`norm_gaussianCentralGap_le_of_zeroFree`).  If every zero with `|γ| ≥ t₀` has
  `β ≤ 1 − η(|γ|)` with `η` antitone, then for all `u ≥ 0` and `T ≥ t₀`
  `|G(u)| ≤ C (1 + e^{u/4}(e^{-uη(T)/2} + e^{-πT/8} + e^{-uδ/2}))`.
  The zero expansion `G = A − Σ_ρ ½Γ((ρ−½)/2) e^{(ρ−½)u/2} − Σ_ρ R_ρ` and the sharp strip decay
  `|Γ(x+it)| ≤ C|t|^N e^{-π|t|/2}` make the zeros above height `T` exponentially negligible, so the
  budget at scale `u` is decided by zeros of height `≲ u`.
* **de la Vallée Poussin form** (`exists_norm_gaussianCentralGap_le_dlvp`).  With the explicit region
  `β ≤ 1 − 1/(58 log|γ|)` (`|γ| ≥ 4`): `|G(u)| ≤ C exp(u/4 − u/(116 log u))` for large `u`.  The
  Gaussian damping turns the classical saving `exp(−c√(log x))` into `exp(−c log x / log log x)`.
* **Vinogradov–Korobov form** (`exists_norm_gaussianCentralGap_le_vinogradovKorobov`).
  `|G(u)| ≤ C exp(u/4 − u (log u)^{-2/3}(log log u)^{-5/3}/(2·10⁸))` for large `u`.

The exponent `1/4` is the budget abscissa of a zero on `Re s = 1`; any saving in the exponent itself
is a zero-free strip `Re s > 1 − ε`.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- Every Bohr amplitude is `O(|ρ − ½|^{-2})`. -/
theorem exists_norm_zeroBohrAmplitude_le_inv_sq :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ q : XiZeroCopy,
      ‖zeroBohrAmplitude q‖ ≤ W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
  obtain ⟨W, hW⟩ := exists_norm_criticalZeroGerm_one_le
  refine ⟨|W| + 4, by positivity, fun q => ?_⟩
  have h1 := norm_criticalZeroGerm_sub_zeroBohr_le one_pos q
  have hone : ((1 : ℝ) : ℂ) ^ (-((xiZero q - 1 / 2) / 2)) = 1 := by
    rw [Complex.ofReal_one, Complex.one_cpow]
  rw [hone, mul_one] at h1
  have h3 : ‖zeroBohrAmplitude q‖ ≤ ‖criticalZeroGerm 1 q‖ +
      ‖criticalZeroGerm 1 q - zeroBohrAmplitude q‖ := by
    have := norm_sub_le (criticalZeroGerm 1 q) (criticalZeroGerm 1 q - zeroBohrAmplitude q)
    rwa [sub_sub_cancel] at this
  have h2 := hW q
  have hn : 0 ≤ ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by positivity
  have hWa : W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 ≤ |W| * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self W) hn
  rw [show (2 * (1 : ℝ) + 2 * 1 ^ 2) = 4 by norm_num] at h1
  linarith

/-- **Exponential decay of the Bohr amplitudes.**  Off the low strip `|γ| < 2` the amplitude
`½Γ((ρ−½)/2)` times `e^{π|γ|/8}` is still `O(|ρ − ½|^{-2})`. -/
theorem exists_norm_zeroBohrAmplitude_mul_exp_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q : XiZeroCopy, 2 ≤ |(xiZero q).im| →
      ‖zeroBohrAmplitude q‖ * Real.exp (Real.pi * |(xiZero q).im| / 8) ≤
        D * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
  obtain ⟨C, N, hC, hb⟩ := GaloisForLFunctions.HTGeometry.exists_sharp_bound_norm_Gamma_strip
    (-1 / 4) (1 / 4)
  set k : ℕ := N + 2 with hk
  set M : ℝ := (8 / Real.pi) ^ k * (k.factorial : ℝ) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨C * M * 2, by positivity, fun q hq => ?_⟩
  set γ : ℝ := |(xiZero q).im| with hγ
  have hγ2 : 2 ≤ γ := hq
  have hγ0 : 0 < γ := by linarith
  set z : ℂ := (xiZero q - 1 / 2) / 2 with hz
  have hb' := re_xiZero_sub_half_bounds q
  have hzre : z.re = (xiZero q - 1 / 2).re / 2 := by rw [hz]; simp
  have hzim : |z.im| = γ / 2 := by
    rw [hz, hγ]; simp [abs_div]
  have hΓ := hb z (by rw [hzre]; linarith [hb'.1]) (by rw [hzre]; linarith [hb'.2])
    (by rw [hzim]; linarith)
  rw [hzim] at hΓ
  -- `t^k ≤ (8/π)^k k! e^{πt/8}`
  have hpow : γ ^ k ≤ M * Real.exp (Real.pi * γ / 8) := by
    have h := Real.pow_div_factorial_le_exp (x := Real.pi * γ / 8) (by positivity) k
    have hpi : 0 < Real.pi := Real.pi_pos
    have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ hfac] at h
    have hγk : γ ^ k = (8 / Real.pi) ^ k * (Real.pi * γ / 8) ^ k := by
      rw [← mul_pow]; congr 1; field_simp
    rw [hγk, hM]
    calc (8 / Real.pi) ^ k * (Real.pi * γ / 8) ^ k
        ≤ (8 / Real.pi) ^ k * (Real.exp (Real.pi * γ / 8) * (k.factorial : ℝ)) := by gcongr
      _ = _ := by ring
  have hinv : 1 / γ ^ 2 ≤ 2 * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
    have hn : ‖xiZero q - 1 / 2‖ ^ 2 ≤ 2 * γ ^ 2 := by
      have h1 : ‖xiZero q - 1 / 2‖ ≤ |(xiZero q - 1 / 2).re| + |(xiZero q - 1 / 2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      have h2 : |(xiZero q - 1 / 2).re| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hb'.1], by linarith [hb'.2]⟩
      have h3 : |(xiZero q - 1 / 2).im| = γ := by rw [hγ]; simp
      have h4 : ‖xiZero q - 1 / 2‖ ≤ 1 / 2 + γ := by linarith
      have h5 : 0 ≤ ‖xiZero q - 1 / 2‖ := norm_nonneg _
      nlinarith
    have hne : 0 < ‖xiZero q - 1 / 2‖ := norm_pos_iff.2 (xiZero_sub_half_ne_zero q)
    rw [norm_inv, inv_pow, div_le_iff₀ (by positivity)]
    calc 1 = (‖xiZero q - 1 / 2‖ ^ 2)⁻¹ * ‖xiZero q - 1 / 2‖ ^ 2 := by
          rw [inv_mul_cancel₀ (by positivity)]
      _ ≤ (‖xiZero q - 1 / 2‖ ^ 2)⁻¹ * (2 * γ ^ 2) := by gcongr
      _ = 2 * (‖xiZero q - 1 / 2‖ ^ 2)⁻¹ * γ ^ 2 := by ring
  have hamp : ‖zeroBohrAmplitude q‖ ≤ C * γ ^ N * Real.exp (-(Real.pi * γ / 4)) := by
    rw [zeroBohrAmplitude, norm_mul, ← hz]
    have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hh]
    have hγN : (γ / 2) ^ N ≤ γ ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
    have hexp : Real.exp (-(Real.pi * (γ / 2) / 2)) = Real.exp (-(Real.pi * γ / 4)) := by
      congr 1; ring
    rw [hexp] at hΓ
    calc 1 / 2 * ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma z‖ := by
          linarith [norm_nonneg (Complex.Gamma z)]
      _ ≤ C * (γ / 2) ^ N * Real.exp (-(Real.pi * γ / 4)) := hΓ
      _ ≤ C * γ ^ N * Real.exp (-(Real.pi * γ / 4)) := by gcongr
  have hexp2 : Real.exp (-(Real.pi * γ / 4)) * Real.exp (Real.pi * γ / 8) =
      Real.exp (-(Real.pi * γ / 8)) := by rw [← Real.exp_add]; congr 1; ring
  calc ‖zeroBohrAmplitude q‖ * Real.exp (Real.pi * γ / 8)
      ≤ C * γ ^ N * Real.exp (-(Real.pi * γ / 4)) * Real.exp (Real.pi * γ / 8) := by gcongr
    _ = C * (γ ^ k * Real.exp (-(Real.pi * γ / 8))) / γ ^ 2 := by
        rw [mul_assoc, hexp2, hk, pow_add]; field_simp
    _ ≤ C * (M * Real.exp (Real.pi * γ / 8) * Real.exp (-(Real.pi * γ / 8))) / γ ^ 2 := by
        gcongr
    _ = C * M * (1 / γ ^ 2) := by
        rw [mul_assoc M, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]; ring
    _ ≤ C * M * (2 * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2) := by gcongr
    _ = C * M * 2 * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by ring

/-- Zeros of bounded height stay a fixed distance left of `Re s = 1`. -/
theorem exists_xi_zero_re_le_of_abs_im_le (t₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℂ, xi ρ = 0 → |ρ.im| ≤ t₀ → ρ.re ≤ 1 - δ := by
  set K : Set ℂ := {ρ : ℂ | xi ρ = 0} ∩ ({ρ : ℂ | |ρ.im| ≤ t₀} ∩
    ({ρ : ℂ | 1 / 2 ≤ ρ.re} ∩ {ρ : ℂ | ρ.re ≤ 1})) with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_eq xi_differentiable.continuous continuous_const).inter
        ((isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const).inter
          ((isClosed_le continuous_const Complex.continuous_re).inter
            (isClosed_le Complex.continuous_re continuous_const)))
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |t₀|)).subset ?_
      rintro ρ ⟨-, him, hre1, hre2⟩
      have him' : |ρ.im| ≤ t₀ := him
      have hre1' : 1 / 2 ≤ ρ.re := hre1
      have hre2' : ρ.re ≤ 1 := hre2
      rw [Metric.mem_closedBall, dist_zero_right]
      have habs : |ρ.re| ≤ 1 := abs_le.2 ⟨by linarith, hre2'⟩
      calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
        _ ≤ 1 + |t₀| := by linarith [le_abs_self t₀]
  rcases K.eq_empty_or_nonempty with hE | hne
  · refine ⟨1 / 2, by norm_num, fun ρ hρ him => ?_⟩
    by_contra hlt
    push Not at hlt
    have hρ1 : ρ.re ≤ 1 := by
      by_contra h1; push Not at h1; exact xi_ne_zero_of_one_le_re h1.le hρ
    have hhalf : (1 : ℝ) / 2 ≤ ρ.re := by linarith
    have hmem : ρ ∈ K := ⟨hρ, him, hhalf, hρ1⟩
    rw [hE] at hmem
    exact hmem
  · obtain ⟨s₀, hs₀K, hmax⟩ := hKc.exists_isMaxOn hne Complex.continuous_re.continuousOn
    have hs₀ : s₀.re < 1 := by
      by_contra h1; push Not at h1; exact xi_ne_zero_of_one_le_re h1 hs₀K.1
    refine ⟨min (1 / 2) (1 - s₀.re), lt_min (by norm_num) (by linarith), fun ρ hρ him => ?_⟩
    by_cases hhalf : 1 / 2 ≤ ρ.re
    · have hρ1 : ρ.re ≤ 1 := by
        by_contra h1; push Not at h1; exact xi_ne_zero_of_one_le_re h1.le hρ
      have hle : ρ.re ≤ s₀.re := hmax ⟨hρ, him, hhalf, hρ1⟩
      have := min_le_right (1 / 2 : ℝ) (1 - s₀.re)
      linarith
    · push Not at hhalf
      have := min_le_left (1 / 2 : ℝ) (1 - s₀.re)
      linarith

/-- The zero-free majorant `e^{u/4}(e^{-uη(T)/2} + e^{-πT/8} + e^{-uδ/2})`. -/
def zeroFreeBudgetMajorant (η : ℝ → ℝ) (δ u T : ℝ) : ℝ :=
  Real.exp (u / 4) * (Real.exp (-(u * η T / 2)) + Real.exp (-(Real.pi * T / 8)) +
    Real.exp (-(u * δ / 2)))

theorem zeroFreeBudgetMajorant_nonneg (η : ℝ → ℝ) (δ u T : ℝ) :
    0 ≤ zeroFreeBudgetMajorant η δ u T := by
  unfold zeroFreeBudgetMajorant; positivity

/-- **One zero term.**  Under the zero-free hypotheses each term of the zero series is bounded by
`(W + D) E ‖(ρ−½)⁻¹‖²`. -/
theorem norm_zeroBohrTerm_le {η : ℝ → ℝ} {t₀ W D δ u T : ℝ} (ht₀ : 2 ≤ t₀)
    (hηanti : ∀ s t : ℝ, t₀ ≤ s → s ≤ t → η t ≤ η s)
    (hzf : ∀ q : XiZeroCopy, t₀ ≤ |(xiZero q).im| → (xiZero q).re ≤ 1 - η |(xiZero q).im|)
    (hW0 : 0 ≤ W) (hW : ∀ q : XiZeroCopy, ‖zeroBohrAmplitude q‖ ≤ W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2)
    (hD0 : 0 ≤ D) (hD : ∀ q : XiZeroCopy, 2 ≤ |(xiZero q).im| →
      ‖zeroBohrAmplitude q‖ * Real.exp (Real.pi * |(xiZero q).im| / 8) ≤
        D * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2)
    (hδz : ∀ ρ : ℂ, xi ρ = 0 → |ρ.im| ≤ t₀ → ρ.re ≤ 1 - δ) (hu : 0 ≤ u) (hT : t₀ ≤ T)
    (q : XiZeroCopy) :
    ‖zeroBohrAmplitude q‖ * Real.exp (((xiZero q).re - 1 / 2) * u / 2) ≤
      (W + D) * zeroFreeBudgetMajorant η δ u T * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
  set E : ℝ := zeroFreeBudgetMajorant η δ u T with hE
  have hE0 : 0 ≤ E := zeroFreeBudgetMajorant_nonneg η δ u T
  set β : ℝ := (xiZero q).re with hβ
  set γ : ℝ := |(xiZero q).im| with hγ
  set n : ℝ := ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hn
  have hn0 : 0 ≤ n := by positivity
  have e1 : 0 < Real.exp (-(u * η T / 2)) := Real.exp_pos _
  have e2 : 0 < Real.exp (-(Real.pi * T / 8)) := Real.exp_pos _
  have e3 : 0 < Real.exp (-(u * δ / 2)) := Real.exp_pos _
  have hfin : (W * n) * E ≤ (W + D) * E * n := by
    nlinarith [mul_nonneg (mul_nonneg hD0 hE0) hn0]
  by_cases hlow : γ < t₀
  · have hβδ : β ≤ 1 - δ := hδz _ (xi_xiZero q) hlow.le
    have hb : Real.exp ((β - 1 / 2) * u / 2) ≤ Real.exp (u / 4) * Real.exp (-(u * δ / 2)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
    have hx : Real.exp (u / 4) * Real.exp (-(u * δ / 2)) ≤ E := by
      rw [hE, zeroFreeBudgetMajorant]
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    calc ‖zeroBohrAmplitude q‖ * Real.exp ((β - 1 / 2) * u / 2) ≤ (W * n) * E := by
          gcongr
          · exact hW q
          · exact hb.trans hx
      _ ≤ _ := hfin
  · push Not at hlow
    by_cases hmid : γ ≤ T
    · have hβη : β ≤ 1 - η γ := hzf q hlow
      have hηT : η T ≤ η γ := hηanti γ T hlow hmid
      have hb : Real.exp ((β - 1 / 2) * u / 2) ≤
          Real.exp (u / 4) * Real.exp (-(u * η T / 2)) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
      have hx : Real.exp (u / 4) * Real.exp (-(u * η T / 2)) ≤ E := by
        rw [hE, zeroFreeBudgetMajorant]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      calc ‖zeroBohrAmplitude q‖ * Real.exp ((β - 1 / 2) * u / 2) ≤ (W * n) * E := by
            gcongr
            · exact hW q
            · exact hb.trans hx
        _ ≤ _ := hfin
    · push Not at hmid
      have hγ2 : 2 ≤ γ := by linarith
      have hdec := hD q hγ2
      have hpos : 0 < Real.exp (Real.pi * γ / 8) := Real.exp_pos _
      have h1 : ‖zeroBohrAmplitude q‖ ≤ D * n * Real.exp (-(Real.pi * γ / 8)) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
        exact hdec
      have h2 : Real.exp (-(Real.pi * γ / 8)) ≤ Real.exp (-(Real.pi * T / 8)) :=
        Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
      have hβ1 : β ≤ 1 := xiZero_re_le_one q
      have hb1 : Real.exp ((β - 1 / 2) * u / 2) ≤ Real.exp (u / 4) :=
        Real.exp_le_exp.2 (by nlinarith)
      have hx : Real.exp (u / 4) * Real.exp (-(Real.pi * T / 8)) ≤ E := by
        rw [hE, zeroFreeBudgetMajorant]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      have hDn : 0 ≤ D * n := mul_nonneg hD0 hn0
      calc ‖zeroBohrAmplitude q‖ * Real.exp ((β - 1 / 2) * u / 2)
          ≤ (D * n * Real.exp (-(Real.pi * T / 8))) * Real.exp (u / 4) := by
            gcongr
            exact h1.trans (by gcongr)
        _ = D * n * (Real.exp (u / 4) * Real.exp (-(Real.pi * T / 8))) := by ring
        _ ≤ D * n * E := by gcongr
        _ ≤ (W + D) * E * n := by nlinarith [mul_nonneg (mul_nonneg hW0 hE0) hn0]

/-- **Transfer law.**  A zero-free region `β ≤ 1 − η(|γ|)` (`|γ| ≥ t₀`, `η` antitone) bounds the
central Gaussian gap at every scale `u` by the zeros of height at most `T`. -/
theorem norm_gaussianCentralGap_le_of_zeroFree {η : ℝ → ℝ} {t₀ : ℝ} (ht₀ : 2 ≤ t₀)
    (hηanti : ∀ s t : ℝ, t₀ ≤ s → s ≤ t → η t ≤ η s)
    (hzf : ∀ q : XiZeroCopy, t₀ ≤ |(xiZero q).im| → (xiZero q).re ≤ 1 - η |(xiZero q).im|) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ u : ℝ, 0 ≤ u → ∀ T : ℝ, t₀ ≤ T →
      |gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))| ≤
        C * (1 + zeroFreeBudgetMajorant η δ u T) := by
  obtain ⟨W, hW0, hW⟩ := exists_norm_zeroBohrAmplitude_le_inv_sq
  obtain ⟨D, hD0, hD⟩ := exists_norm_zeroBohrAmplitude_mul_exp_le
  obtain ⟨δ, hδ, hδz⟩ := exists_xi_zero_re_le_of_abs_im_le t₀
  have hSs : Summable fun q : XiZeroCopy => ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 :=
    summable_norm_inv_xiZero_sub_half_sq
  set S : ℝ := ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set A₀ : ℝ := ‖gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ)‖ with hA₀
  have hA0 : 0 ≤ A₀ := norm_nonneg _
  refine ⟨A₀ + 31 + 4 * S + (W + D) * S, δ, by positivity, hδ, fun u hu T hT => ?_⟩
  set y : ℝ := Real.exp (-u) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy1 : y ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  set E : ℝ := zeroFreeBudgetMajorant η δ u T with hE
  have hE0 : 0 ≤ E := zeroFreeBudgetMajorant_nonneg η δ u T
  have hterm : ∀ q : XiZeroCopy, ‖zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))‖ ≤
      (W + D) * E * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
    intro q
    have hcpow : ‖(y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))‖ =
        Real.exp (((xiZero q).re - 1 / 2) * u / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0, hy, ← Real.exp_mul]
      congr 1
      simp
      ring
    rw [norm_mul, hcpow]
    exact norm_zeroBohrTerm_le ht₀ hηanti hzf hW0 hW hD0 hD hδz hu hT q
  have hmaj : Summable fun q : XiZeroCopy => (W + D) * E * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 :=
    hSs.mul_left _
  have hsZ : Summable fun q : XiZeroCopy =>
      ‖zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmaj
  have hsumZ : ‖∑' q : XiZeroCopy, zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))‖ ≤
      (W + D) * E * S := by
    refine (norm_tsum_le_tsum_norm hsZ).trans ?_
    rw [hS, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsZ hmaj
  have hb : ∀ q : XiZeroCopy, ‖criticalZeroGerm y q -
      zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))‖ ≤
      4 * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
    intro q
    refine (norm_criticalZeroGerm_sub_zeroBohr_le hy0 q).trans ?_
    have hy2 : y ^ 2 ≤ 1 := by nlinarith
    gcongr
    linarith
  have hsR : Summable fun q : XiZeroCopy => ‖criticalZeroGerm y q -
      zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hSs.mul_left 4)
  have hsumR : ‖∑' q : XiZeroCopy, (criticalZeroGerm y q -
      zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2)))‖ ≤ 4 * S := by
    refine (norm_tsum_le_tsum_norm hsR).trans ?_
    rw [hS, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hb hsR (hSs.mul_left 4)
  have hMB : ‖gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ)‖ ≤ A₀ + 31 := by
    have h := norm_gaussianArchimedeanCurrent_half_sub_MB_le hy0 hy1
    have hs : Real.sqrt y ≤ 1 := Real.sqrt_le_one.2 hy1
    have h2 := norm_sub_norm_le (gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ))
      (gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ))
    rw [norm_sub_rev] at h2
    nlinarith
  have hexp := gaussianCentralGap_eq_archimedean_sub_zeroSeries hy0
  have hreal : |gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y| =
      ‖((gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hreal, hexp]
  have htri := norm_sub_le (gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ) -
      ∑' q : XiZeroCopy, zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2)))
    (∑' q : XiZeroCopy, (criticalZeroGerm y q -
      zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))))
  have htri2 := norm_sub_le (gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ))
    (∑' q : XiZeroCopy, zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2)))
  have hWD : 0 ≤ (W + D) * S := by positivity
  have hfinal : A₀ + 31 + (W + D) * E * S + 4 * S ≤ (A₀ + 31 + 4 * S + (W + D) * S) * (1 + E) := by
    nlinarith [mul_nonneg hWD hE0, mul_nonneg (show 0 ≤ A₀ + 31 + 4 * S by positivity) hE0]
  linarith

/-- **Asymptotic transfer.**  If the width `η` is antitone, nonnegative and tends to `0`, then
`|G(u)| ≤ C exp(u/4 − u η(u)/2)` for all large `u`. -/
theorem exists_norm_gaussianCentralGap_le_exp_of_zeroFree {η : ℝ → ℝ} {t₀ : ℝ} (ht₀ : 2 ≤ t₀)
    (hηanti : ∀ s t : ℝ, t₀ ≤ s → s ≤ t → η t ≤ η s)
    (hzf : ∀ q : XiZeroCopy, t₀ ≤ |(xiZero q).im| → (xiZero q).re ≤ 1 - η |(xiZero q).im|)
    (hηlim : Tendsto η atTop (𝓝 0)) :
    ∃ C U₀ : ℝ, ∀ u : ℝ, U₀ ≤ u →
      |gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))| ≤
        C * Real.exp (u / 4 - u * η u / 2) := by
  obtain ⟨C, δ, hC, hδ, hbd⟩ := norm_gaussianCentralGap_le_of_zeroFree ht₀ hηanti hzf
  set m : ℝ := min δ (1 / 2) with hm
  have hm0 : 0 < m := lt_min hδ (by norm_num)
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.1 (hηlim.eventually (ge_mem_nhds hm0))
  refine ⟨4 * C, max U₁ t₀, fun u hu => ?_⟩
  have hu1 : U₁ ≤ u := le_trans (le_max_left _ _) hu
  have hut : t₀ ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : 0 ≤ u := by linarith
  have hηu : η u ≤ m := hU₁ u hu1
  have hηδ : η u ≤ δ := hηu.trans (min_le_left _ _)
  have hηh : η u ≤ 1 / 2 := hηu.trans (min_le_right _ _)
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  set X : ℝ := Real.exp (u / 4 - u * η u / 2) with hX
  have hX1 : 1 ≤ X := Real.one_le_exp (by nlinarith)
  have hmaj : zeroFreeBudgetMajorant η δ u u ≤ 3 * X := by
    rw [zeroFreeBudgetMajorant, hX]
    have h1 : Real.exp (u / 4) * Real.exp (-(u * η u / 2)) = Real.exp (u / 4 - u * η u / 2) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (u / 4) * Real.exp (-(Real.pi * u / 8)) ≤ Real.exp (u / 4 - u * η u / 2) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
    have h3 : Real.exp (u / 4) * Real.exp (-(u * δ / 2)) ≤ Real.exp (u / 4 - u * η u / 2) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
    nlinarith [h1, h2, h3]
  calc _ ≤ C * (1 + zeroFreeBudgetMajorant η δ u u) := hbd u hu0 u hut
    _ ≤ C * (X + 3 * X) := by gcongr
    _ = 4 * C * X := by ring

/-- The explicit zero-free region `β ≤ 1 − 1/(58 log|γ|)` for `|γ| ≥ 4`, on zero copies. -/
theorem xiZero_re_le_dlvp (q : XiZeroCopy) (hq : 4 ≤ |(xiZero q).im|) :
    (xiZero q).re ≤ 1 - 1 / 58 / Real.log |(xiZero q).im| := by
  have hζ := (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.1 (xi_xiZero q)).1
  rw [← Complex.re_add_im (xiZero q)] at hζ
  exact re_le_one_sub_of_riemannZeta_eq_zero hq hζ

/-- **de la Vallée Poussin budget.**  Unconditionally,
`|P_½ − C_½|(e^{-u}) ≤ C exp(u/4 − u/(116 log u))` for all large `u`. -/
theorem exists_norm_gaussianCentralGap_le_dlvp :
    ∃ C U₀ : ℝ, ∀ u : ℝ, U₀ ≤ u →
      |gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))| ≤
        C * Real.exp (u / 4 - u * (1 / 58 / Real.log u) / 2) := by
  refine exists_norm_gaussianCentralGap_le_exp_of_zeroFree (η := fun t => 1 / 58 / Real.log t)
    (t₀ := 4) (by norm_num) (fun s t hs hst => ?_) (fun q hq => xiZero_re_le_dlvp q hq) ?_
  · have hs0 : 0 < Real.log s := Real.log_pos (by linarith)
    have hlog : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst
    exact div_le_div_of_nonneg_left (by norm_num) hs0 hlog
  · have h := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (1 / 58 : ℝ)
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    simp [div_eq_mul_inv]

/-- The Vinogradov–Korobov width `(log t)^{-2/3} (log log t)^{-5/3} / 10⁸`. -/
def vinogradovKorobovGaussianWidth (t : ℝ) : ℝ :=
  Real.log t ^ (-(2 : ℝ) / 3) * Real.log (Real.log t) ^ (-(5 : ℝ) / 3) / 10 ^ 8

theorem vinogradovKorobovGaussianWidth_anti {s t : ℝ} (hs : Real.exp (Real.exp 1) ≤ s)
    (hst : s ≤ t) : vinogradovKorobovGaussianWidth t ≤ vinogradovKorobovGaussianWidth s := by
  have hs0 : 0 < s := lt_of_lt_of_le (Real.exp_pos _) hs
  have hls : Real.exp 1 ≤ Real.log s := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hs
  have hls0 : 0 < Real.log s := lt_of_lt_of_le (Real.exp_pos _) hls
  have hlst : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst
  have hlls : 1 ≤ Real.log (Real.log s) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hls
  have hllst : Real.log (Real.log s) ≤ Real.log (Real.log t) := Real.log_le_log hls0 hlst
  unfold vinogradovKorobovGaussianWidth
  have h1 : Real.log t ^ (-(2 : ℝ) / 3) ≤ Real.log s ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hls0 hlst (by norm_num)
  have h2 : Real.log (Real.log t) ^ (-(5 : ℝ) / 3) ≤ Real.log (Real.log s) ^ (-(5 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hllst (by norm_num)
  gcongr
  exact Real.rpow_nonneg (by linarith) _

theorem tendsto_vinogradovKorobovGaussianWidth :
    Tendsto vinogradovKorobovGaussianWidth atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log t ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp Real.tendsto_log_atTop
  have h2 : Tendsto (fun t : ℝ => Real.log (Real.log t) ^ (-(5 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 3)).comp
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have h := (h1.mul h2).div_const (10 ^ 8 : ℝ)
  rw [mul_zero, zero_div] at h
  refine h.congr fun t => ?_
  unfold vinogradovKorobovGaussianWidth
  norm_num [neg_div]

/-- The Vinogradov–Korobov zero-free region on zero copies of either sign of the ordinate. -/
theorem exists_xiZero_re_le_vinogradovKorobov :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ Real.exp (Real.exp 1) ≤ t₀ ∧ ∀ q : XiZeroCopy, t₀ ≤ |(xiZero q).im| →
      (xiZero q).re ≤ 1 - vinogradovKorobovGaussianWidth |(xiZero q).im| := by
  obtain ⟨γ₀, hγ₀⟩ := Sieve.riemannZeta_ne_zero_vinogradovKorobov
  have he : (2 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : Real.exp 1 ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.2 h1
    linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨max γ₀ (Real.exp (Real.exp 1)), le_trans he (le_max_right _ _), le_max_right _ _,
    fun q hq => ?_⟩
  have hζ := (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.1 (xi_xiZero q)).1
  set β : ℝ := (xiZero q).re
  set γ : ℝ := (xiZero q).im
  have hγ₀' : γ₀ ≤ |γ| := le_trans (le_max_left _ _) hq
  by_contra hlt
  push Not at hlt
  have hlt' : 1 - Real.log |γ| ^ (-(2 : ℝ) / 3) * Real.log (Real.log |γ|) ^ (-(5 : ℝ) / 3) /
      10 ^ 8 < β := by simpa [vinogradovKorobovGaussianWidth] using hlt
  rcases le_or_gt 0 γ with hγ | hγ
  · rw [abs_of_nonneg hγ] at hγ₀' hlt'
    refine hγ₀ β γ hγ₀' hlt' ?_
    rw [← Complex.re_add_im (xiZero q)] at hζ
    exact hζ
  · rw [abs_of_neg hγ] at hγ₀' hlt'
    refine hγ₀ β (-γ) hγ₀' hlt' ?_
    have hc := riemannZeta_conj (xiZero q)
    rw [hζ, map_zero] at hc
    have hcz : (starRingEnd ℂ) (xiZero q) = (β : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [β, γ]
    rw [hcz] at hc
    exact hc

/-- **Vinogradov–Korobov budget.**  Unconditionally, for all large `u`,
`|P_½ − C_½|(e^{-u}) ≤ C exp(u/4 − u (log u)^{-2/3} (log log u)^{-5/3} / (2·10⁸))`. -/
theorem exists_norm_gaussianCentralGap_le_vinogradovKorobov :
    ∃ C U₀ : ℝ, ∀ u : ℝ, U₀ ≤ u →
      |gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))| ≤
        C * Real.exp (u / 4 - u * vinogradovKorobovGaussianWidth u / 2) := by
  obtain ⟨t₀, ht₀2, ht₀e, hzf⟩ := exists_xiZero_re_le_vinogradovKorobov
  exact exists_norm_gaussianCentralGap_le_exp_of_zeroFree ht₀2
    (fun s t hs hst => vinogradovKorobovGaussianWidth_anti (le_trans ht₀e hs) hst) hzf
    tendsto_vinogradovKorobovGaussianWidth

end

end RHTower

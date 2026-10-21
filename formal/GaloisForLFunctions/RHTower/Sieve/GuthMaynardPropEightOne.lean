import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSmoothedLagSumMoments
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropEightOneHolder

set_option autoImplicit false

/-!
# Guth–Maynard Proposition 8.1: `S₃` is controlled by the additive energy

Guth–Maynard (arXiv 2405.20552) Proposition 8.1: for a `T^ε`-separated set `W` in an interval of
length `T`, `S₃ ⪅ T² |W|^{1/2} E(W)^{1/2}`. Its proof starts from Proposition 7.2,

`S₃ ⪅ (N²/M) Σ_{|m₁| ∼ M₁, |m₂|, |m₃| ≍ M} Ĩ_m + O(T^{-100})`,
`Ĩ_m = ∫_{1/2}^{2} |R(v)| R̃((m₁v + m₃)/(m₂v)) R̃((m₁v + m₃)/m₂) dv`,

and bounds each `Ĩ_m` by Hölder with exponents `(2, 4, 4)`: the first factor by the `L²` bound
(Lemma 8.2), the other two, after the substitutions `u = (m₁v + m₃)/(m₂v)` (Jacobian `≍ 1`) and
`u = (m₁v + m₃)/m₂` (Jacobian `≍ M₁/M`), by the `L⁴` bound for `R̃` (Lemma 8.3).

This module proves that deduction. Proposition 7.2 is a separate brick: the main theorem
`propEightOne_of_expansion` is an **assembly lemma** whose hypothesis is the Proposition 7.2
inequality for an arbitrary real number `S₃`, an arbitrary finite index set `𝓜 ⊂ ℤ³` in the
dyadic box, and an arbitrary smoothing pair; everything else (Lemmas 8.2, 8.3, Hölder, the
changes of variables, the count of `𝓜`) is proved here or in the imported modules.
-/

open MeasureTheory Set Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The bound for one `Ĩ_m` -/

/-- The constant `(5π/2) A max(1, log A)` of the window moment bounds (Lemmas 8.2 and 8.3). -/
def momentConstant (A : ℝ) : ℝ := 5 * Real.pi / 2 * A * max 1 (Real.log A)

theorem momentConstant_nonneg {A : ℝ} (hA : 0 ≤ A) : 0 ≤ momentConstant A :=
  mul_nonneg (mul_nonneg (by positivity) hA) (le_trans zero_le_one (le_max_left _ _))

/-- `|R|²` is integrable on every compact interval. -/
theorem integrableOn_Icc_norm_lagSum_sq (W : Finset ℝ) (a b : ℝ) :
    IntegrableOn (fun v => ‖lagSum W v‖ ^ 2) (Icc a b) :=
  Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (measurable_norm_lagSum_sq W).aestronglyMeasurable (M := (W.card : ℝ) ^ 2)
    (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W v) 2)

/-- `R̃(φ(v))⁴` is integrable on every compact interval, for measurable `φ`. -/
theorem integrableOn_Icc_smoothedLagSum_comp_pow_four {ψ₁ ψ₂ : ℝ → ℝ}
    (hψ : IsSmoothingPair ψ₁ ψ₂) {N M : ℝ} (hNM : 0 < N * M) (W : Finset ℝ) {φ : ℝ → ℝ}
    (hφ : Measurable φ) (a b : ℝ) :
    IntegrableOn (fun v => smoothedLagSum ψ₁ ψ₂ N M W (φ v) ^ 4) (Icc a b) :=
  Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (((measurable_smoothedLagSum hψ N M W).comp hφ).pow_const 4).aestronglyMeasurable
    (M := ((W.card : ℝ) * Real.sqrt (∫ x, ψ₁ x)) ^ 4)
    (Filter.Eventually.of_forall fun v => by
      have h0 := smoothedLagSum_nonneg ψ₁ ψ₂ N M W (φ v)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ h0 (smoothedLagSum_le hψ hNM W _) 4)

/-- `R̃(u)⁴` is nonnegative. -/
theorem smoothedLagSum_pow_four_nonneg (ψ₁ ψ₂ : ℝ → ℝ) (N M : ℝ) (W : Finset ℝ) (u : ℝ) :
    0 ≤ smoothedLagSum ψ₁ ψ₂ N M W u ^ 4 := by
  have := smoothedLagSum_nonneg ψ₁ ψ₂ N M W u
  positivity

/-- **The Möbius substitution.** For `m₂, m₃ ≠ 0`,
`∫_{1/2}^{2} R̃((m₁v + m₃)/(m₂v))⁴ dv ≤ (4|m₂|/|m₃|) ∫_ℝ R̃⁴`. -/
theorem setIntegral_smoothedLagSum_mobius_pow_four_le {ψ₁ ψ₂ : ℝ → ℝ}
    (hψ : IsSmoothingPair ψ₁ ψ₂) {A : ℝ} (hsupp : ∀ x, x ∉ Icc A⁻¹ A → ψ₂ x = 0) {N M : ℝ}
    (hNM : 0 < N * M) (W : Finset ℝ) {m₁ m₂ m₃ : ℤ} (h₂ : m₂ ≠ 0) (h₃ : m₃ ≠ 0) :
    ∫ v in Icc (1 / 2 : ℝ) 2, smoothedLagSum ψ₁ ψ₂ N M W ((m₁ * v + m₃) / (m₂ * v)) ^ 4
      ≤ 4 * |(m₂ : ℝ)| / |(m₃ : ℝ)| * ∫ u, smoothedLagSum ψ₁ ψ₂ N M W u ^ 4 := by
  have h₂' : (m₂ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h₂
  have h₃' : (m₃ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h₃
  have ha₂ : 0 < |(m₂ : ℝ)| := abs_pos.mpr h₂'
  have ha₃ : 0 < |(m₃ : ℝ)| := abs_pos.mpr h₃'
  have hpos : ∀ v ∈ Icc (1 / 2 : ℝ) 2, 0 < v := fun v hv => by linarith [hv.1]
  have hφm : Measurable fun v : ℝ => ((m₁ : ℝ) * v + m₃) / (m₂ * v) := by fun_prop
  have hmain := setIntegral_comp_le_inv_mul_integral (S := Icc (1 / 2 : ℝ) 2) measurableSet_Icc
    (φ := fun v : ℝ => ((m₁ : ℝ) * v + m₃) / (m₂ * v))
    (φ' := fun v : ℝ => -(m₃ : ℝ) / (m₂ * v ^ 2))
    (fun v hv => (hasDerivAt_mobius _ _ _ (hpos v hv).ne' h₂').hasDerivWithinAt)
    (injOn_mobius h₃' h₂' fun v hv => (hpos v hv).ne') (lam := |(m₃ : ℝ)| / (4 * |(m₂ : ℝ)|))
    (by positivity) (fun v hv => by
      have hv0 := hpos v hv
      rw [abs_div, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2)]
      refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
      have : v ^ 2 ≤ 4 := by nlinarith [hv.2]
      nlinarith)
    (integrable_and_integral_smoothedLagSum_pow_four_le hψ hNM hsupp W).1
    (smoothedLagSum_pow_four_nonneg ψ₁ ψ₂ N M W)
    (integrableOn_Icc_smoothedLagSum_comp_pow_four hψ hNM W hφm _ _)
  rwa [inv_div] at hmain

/-- **The affine substitution.** For `m₁, m₂ ≠ 0`,
`∫_{1/2}^{2} R̃((m₁v + m₃)/m₂)⁴ dv ≤ (|m₂|/|m₁|) ∫_ℝ R̃⁴`. -/
theorem setIntegral_smoothedLagSum_affine_pow_four_le {ψ₁ ψ₂ : ℝ → ℝ}
    (hψ : IsSmoothingPair ψ₁ ψ₂) {A : ℝ} (hsupp : ∀ x, x ∉ Icc A⁻¹ A → ψ₂ x = 0) {N M : ℝ}
    (hNM : 0 < N * M) (W : Finset ℝ) {m₁ m₂ m₃ : ℤ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) :
    ∫ v in Icc (1 / 2 : ℝ) 2, smoothedLagSum ψ₁ ψ₂ N M W ((m₁ * v + m₃) / m₂) ^ 4
      ≤ |(m₂ : ℝ)| / |(m₁ : ℝ)| * ∫ u, smoothedLagSum ψ₁ ψ₂ N M W u ^ 4 := by
  have h₁' : (m₁ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h₁
  have h₂' : (m₂ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h₂
  have hφm : Measurable fun v : ℝ => ((m₁ : ℝ) * v + m₃) / m₂ := by fun_prop
  have hmain := setIntegral_comp_le_inv_mul_integral (S := Icc (1 / 2 : ℝ) 2) measurableSet_Icc
    (φ := fun v : ℝ => ((m₁ : ℝ) * v + m₃) / m₂) (φ' := fun _ => (m₁ : ℝ) / m₂)
    (fun v _ => ((((hasDerivAt_id' v).const_mul (m₁ : ℝ)).add_const (m₃ : ℝ)).div_const
      (m₂ : ℝ)).hasDerivWithinAt.congr_deriv (by ring))
    (injective_affine h₁' h₂').injOn (lam := |(m₁ : ℝ)| / |(m₂ : ℝ)|)
    (div_pos (abs_pos.mpr h₁') (abs_pos.mpr h₂')) (fun _ _ => (abs_div _ _).ge)
    (integrable_and_integral_smoothedLagSum_pow_four_le hψ hNM hsupp W).1
    (smoothedLagSum_pow_four_nonneg ψ₁ ψ₂ N M W)
    (integrableOn_Icc_smoothedLagSum_comp_pow_four hψ hNM W hφm _ _)
  rwa [inv_div] at hmain

/-- `(√√y)⁴ = y` for `y ≥ 0`. -/
theorem sqrt_sqrt_pow_four {y : ℝ} (hy : 0 ≤ y) : Real.sqrt (Real.sqrt y) ^ 4 = y := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hy]

/-- **The bound for one `Ĩ_m`.** For `m₁, m₂, m₃ ≠ 0`, a `1`-separated `W`, and any `Λ` dominating
both Jacobian factors `4|m₂|/|m₃|` and `|m₂|/|m₁|`:
`Ĩ_m ≤ (K₂ |W|)^{1/2} (Λ (∫ψ₁)² K_A E(W))^{1/2}` with `K₂, K_A` the moment constants. -/
theorem smoothedCubicTerm_le {ψ₁ ψ₂ : ℝ → ℝ} (hψ : IsSmoothingPair ψ₁ ψ₂) {A : ℝ} (hA : 1 ≤ A)
    (hsupp : ∀ x, x ∉ Icc A⁻¹ A → ψ₂ x = 0) {N M : ℝ} (hNM : 0 < N * M) {W : Finset ℝ}
    (hW : IsSeparated 1 W) {m₁ m₂ m₃ : ℤ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (h₃ : m₃ ≠ 0) {Λ : ℝ}
    (hΛ₁ : 4 * |(m₂ : ℝ)| / |(m₃ : ℝ)| ≤ Λ) (hΛ₂ : |(m₂ : ℝ)| / |(m₁ : ℝ)| ≤ Λ) :
    smoothedCubicTerm ψ₁ ψ₂ N M W m₁ m₂ m₃
      ≤ Real.sqrt (momentConstant 2 * W.card)
        * Real.sqrt (Λ * ((∫ x, ψ₁ x) ^ 2 * momentConstant A * additiveEnergy W)) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (∫ x, ψ₁ x) ^ 2 * momentConstant A * additiveEnergy W := ⟨_, rfl⟩
  have hR4 : ∫ u, smoothedLagSum ψ₁ ψ₂ N M W u ^ 4 ≤ Q := by
    rw [hQ]
    exact integral_smoothedLagSum_pow_four_le_energy hA hψ hNM hsupp W
  have hR40 : 0 ≤ ∫ u, smoothedLagSum ψ₁ ψ₂ N M W u ^ 4 :=
    integral_nonneg (smoothedLagSum_pow_four_nonneg ψ₁ ψ₂ N M W)
  have hΛ0 : 0 ≤ Λ := le_trans (div_nonneg (abs_nonneg _) (abs_nonneg _)) hΛ₂
  have hQ0 : 0 ≤ Q := hR40.trans hR4
  have hΛQ : 0 ≤ Λ * Q := mul_nonneg hΛ0 hQ0
  have hφ₁m : Measurable fun v : ℝ => ((m₁ : ℝ) * v + m₃) / (m₂ * v) := by fun_prop
  have hφ₂m : Measurable fun v : ℝ => ((m₁ : ℝ) * v + m₃) / m₂ := by fun_prop
  have hG : ∫ v in Icc (1 / 2 : ℝ) 2, smoothedLagSum ψ₁ ψ₂ N M W ((m₁ * v + m₃) / (m₂ * v)) ^ 4
      ≤ Real.sqrt (Real.sqrt (Λ * Q)) ^ 4 := by
    rw [sqrt_sqrt_pow_four hΛQ]
    refine (setIntegral_smoothedLagSum_mobius_pow_four_le hψ hsupp hNM W h₂ h₃).trans ?_
    exact mul_le_mul hΛ₁ hR4 hR40 hΛ0
  have hH : ∫ v in Icc (1 / 2 : ℝ) 2, smoothedLagSum ψ₁ ψ₂ N M W ((m₁ * v + m₃) / m₂) ^ 4
      ≤ Real.sqrt (Real.sqrt (Λ * Q)) ^ 4 := by
    rw [sqrt_sqrt_pow_four hΛQ]
    refine (setIntegral_smoothedLagSum_affine_pow_four_le hψ hsupp hNM W h₁ h₂).trans ?_
    exact mul_le_mul hΛ₂ hR4 hR40 hΛ0
  have hF : ∫ v in Icc (1 / 2 : ℝ) 2, ‖lagSum W v‖ ^ 2
      ≤ Real.sqrt (momentConstant 2 * W.card) ^ 2 := by
    rw [Real.sq_sqrt (mul_nonneg (momentConstant_nonneg (by norm_num)) (Nat.cast_nonneg _)),
      one_div]
    exact setIntegral_Icc_inv_normSq_lagSum_le (by norm_num) hW
  have hmain := setIntegral_mul_mul_le (S := Icc (1 / 2 : ℝ) 2) measurableSet_Icc
    (f := fun v => ‖lagSum W v‖)
    (g := fun v => smoothedLagSum ψ₁ ψ₂ N M W ((m₁ * v + m₃) / (m₂ * v)))
    (h := fun v => smoothedLagSum ψ₁ ψ₂ N M W ((m₁ * v + m₃) / m₂))
    (integrableOn_Icc_norm_lagSum_sq W _ _)
    (integrableOn_Icc_smoothedLagSum_comp_pow_four hψ hNM W hφ₁m _ _)
    (integrableOn_Icc_smoothedLagSum_comp_pow_four hψ hNM W hφ₂m _ _)
    (integrableOn_norm_lagSum_mul_smoothedLagSum hψ hNM W hφ₁m hφ₂m)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hF hG hH
  rw [← hQ]
  refine hmain.trans (le_of_eq ?_)
  rw [mul_assoc, Real.mul_self_sqrt (Real.sqrt_nonneg _)]

/-! ### Proposition 8.1 -/

/-- The constant of Proposition 8.1 for the box constants `c, C` and the support window of
`ψ₂`: `5 (2C + 1)² (1 + 4C/c)(1 + C) √(K₂ K_A)`. -/
def propEightOneConstant (c C A : ℝ) : ℝ :=
  5 * (2 * C + 1) ^ 2 * ((1 + 4 * C / c) * (1 + C))
    * (Real.sqrt (momentConstant 2) * Real.sqrt (momentConstant A))

/-- **Guth–Maynard Proposition 8.1, assembly from Proposition 7.2 (explicit form).**

Assembly lemma: the hypothesis `hS₃` is the conclusion of Proposition 7.2 for an arbitrary real
`S₃`, an arbitrary finite set `𝓜` of frequency triples in the box `|m₁| ∈ [M₁, 2M₁]`,
`|m₂|, |m₃| ∈ [cM, CM]`, and an arbitrary smoothing pair `ψ₁, ψ₂` with `ψ₂` supported in
`[A⁻¹, A]`. For a `1`-separated `W`, `N > 0` and `1 ≤ M₁ ≤ M`:

`S₃ ≤ X · K(c, C, A) · (∫ψ₁) · (NM)² · |W|^{1/2} E(W)^{1/2} + Y`. -/
theorem propEightOne_of_expansion {ψ₁ ψ₂ : ℝ → ℝ} (hψ : IsSmoothingPair ψ₁ ψ₂) {A : ℝ}
    (hA : 1 ≤ A) (hsupp : ∀ x, x ∉ Icc A⁻¹ A → ψ₂ x = 0) {N M M₁ c C : ℝ} (hN : 0 < N)
    (hM₁ : 1 ≤ M₁) (hM₁M : M₁ ≤ M) (hc : 0 < c) (hC : 0 ≤ C) {W : Finset ℝ}
    (hW : IsSeparated 1 W) (𝓜 : Finset (ℤ × ℤ × ℤ))
    (h𝓜 : ∀ m ∈ 𝓜, M₁ ≤ |(m.1 : ℝ)| ∧ |(m.1 : ℝ)| ≤ 2 * M₁ ∧ c * M ≤ |(m.2.1 : ℝ)| ∧
      |(m.2.1 : ℝ)| ≤ C * M ∧ c * M ≤ |(m.2.2 : ℝ)| ∧ |(m.2.2 : ℝ)| ≤ C * M)
    {S₃ X Y : ℝ} (hX : 0 ≤ X)
    (hS₃ : S₃ ≤ X * (N ^ 2 / M) * ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2 + Y) :
    S₃ ≤ X * propEightOneConstant c C A * (∫ x, ψ₁ x) * (N * M) ^ 2
        * Real.sqrt W.card * Real.sqrt (additiveEnergy W) + Y := by
  have hM : 0 < M := by linarith
  have hNM : 0 < N * M := mul_pos hN hM
  have hψ₁ : 0 ≤ ∫ x, ψ₁ x := integral_nonneg hψ.nonneg₁
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = (1 + 4 * C / c) * (1 + C * M / M₁) := ⟨_, rfl⟩
  have hc4 : 0 ≤ 4 * C / c := by positivity
  have hCM : 0 ≤ C * M / M₁ := by positivity
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; nlinarith
  -- the per-term bound
  obtain ⟨B, hB⟩ : ∃ B, B = Real.sqrt (momentConstant 2 * W.card)
      * Real.sqrt (Λ * ((∫ x, ψ₁ x) ^ 2 * momentConstant A * additiveEnergy W)) := ⟨_, rfl⟩
  have hterm : ∀ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2 ≤ B := by
    intro m hm
    obtain ⟨h1l, h1u, h2l, h2u, h3l, h3u⟩ := h𝓜 m hm
    have hcM : 0 < c * M := mul_pos hc hM
    have hm₁ : (m.1 : ℝ) ≠ 0 := abs_pos.mp (by linarith)
    have hm₂ : (m.2.1 : ℝ) ≠ 0 := abs_pos.mp (by linarith)
    have hm₃ : (m.2.2 : ℝ) ≠ 0 := abs_pos.mp (by linarith)
    rw [hB]
    refine smoothedCubicTerm_le hψ hA hsupp hNM hW (Int.cast_ne_zero.mp hm₁)
      (Int.cast_ne_zero.mp hm₂) (Int.cast_ne_zero.mp hm₃) ?_ ?_
    · have hj : 4 * |(m.2.1 : ℝ)| / |(m.2.2 : ℝ)| ≤ 4 * C / c := by
        rw [div_le_div_iff₀ (by linarith) hc]
        nlinarith
      rw [hΛ]
      nlinarith
    · have hj : |(m.2.1 : ℝ)| / |(m.1 : ℝ)| ≤ C * M / M₁ := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [abs_nonneg (m.2.1 : ℝ)]
      rw [hΛ]
      nlinarith
  -- the count of `𝓜`
  have hcard : (𝓜.card : ℝ) ≤ 5 * M₁ * ((2 * C + 1) ^ 2 * M ^ 2) := by
    refine (card_le_of_mem_box 𝓜 (by linarith) (by positivity) (by positivity) fun m hm =>
      ⟨(h𝓜 m hm).2.1, (h𝓜 m hm).2.2.2.1, (h𝓜 m hm).2.2.2.2.2⟩).trans ?_
    have h2 : 2 * (C * M) + 1 ≤ (2 * C + 1) * M := by nlinarith
    have h0 : 0 ≤ 2 * (C * M) + 1 := by positivity
    calc (2 * (2 * M₁) + 1) * ((2 * (C * M) + 1) * (2 * (C * M) + 1))
        ≤ (5 * M₁) * (((2 * C + 1) * M) * ((2 * C + 1) * M)) := by
          gcongr
          linarith
      _ = 5 * M₁ * ((2 * C + 1) ^ 2 * M ^ 2) := by ring
  -- the per-term bound in closed form
  have hB' : B ≤ Real.sqrt (momentConstant 2) * Real.sqrt W.card
      * ((1 + 4 * C / c) * (1 + C) * (M / M₁))
      * ((∫ x, ψ₁ x) * Real.sqrt (momentConstant A) * Real.sqrt (additiveEnergy W)) := by
    have hK2 := momentConstant_nonneg (A := 2) (by norm_num)
    have hKA := momentConstant_nonneg (A := A) (by linarith)
    have hsΛ : Real.sqrt Λ ≤ (1 + 4 * C / c) * (1 + C) * (M / M₁) := by
      have hMM : 1 ≤ M / M₁ := by rw [le_div_iff₀ (by linarith)]; linarith
      have hΛle : Λ ≤ (1 + 4 * C / c) * (1 + C) * (M / M₁) := by
        rw [hΛ, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : C * M / M₁ = C * (M / M₁) := by ring
        rw [this]
        nlinarith
      refine le_trans ?_ hΛle
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    rw [hB, Real.sqrt_mul hK2, Real.sqrt_mul (by linarith), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq hψ₁]
    have h1 : 0 ≤ Real.sqrt (momentConstant 2) * Real.sqrt W.card := by positivity
    have h2 : 0 ≤ (∫ x, ψ₁ x) * Real.sqrt (momentConstant A) * Real.sqrt (additiveEnergy W) := by
      positivity
    calc Real.sqrt (momentConstant 2) * Real.sqrt W.card * (Real.sqrt Λ
          * ((∫ x, ψ₁ x) * Real.sqrt (momentConstant A) * Real.sqrt (additiveEnergy W)))
        = Real.sqrt (momentConstant 2) * Real.sqrt W.card * Real.sqrt Λ
          * ((∫ x, ψ₁ x) * Real.sqrt (momentConstant A) * Real.sqrt (additiveEnergy W)) := by
          ring
      _ ≤ _ := by gcongr
  -- assembly
  have hsum : ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2 ≤ 𝓜.card * B := by
    have := Finset.sum_le_card_nsmul 𝓜 _ B hterm
    rwa [nsmul_eq_mul] at this
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hpre : 0 ≤ X * (N ^ 2 / M) := by positivity
  suffices hfin : X * (N ^ 2 / M) * ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2
      ≤ X * propEightOneConstant c C A * (∫ x, ψ₁ x) * (N * M) ^ 2
        * Real.sqrt W.card * Real.sqrt (additiveEnergy W) by linarith
  calc X * (N ^ 2 / M) * ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2
      ≤ X * (N ^ 2 / M) * (𝓜.card * B) := mul_le_mul_of_nonneg_left hsum hpre
    _ ≤ X * (N ^ 2 / M) * ((5 * M₁ * ((2 * C + 1) ^ 2 * M ^ 2))
          * (Real.sqrt (momentConstant 2) * Real.sqrt W.card
            * ((1 + 4 * C / c) * (1 + C) * (M / M₁))
            * ((∫ x, ψ₁ x) * Real.sqrt (momentConstant A) * Real.sqrt (additiveEnergy W)))) := by
        gcongr
    _ = X * propEightOneConstant c C A * (∫ x, ψ₁ x) * (N * M) ^ 2
          * Real.sqrt W.card * Real.sqrt (additiveEnergy W) := by
        unfold propEightOneConstant
        have hkey : N ^ 2 / M * (5 * M₁ * ((2 * C + 1) ^ 2 * M ^ 2)) * (M / M₁)
            = 5 * (2 * C + 1) ^ 2 * (N * M) ^ 2 := by
          have hM0 : M ≠ 0 := hM.ne'
          have hM₁0 : M₁ ≠ 0 := (show (0 : ℝ) < M₁ by linarith).ne'
          field_simp
        generalize Real.sqrt (momentConstant 2) = s₂
        generalize Real.sqrt (momentConstant A) = sA
        generalize Real.sqrt W.card = sW
        generalize Real.sqrt (additiveEnergy W) = sE
        generalize (∫ x, ψ₁ x) = I
        linear_combination (X * ((1 + 4 * C / c) * (1 + C)) * s₂ * sW * I * sA * sE) * hkey

/-- A nonempty set has additive energy at least `1` (the diagonal quadruple). -/
theorem one_le_additiveEnergy {W : Finset ℝ} (hW : W.Nonempty) : 1 ≤ additiveEnergy W := by
  classical
  obtain ⟨t, ht⟩ := hW
  unfold additiveEnergy
  refine Finset.card_pos.mpr ⟨(t, t, t, t), ?_⟩
  simp [ht]

/-- **Guth–Maynard Proposition 8.1** (`S₃ ⪅ T² |W|^{1/2} E(W)^{1/2}`), assembled from
Proposition 7.2 in the paper's `T^{o(1)}` form.

Assembly lemma: the hypothesis is the conclusion of Proposition 7.2 with an arbitrary constant
`C₇` and loss `T^ε` — `S₃ ≤ C₇ T^ε (N²/M) Σ_{m ∈ 𝓜} Ĩ_m + C₇ T^{-100}` with `NM ≤ C₇ T^{1+ε}`
(`M ⪅ T/N`) and `∫ψ₁ ≤ C₇ T^ε` (`‖ψ̃₁‖_{L¹} ⪅ 1`). For a nonempty `1`-separated `W` (in particular a `T^ε`-separated one) the
conclusion is `S₃ ≤ (K C₇⁴ + C₇) T^{4ε} T² |W|^{1/2} E(W)^{1/2}` with `K` depending only on the
box constants `c, C` and the window `A`. -/
theorem guthMaynard_prop81 {A c C : ℝ} (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K ≥ 0, ∀ (ε T N M M₁ C₇ S₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (W : Finset ℝ)
      (𝓜 : Finset (ℤ × ℤ × ℤ)), 0 ≤ ε → 2 ≤ T → 0 ≤ C₇ →
      IsSmoothingPair ψ₁ ψ₂ → (∀ x, x ∉ Icc A⁻¹ A → ψ₂ x = 0) → (∫ x, ψ₁ x) ≤ C₇ * T ^ ε →
      0 < N → 1 ≤ M₁ → M₁ ≤ M → N * M ≤ C₇ * T ^ (1 + ε) →
      W.Nonempty → IsSeparated 1 W →
      (∀ m ∈ 𝓜, M₁ ≤ |(m.1 : ℝ)| ∧ |(m.1 : ℝ)| ≤ 2 * M₁ ∧ c * M ≤ |(m.2.1 : ℝ)| ∧
        |(m.2.1 : ℝ)| ≤ C * M ∧ c * M ≤ |(m.2.2 : ℝ)| ∧ |(m.2.2 : ℝ)| ≤ C * M) →
      S₃ ≤ C₇ * T ^ ε * (N ^ 2 / M) * ∑ m ∈ 𝓜, smoothedCubicTerm ψ₁ ψ₂ N M W m.1 m.2.1 m.2.2
        + C₇ * T ^ (-100 : ℝ) →
      S₃ ≤ (K * C₇ ^ 4 + C₇) * T ^ (4 * ε)
        * (T ^ 2 * Real.sqrt W.card * Real.sqrt (additiveEnergy W)) := by
  have hK0 : 0 ≤ propEightOneConstant c C A := by
    unfold propEightOneConstant
    positivity
  refine ⟨propEightOneConstant c C A, hK0, ?_⟩
  intro ε T N M M₁ C₇ S₃ ψ₁ ψ₂ W 𝓜 hε hT hC₇ hψ hsupp hψ₁ hN hM₁ hM₁M hNM hWne hW1 h𝓜 hS₃
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε
  have hX : 0 ≤ C₇ * T ^ ε := by positivity
  have hmain := propEightOne_of_expansion hψ hA hsupp hN hM₁ hM₁M hc hC hW1 𝓜 h𝓜 hX hS₃
  obtain ⟨P, hP⟩ : ∃ P, P = Real.sqrt W.card * Real.sqrt (additiveEnergy W) := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := by
    rw [hP]
    have h1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hWne.card_pos
    have h2 : (1 : ℝ) ≤ additiveEnergy W := by exact_mod_cast one_le_additiveEnergy hWne
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ Real.sqrt W.card * Real.sqrt (additiveEnergy W) :=
        mul_le_mul (Real.one_le_sqrt.mpr h1) (Real.one_le_sqrt.mpr h2) zero_le_one
          (Real.sqrt_nonneg _)
  have hψ₁0 : 0 ≤ ∫ x, ψ₁ x := integral_nonneg hψ.nonneg₁
  have hM : 0 < M := by linarith
  have hNM0 : 0 ≤ N * M := by positivity
  -- `T^{1+ε} = T · T^ε` and `T^{4ε} = (T^ε)⁴`
  have hpow1 : T ^ (1 + ε) = T * T ^ ε := by rw [Real.rpow_add hT0, Real.rpow_one]
  have hpow4 : T ^ (4 * ε) = (T ^ ε) ^ 4 := by
    rw [mul_comm, Real.rpow_mul hT0.le]
    norm_cast
  have hT100 : T ^ (-100 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
  have hNMsq : (N * M) ^ 2 ≤ (C₇ * (T * T ^ ε)) ^ 2 := by
    rw [← hpow1]
    exact pow_le_pow_left₀ hNM0 hNM 2
  have hmain' : S₃ ≤ C₇ * T ^ ε * propEightOneConstant c C A * (∫ x, ψ₁ x) * (N * M) ^ 2 * P
      + C₇ * T ^ (-100 : ℝ) := by
    rw [hP]
    linarith [hmain]
  have hbig : C₇ * T ^ ε * propEightOneConstant c C A * (∫ x, ψ₁ x) * (N * M) ^ 2 * P
      ≤ propEightOneConstant c C A * C₇ ^ 4 * (T ^ ε) ^ 4 * (T ^ 2 * P) := by
    have hP0 : 0 ≤ P := by linarith
    calc C₇ * T ^ ε * propEightOneConstant c C A * (∫ x, ψ₁ x) * (N * M) ^ 2 * P
        ≤ C₇ * T ^ ε * propEightOneConstant c C A * (C₇ * T ^ ε) * (C₇ * (T * T ^ ε)) ^ 2 * P := by
          gcongr
      _ = propEightOneConstant c C A * C₇ ^ 4 * (T ^ ε) ^ 4 * (T ^ 2 * P) := by ring
  have hsmall : C₇ * T ^ (-100 : ℝ) ≤ C₇ * (T ^ ε) ^ 4 * (T ^ 2 * P) := by
    have h1 : 1 ≤ (T ^ ε) ^ 4 := one_le_pow₀ hTε
    have h2 : 1 ≤ T ^ 2 := one_le_pow₀ hT1
    have h3 : 1 ≤ (T ^ ε) ^ 4 * (T ^ 2 * P) := by
      calc (1 : ℝ) = 1 * (1 * 1) := by ring
        _ ≤ (T ^ ε) ^ 4 * (T ^ 2 * P) := by gcongr
    calc C₇ * T ^ (-100 : ℝ) ≤ C₇ * 1 := mul_le_mul_of_nonneg_left hT100 hC₇
      _ ≤ C₇ * ((T ^ ε) ^ 4 * (T ^ 2 * P)) := mul_le_mul_of_nonneg_left h3 hC₇
      _ = C₇ * (T ^ ε) ^ 4 * (T ^ 2 * P) := by ring
  rw [hpow4, show T ^ 2 * Real.sqrt W.card * Real.sqrt (additiveEnergy W) = T ^ 2 * P by
    rw [hP]; ring]
  calc S₃ ≤ propEightOneConstant c C A * C₇ ^ 4 * (T ^ ε) ^ 4 * (T ^ 2 * P)
        + C₇ * (T ^ ε) ^ 4 * (T ^ 2 * P) := by linarith
    _ = (propEightOneConstant c C A * C₇ ^ 4 + C₇) * (T ^ ε) ^ 4 * (T ^ 2 * P) := by ring

/-! ### The bumps of Proposition 7.2 -/

/-- `∫ ψ̃₁ ≤ 4A` for the inner bump of width `A` (values in `[0, 1]`, support `|x| < 2A`). -/
theorem integral_innerBump_le {A : ℝ} (hA : 0 < A) : ∫ x, innerBump A x ≤ 4 * A := by
  have hzero : ∀ x, x ∉ Icc (-(2 * A)) (2 * A) → innerBump A x = 0 := fun x hx =>
    innerBump_eq_zero hA (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc ∫ x in Icc (-(2 * A)) (2 * A), innerBump A x
      ≤ ∫ _x in Icc (-(2 * A)) (2 * A), (1 : ℝ) :=
        setIntegral_mono_on (contDiff_innerBump A).continuous.integrableOn_Icc
          continuous_const.integrableOn_Icc measurableSet_Icc fun x _ => innerBump_le_one A x
    _ = 4 * A := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring

/-- The outer bump vanishes off `[1/8, 8]`. -/
theorem outerBump_eq_zero_of_not_mem_Icc {x : ℝ} (hx : x ∉ Icc (8 : ℝ)⁻¹ 8) : outerBump x = 0 :=
  outerBump_eq_zero fun h => hx ⟨by norm_num at h ⊢; linarith [h.1], by linarith [h.2]⟩

/-- **Guth–Maynard Proposition 8.1 for the bumps of Proposition 7.2.**

Assembly lemma, specialised to `ψ̃₁ = innerBump (2T^{ε/2})`, `ψ̃₂ = outerBump` and the block
`|m₁| ∈ [M₁, 2M₁]`, `|m₂|, |m₃| ∈ [M, 9M]`: if
`S₃ ≤ C₇ T^ε (N²/M) Σ_{m ∈ 𝓜} Ĩ_m + C₇ T^{-100}` with `NM ≤ T^{1+ε}` (i.e. `M ≤ T^{1+ε}/N`), then
`S₃ ≤ (K (8C₇)⁴ + 8C₇) T^{4ε} T² |W|^{1/2} E(W)^{1/2}` for every nonempty `1`-separated `W`. -/
theorem guthMaynard_prop81_innerBump_outerBump :
    ∃ K ≥ 0, ∀ (ε T N M M₁ C₇ S₃ : ℝ) (W : Finset ℝ) (𝓜 : Finset (ℤ × ℤ × ℤ)),
      0 < ε → 2 ≤ T → 1 ≤ C₇ → 0 < N → 1 ≤ M₁ → M₁ ≤ M → N * M ≤ T ^ (1 + ε) →
      W.Nonempty → IsSeparated 1 W →
      (∀ m ∈ 𝓜, M₁ ≤ |(m.1 : ℝ)| ∧ |(m.1 : ℝ)| ≤ 2 * M₁ ∧ M ≤ |(m.2.1 : ℝ)| ∧
        |(m.2.1 : ℝ)| ≤ 9 * M ∧ M ≤ |(m.2.2 : ℝ)| ∧ |(m.2.2 : ℝ)| ≤ 9 * M) →
      S₃ ≤ C₇ * T ^ ε * (N ^ 2 / M) * ∑ m ∈ 𝓜, smoothedCubicTerm (innerBump (2 * T ^ (ε / 2)))
          outerBump N M W m.1 m.2.1 m.2.2 + C₇ * T ^ (-100 : ℝ) →
      S₃ ≤ (K * (8 * C₇) ^ 4 + 8 * C₇) * T ^ (4 * ε)
        * (T ^ 2 * Real.sqrt W.card * Real.sqrt (additiveEnergy W)) := by
  obtain ⟨K, hK0, hK⟩ := guthMaynard_prop81 (A := 8) (c := 1) (C := 9) (by norm_num) one_pos
    (by norm_num)
  refine ⟨K, hK0, fun ε T N M M₁ C₇ S₃ W 𝓜 hε hT hC₇ hN hM₁ hM₁M hNM hWne hW h𝓜 hS₃ => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hTε2 : T ^ (ε / 2) ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTε0 : 0 < T ^ (ε / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hψ₁ : ∫ x, innerBump (2 * T ^ (ε / 2)) x ≤ 8 * C₇ * T ^ ε := by
    refine (integral_innerBump_le (by positivity)).trans ?_
    nlinarith
  have hNM' : N * M ≤ 8 * C₇ * T ^ (1 + ε) := by
    have : 0 ≤ T ^ (1 + ε) := by positivity
    nlinarith
  have hsum : 0 ≤ N ^ 2 / M * ∑ m ∈ 𝓜, smoothedCubicTerm (innerBump (2 * T ^ (ε / 2)))
      outerBump N M W m.1 m.2.1 m.2.2 :=
    mul_nonneg (div_nonneg (sq_nonneg _) (by linarith))
      (Finset.sum_nonneg fun m _ => smoothedCubicTerm_nonneg _ _ _ _ _ _ _ _)
  have hS₃' : S₃ ≤ 8 * C₇ * T ^ ε * (N ^ 2 / M) * ∑ m ∈ 𝓜, smoothedCubicTerm
      (innerBump (2 * T ^ (ε / 2))) outerBump N M W m.1 m.2.1 m.2.2
        + 8 * C₇ * T ^ (-100 : ℝ) := by
    have hTe : 0 ≤ T ^ ε := by positivity
    have hT100 : 0 ≤ T ^ (-100 : ℝ) := by positivity
    have h1 : C₇ * T ^ ε * (N ^ 2 / M * ∑ m ∈ 𝓜, smoothedCubicTerm (innerBump (2 * T ^ (ε / 2)))
        outerBump N M W m.1 m.2.1 m.2.2) ≤ 8 * C₇ * T ^ ε * (N ^ 2 / M * ∑ m ∈ 𝓜,
        smoothedCubicTerm (innerBump (2 * T ^ (ε / 2))) outerBump N M W m.1 m.2.1 m.2.2) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hsum
    have h2 : C₇ * T ^ (-100 : ℝ) ≤ 8 * C₇ * T ^ (-100 : ℝ) := by nlinarith
    simp only [mul_assoc] at hS₃ h1 ⊢
    linarith
  exact hK ε T N M M₁ (8 * C₇) S₃ (innerBump (2 * T ^ (ε / 2))) outerBump W 𝓜 hε.le hT
    (by linarith) (isSmoothingPair_innerBump_outerBump (by positivity))
    (fun x hx => outerBump_eq_zero_of_not_mem_Icc hx) hψ₁ hN hM₁ hM₁M hNM' hWne hW
    (fun m hm => by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h𝓜 m hm
      exact ⟨h1, h2, by linarith, h4, by linarith, h6⟩) hS₃'

end

end RHTower.GuthMaynard

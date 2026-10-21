import GaloisForLFunctions.RHTower.Sieve.GuthMaynardAffineSpectral
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

set_option autoImplicit false

/-!
# Iterative bound for `J(f)` (Guth–Maynard, Lemma 9.2)

Let `f ≥ 0` be continuous with compact support and `η² |f̂(η)| ≤ B` for all `η`. For every
`Ξ > 0`, `ε > 0` and scales `M₁, M₂, M₃` with `μ = max(M₁, M₂, M₃, 1/2)`
(`affineEnergy_le_iteration`):

`∫ A² ≤ 124416π μ⁶ (∫ f)² + 3072 (1 + C_ε (3Ξ)^ε) μ² ‖f‖₂ (∫ A'²)^{1/2} + 373248π μ⁶ B² Ξ⁻³`,

where `A'` is the affine sum at scales `(M₂, M₂, 2⌊M₃⌋ + 1)`. Proof: `A(u) = A₊(u) + A₊(−u)`,
`L · A₊ ≤ G` (Fejér majorant, `K = 2L` terms), the spectral bound for `∫ G²`, the square-function
bound `∫ χ² ≤ 2 K M₂ ∫ f A₊'` and Cauchy–Schwarz `∫ f A₊' ≤ ‖f‖₂ ‖A₊'‖₂`.

In terms of `J` (`affineSup_le_iteration`), for `M > 0`:

`J_M(f) ≤ 124416π M⁶ (∫ f)² + 3072 (1 + C_ε (3Ξ)^ε) M² ‖f‖₂ J_{4M}(f)^{1/2} + 373248π M⁶ B² Ξ⁻³`.

This is Guth–Maynard's Lemma 9.2 with the smoothing `ψ` replaced by the identity: the paper bounds
the off-diagonal frequencies through a `1/T`-smoothed copy `f̃`; here the exact Fejér factorisation
`|Ĝ(ξ)| ≤ Σ_n n⁻¹ |D_K(ξ/n)| |χ̂(ξ/n)|` and Plancherel for `χ` return `f` itself, at the cost of
the scale `4M` in place of `M`. With `Ξ = T⁴` and `B ≪ T^{O(1)} ∫ f` the last term is `≪ M⁶ (∫ f)²`
and the only loss is the divisor bound `C_ε (3Ξ)^ε ≪_ε T^{4ε}`.
-/

open MeasureTheory Finset Real
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

open RHTower.Sieve (divisorBoundConst)

variable {f : ℝ → ℝ}

/-- Cauchy–Schwarz on the line in square-root form (from `HTGeometry.sq_integral_mul_le`). -/
theorem integral_mul_le_sqrt_mul_sqrt {g h : ℝ → ℝ} (hg : MemLp g 2) (hh : MemLp h 2) :
    ∫ x, g x * h x ≤ √(∫ x, g x ^ 2) * √(∫ x, h x ^ 2) := by
  have hcs := GaloisForLFunctions.HTGeometry.sq_integral_mul_le hg.aestronglyMeasurable
    hh.aestronglyMeasurable hg.integrable_sq hh.integrable_sq
  have h0 : 0 ≤ ∫ x, g x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [← Real.sqrt_mul h0]
  exact (le_abs_self _).trans (Real.abs_le_sqrt hcs)

/-- The real-number bookkeeping of Lemma 9.2: with `K = 2L`, `K ≤ 6μ`, `M₁, M₂ ≤ μ` and
`D ≤ 32 (1 + C) μ K`, the three spectral terms collapse to powers of `μ`. -/
theorem iteration_real_bound {K L μ M₁ M₂ D C F S Y : ℝ} (hKL : K = 2 * L) (hL : 1 ≤ L)
    (hKμ : K ≤ 6 * μ) (hM₁ : 0 ≤ M₁) (hM₁μ : M₁ ≤ μ) (hM₂ : 0 ≤ M₂) (hM₂μ : M₂ ≤ μ)
    (hC : 0 ≤ C) (hD : D ≤ 32 * (1 + C) * μ * K) (hF : 0 ≤ F) (hS : 0 ≤ S) (hY : 0 ≤ Y) :
    4 * (L⁻¹ ^ 2 * (36 * π * K ^ 3 * M₁ * (6 * M₂ ^ 2 * F) ^ 2 + 3 * D * (K * (2 * M₂) * S) +
      648 * π * K ^ 4 * M₁ ^ 4 * Y)) ≤
      124416 * π * μ ^ 6 * F ^ 2 + 3072 * (1 + C) * μ ^ 2 * S + 373248 * π * μ ^ 6 * Y := by
  have hL0 : 0 < L := by linarith
  have hK0 : 0 < K := by linarith
  have hμ0 : 0 ≤ μ := by linarith
  have hLK : L⁻¹ ^ 2 = 4 / K ^ 2 := by
    rw [hKL]
    field_simp
    ring
  have e : 4 * (L⁻¹ ^ 2 * (36 * π * K ^ 3 * M₁ * (6 * M₂ ^ 2 * F) ^ 2 + 3 * D * (K * (2 * M₂) * S) +
      648 * π * K ^ 4 * M₁ ^ 4 * Y)) =
      20736 * π * K * M₁ * M₂ ^ 4 * F ^ 2 + 96 * D * M₂ * S / K + 10368 * π * K ^ 2 * M₁ ^ 4 * Y := by
    rw [hLK]
    field_simp
    ring
  rw [e]
  have t1 : 20736 * π * K * M₁ * M₂ ^ 4 * F ^ 2 ≤ 124416 * π * μ ^ 6 * F ^ 2 := by
    calc 20736 * π * K * M₁ * M₂ ^ 4 * F ^ 2 ≤ 20736 * π * (6 * μ) * μ * μ ^ 4 * F ^ 2 := by
          gcongr
      _ = 124416 * π * μ ^ 6 * F ^ 2 := by ring
  have t2 : 96 * D * M₂ * S / K ≤ 3072 * (1 + C) * μ ^ 2 * S := by
    rw [div_le_iff₀ hK0]
    have hDS : D * (M₂ * S) ≤ (32 * (1 + C) * μ * K) * (μ * S) := by
      have hDK0 : 0 ≤ 32 * (1 + C) * μ * K :=
        mul_nonneg (mul_nonneg (by linarith) hμ0) hK0.le
      exact mul_le_mul hD (mul_le_mul_of_nonneg_right hM₂μ hS) (by positivity) hDK0
    nlinarith [hDS]
  have t3 : 10368 * π * K ^ 2 * M₁ ^ 4 * Y ≤ 373248 * π * μ ^ 6 * Y := by
    calc 10368 * π * K ^ 2 * M₁ ^ 4 * Y ≤ 10368 * π * (6 * μ) ^ 2 * μ ^ 4 * Y := by gcongr
      _ = 373248 * π * μ ^ 6 * Y := by ring
  linarith

/-- The analytic part of Lemma 9.2: `∫ A₊² ≤ L⁻² (36π K³ M₁ Ψ₀² + 3D K 2M₂ ‖f‖₂ ‖A₊'‖₂ +
648π K⁴ B² M₁⁴ Ξ⁻³)` with `L = ⌊M₃⌋ + 1`, `K = 2L`. -/
theorem integral_posAffineSum_sq_le_spectral (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hB : ∀ η : ℝ, η ^ 2 * ‖𝓕 (complexify f) η‖ ≤ B)
    {Ξ ε : ℝ} (hΞ : 0 < Ξ) (hε : 0 < ε) {M₁ M₂ M₃ : ℝ} (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂)
    (hM₃ : 0 ≤ M₃) :
    ∫ u, posAffineSum f M₁ M₂ M₃ u ^ 2 ≤
      ((⌊M₃⌋₊ + 1 : ℕ) : ℝ)⁻¹ ^ 2 *
        (36 * π * ((2 * (⌊M₃⌋₊ + 1) : ℕ) : ℝ) ^ 3 * M₁ * (6 * M₂ ^ 2 * ∫ x, f x) ^ 2 +
          3 * fejerCount ε Ξ M₁ (2 * (⌊M₃⌋₊ + 1)) *
            (((2 * (⌊M₃⌋₊ + 1) : ℕ) : ℝ) * (2 * M₂) *
              (√(∫ x, f x ^ 2) * √(affineEnergy f M₂ M₂ (2 * ⌊M₃⌋₊ + 1)))) +
          648 * π * ((2 * (⌊M₃⌋₊ + 1) : ℕ) : ℝ) ^ 4 * M₁ ^ 4 * (B ^ 2 * Ξ⁻¹ ^ 3)) := by
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ⌊M₃⌋₊ + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 2 * (⌊M₃⌋₊ + 1) := ⟨_, rfl⟩
  rw [← hK, ← hL]
  have hK1 : 1 ≤ K := by omega
  have hK3 : ((K : ℝ) - 1) = 2 * ⌊M₃⌋₊ + 1 := by rw [hK]; push_cast; ring
  -- `∫ A₊² ≤ L⁻² ∫ G²`
  have hmaj : ∫ u, posAffineSum f M₁ M₂ M₃ u ^ 2 ≤
      (L : ℝ)⁻¹ ^ 2 * ∫ u, fejerMajorant f M₁ M₂ K u ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono (memLp_posAffineSum hf hfc M₁ M₂ M₃ 2).integrable_sq
      ((memLp_fejerMajorant hf hfc M₁ M₂ K 2).integrable_sq.const_mul _) fun u => ?_
    have h1 := posAffineSum_le_fejerMajorant hf0 M₁ M₂ hM₃ u
    rw [← hK, ← hL] at h1
    have h0 := posAffineSum_nonneg hf0 M₁ M₂ M₃ u
    have hL0 : (0 : ℝ) < L := by rw [hL]; positivity
    have h2 : posAffineSum f M₁ M₂ M₃ u ≤ (L : ℝ)⁻¹ * fejerMajorant f M₁ M₂ K u := by
      rw [inv_mul_eq_div, le_div_iff₀ hL0, mul_comm]
      exact h1
    calc posAffineSum f M₁ M₂ M₃ u ^ 2 ≤ ((L : ℝ)⁻¹ * fejerMajorant f M₁ M₂ K u) ^ 2 :=
          pow_le_pow_left₀ h0 h2 2
      _ = (L : ℝ)⁻¹ ^ 2 * fejerMajorant f M₁ M₂ K u ^ 2 := by ring
  -- the square function of `χ`
  have hHE : ∫ u, posAffineSum f M₂ M₂ ((K : ℝ) - 1) u ^ 2 ≤
      affineEnergy f M₂ M₂ (2 * ⌊M₃⌋₊ + 1) := by
    rw [← hK3]
    refine integral_mono (memLp_posAffineSum hf hfc _ _ _ 2).integrable_sq
      (memLp_affineSum hf hfc _ _ _ 2).integrable_sq fun u => ?_
    exact pow_le_pow_left₀ (posAffineSum_nonneg hf0 _ _ _ u)
      (posAffineSum_le_affineSum hf0 _ _ _ u) 2
  have hχ : ∫ x, translateSum f M₂ K x ^ 2 ≤
      K * (2 * M₂) * (√(∫ x, f x ^ 2) * √(affineEnergy f M₂ M₂ (2 * ⌊M₃⌋₊ + 1))) := by
    refine (integral_translateSum_sq_le hf hfc hf0 M₂ K).trans ?_
    have hK0 : (0 : ℝ) ≤ K * (2 * M₂) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hK0
    refine (integral_mul_le_sqrt_mul_sqrt (hf.memLp_of_hasCompactSupport hfc)
      (memLp_posAffineSum hf hfc _ _ _ 2)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHE) (Real.sqrt_nonneg _)
  have hG := integral_fejerMajorant_sq_le hf hfc hf0 hB hM₁ hM₂ hΞ hε hK1
  have hD0 : 0 ≤ fejerCount ε Ξ M₁ K := fejerCount_nonneg hε hΞ.le (by linarith) K
  refine hmaj.trans (mul_le_mul_of_nonneg_left (hG.trans ?_) (by positivity))
  have := mul_le_mul_of_nonneg_left hχ (by positivity : (0 : ℝ) ≤ 3 * fejerCount ε Ξ M₁ K)
  have e : 648 * π * (K : ℝ) ^ 4 * B ^ 2 * M₁ ^ 4 * Ξ⁻¹ ^ 3 =
      648 * π * (K : ℝ) ^ 4 * M₁ ^ 4 * (B ^ 2 * Ξ⁻¹ ^ 3) := by ring
  rw [e]
  linarith

/-- The high-frequency count is `≤ 32 (1 + C_ε (3Ξ)^ε) μ K` once `K ≥ 2`, `K ≤ 6μ`, `M₁ ≤ μ`. -/
theorem fejerCount_le {ε Ξ M₁ μ : ℝ} (hε : 0 < ε) (hΞ : 0 ≤ Ξ) {K : ℕ} (hK2 : (2 : ℝ) ≤ K)
    (hKμ : (K : ℝ) ≤ 6 * μ) (hM₁ : 0 ≤ M₁) (hM₁μ : M₁ ≤ μ) :
    fejerCount ε Ξ M₁ K ≤ 32 * (1 + divisorBoundConst ε * (3 * Ξ) ^ ε) * μ * K := by
  obtain ⟨C, hC⟩ : ∃ C, C = divisorBoundConst ε * (3 * Ξ) ^ ε := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (divisorBoundConst_nonneg hε) (Real.rpow_nonneg (by linarith) _)
  rw [fejerCount, ← hC]
  have hπ : π ≤ 4 := Real.pi_lt_four.le
  have h1 : 12 * M₁ ≤ 6 * μ * K := by nlinarith
  have h2 : 4 * (K : ℝ) ^ 2 + 2 * π * K * M₁ ≤ 32 * μ * K := by
    have h3 : 2 * π * M₁ ≤ 8 * μ := by nlinarith [Real.pi_pos]
    have h4 : 4 * (K : ℝ) ^ 2 ≤ 24 * μ * K := by nlinarith
    nlinarith
  have h5 := mul_le_mul_of_nonneg_left h2 hC0
  nlinarith

/-- **Lemma 9.2, explicit form.** One step of the iteration at fixed scales:
`∫ A² ≤ 124416π μ⁶ (∫ f)² + 3072 (1 + C_ε (3Ξ)^ε) μ² ‖f‖₂ (∫ A'²)^{1/2} + 373248π μ⁶ B² Ξ⁻³`,
`A'` the affine sum at scales `(M₂, M₂, 2⌊M₃⌋ + 1)`. -/
theorem affineEnergy_le_iteration (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hB : ∀ η : ℝ, η ^ 2 * ‖𝓕 (complexify f) η‖ ≤ B)
    {Ξ ε : ℝ} (hΞ : 0 < Ξ) (hε : 0 < ε) (M₁ M₂ M₃ : ℝ) :
    affineEnergy f M₁ M₂ M₃ ≤
      124416 * π * affineScale M₁ M₂ M₃ ^ 6 * (∫ x, f x) ^ 2 +
        3072 * (1 + divisorBoundConst ε * (3 * Ξ) ^ ε) * affineScale M₁ M₂ M₃ ^ 2 *
          (√(∫ x, f x ^ 2) * √(affineEnergy f M₂ M₂ (2 * ⌊M₃⌋₊ + 1))) +
        373248 * π * affineScale M₁ M₂ M₃ ^ 6 * (B ^ 2 * Ξ⁻¹ ^ 3) := by
  have hC0 : 0 ≤ divisorBoundConst ε * (3 * Ξ) ^ ε :=
    mul_nonneg (divisorBoundConst_nonneg hε) (Real.rpow_nonneg (by linarith) _)
  have hμ := half_le_affineScale M₁ M₂ M₃
  obtain ⟨hμ1, hμ2, hμ3⟩ := le_affineScale M₁ M₂ M₃
  have hF0 : 0 ≤ ∫ x, f x := integral_nonneg hf0
  by_cases hs : M₁ < 1 / 2 ∨ M₂ < 1 / 2 ∨ M₃ < 0
  · rw [affineEnergy_eq_zero_of_scales hs]
    have : 0 ≤ affineScale M₁ M₂ M₃ := by linarith
    positivity
  simp only [not_or, not_lt] at hs
  obtain ⟨hM₁, hM₂, hM₃⟩ := hs
  have hfl := Nat.floor_le hM₃
  have hL1 : (1 : ℝ) ≤ ((⌊M₃⌋₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hKL : ((2 * (⌊M₃⌋₊ + 1) : ℕ) : ℝ) = 2 * ((⌊M₃⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
  have hKμ : ((2 * (⌊M₃⌋₊ + 1) : ℕ) : ℝ) ≤ 6 * affineScale M₁ M₂ M₃ := by
    push_cast
    linarith
  have hspec := integral_posAffineSum_sq_le_spectral hf hfc hf0 hB hΞ hε hM₁ hM₂ hM₃
  have hD := fejerCount_le hε hΞ.le (K := 2 * (⌊M₃⌋₊ + 1)) (by rw [hKL]; linarith) hKμ
    (by linarith) hμ1
  have hreal := iteration_real_bound hKL hL1 hKμ (by linarith) hμ1 (by linarith) hμ2 hC0 hD
    hF0 (by positivity) (by positivity)
  calc affineEnergy f M₁ M₂ M₃ ≤ 4 * ∫ u, posAffineSum f M₁ M₂ M₃ u ^ 2 :=
        affineEnergy_le_four_mul hf hfc M₁ M₂ M₃
    _ ≤ _ := (mul_le_mul_of_nonneg_left hspec (by norm_num)).trans hreal

/-- `J(f)` is nonnegative. -/
theorem affineSup_nonneg (f : ℝ → ℝ) (M : ℝ) : 0 ≤ affineSup f M := by
  refine Real.sSup_nonneg fun x hx => ?_
  obtain ⟨t, -, rfl⟩ := hx
  exact affineEnergy_nonneg f _ _ _

/-- **Lemma 9.2, `J`-form.** For `M > 0`:
`J_M(f) ≤ 124416π M⁶ (∫ f)² + 3072 (1 + C_ε (3Ξ)^ε) M² ‖f‖₂ J_{4M}(f)^{1/2} + 373248π M⁶ B² Ξ⁻³`. -/
theorem affineSup_le_iteration (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hB : ∀ η : ℝ, η ^ 2 * ‖𝓕 (complexify f) η‖ ≤ B)
    {Ξ ε : ℝ} (hΞ : 0 < Ξ) (hε : 0 < ε) {M : ℝ} (hM : 0 < M) :
    affineSup f M ≤
      124416 * π * M ^ 6 * (∫ x, f x) ^ 2 +
        3072 * (1 + divisorBoundConst ε * (3 * Ξ) ^ ε) * M ^ 2 *
          (√(∫ x, f x ^ 2) * √(affineSup f (4 * M))) +
        373248 * π * M ^ 6 * (B ^ 2 * Ξ⁻¹ ^ 3) := by
  set C := divisorBoundConst ε * (3 * Ξ) ^ ε with hCdef
  have hC0 : 0 ≤ C := mul_nonneg (divisorBoundConst_nonneg hε) (Real.rpow_nonneg (by linarith) _)
  have hF0 : 0 ≤ ∫ x, f x := integral_nonneg hf0
  have hRHS0 : 0 ≤ 124416 * π * M ^ 6 * (∫ x, f x) ^ 2 +
      3072 * (1 + C) * M ^ 2 * (√(∫ x, f x ^ 2) * √(affineSup f (4 * M))) +
      373248 * π * M ^ 6 * (B ^ 2 * Ξ⁻¹ ^ 3) := by
    positivity
  refine affineSup_le hM fun t ht => ?_
  obtain ⟨h1, h1', h2, h2', h3, h3'⟩ := ht
  by_cases hs : t.1 < 1 / 2 ∨ t.2.1 < 1 / 2 ∨ t.2.2 < 0
  · rw [affineEnergy_eq_zero_of_scales hs]
    exact hRHS0
  simp only [not_or, not_lt] at hs
  obtain ⟨hM₁, hM₂, hM₃⟩ := hs
  have hM2 : 1 / 2 ≤ M := by linarith
  have hμM : affineScale t.1 t.2.1 t.2.2 ≤ M :=
    max_le (max_le h1'.le h2'.le) (max_le h3'.le hM2)
  have hμ0 : 0 ≤ affineScale t.1 t.2.1 t.2.2 := by linarith [half_le_affineScale t.1 t.2.1 t.2.2]
  have hwin : (t.2.1, t.2.1, (2 * ⌊t.2.2⌋₊ + 1 : ℝ)) ∈ affineWindow (4 * M) := by
    have hfl := Nat.floor_le hM₃
    refine ⟨h2, by linarith, h2, by linarith, by positivity, by linarith⟩
  have hE' := affineEnergy_le_affineSup hf hfc hwin
  refine (affineEnergy_le_iteration hf hfc hf0 hB hΞ hε t.1 t.2.1 t.2.2).trans ?_
  have hB2 : 0 ≤ B ^ 2 * Ξ⁻¹ ^ 3 := by positivity
  gcongr

end

end RHTower.GuthMaynard

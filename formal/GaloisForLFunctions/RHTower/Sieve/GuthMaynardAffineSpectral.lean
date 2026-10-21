import GaloisForLFunctions.RHTower.Sieve.GuthMaynardAffineDivisorCount
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral

set_option autoImplicit false

/-!
# The spectral side of the Fejér majorant

Let `G` be the Fejér majorant of `A₊` (module `GuthMaynardAffineFejer`), with `K` Fejér terms, and
suppose `η² |f̂(η)| ≤ B` for all `η`. Write `ψ̂, χh` for the transforms of `ψ = Σ_m f(·/m)` and
`χ = Σ_{a<K} ψ(· + a)`, and `P_K = |D_K|²`. From
`|Ĝ(ξ)| ≤ Σ_{n ∼ M₁} n⁻¹ |D_K(ξ/n)| |χh(ξ/n)|` and `|χh| = |D_K| |ψ̂|`:

* `|ξ| ≤ M₁/2` (`normSq_fourier_fejerMajorant_le_low`): `|ψ̂| ≤ Ψ₀ = 6M₂² ∫ f` and
  `P_K(ξ/n) ≤ 2K² f_{M₁/K}(ξ)` give `|Ĝ(ξ)|² ≤ 36 K⁴ Ψ₀² f_{M₁/K}(ξ)`;
* `M₁/2 < |ξ| ≤ Ξ` (`normSq_fourier_fejerMajorant_le_high`): Cauchy–Schwarz over `n` and the
  divisor-bound count `Σ_n P_K(ξ/n) ≤ D` give `|Ĝ(ξ)|² ≤ (D/M₁) Σ_n n⁻¹ |χh(ξ/n)|²`;
* `|ξ| > Ξ` (`normSq_fourier_fejerMajorant_le_far`): `|ψ̂(θ)| ≤ 3B/θ²` and `P_K ≤ K²` give
  `|Ĝ(ξ)| ≤ 18 K² B M₁²/ξ²`, hence `|Ĝ(ξ)|² ≤ 648 K⁴ B² M₁⁴ Ξ⁻⁴ f_Ξ(ξ)`.

Integrating (Plancherel for `G` and `χ`, `∫ f_τ = πτ`, `∫ |χh(ξ/n)|² dξ = n ∫ χ²`) gives
(`integral_fejerMajorant_sq_le`)

`∫ G² ≤ 36π K³ M₁ Ψ₀² + 3D ∫ χ² + 648π K⁴ B² M₁⁴ Ξ⁻³`,
`D = 12M₁ + C_ε (3Ξ)^ε (4K² + 2πKM₁)`.
-/

open MeasureTheory Finset Real
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

open RHTower.Sieve (finitePhaseProgression divisorBoundConst)
open GaloisForLFunctions.HTGeometry (lorentzF lorentzF_nonneg lorentzF_le_one)

/-- The high-frequency count `D = 12 M₁ + C_ε (3Ξ)^ε (4K² + 2π K M₁)`. -/
def fejerCount (ε Ξ M₁ : ℝ) (K : ℕ) : ℝ :=
  12 * M₁ + divisorBoundConst ε * (3 * Ξ) ^ ε * (4 * (K : ℝ) ^ 2 + 2 * π * K * M₁)

theorem fejerCount_nonneg {ε Ξ M₁ : ℝ} (hε : 0 < ε) (hΞ : 0 ≤ Ξ) (hM₁ : 0 ≤ M₁) (K : ℕ) :
    0 ≤ fejerCount ε Ξ M₁ K := by
  unfold fejerCount
  have := divisorBoundConst_nonneg hε
  have : 0 ≤ (3 * Ξ) ^ ε := Real.rpow_nonneg (by linarith) _
  positivity

variable {f : ℝ → ℝ}

/-- `|Ĝ(ξ)| ≤ Σ_n n⁻¹ P_K(ξ/n) |ψ̂(ξ/n)|`. -/
theorem norm_fourier_fejerMajorant_le_weight (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₁ M₂ : ℝ) (K : ℕ) (ξ : ℝ) :
    ‖𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ‖ ≤
      ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ *
        (fejerWeight K (ξ / n) * ‖𝓕 (complexify (dilationSum f M₂)) (ξ / n)‖) := by
  refine (norm_fourier_fejerMajorant_le hf hfc M₁ M₂ K ξ).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [norm_fourier_translateSum hf hfc, fejerWeight]
  ring

/-- `|ψ̂(θ)| ≤ 6 M₂² ∫ f`. -/
theorem norm_fourier_dilationSum_le_mass (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) {M₂ : ℝ} (hM₂ : 1 / 2 ≤ M₂) (θ : ℝ) :
    ‖𝓕 (complexify (dilationSum f M₂)) θ‖ ≤ 6 * M₂ ^ 2 * ∫ x, f x := by
  have hF0 : 0 ≤ ∫ x, f x := integral_nonneg hf0
  calc ‖𝓕 (complexify (dilationSum f M₂)) θ‖
      ≤ ∑ m ∈ dyadicNat M₂, (m : ℝ) * ‖𝓕 (complexify f) (m * θ)‖ :=
        norm_fourier_dilationSum_le hf hfc M₂ θ
    _ ≤ ∑ m ∈ dyadicNat M₂, (m : ℝ) * ∫ x, f x :=
        Finset.sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_left (norm_fourier_complexify_le hf0 _) (Nat.cast_nonneg m)
    _ = (∑ m ∈ dyadicNat M₂, (m : ℝ)) * ∫ x, f x := by rw [Finset.sum_mul]
    _ ≤ 6 * M₂ ^ 2 * ∫ x, f x := by gcongr; exact sum_dyadicNat_le hM₂

/-- `|ψ̂(θ)| ≤ 3B/θ²` when `η² |f̂(η)| ≤ B`. -/
theorem norm_fourier_dilationSum_le_decay (hf : Continuous f) (hfc : HasCompactSupport f)
    {B : ℝ} (hB : ∀ η : ℝ, η ^ 2 * ‖𝓕 (complexify f) η‖ ≤ B) {M₂ : ℝ} (hM₂ : 1 / 2 ≤ M₂)
    {θ : ℝ} (hθ : θ ≠ 0) :
    ‖𝓕 (complexify (dilationSum f M₂)) θ‖ ≤ 3 * B / θ ^ 2 := by
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB 0)
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hterm : ∀ m ∈ dyadicNat M₂, (m : ℝ) * ‖𝓕 (complexify f) (m * θ)‖ ≤ B / (M₂ * θ ^ 2) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast one_le_of_mem_dyadicNat hm
    have hmM : M₂ ≤ m := (mem_dyadicNat.mp hm).1.le
    have h := hB (m * θ)
    rw [le_div_iff₀ (by positivity)]
    have hn0 := norm_nonneg (𝓕 (complexify f) (m * θ))
    calc (m : ℝ) * ‖𝓕 (complexify f) (m * θ)‖ * (M₂ * θ ^ 2)
        ≤ (m : ℝ) * ‖𝓕 (complexify f) (m * θ)‖ * (m * θ ^ 2) := by gcongr
      _ = (m * θ) ^ 2 * ‖𝓕 (complexify f) (m * θ)‖ := by ring
      _ ≤ B := h
  calc ‖𝓕 (complexify (dilationSum f M₂)) θ‖
      ≤ ∑ m ∈ dyadicNat M₂, (m : ℝ) * ‖𝓕 (complexify f) (m * θ)‖ :=
        norm_fourier_dilationSum_le hf hfc M₂ θ
    _ ≤ ∑ _m ∈ dyadicNat M₂, B / (M₂ * θ ^ 2) := Finset.sum_le_sum hterm
    _ = (dyadicNat M₂).card * (B / (M₂ * θ ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * M₂ * (B / (M₂ * θ ^ 2)) := by
        gcongr
        exact card_dyadicNat_le_three_mul hM₂
    _ = 3 * B / θ ^ 2 := by
        have : M₂ ≠ 0 := by linarith
        field_simp

/-- **Low frequencies.** `|ξ| ≤ M₁/2` ⇒ `|Ĝ(ξ)|² ≤ 36 K⁴ (6M₂² ∫ f)² f_{M₁/K}(ξ)`. -/
theorem normSq_fourier_fejerMajorant_le_low (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) {M₁ M₂ : ℝ} (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂) {K : ℕ}
    (hK : 1 ≤ K) {ξ : ℝ} (hξ : |ξ| ≤ M₁ / 2) :
    ‖𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ‖ ^ 2 ≤
      36 * (K : ℝ) ^ 4 * (6 * M₂ ^ 2 * ∫ x, f x) ^ 2 * lorentzF (M₁ / K) ξ := by
  set Ψ₀ := 6 * M₂ ^ 2 * ∫ x, f x
  set w := lorentzF (M₁ / K) ξ
  have hF0 : 0 ≤ ∫ x, f x := integral_nonneg hf0
  have hΨ0 : 0 ≤ Ψ₀ := by positivity
  have hw0 : 0 ≤ w := lorentzF_nonneg _ _
  have hw1 : w ≤ 1 := lorentzF_le_one (div_pos (by linarith) (by exact_mod_cast hK)) _
  have hbound : ‖𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ‖ ≤ 6 * (K : ℝ) ^ 2 * w * Ψ₀ := by
    refine (norm_fourier_fejerMajorant_le_weight hf hfc M₁ M₂ K ξ).trans ?_
    calc ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ *
          (fejerWeight K (ξ / n) * ‖𝓕 (complexify (dilationSum f M₂)) (ξ / n)‖)
        ≤ ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ * (2 * (K : ℝ) ^ 2 * w * Ψ₀) := by
          refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul (fejerWeight_div_le_low K hn hK hξ)
            (norm_fourier_dilationSum_le_mass hf hfc hf0 hM₂ _) (norm_nonneg _) (by positivity)
      _ = (∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹) * (2 * (K : ℝ) ^ 2 * w * Ψ₀) := by
          rw [Finset.sum_mul]
      _ ≤ 3 * (2 * (K : ℝ) ^ 2 * w * Ψ₀) := by
          gcongr
          exact sum_dyadicNat_inv_le hM₁
      _ = 6 * (K : ℝ) ^ 2 * w * Ψ₀ := by ring
  calc ‖𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ‖ ^ 2 ≤ (6 * (K : ℝ) ^ 2 * w * Ψ₀) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = 36 * (K : ℝ) ^ 4 * Ψ₀ ^ 2 * (w * w) := by ring
    _ ≤ 36 * (K : ℝ) ^ 4 * Ψ₀ ^ 2 * (w * 1) := by gcongr
    _ = 36 * (K : ℝ) ^ 4 * Ψ₀ ^ 2 * w := by ring

/-- **Middle frequencies.** `M₁/2 < |ξ| ≤ Ξ` ⇒ `|Ĝ(ξ)|² ≤ (D/M₁) Σ_n n⁻¹ |χh(ξ/n)|²`. -/
theorem normSq_fourier_fejerMajorant_le_high (hf : Continuous f) (hfc : HasCompactSupport f)
    {M₁ M₂ Ξ ε : ℝ} (hM₁ : 1 / 2 ≤ M₁) (hε : 0 < ε) {K : ℕ} (hK : 1 ≤ K) {ξ : ℝ}
    (hξ1 : M₁ / 2 < |ξ|) (hξ2 : |ξ| ≤ Ξ) :
    ‖𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ‖ ^ 2 ≤
      fejerCount ε Ξ M₁ K / M₁ *
        ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ * ‖𝓕 (complexify (translateSum f M₂ K)) (ξ / n)‖ ^ 2 := by
  have hM0 : 0 < M₁ := by linarith
  set χh := 𝓕 (complexify (translateSum f M₂ K))
  have hinv : ∀ n ∈ dyadicNat M₁, 0 ≤ (n : ℝ)⁻¹ := fun n _ => by positivity
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (dyadicNat M₁)
    (r := fun n : ℕ => (n : ℝ)⁻¹ * (‖finitePhaseProgression K (ξ / n)‖ * ‖χh (ξ / n)‖))
    (f := fun n : ℕ => (n : ℝ)⁻¹ * fejerWeight K (ξ / n))
    (g := fun n : ℕ => (n : ℝ)⁻¹ * ‖χh (ξ / n)‖ ^ 2)
    (fun n hn => mul_nonneg (hinv n hn) (fejerWeight_nonneg _ _))
    (fun n hn => mul_nonneg (hinv n hn) (sq_nonneg _))
    (fun n _ => le_of_eq (by simp only [fejerWeight]; ring))
  have hP : ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ * fejerWeight K (ξ / n) ≤ fejerCount ε Ξ M₁ K / M₁ := by
    calc ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ * fejerWeight K (ξ / n)
        ≤ ∑ n ∈ dyadicNat M₁, M₁⁻¹ * fejerWeight K (ξ / n) :=
          Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right
            (inv_anti₀ hM0 (mem_dyadicNat.mp hn).1.le) (fejerWeight_nonneg _ _)
      _ = M₁⁻¹ * ∑ n ∈ dyadicNat M₁, fejerWeight K (ξ / n) := by rw [Finset.mul_sum]
      _ ≤ M₁⁻¹ * fejerCount ε Ξ M₁ K := by
          gcongr
          exact sum_fejerWeight_div_le hK hM₁ hε hξ1 hξ2
      _ = fejerCount ε Ξ M₁ K / M₁ := by rw [inv_mul_eq_div]
  have hg0 : 0 ≤ ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ * ‖χh (ξ / n)‖ ^ 2 :=
    Finset.sum_nonneg fun n hn => mul_nonneg (hinv n hn) (sq_nonneg _)
  calc ‖𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ‖ ^ 2
      ≤ (∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ *
          (‖finitePhaseProgression K (ξ / n)‖ * ‖χh (ξ / n)‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_fourier_fejerMajorant_le hf hfc M₁ M₂ K ξ) 2
    _ ≤ (∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ * fejerWeight K (ξ / n)) *
          ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ * ‖χh (ξ / n)‖ ^ 2 := hCS
    _ ≤ _ := mul_le_mul_of_nonneg_right hP hg0

/-- **High frequencies.** `Ξ ≤ |ξ|` ⇒ `|Ĝ(ξ)|² ≤ 648 K⁴ B² M₁⁴ Ξ⁻⁴ f_Ξ(ξ)`. -/
theorem normSq_fourier_fejerMajorant_le_far (hf : Continuous f) (hfc : HasCompactSupport f)
    {B : ℝ} (hB : ∀ η : ℝ, η ^ 2 * ‖𝓕 (complexify f) η‖ ≤ B) {M₁ M₂ Ξ : ℝ} (hM₁ : 1 / 2 ≤ M₁)
    (hM₂ : 1 / 2 ≤ M₂) (hΞ : 0 < Ξ) (K : ℕ) {ξ : ℝ} (hξ : Ξ ≤ |ξ|) :
    ‖𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ‖ ^ 2 ≤
      648 * (K : ℝ) ^ 4 * B ^ 2 * M₁ ^ 4 * Ξ⁻¹ ^ 4 * lorentzF Ξ ξ := by
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB 0)
  have hξ0 : ξ ≠ 0 := fun h => by rw [h, abs_zero] at hξ; linarith
  have hξ2 : 0 < ξ ^ 2 := by positivity
  have hbound : ‖𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ‖ ≤
      18 * (K : ℝ) ^ 2 * B * M₁ ^ 2 / ξ ^ 2 := by
    refine (norm_fourier_fejerMajorant_le_weight hf hfc M₁ M₂ K ξ).trans ?_
    calc ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ *
          (fejerWeight K (ξ / n) * ‖𝓕 (complexify (dilationSum f M₂)) (ξ / n)‖)
        ≤ ∑ n ∈ dyadicNat M₁, (n : ℝ) * (3 * (K : ℝ) ^ 2 * B / ξ ^ 2) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn0 : (0 : ℝ) < n := by exact_mod_cast one_le_of_mem_dyadicNat hn
          have hdec := norm_fourier_dilationSum_le_decay hf hfc hB hM₂
            (div_ne_zero hξ0 hn0.ne')
          have hP := fejerWeight_le K (ξ / n)
          calc (n : ℝ)⁻¹ * (fejerWeight K (ξ / n) * ‖𝓕 (complexify (dilationSum f M₂)) (ξ / n)‖)
              ≤ (n : ℝ)⁻¹ * ((K : ℝ) ^ 2 * (3 * B / (ξ / n) ^ 2)) := by
                gcongr
              _ = (n : ℝ) * (3 * (K : ℝ) ^ 2 * B / ξ ^ 2) := by
                field_simp
      _ = (∑ n ∈ dyadicNat M₁, (n : ℝ)) * (3 * (K : ℝ) ^ 2 * B / ξ ^ 2) := by
          rw [Finset.sum_mul]
      _ ≤ 6 * M₁ ^ 2 * (3 * (K : ℝ) ^ 2 * B / ξ ^ 2) := by
          gcongr
          exact sum_dyadicNat_le hM₁
      _ = 18 * (K : ℝ) ^ 2 * B * M₁ ^ 2 / ξ ^ 2 := by ring
  have hlor : (ξ ^ 2) ^ 2 * (2 * Ξ⁻¹ ^ 4 * lorentzF Ξ ξ) ≥ 1 := by
    have hΞ2 : Ξ ^ 2 ≤ ξ ^ 2 := by
      have := pow_le_pow_left₀ hΞ.le hξ 2
      rwa [sq_abs] at this
    unfold lorentzF
    rw [ge_iff_le, inv_pow, ← div_eq_mul_inv, mul_div_assoc', mul_div_assoc',
      le_div_iff₀ (by positivity)]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hΞ2 (sq_nonneg Ξ)]
  have hfac : 0 ≤ 324 * (K : ℝ) ^ 4 * B ^ 2 * M₁ ^ 4 := by positivity
  calc ‖𝓕 (complexify (fejerMajorant f M₁ M₂ K)) ξ‖ ^ 2
      ≤ (18 * (K : ℝ) ^ 2 * B * M₁ ^ 2 / ξ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = 324 * (K : ℝ) ^ 4 * B ^ 2 * M₁ ^ 4 * (1 / (ξ ^ 2) ^ 2) := by
        field_simp
        ring
    _ ≤ 324 * (K : ℝ) ^ 4 * B ^ 2 * M₁ ^ 4 * (2 * Ξ⁻¹ ^ 4 * lorentzF Ξ ξ) := by
        gcongr
        rw [div_le_iff₀ (by positivity)]
        linarith
    _ = 648 * (K : ℝ) ^ 4 * B ^ 2 * M₁ ^ 4 * Ξ⁻¹ ^ 4 * lorentzF Ξ ξ := by ring

/-- `∫ |χh(ξ/n)|² dξ = n ∫ χ²`. -/
theorem integral_normSq_fourier_translateSum_div (hf : Continuous f) (hfc : HasCompactSupport f)
    (M₂ : ℝ) (K : ℕ) {n : ℝ} (hn : 0 < n) :
    ∫ ξ, ‖𝓕 (complexify (translateSum f M₂ K)) (ξ / n)‖ ^ 2 =
      n * ∫ x, translateSum f M₂ K x ^ 2 := by
  have h := Measure.integral_comp_div (fun θ => ‖𝓕 (complexify (translateSum f M₂ K)) θ‖ ^ 2) n
  rw [h, smul_eq_mul, abs_of_pos hn,
    GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq
      (integrable_complexify (memLp_translateSum hf hfc M₂ K 1))
      (memLp_complexify (memLp_translateSum hf hfc M₂ K 2))]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [complexify, sq_abs]

/-- **The spectral bound.** `∫ G² ≤ 36π K³ M₁ Ψ₀² + 3D (∫ χ²) + 648π K⁴ B² M₁⁴ Ξ⁻³`. -/
theorem integral_fejerMajorant_sq_le (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hB : ∀ η : ℝ, η ^ 2 * ‖𝓕 (complexify f) η‖ ≤ B)
    {M₁ M₂ Ξ ε : ℝ} (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂) (hΞ : 0 < Ξ) (hε : 0 < ε) {K : ℕ}
    (hK : 1 ≤ K) :
    ∫ u, fejerMajorant f M₁ M₂ K u ^ 2 ≤
      36 * π * (K : ℝ) ^ 3 * M₁ * (6 * M₂ ^ 2 * ∫ x, f x) ^ 2 +
        3 * fejerCount ε Ξ M₁ K * (∫ x, translateSum f M₂ K x ^ 2) +
        648 * π * (K : ℝ) ^ 4 * B ^ 2 * M₁ ^ 4 * Ξ⁻¹ ^ 3 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hM0 : 0 < M₁ := by linarith
  set GC := complexify (fejerMajorant f M₁ M₂ K)
  set χh := 𝓕 (complexify (translateSum f M₂ K))
  set D := fejerCount ε Ξ M₁ K
  have hD0 : 0 ≤ D := fejerCount_nonneg hε hΞ.le hM0.le K
  set Ψ₀ := 6 * M₂ ^ 2 * ∫ x, f x
  set U₁ : ℝ → ℝ := fun ξ => 36 * (K : ℝ) ^ 4 * Ψ₀ ^ 2 * lorentzF (M₁ / K) ξ
  set U₂ : ℝ → ℝ := fun ξ => D / M₁ * ∑ n ∈ dyadicNat M₁, (n : ℝ)⁻¹ * ‖χh (ξ / n)‖ ^ 2
  set U₃ : ℝ → ℝ := fun ξ => 648 * (K : ℝ) ^ 4 * B ^ 2 * M₁ ^ 4 * Ξ⁻¹ ^ 4 * lorentzF Ξ ξ
  have hU₁0 : ∀ ξ, 0 ≤ U₁ ξ := fun ξ => mul_nonneg (by positivity) (lorentzF_nonneg _ _)
  have hU₂0 : ∀ ξ, 0 ≤ U₂ ξ := fun ξ => mul_nonneg (div_nonneg hD0 hM0.le)
    (Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (sq_nonneg _))
  have hU₃0 : ∀ ξ, 0 ≤ U₃ ξ := fun ξ => mul_nonneg (by positivity) (lorentzF_nonneg _ _)
  -- the pointwise bound in the three regions
  have hpt : ∀ ξ, ‖𝓕 GC ξ‖ ^ 2 ≤ U₁ ξ + U₂ ξ + U₃ ξ := fun ξ => by
    rcases le_or_gt |ξ| (M₁ / 2) with h1 | h1
    · have := normSq_fourier_fejerMajorant_le_low hf hfc hf0 hM₁ hM₂ hK h1
      linarith [hU₂0 ξ, hU₃0 ξ]
    · rcases le_or_gt |ξ| Ξ with h2 | h2
      · have := normSq_fourier_fejerMajorant_le_high hf hfc (M₂ := M₂) hM₁ hε hK h1 h2
        linarith [hU₁0 ξ, hU₃0 ξ]
      · have := normSq_fourier_fejerMajorant_le_far hf hfc hB hM₁ hM₂ hΞ K h2.le
        linarith [hU₁0 ξ, hU₂0 ξ]
  -- integrability
  have hGint : Integrable GC := integrable_complexify (memLp_fejerMajorant hf hfc M₁ M₂ K 1)
  have hGL2 : MemLp GC 2 := memLp_complexify (memLp_fejerMajorant hf hfc M₁ M₂ K 2)
  have hχint : Integrable (fun θ => ‖χh θ‖ ^ 2) :=
    GaloisForLFunctions.RHTower.integrable_norm_sq_fourier
      (integrable_complexify (memLp_translateSum hf hfc M₂ K 1))
      (memLp_complexify (memLp_translateSum hf hfc M₂ K 2))
  have hU₁i : Integrable U₁ := (integrable_lorentzF (div_pos hM0 hK0)).const_mul _
  have hU₂i : Integrable U₂ := by
    refine Integrable.const_mul (integrable_finsetSum _ fun n hn => ?_) _
    have hn0 : (n : ℝ) ≠ 0 := by
      have := one_le_of_mem_dyadicNat hn
      exact Nat.cast_ne_zero.mpr (by omega)
    exact (hχint.comp_div hn0).const_mul _
  have hU₃i : Integrable U₃ := (integrable_lorentzF hΞ).const_mul _
  -- the three integrals
  have hI₁ : ∫ ξ, U₁ ξ = 36 * π * (K : ℝ) ^ 3 * M₁ * Ψ₀ ^ 2 := by
    simp only [U₁]
    rw [integral_const_mul, integral_lorentzF_univ (div_pos hM0 hK0)]
    field_simp
  have hI₂ : ∫ ξ, U₂ ξ ≤ 3 * D * ∫ x, translateSum f M₂ K x ^ 2 := by
    have hχ0 : 0 ≤ ∫ x, translateSum f M₂ K x ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have heq : ∫ ξ, U₂ ξ = D / M₁ * ((dyadicNat M₁).card * ∫ x, translateSum f M₂ K x ^ 2) := by
      simp only [U₂]
      rw [integral_const_mul, integral_finsetSum]
      · congr 1
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast one_le_of_mem_dyadicNat hn
        rw [integral_const_mul, integral_normSq_fourier_translateSum_div hf hfc M₂ K hn0,
          ← mul_assoc, inv_mul_cancel₀ hn0.ne', one_mul]
      · intro n hn
        have hn0 : (n : ℝ) ≠ 0 := by
          have := one_le_of_mem_dyadicNat hn
          exact Nat.cast_ne_zero.mpr (by omega)
        exact (hχint.comp_div hn0).const_mul _
    rw [heq]
    have hcard := card_dyadicNat_le_three_mul hM₁
    calc D / M₁ * ((dyadicNat M₁).card * ∫ x, translateSum f M₂ K x ^ 2)
        ≤ D / M₁ * (3 * M₁ * ∫ x, translateSum f M₂ K x ^ 2) := by gcongr
      _ = 3 * D * ∫ x, translateSum f M₂ K x ^ 2 := by field_simp
  have hI₃ : ∫ ξ, U₃ ξ = 648 * π * (K : ℝ) ^ 4 * B ^ 2 * M₁ ^ 4 * Ξ⁻¹ ^ 3 := by
    simp only [U₃]
    rw [integral_const_mul, integral_lorentzF_univ hΞ]
    field_simp
  -- assemble
  have hplan : ∫ u, fejerMajorant f M₁ M₂ K u ^ 2 = ∫ ξ, ‖𝓕 GC ξ‖ ^ 2 := by
    rw [GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq hGint hGL2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [GC, complexify, sq_abs]
  rw [hplan]
  calc ∫ ξ, ‖𝓕 GC ξ‖ ^ 2 ≤ ∫ ξ, (U₁ ξ + U₂ ξ + U₃ ξ) :=
        integral_mono (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hGint hGL2)
          ((hU₁i.add hU₂i).add hU₃i) hpt
    _ = (∫ ξ, U₁ ξ) + (∫ ξ, U₂ ξ) + ∫ ξ, U₃ ξ :=
        (integral_add (f := fun ξ => U₁ ξ + U₂ ξ) (hU₁i.add hU₂i) hU₃i).trans
          (congrArg (· + ∫ ξ, U₃ ξ) (integral_add hU₁i hU₂i))
    _ ≤ _ := add_le_add (add_le_add (le_of_eq hI₁) hI₂) (le_of_eq hI₃)

end

end RHTower.GuthMaynard

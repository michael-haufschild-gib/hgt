import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropElevenOne
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropTenOneUnconditional
import GaloisForLFunctions.RHTower.ReciprocalCoareaOptimality

set_option autoImplicit false

/-!
# Guth–Maynard Proposition 11.2: the `S₃` bound

For a real CGL bump `w`, `T^{3/4} ≤ N ≤ T`, `|b_n| ≤ 1` and a `1`-separated `W ⊆ [0, T]` with
`|D(t)| ≥ N^σ` on `W` (Guth–Maynard, arXiv 2405.20552, Proposition 11.2), unconditionally:

`S₃ ⪅ T² |W|^{3/2} + T |W| N^{3−2σ} + T |W|² N^{3/2−σ} + T^{9/8} |W|^{29/16} N^{3/2−σ}`

(up to the `O(T^{−100})` of Proposition 10.1). Proof: Proposition 10.1 (`prop101`),
`S₃ ⪅ T²|W|^{3/2} + T N |W|^{1/2} E(W)^{1/2}`, with Proposition 11.1 substituted for `E(W)` and
`√(a + b + c) ≤ √a + √b + √c`. With `x = |W|^{1/16}`, `τ = T^{1/8}`, `ν = N^{1/2−σ}` all the
powers are monomials.
-/

open Finset Set

namespace RHTower.GuthMaynard

noncomputable section

/-- **The substitution step.** For `X, T ≥ 0`, `N > 0`:
`T N √X · √(X N^{4−4σ} + X^{21/8} T^{1/4} N^{1−2σ} + X³ N^{1−2σ}) ≤
  T X N^{3−2σ} + T X² N^{3/2−σ} + T^{9/8} X^{29/16} N^{3/2−σ}`. -/
theorem substitution_le {X T N σ : ℝ} (hX : 0 ≤ X) (hT : 0 ≤ T) (hN : 0 < N) :
    T * N * Real.sqrt X * Real.sqrt (X * N ^ (4 - 4 * σ) +
        X ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ) + X ^ 3 * N ^ (1 - 2 * σ)) ≤
      T * X * N ^ (3 - 2 * σ) + T * X ^ 2 * N ^ (3 / 2 - σ) +
        T ^ (9 / 8 : ℝ) * X ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ) := by
  have pw : ∀ {Y : ℝ}, 0 ≤ Y → ∀ (a : ℝ) (k : ℕ), (Y ^ a) ^ k = Y ^ (a * k) :=
    fun hY a k => (Real.rpow_mul_natCast hY a k).symm
  -- monomials in `x = X^{1/16}`, `τ = T^{1/8}`, `ν = N^{1/2−σ}`
  have eX : X = (X ^ (1 / 16 : ℝ)) ^ 16 := by rw [pw hX]; norm_num
  have eX218 : X ^ (21 / 8 : ℝ) = (X ^ (1 / 16 : ℝ)) ^ 42 := by rw [pw hX]; norm_num
  have eX2916 : X ^ (29 / 16 : ℝ) = (X ^ (1 / 16 : ℝ)) ^ 29 := by rw [pw hX]; norm_num
  have eXs : Real.sqrt X = (X ^ (1 / 16 : ℝ)) ^ 8 := by rw [Real.sqrt_eq_rpow, pw hX]; norm_num
  have eT : T = (T ^ (1 / 8 : ℝ)) ^ 8 := by rw [pw hT]; norm_num
  have eT14 : T ^ (1 / 4 : ℝ) = (T ^ (1 / 8 : ℝ)) ^ 2 := by rw [pw hT]; norm_num
  have eT98 : T ^ (9 / 8 : ℝ) = (T ^ (1 / 8 : ℝ)) ^ 9 := by rw [pw hT]; norm_num
  have eN1 : N ^ (1 - 2 * σ) = (N ^ (1 / 2 - σ)) ^ 2 := by
    rw [pw hN.le]; congr 1; push_cast; ring
  have eN4 : N ^ (4 - 4 * σ) = N ^ 2 * (N ^ (1 / 2 - σ)) ^ 4 := by
    rw [pw hN.le, ← Real.rpow_natCast N 2, ← Real.rpow_add hN]; congr 1; push_cast; ring
  have eN3 : N ^ (3 - 2 * σ) = N ^ 2 * (N ^ (1 / 2 - σ)) ^ 2 := by
    rw [pw hN.le, ← Real.rpow_natCast N 2, ← Real.rpow_add hN]; congr 1; push_cast; ring
  have eN32 : N ^ (3 / 2 - σ) = N * N ^ (1 / 2 - σ) := by
    conv_rhs => rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN]; congr 1; ring
  set x := X ^ (1 / 16 : ℝ)
  set τ := T ^ (1 / 8 : ℝ)
  set ν := N ^ (1 / 2 - σ)
  have hx : 0 ≤ x := by positivity
  have hτ : 0 ≤ τ := by positivity
  have hν : 0 ≤ ν := by positivity
  have hinner : X * N ^ (4 - 4 * σ) + X ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ) +
      X ^ 3 * N ^ (1 - 2 * σ) = (x ^ 8 * N * ν ^ 2) ^ 2 + (x ^ 21 * τ * ν) ^ 2 + (x ^ 24 * ν) ^ 2 := by
    rw [eN4, eX218, eT14, eN1, show X ^ 3 = x ^ 48 by rw [eX]; ring, eX]; ring
  rw [hinner]
  -- `√(a + b + c) ≤ √a + √b + √c` (corpus `sqrt_add_le_sqrt_add_sqrt`, twice)
  have hs : Real.sqrt ((x ^ 8 * N * ν ^ 2) ^ 2 + (x ^ 21 * τ * ν) ^ 2 + (x ^ 24 * ν) ^ 2) ≤
      Real.sqrt ((x ^ 8 * N * ν ^ 2) ^ 2) + Real.sqrt ((x ^ 21 * τ * ν) ^ 2) +
        Real.sqrt ((x ^ 24 * ν) ^ 2) :=
    (sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)).trans
      (add_le_add_right (sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)) _)
  rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity),
    Real.sqrt_sq (by positivity)] at hs
  have hpre : 0 ≤ T * N * Real.sqrt X := by positivity
  calc T * N * Real.sqrt X * Real.sqrt ((x ^ 8 * N * ν ^ 2) ^ 2 + (x ^ 21 * τ * ν) ^ 2 +
        (x ^ 24 * ν) ^ 2)
      ≤ T * N * Real.sqrt X * (x ^ 8 * N * ν ^ 2 + x ^ 21 * τ * ν + x ^ 24 * ν) :=
        mul_le_mul_of_nonneg_left hs hpre
    _ = _ := by
        rw [eXs, eN3, eN32, eT98, eX2916, show X ^ 2 = x ^ 32 by rw [eX]; ring, eT, eX]; ring

/-- **Guth–Maynard Proposition 11.2** (`S₃` bound), unconditionally: for a real CGL bump `w` and
every `ε > 0` there is `C ≥ 0` such that for `T ≥ 2`, `T^{3/4} ≤ N ≤ T`, `|b_n| ≤ 1` and every
`1`-separated `W ⊆ [0, T]` with `|D(t)| ≥ N^σ` on `W`:
`‖S₃‖ ≤ C T^ε (T² |W|^{3/2} + T |W| N^{3−2σ} + T |W|² N^{3/2−σ} + T^{9/8} |W|^{29/16} N^{3/2−σ})
  + C T^{−100}`, with `S₃ = allNonzeroCubicSum w W N`. -/
theorem guthMaynard_prop112 (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (b : ℕ → ℂ) (σ : ℝ) (W : Finset ℝ) (T : ℝ),
      2 ≤ T → T ^ (3 / 4 : ℝ) ≤ N → (N : ℝ) ≤ T → (∀ n, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t ∈ Icc 0 T) → IsSeparated 1 W →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖dyadicDirichletPoly N b t‖) →
      ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖ ≤
        C * T ^ ε * (T ^ 2 * W.card * Real.sqrt W.card + T * W.card * (N : ℝ) ^ (3 - 2 * σ) +
          T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 - σ) +
          T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ)) +
        C * T ^ (-100 : ℝ) := by
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ, ε₁ = min ε 1 / 10 := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; have := lt_min hε one_pos; positivity
  have hε₁1 : ε₁ ≤ 3 / 4 := by rw [hε₁]; have := min_le_right ε 1; linarith
  have hε₁ε : 5 * ε₁ ≤ ε / 2 := by rw [hε₁]; have := min_le_left ε 1; linarith
  obtain ⟨C₁, hC₁, h101⟩ := prop101 w hε₁0
  obtain ⟨C₂, hC₂, h111⟩ := guthMaynard_prop111 hε
  refine ⟨C₁ * (1 + Real.sqrt C₂), by positivity,
    fun N b σ W T hT hNT hNle hb hW hsep hD => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hN1r : (1 : ℝ) ≤ N := (Real.one_le_rpow hT1 (by norm_num)).trans hNT
  have hN0 : (0 : ℝ) < N := by linarith
  have hTε₁N : T ^ ε₁ ≤ N :=
    (Real.rpow_le_rpow_of_exponent_le hT1 hε₁1).trans hNT
  have hW' : ∀ t ∈ W, (0 : ℝ) ≤ t ∧ t ≤ 0 + T := fun t ht => by
    have := hW t ht; rw [zero_add]; exact this
  have h1 := h101 T N W hT hN1r hNle hTε₁N hW hsep
  have h2 := h111 N b σ W T 0 hT hNT hNle hb hW' hsep hD
  set X : ℝ := (W.card : ℝ)
  set E : ℝ := (additiveEnergy W : ℝ)
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  set Q := X * (N : ℝ) ^ (4 - 4 * σ) + X ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 - 2 * σ) +
    X ^ 3 * (N : ℝ) ^ (1 - 2 * σ)
  have hQ0 : 0 ≤ Q := by positivity
  set R₃ := T * X * (N : ℝ) ^ (3 - 2 * σ) + T * X ^ 2 * (N : ℝ) ^ (3 / 2 - σ) +
    T ^ (9 / 8 : ℝ) * X ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ)
  have hR₃0 : 0 ≤ R₃ := by positivity
  -- `√E ≤ √C₂ T^{ε/2} √Q`
  have hsE : Real.sqrt E ≤ Real.sqrt C₂ * T ^ (ε / 2) * Real.sqrt Q := by
    have hTh : Real.sqrt (T ^ ε) = T ^ (ε / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]; ring_nf
    calc Real.sqrt E ≤ Real.sqrt (C₂ * T ^ ε * Q) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt C₂ * T ^ (ε / 2) * Real.sqrt Q := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC₂, hTh]
  have hsub := substitution_le (σ := σ) hX0 hT0.le hN0
  have hTN : T * N * Real.sqrt X * Real.sqrt E ≤ Real.sqrt C₂ * T ^ (ε / 2) * R₃ := by
    calc T * N * Real.sqrt X * Real.sqrt E ≤
          T * N * Real.sqrt X * (Real.sqrt C₂ * T ^ (ε / 2) * Real.sqrt Q) :=
          mul_le_mul_of_nonneg_left hsE (by positivity)
      _ = Real.sqrt C₂ * T ^ (ε / 2) * (T * N * Real.sqrt X * Real.sqrt Q) := by ring
      _ ≤ Real.sqrt C₂ * T ^ (ε / 2) * R₃ := mul_le_mul_of_nonneg_left hsub (by positivity)
  have hT5 : T ^ (5 * ε₁) ≤ T ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_le hT1 hε₁ε
  have hTε2 : T ^ (ε / 2) * T ^ (ε / 2) = T ^ ε := by rw [← Real.rpow_add hT0]; ring_nf
  have hTε21 : 1 ≤ T ^ (ε / 2) := Real.one_le_rpow hT1 (by positivity)
  have hA0 : 0 ≤ T ^ 2 * X * Real.sqrt X := by positivity
  have hmain : C₁ * T ^ (5 * ε₁) * (T ^ 2 * X * Real.sqrt X + T * N * Real.sqrt X * Real.sqrt E) ≤
      C₁ * (1 + Real.sqrt C₂) * T ^ ε * (T ^ 2 * X * Real.sqrt X + R₃) := by
    have hB : T ^ 2 * X * Real.sqrt X + T * N * Real.sqrt X * Real.sqrt E ≤
        T ^ (ε / 2) * (T ^ 2 * X * Real.sqrt X) + Real.sqrt C₂ * T ^ (ε / 2) * R₃ := by
      have := le_mul_of_one_le_left hA0 hTε21
      linarith
    have hB0 : 0 ≤ T ^ 2 * X * Real.sqrt X + T * N * Real.sqrt X * Real.sqrt E := by positivity
    calc C₁ * T ^ (5 * ε₁) * (T ^ 2 * X * Real.sqrt X + T * N * Real.sqrt X * Real.sqrt E)
        ≤ C₁ * T ^ (ε / 2) * (T ^ (ε / 2) * (T ^ 2 * X * Real.sqrt X) +
            Real.sqrt C₂ * T ^ (ε / 2) * R₃) := by
          gcongr
      _ = C₁ * (T ^ (ε / 2) * T ^ (ε / 2)) * (T ^ 2 * X * Real.sqrt X + Real.sqrt C₂ * R₃) := by
          ring
      _ ≤ C₁ * (1 + Real.sqrt C₂) * T ^ ε * (T ^ 2 * X * Real.sqrt X + R₃) := by
          rw [hTε2]
          have hs0 : 0 ≤ Real.sqrt C₂ := Real.sqrt_nonneg _
          have hTε0 : 0 ≤ T ^ ε := by positivity
          have : T ^ 2 * X * Real.sqrt X + Real.sqrt C₂ * R₃ ≤
              (1 + Real.sqrt C₂) * (T ^ 2 * X * Real.sqrt X + R₃) := by nlinarith
          calc C₁ * T ^ ε * (T ^ 2 * X * Real.sqrt X + Real.sqrt C₂ * R₃)
              ≤ C₁ * T ^ ε * ((1 + Real.sqrt C₂) * (T ^ 2 * X * Real.sqrt X + R₃)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
  have herr : C₁ * T ^ (-100 : ℝ) ≤ C₁ * (1 + Real.sqrt C₂) * T ^ (-100 : ℝ) :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC₁ (by
      have := Real.sqrt_nonneg C₂; linarith)) (by positivity)
  calc ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖
      ≤ C₁ * T ^ (5 * ε₁) * (T ^ 2 * X * Real.sqrt X + T * N * Real.sqrt X * Real.sqrt E) +
          C₁ * T ^ (-100 : ℝ) := h1
    _ ≤ C₁ * (1 + Real.sqrt C₂) * T ^ ε * (T ^ 2 * X * Real.sqrt X + R₃) +
          C₁ * (1 + Real.sqrt C₂) * T ^ (-100 : ℝ) := add_le_add hmain herr
    _ = _ := by simp only [R₃]; ring

end

end RHTower.GuthMaynard

import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveDispersionOfTheCrossScaleRemainder
import GaloisForLFunctions.BezoutValuationIncidence.CanonicalPrimitiveSpectralFormAndJordanWindowEnergy

/-!
# Large-sieve dispersion in Selberg coordinates

The fluctuation of every row is the canonical primitive,

`F_c(M) = W_{N,c}(M) = Σ_{ζ ≠ 1} Y_c(ord ζ) ζ/(ζ - 1) ζ^M`,

an exponential sum over the roots of unity of order at most the support of `c`, each frequency
appearing exactly once with the Selberg coordinate of its order. The large-sieve argument of
`LargeSieveDispersionOfTheCrossScaleRemainder` uses nothing else: for any fluctuation
`F_c(M) = Σ_{ζ ∈ T} κ(ζ) ζ^M` over a set `T` of nontrivial roots of order `≤ Q₀`,

`|B(c, c') + m(c) R(c') + β(c) H(c')| ≤ 4 √(Σ_T |κ|²/|ζ-1|²) √(L + 2Q₀² - 1) √(Σ_n c'(n)²/n⁴)
  + 8 (Σ_T |κ|/|ζ-1|²) Σ_n |c'(n)|/n³`.

With `κ(ζ) = Y_c(ord ζ) ζ/(ζ - 1)` and the Farey bounds `Σ_{ζ prim e} |ζ-1|^{-4} ≤ e⁴/64`,
`Σ_{ζ prim e} |ζ-1|^{-3} ≤ e³/16`, this is, for every row `c` supported on `[1, Q₀]`,

`|B(c, c') + m(c) R(c') + β(c) H(c')| ≤ ½ √(Σ_e Y_c(e)² e⁴) √(L + 2Q₀² - 1) √(Σ_n c'(n)²/n⁴)
  + ½ Σ_e |Y_c(e)| e³ · Σ_n |c'(n)|/n³`.

The cross-scale dispersion therefore holds for the receiver's own rows on all moduli, with the
Jordan-type weight `e⁴` on the Selberg coordinates of the small scale; on prime packets
`Y(p) = c(p)/p` it is the prime theorem.
-/

open Finset Complex Filter Topology RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The abstract large-sieve bound -/

/-- **Large-sieve dispersion for a spectral fluctuation.** If `F_c(M) = Σ_{ζ ∈ T} κ(ζ) ζ^M` with
`T` a set of nontrivial roots of order at most `Q₀`, and `c'` lives on `[A+1, A+L]`, then
`|B + m R' + β H'| ≤ 4 √(Σ_T |κ|²/|ζ-1|²) √(L+2Q₀²-1) √(Σ c'(n)²/n⁴) + 8 Σ_T |κ|/|ζ-1|² · Σ |c'(n)|/n³`. -/
theorem abs_rowBilinear_add_mean_add_beta_le_spectral {N Q₀ A L : ℕ} {c c' : ℕ → ℝ}
    {T : Finset ℂ} {κ : ℂ → ℂ} (hQ₀ : 2 ≤ Q₀) (hT : T ⊆ responseRoots Q₀)
    (hT1 : ∀ ζ ∈ T, ζ ≠ 1) (hspec : ∀ M, (rowFluct N c M : ℂ) = ∑ ζ ∈ T, κ ζ * ζ ^ M)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'| ≤
      4 * Real.sqrt (∑ ζ ∈ T, ‖κ ζ‖ ^ 2 / ‖ζ - 1‖ ^ 2) *
          Real.sqrt ((L : ℝ) + 2 * (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        8 * (∑ ζ ∈ T, ‖κ ζ‖ / ‖ζ - 1‖ ^ 2) * ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 3 := by
  classical
  set W := Icc (A + 1) (A + L) with hW
  have hWN : W ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  have hW1 : ∀ n ∈ W, 1 ≤ n := fun n hn => by simp only [hW, mem_Icc] at hn; omega
  set F := rowFluct N c
  have hroot : ∀ ζ ∈ T, ‖ζ‖ = 1 ∧ ζ ≠ 1 := fun ζ hζ =>
    ⟨norm_eq_one_of_mem_responseRoots (hT hζ), hT1 ζ hζ⟩
  have ha : ∀ ζ ∈ T, 0 < ‖ζ - 1‖ := fun ζ hζ => norm_pos_iff.mpr (sub_ne_zero.mpr (hT1 ζ hζ))
  set α : ℂ → ℂ := fun ζ => κ ζ / (1 - ζ)
  set G : ℕ → ℕ → ℂ → ℂ := fun H A ζ => ∑ M ∈ Ico A H, (pw M : ℂ) * ζ ^ M
  set mainG : ℕ → ℕ → ℂ → ℂ := fun H A ζ => if A < H then (pw A : ℂ) * ζ ^ A / (1 - ζ) else 0
  set errB : ℕ → ℕ → ℂ → ℝ := fun H A ζ =>
    if A < H then (pw (H - 1) + 2 * (pw A - pw (A + 1)) / ‖ζ - 1‖) / ‖ζ - 1‖ else 0
  have hGsplit : ∀ H A ζ, 1 ≤ A → ‖ζ‖ = 1 → ζ ≠ 1 → ‖G H A ζ - mainG H A ζ‖ ≤ errB H A ζ := by
    intro H A ζ hA hζ hζ1
    simp only [G, mainG, errB]
    split_ifs with hAH
    · exact norm_sum_Ico_pw_mul_pow_sub_le hζ hζ1 hA hAH
    · rw [Ico_eq_empty_of_le (not_lt.mp hAH), sum_empty, sub_zero, norm_zero]
  set step : ℕ → ℝ := fun H => ∑ n ∈ Icc 1 N, c' n *
    ∑ M ∈ range H, F M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ)
  have hstepW : ∀ H, ((step H : ℝ) : ℂ) = ∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H,
      ∑ ζ ∈ T, κ ζ * G H (j * n) ζ := by
    intro H
    simp only [step]
    rw [← sum_subset hWN fun n _ hn => by
      have : c' n = 0 := by by_contra h; exact hn (hsupp' n h)
      rw [this, zero_mul]]
    push_cast
    refine sum_congr rfl fun n hn => ?_
    congr 1
    have h := sum_range_mul_div_div_pronic_eq (H := H) (hW1 n hn) F
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) h
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_natCast] at hcast
    rw [hcast]
    refine sum_congr rfl fun j _ => ?_
    simp only [G]
    rw [sum_congr rfl fun M _ => by rw [hspec M, sum_mul], sum_comm]
    refine sum_congr rfl fun ζ _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun M _ => by ring
  set X : ℝ := (L : ℝ) + 2 * (Q₀ : ℝ) ^ 2 - 1
  set Y : ℝ := ∑ n ∈ W, c' n ^ 2 / (n : ℝ) ^ 4
  have hX : 0 ≤ X := by
    have : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
    simp only [X]; nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hY : 0 ≤ Y := sum_nonneg fun n _ => by positivity
  set K₂ : ℝ := ∑ ζ ∈ T, ‖κ ζ‖ ^ 2 / ‖ζ - 1‖ ^ 2
  set K₁ : ℝ := ∑ ζ ∈ T, ‖κ ζ‖ / ‖ζ - 1‖ ^ 2
  set E₂ : ℝ := ∑ n ∈ W, |c' n| / (n : ℝ) ^ 3
  set δ : ℕ → ℝ := fun H => (H : ℝ) * pw (H - 1) *
    ((∑ n ∈ W, |c' n|) * ∑ ζ ∈ T, ‖κ ζ‖ / ‖ζ - 1‖)
  have hαnorm : ∀ ζ ∈ T, ‖α ζ‖ ^ 2 = ‖κ ζ‖ ^ 2 / ‖ζ - 1‖ ^ 2 := fun ζ hζ => by
    simp only [α, norm_div, div_pow, norm_sub_rev 1 ζ]
  have hfin : ∀ H, ‖((step H : ℝ) : ℂ)‖ ≤
      4 * Real.sqrt K₂ * Real.sqrt X * Real.sqrt Y + 8 * K₁ * E₂ + δ H := by
    intro H
    rw [hstepW H]
    set y : ℕ → ℕ → ℂ := fun j n => if j * n < H then (c' n : ℂ) * (pw (j * n) : ℂ) else 0
    set Φ : ℕ → ℂ → ℂ := fun j ζ => ∑ n ∈ W, y j n * (ζ ^ j) ^ n
    have hsplit : ∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H, ∑ ζ ∈ T, κ ζ * G H (j * n) ζ =
        ∑ j ∈ Icc 1 H, ∑ ζ ∈ T, α ζ * Φ j ζ +
          ∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H, ∑ ζ ∈ T,
            κ ζ * (G H (j * n) ζ - mainG H (j * n) ζ) := by
      have hmain : ∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H, ∑ ζ ∈ T, κ ζ * mainG H (j * n) ζ =
          ∑ j ∈ Icc 1 H, ∑ ζ ∈ T, α ζ * Φ j ζ := by
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun ζ _ => ?_
        simp only [Φ, mul_sum]
        refine sum_congr rfl fun n _ => ?_
        simp only [mainG, y, α]
        split_ifs
        · rw [← pow_mul, mul_comm j n]; ring
        · simp
      rw [← hmain, ← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [← mul_add, ← sum_add_distrib]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [← sum_add_distrib]
      exact sum_congr rfl fun ζ _ => by ring
    rw [hsplit]
    have hM : ‖∑ j ∈ Icc 1 H, ∑ ζ ∈ T, α ζ * Φ j ζ‖ ≤
        4 * Real.sqrt K₂ * Real.sqrt X * Real.sqrt Y := by
      have hj : ∀ j ∈ Icc 1 H, ‖∑ ζ ∈ T, α ζ * Φ j ζ‖ ≤
          Real.sqrt K₂ * (Real.sqrt X * Real.sqrt Y) * (Real.sqrt j / (j : ℝ) ^ 2) := by
        intro j hj
        have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
        have hjR : (0 : ℝ) < j := by exact_mod_cast hj1
        have hcs : ‖∑ ζ ∈ T, α ζ * Φ j ζ‖ ≤
            Real.sqrt (∑ ζ ∈ T, ‖α ζ‖ ^ 2) * Real.sqrt (∑ ζ ∈ T, ‖Φ j ζ‖ ^ 2) := by
          refine (norm_sum_le _ _).trans ?_
          simp only [norm_mul]
          exact Real.sum_mul_le_sqrt_mul_sqrt T _ _
        rw [sum_congr rfl hαnorm] at hcs
        have hy : ∑ n ∈ W, ‖y j n‖ ^ 2 ≤ Y / (j : ℝ) ^ 4 := by
          rw [div_eq_mul_inv, sum_mul]
          refine sum_le_sum fun n hn => ?_
          have hn1 : 1 ≤ n := hW1 n hn
          have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
          simp only [y]
          split_ifs
          · rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, mul_pow, sq_abs, sq_abs]
            have hpw := pw_le_inv_sq (j * n)
            have hpw0 := pw_nonneg (j * n)
            have hsq : pw (j * n) ^ 2 ≤ (1 / ((j * n : ℕ) : ℝ) ^ 2) ^ 2 :=
              pow_le_pow_left₀ hpw0 hpw 2
            calc c' n ^ 2 * pw (j * n) ^ 2 ≤ c' n ^ 2 * (1 / ((j * n : ℕ) : ℝ) ^ 2) ^ 2 :=
                  mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
              _ = c' n ^ 2 / (n : ℝ) ^ 4 * ((j : ℝ) ^ 4)⁻¹ := by push_cast; field_simp
          · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
            positivity
        have hls := sum_norm_sq_dilated_le hQ₀ hT (by omega : 0 < j) A L (y j)
        have hΦ : ∑ ζ ∈ T, ‖Φ j ζ‖ ^ 2 ≤ (X * Y) * (Real.sqrt j / (j : ℝ) ^ 2) ^ 2 := by
          refine hls.trans ?_
          rw [div_pow, Real.sq_sqrt hjR.le]
          calc (j : ℝ) * (X * ∑ k ∈ Icc (A + 1) (A + L), ‖y j k‖ ^ 2)
              ≤ (j : ℝ) * (X * (Y / (j : ℝ) ^ 4)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy hX) hjR.le
            _ = X * Y * ((j : ℝ) / ((j : ℝ) ^ 2) ^ 2) := by field_simp
        have hroot' : Real.sqrt (∑ ζ ∈ T, ‖Φ j ζ‖ ^ 2) ≤
            Real.sqrt X * Real.sqrt Y * (Real.sqrt j / (j : ℝ) ^ 2) := by
          calc Real.sqrt (∑ ζ ∈ T, ‖Φ j ζ‖ ^ 2) ≤ Real.sqrt ((X * Y) *
                (Real.sqrt j / (j : ℝ) ^ 2) ^ 2) := Real.sqrt_le_sqrt hΦ
            _ = Real.sqrt X * Real.sqrt Y * (Real.sqrt j / (j : ℝ) ^ 2) := by
                rw [Real.sqrt_mul (mul_nonneg hX hY), Real.sqrt_mul hX,
                  Real.sqrt_sq (by positivity)]
        calc ‖∑ ζ ∈ T, α ζ * Φ j ζ‖ ≤ _ := hcs
          _ ≤ Real.sqrt K₂ * (Real.sqrt X * Real.sqrt Y * (Real.sqrt j / (j : ℝ) ^ 2)) :=
              mul_le_mul_of_nonneg_left hroot' (Real.sqrt_nonneg _)
          _ = _ := by ring
      calc ‖∑ j ∈ Icc 1 H, ∑ ζ ∈ T, α ζ * Φ j ζ‖
          ≤ ∑ j ∈ Icc 1 H, Real.sqrt K₂ * (Real.sqrt X * Real.sqrt Y) *
              (Real.sqrt j / (j : ℝ) ^ 2) := (norm_sum_le _ _).trans (sum_le_sum hj)
        _ = Real.sqrt K₂ * (Real.sqrt X * Real.sqrt Y) *
              ∑ j ∈ Icc 1 H, Real.sqrt j / (j : ℝ) ^ 2 := by rw [mul_sum]
        _ ≤ Real.sqrt K₂ * (Real.sqrt X * Real.sqrt Y) * 4 :=
            mul_le_mul_of_nonneg_left (sum_Icc_sqrt_div_sq_le H) (by positivity)
        _ = 4 * Real.sqrt K₂ * Real.sqrt X * Real.sqrt Y := by ring
    have hE : ‖∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H, ∑ ζ ∈ T,
        κ ζ * (G H (j * n) ζ - mainG H (j * n) ζ)‖ ≤ 8 * K₁ * E₂ + δ H := by
      have hpb : ∀ n ∈ W, ∑ ζ ∈ T, ∑ j ∈ Icc 1 H, ‖κ ζ‖ * errB H (j * n) ζ ≤
          (H : ℝ) * pw (H - 1) * (∑ ζ ∈ T, ‖κ ζ‖ / ‖ζ - 1‖) + 8 / (n : ℝ) ^ 3 * K₁ := by
        intro n hn
        have hn1 := hW1 n hn
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_le_sum fun ζ hζ => ?_
        have haζ := ha ζ hζ
        have hterm : ∀ j ∈ Icc 1 H, ‖κ ζ‖ * errB H (j * n) ζ ≤
            ‖κ ζ‖ * ((if j * n < H then pw (H - 1) else 0) / ‖ζ - 1‖ +
              2 * (pw (j * n) - pw (j * n + 1)) / ‖ζ - 1‖ ^ 2) := by
          intro j hj
          have hj1 := (mem_Icc.mp hj).1
          have hjn : 1 ≤ j * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
          have hΔ : 0 ≤ pw (j * n) - pw (j * n + 1) := by rw [pw_sub_pw_succ hjn]; positivity
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          simp only [errB]
          split_ifs with h
          · exact le_of_eq (by field_simp)
          · rw [zero_div, zero_add]; positivity
        calc ∑ j ∈ Icc 1 H, ‖κ ζ‖ * errB H (j * n) ζ
            ≤ ∑ j ∈ Icc 1 H, ‖κ ζ‖ * ((if j * n < H then pw (H - 1) else 0) / ‖ζ - 1‖ +
                2 * (pw (j * n) - pw (j * n + 1)) / ‖ζ - 1‖ ^ 2) := sum_le_sum hterm
          _ = ‖κ ζ‖ / ‖ζ - 1‖ * ∑ j ∈ Icc 1 H, (if j * n < H then pw (H - 1) else 0) +
                2 * (‖κ ζ‖ / ‖ζ - 1‖ ^ 2) * ∑ j ∈ Icc 1 H, (pw (j * n) - pw (j * n + 1)) := by
              rw [mul_sum, mul_sum, ← sum_add_distrib]
              exact sum_congr rfl fun _ _ => by ring
          _ ≤ ‖κ ζ‖ / ‖ζ - 1‖ * ((H : ℝ) * pw (H - 1)) +
                2 * (‖κ ζ‖ / ‖ζ - 1‖ ^ 2) * (4 / (n : ℝ) ^ 3) := by
              refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity))
                (mul_le_mul_of_nonneg_left (sum_Icc_pw_sub_pw_succ_mul_le hn1) (by positivity))
              calc ∑ j ∈ Icc 1 H, (if j * n < H then pw (H - 1) else 0)
                  ≤ ∑ _j ∈ Icc 1 H, pw (H - 1) := sum_le_sum fun j _ => by
                    split_ifs <;> [exact le_rfl; exact pw_nonneg _]
                _ = (H : ℝ) * pw (H - 1) := by rw [sum_const, Nat.card_Icc]; simp
          _ = (H : ℝ) * pw (H - 1) * (‖κ ζ‖ / ‖ζ - 1‖) + 8 / (n : ℝ) ^ 3 * (‖κ ζ‖ / ‖ζ - 1‖ ^ 2) := by
              ring
      calc ‖∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H, ∑ ζ ∈ T,
            κ ζ * (G H (j * n) ζ - mainG H (j * n) ζ)‖
          ≤ ∑ n ∈ W, |c' n| * ∑ ζ ∈ T, ∑ j ∈ Icc 1 H, ‖κ ζ‖ * errB H (j * n) ζ := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, sum_comm]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            refine (norm_sum_le _ _).trans (sum_le_sum fun ζ hζ => ?_)
            refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
            rw [norm_mul]
            have hj1 := (mem_Icc.mp hj).1
            have hn1 := hW1 n hn
            have hjn : 1 ≤ j * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
            exact mul_le_mul_of_nonneg_left (hGsplit H (j * n) ζ hjn (hroot ζ hζ).1
              (hroot ζ hζ).2) (norm_nonneg _)
        _ ≤ ∑ n ∈ W, |c' n| * ((H : ℝ) * pw (H - 1) * (∑ ζ ∈ T, ‖κ ζ‖ / ‖ζ - 1‖) +
              8 / (n : ℝ) ^ 3 * K₁) :=
            sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hpb n hn) (abs_nonneg _)
        _ = 8 * K₁ * E₂ + δ H := by
            set S₁ := ∑ ζ ∈ T, ‖κ ζ‖ / ‖ζ - 1‖
            calc ∑ n ∈ W, |c' n| * ((H : ℝ) * pw (H - 1) * S₁ + 8 / (n : ℝ) ^ 3 * K₁)
                = ∑ n ∈ W, ((H : ℝ) * pw (H - 1) * S₁ * |c' n| + 8 * K₁ * (|c' n| / (n : ℝ) ^ 3)) :=
                  sum_congr rfl fun n hn => by
                    have hnR : (0 : ℝ) < n := by exact_mod_cast hW1 n hn
                    field_simp
              _ = (H : ℝ) * pw (H - 1) * S₁ * ∑ n ∈ W, |c' n| + 8 * K₁ * E₂ := by
                  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
              _ = 8 * K₁ * E₂ + δ H := by simp only [δ]; ring
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add hM hE
      _ = _ := by ring
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h0 : Tendsto (fun H : ℕ => (H : ℝ) * pw (H - 1)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun H => by
          have := pw_nonneg (H - 1); positivity)
        (eventually_atTop.mpr ⟨2, fun H hH => ?_⟩) (tendsto_const_div_atTop_nhds_zero_nat 2)
      have hH1 : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
      rw [pw, hH1, show (H : ℝ) - 1 + 1 = H by ring, mul_one_div,
        div_le_div_iff₀ (by nlinarith) (by linarith)]
      nlinarith
    simpa using h0.mul_const ((∑ n ∈ W, |c' n|) * ∑ ζ ∈ T, ‖κ ζ‖ / ‖ζ - 1‖)
  have hlim := (tendsto_rowStepSum N c c').abs
  have hle := le_of_tendsto_of_tendsto hlim (tendsto_const_nhds.add hδ)
    (Eventually.of_forall fun H => by
      have := hfin H
      rwa [Complex.norm_real, Real.norm_eq_abs] at this)
  simpa only [add_zero] using hle

/-! ## §2. Every row: the canonical primitive restricted to the small orders -/

/-- The fluctuation of a row is its canonical primitive `W_{N,c}`. -/
theorem rowFluct_eq_weightedCenteredSawtoothSum (N M : ℕ) (c : ℕ → ℝ) :
    rowFluct N c M = weightedCenteredSawtoothSum N c M := by
  rw [rowFluct, weightedCenteredSawtoothSum]
  congr 1
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
  rw [centeredResidue, centeredDiscreteSawtooth, Int.fract_div_natCast_eq_div_natCast_mod]
  field_simp

/-- The nontrivial roots of order at most `Q` are the primitive roots of the orders `2, …, Q`. -/
theorem primitiveRoots'_eq_biUnion (Q : ℕ) :
    primitiveRoots' Q = (Icc 2 Q).biUnion fun e => primitiveRoots e ℂ := by
  ext ζ
  simp only [primitiveRoots', mem_erase, mem_biUnion]
  constructor
  · rintro ⟨hζ1, hζ⟩
    have he := orderOf_mem_Icc_of_mem_responseRoots hζ
    refine ⟨orderOf ζ, mem_Icc.mpr ⟨?_, (mem_Icc.mp he).2⟩, (mem_primitiveRoots
      (mem_Icc.mp he).1).mpr (IsPrimitiveRoot.orderOf ζ)⟩
    have h1 : orderOf ζ ≠ 1 := fun h => hζ1 (orderOf_eq_one_iff.mp h)
    have := (mem_Icc.mp he).1
    omega
  · rintro ⟨e, he, hζ⟩
    have he' := mem_Icc.mp he
    have hprim := (mem_primitiveRoots (by omega)).mp hζ
    exact ⟨hprim.ne_one (by omega), primitiveRoot_mem_responseRoots (mem_Icc.mpr ⟨by omega, he'.2⟩)
      hprim⟩

theorem sum_primitiveRoots'_eq (Q : ℕ) (f : ℂ → ℝ) :
    ∑ ζ ∈ primitiveRoots' Q, f ζ = ∑ e ∈ Icc 2 Q, ∑ ζ ∈ primitiveRoots e ℂ, f ζ := by
  rw [primitiveRoots'_eq_biUnion, sum_biUnion fun e _ e' _ hne => IsPrimitiveRoot.disjoint hne]

/-- **Large-sieve dispersion in Selberg coordinates.** For every row `c` supported on `[1, Q₀]`
and every row `c'` on `[A+1, A+L]`, with `Y = Y_{N,c}` the Selberg coordinates,
`|B + m R' + β H'| ≤ ½ √(Σ_e Y(e)² e⁴) √(L+2Q₀²-1) √(Σ c'(n)²/n⁴) + ½ Σ_e |Y(e)| e³ · Σ |c'(n)|/n³`. -/
theorem abs_rowBilinear_add_mean_add_beta_le_selberg {N Q₀ A L : ℕ} {c c' : ℕ → ℝ}
    (hQ₀ : 2 ≤ Q₀) (hQN : Q₀ ≤ N) (hsupp : ∀ n, c n ≠ 0 → n ≤ Q₀)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'| ≤
      1 / 2 * Real.sqrt (∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4) *
          Real.sqrt ((L : ℝ) + 2 * (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 2 * (∑ e ∈ Icc 2 Q₀, |selbergMultiplesCoord N c e| * (e : ℝ) ^ 3) *
          ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 3 := by
  set T := primitiveRoots' Q₀
  set κ := primitiveSpectralCoeff N c
  have hT : T ⊆ responseRoots Q₀ := erase_subset _ _
  have hT1 : ∀ ζ ∈ T, ζ ≠ 1 := fun ζ hζ => ne_of_mem_erase hζ
  -- Selberg coordinates vanish beyond the support
  have hY0 : ∀ e, Q₀ < e → selbergMultiplesCoord N c e = 0 := fun e he =>
    sum_eq_zero fun d hd => by
      obtain ⟨hd1, hed⟩ := mem_filter.mp hd
      have : c d = 0 := by
        by_contra h
        have := hsupp d h
        have := Nat.le_of_dvd (mem_Icc.mp hd1).1 hed
        omega
      rw [this, zero_div]
  have hspec : ∀ M, (rowFluct N c M : ℂ) = ∑ ζ ∈ T, κ ζ * ζ ^ M := by
    intro M
    rw [rowFluct_eq_weightedCenteredSawtoothSum,
      weightedCenteredSawtoothSum_eq_spectral (by omega)]
    symm
    have hmono : responseRoots Q₀ ⊆ responseRoots N := fun ζ hζ => by
      obtain ⟨d, hd, h⟩ := mem_biUnion.mp hζ
      exact mem_biUnion.mpr ⟨d, mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans hQN⟩, h⟩
    refine sum_subset (erase_subset_erase 1 hmono) fun ζ hζN hζT => ?_
    have hord : Q₀ < orderOf ζ := by
      by_contra h
      apply hζT
      have hζN' := mem_of_mem_erase hζN
      have he := orderOf_mem_Icc_of_mem_responseRoots hζN'
      exact mem_erase.mpr ⟨ne_of_mem_erase hζN, primitiveRoot_mem_responseRoots
        (mem_Icc.mpr ⟨(mem_Icc.mp he).1, not_lt.mp h⟩) (IsPrimitiveRoot.orderOf ζ)⟩
    simp only [κ, primitiveSpectralCoeff, hY0 _ hord, Complex.ofReal_zero, zero_mul, zero_div]
  have hmain := abs_rowBilinear_add_mean_add_beta_le_spectral hQ₀ hT hT1 hspec hsupp' hAL
  -- Farey evaluation of the two spectral weights
  have hκ : ∀ e ∈ Icc 2 Q₀, ∀ ζ ∈ primitiveRoots e ℂ,
      ‖κ ζ‖ = |selbergMultiplesCoord N c e| / ‖ζ - 1‖ := by
    intro e he ζ hζ
    have hprim := (mem_primitiveRoots (by have := (mem_Icc.mp he).1; omega)).mp hζ
    have hn : ‖ζ‖ = 1 := hprim.norm'_eq_one (by have := (mem_Icc.mp he).1; omega)
    simp only [κ, primitiveSpectralCoeff, ← hprim.eq_orderOf, norm_div, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, hn, mul_one]
  have hK₂ : ∑ ζ ∈ T, ‖κ ζ‖ ^ 2 / ‖ζ - 1‖ ^ 2 ≤
      1 / 64 * ∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4 := by
    rw [sum_primitiveRoots'_eq, mul_sum]
    refine sum_le_sum fun e he => ?_
    have he2 := (mem_Icc.mp he).1
    rw [sum_congr rfl fun ζ hζ => by
      rw [hκ e he ζ hζ, div_pow, sq_abs, div_div, ← pow_add,
        div_eq_mul_one_div (selbergMultiplesCoord N c e ^ 2)], ← mul_sum]
    calc selbergMultiplesCoord N c e ^ 2 * ∑ ζ ∈ primitiveRoots e ℂ, 1 / ‖ζ - 1‖ ^ (2 + 2)
        ≤ selbergMultiplesCoord N c e ^ 2 * (((e : ℝ) / 4) ^ 2 * ((e : ℝ) ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_pow_le he2 2)
            (sq_nonneg _)
      _ = 1 / 64 * (selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4) := by ring
  have hK₁ : ∑ ζ ∈ T, ‖κ ζ‖ / ‖ζ - 1‖ ^ 2 ≤
      1 / 16 * ∑ e ∈ Icc 2 Q₀, |selbergMultiplesCoord N c e| * (e : ℝ) ^ 3 := by
    rw [sum_primitiveRoots'_eq, mul_sum]
    refine sum_le_sum fun e he => ?_
    have he2 := (mem_Icc.mp he).1
    rw [sum_congr rfl fun ζ hζ => show ‖κ ζ‖ / ‖ζ - 1‖ ^ 2 =
        |selbergMultiplesCoord N c e| * (1 / ‖ζ - 1‖ ^ (1 + 2)) by
      have hne : ‖ζ - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr
        (((mem_primitiveRoots (by omega)).mp hζ).ne_one (by omega)))
      rw [hκ e he ζ hζ]; field_simp, ← mul_sum]
    calc |selbergMultiplesCoord N c e| * ∑ ζ ∈ primitiveRoots e ℂ, 1 / ‖ζ - 1‖ ^ (1 + 2)
        ≤ |selbergMultiplesCoord N c e| * (((e : ℝ) / 4) ^ 1 * ((e : ℝ) ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_pow_le he2 1)
            (abs_nonneg _)
      _ = 1 / 16 * (|selbergMultiplesCoord N c e| * (e : ℝ) ^ 3) := by ring
  refine hmain.trans (add_le_add ?_ ?_)
  · have hs : Real.sqrt (∑ ζ ∈ T, ‖κ ζ‖ ^ 2 / ‖ζ - 1‖ ^ 2) ≤
        1 / 8 * Real.sqrt (∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4) := by
      rw [show (1 : ℝ) / 8 = Real.sqrt (1 / 64) by
        rw [show (1 : ℝ) / 64 = (1 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
        ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hK₂
    have := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4)
    calc 4 * Real.sqrt (∑ ζ ∈ T, ‖κ ζ‖ ^ 2 / ‖ζ - 1‖ ^ 2) *
          Real.sqrt ((L : ℝ) + 2 * (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4)
        ≤ 4 * (1 / 8 * Real.sqrt (∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4)) *
          Real.sqrt ((L : ℝ) + 2 * (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) := by gcongr
      _ = _ := by ring
  · calc 8 * (∑ ζ ∈ T, ‖κ ζ‖ / ‖ζ - 1‖ ^ 2) * ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 3
        ≤ 8 * (1 / 16 * ∑ e ∈ Icc 2 Q₀, |selbergMultiplesCoord N c e| * (e : ℝ) ^ 3) *
            ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 3 := by
          gcongr
      _ = _ := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence

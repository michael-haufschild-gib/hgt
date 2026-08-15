import GaloisForLFunctions.RHTower.WallSymbolFrequencyJets
import GaloisForLFunctions.RHTower.GammaJumpMultiplierBounds

/-!
# The shifted Gamma symbol has a finite lower numerical range

Writing the shifted symbol through the Gauss series of the digamma,

`Re r(x+iσ) = Σ_{a≥1} [2/a − (a−σ)/((a−σ)²+x²) − (a+σ)/((a+σ)²+x²)]`,

each term is bounded below by its value at `x = 0`,

`2/a − 1/(a−σ) − 1/(a+σ) = −2σ²/(a(a²−σ²))`,

and that series converges for `σ < 1` because `a² − σ² ≥ a²(1−σ²)` for `a ≥ 1`.  Hence

`Re r(x+iσ) ≥ −κ_σ`,   `κ_σ = 2σ²/(1−σ²) · Σ_{a≥1} a^{-3}`,

uniformly in the frequency.  The bound is what lets a cutoff translated far enough down the
logarithmic ray make the position term `2L` dominate the loss: the jump symbol can only push the
numerical range down by a fixed amount, no matter how large the frequency.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The termwise lower bound of the shifted Gauss series. -/
def kappaTerm (σ : ℝ) (n : ℕ) : ℝ := 2 * σ ^ 2 / (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ 2 - σ ^ 2))

theorem kappaTerm_nonneg {σ : ℝ} (hσ1 : σ < 1) (hσ0 : 0 < σ) (n : ℕ) : 0 ≤ kappaTerm σ n := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 - σ ^ 2 := by nlinarith
  rw [kappaTerm]
  positivity

theorem kappaTerm_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (n : ℕ) :
    kappaTerm σ n ≤ 2 * σ ^ 2 / ((1 - σ ^ 2) * ((n : ℝ) + 1) ^ 3) := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hsq : (1 : ℝ) - σ ^ 2 > 0 := by nlinarith
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hkey : ((n : ℝ) + 1) ^ 2 * (1 - σ ^ 2) ≤ ((n : ℝ) + 1) ^ 2 - σ ^ 2 := by
    nlinarith [sq_nonneg σ, h1]
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 - σ ^ 2 := by nlinarith
  rw [kappaTerm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey, hn, hsq, sq_nonneg σ, mul_nonneg (sq_nonneg σ) (by linarith : (0:ℝ) ≤ (n:ℝ)+1)]

theorem summable_kappaTerm {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) : Summable (kappaTerm σ) := by
  have hcube : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3 := by
    have h : Summable fun n : ℕ => 1 / (n : ℝ) ^ 3 :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    refine ((summable_nat_add_iff 1).mpr h).congr fun n => ?_
    push_cast
    ring
  have hmaj : Summable fun n : ℕ => 2 * σ ^ 2 / ((1 - σ ^ 2) * ((n : ℝ) + 1) ^ 3) := by
    refine (hcube.mul_left (2 * σ ^ 2 / (1 - σ ^ 2))).congr fun n => ?_
    rw [div_mul_eq_mul_div, mul_one_div, div_div, mul_comm (((n : ℝ) + 1) ^ 3) (1 - σ ^ 2)]
  exact Summable.of_nonneg_of_le (fun n => kappaTerm_nonneg hσ1 hσ0 n)
    (fun n => kappaTerm_le hσ0 hσ1 n) hmaj

/-- The explicit numerical-range constant. -/
def gammaShiftKappa (σ : ℝ) : ℝ := ∑' n : ℕ, kappaTerm σ n

theorem gammaShiftKappa_nonneg {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) : 0 ≤ gammaShiftKappa σ :=
  tsum_nonneg fun n => kappaTerm_nonneg hσ1 hσ0 n

/-! ## The shifted symbol through the Gauss series -/

/-- The real Gauss series is summable on every vertical line in the right half plane. -/
theorem summable_gaussRealTerm {a t : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + 1) - (a + n) / ((a + n) ^ 2 + t ^ 2) := by
  have hre : (0 : ℝ) < ((a : ℂ) + (t : ℂ) * Complex.I).re := by simpa using ha
  have hs := _root_.RHTower.summable_gaussDigammaSeriesTerm hre
  have hmap := hs.map (Complex.reCLM.toLinearMap.toAddMonoidHom) Complex.reCLM.continuous
  refine hmap.congr fun n => ?_
  have hn : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  simp only [Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    ContinuousLinearMap.coe_coe, Complex.reCLM_apply]
  rw [_root_.RHTower.gaussDigammaSeriesTerm, Complex.sub_re, hn, one_div, one_div,
    ← Complex.ofReal_inv, Complex.ofReal_re, _root_.RHTower.re_inv_shift]
  ring

/-- **The shifted symbol as a real Gauss series.** -/
theorem re_wallSymbol_eq_tsum {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    (wallSymbol σ x).re
      = (∑' n : ℕ, (1 / ((n : ℝ) + 1) - ((1 - σ) + n) / (((1 - σ) + n) ^ 2 + x ^ 2)))
        + ∑' n : ℕ, (1 / ((n : ℝ) + 1) - ((1 + σ) + n) / (((1 + σ) + n) ^ 2 + x ^ 2)) := by
  have hlow : (0 : ℝ) < 1 - σ := by linarith
  have hup : (0 : ℝ) < 1 + σ := by linarith
  have h₁ := re_digamma_vertical_series hlow x
  have h₂ := re_digamma_vertical_series hup (-x)
  have h₂' : (Complex.digamma (((1 + σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * Complex.I)).re
      = -Real.eulerMascheroniConstant
        + ∑' n : ℕ, (1 / ((n : ℝ) + 1) - ((1 + σ) + n) / (((1 + σ) + n) ^ 2 + x ^ 2)) := by
    rw [h₂]
    congr 1
    exact tsum_congr fun k => by rw [neg_sq]
  rw [wallSymbol]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
  rw [h₁, h₂']
  ring

/-- **`(17)`: the shifted Gamma symbol has a finite lower numerical range.**  Uniformly in the
frequency, the real part of the symbol is bounded below by `−κ_σ`. -/
theorem neg_gammaShiftKappa_le_re_wallSymbol {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    -gammaShiftKappa σ ≤ (wallSymbol σ x).re := by
  have hlow : (0 : ℝ) < 1 - σ := by linarith
  have hup : (0 : ℝ) < 1 + σ := by linarith
  set F₁ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) - ((1 - σ) + n) / (((1 - σ) + n) ^ 2 + x ^ 2)
    with hF₁
  set F₂ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) - ((1 + σ) + n) / (((1 + σ) + n) ^ 2 + x ^ 2)
    with hF₂
  have hs₁ : Summable F₁ := summable_gaussRealTerm hlow
  have hs₂ : Summable F₂ := summable_gaussRealTerm hup
  have hsk : Summable (kappaTerm σ) := summable_kappaTerm hσ0 hσ1
  -- termwise lower bound
  have hterm : ∀ n : ℕ, -kappaTerm σ n ≤ F₁ n + F₂ n := by
    intro n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have ha₁ : (0 : ℝ) < (1 - σ) + n := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have ha₂ : (0 : ℝ) < (1 + σ) + n := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hb₁ : ((1 - σ) + n) / (((1 - σ) + n) ^ 2 + x ^ 2) ≤ 1 / ((1 - σ) + n) := by
      rw [div_le_div_iff₀ (by positivity) ha₁]
      nlinarith [sq_nonneg x]
    have hb₂ : ((1 + σ) + n) / (((1 + σ) + n) ^ 2 + x ^ 2) ≤ 1 / ((1 + σ) + n) := by
      rw [div_le_div_iff₀ (by positivity) ha₂]
      nlinarith [sq_nonneg x]
    have hkey : 2 / ((n : ℝ) + 1) - 1 / ((1 - σ) + n) - 1 / ((1 + σ) + n)
        = -kappaTerm σ n := by
      rw [kappaTerm]
      have h1 : (1 - σ) + (n : ℝ) = ((n : ℝ) + 1) - σ := by ring
      have h2 : (1 + σ) + (n : ℝ) = ((n : ℝ) + 1) + σ := by ring
      rw [h1, h2]
      have hne₁ : ((n : ℝ) + 1) - σ ≠ 0 := by
        rw [h1] at ha₁
        linarith
      have hne₂ : ((n : ℝ) + 1) + σ ≠ 0 := by
        rw [h2] at ha₂
        linarith
      have hne₃ : ((n : ℝ) + 1) ≠ 0 := by linarith
      have hne₄ : ((n : ℝ) + 1) ^ 2 - σ ^ 2 ≠ 0 := by
        have : ((n : ℝ) + 1) ^ 2 - σ ^ 2 = (((n : ℝ) + 1) - σ) * (((n : ℝ) + 1) + σ) := by ring
        rw [this]
        exact mul_ne_zero hne₁ hne₂
      field_simp
      ring
    rw [hF₁, hF₂, ← hkey]
    have hsplit : 2 / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
    rw [hsplit]
    linarith [hb₁, hb₂]
  have hsum : Summable fun n : ℕ => F₁ n + F₂ n := hs₁.add hs₂
  have hmono : (∑' n : ℕ, -kappaTerm σ n) ≤ ∑' n : ℕ, (F₁ n + F₂ n) :=
    Summable.tsum_le_tsum hterm hsk.neg hsum
  rw [tsum_neg] at hmono
  rw [re_wallSymbol_eq_tsum hσ0 hσ1 x, ← hs₁.tsum_add hs₂]
  rw [gammaShiftKappa]
  exact hmono

end GaloisForLFunctions.RHTower

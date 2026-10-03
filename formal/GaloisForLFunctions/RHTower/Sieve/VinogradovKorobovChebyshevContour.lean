import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovChebyshevParameters
import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneShaped
import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneShape
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodWidth
import GaloisForLFunctions.RHTower.Sieve.ChebyshevExplicitBound
import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform

/-!
# The smoothed Chebyshev sum on the Vinogradov–Korobov contour

The rectangle has left edge `c = 1 - u`, `u = vkUniformRegWidth δ T`, right edge
`d = 1 + 1/log T` and height `T = vkHeight N`.  On it `ζ` has no zeros and the regular part of
`ζ'/ζ` is at most `C log T/w(T+1) ≤ 6·10⁸ C (log N)²`.  With `E = 3e^{-s}`, `s = log T/2`, every
edge power is controlled by the zero-free region alone:

```text
Z^d ≤ Z·E·T        (2 log Z ≤ log²T),
Z^c, Y^c ≤ Z·E     (s ≤ u log N),
```

so the five contour terms are at most `(1 + W)·10¹⁰(1 + C)(log N)²·Z·E`, and the smoothing price
`W ≤ 9 Cm e^{s/3}` leaves

```text
‖2π ∑ Λ(n) w(n) - (mass)·(bracket)‖ ≤ B (log N)² (N + H + 1) e^{-2s/3}.
```
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

noncomputable section

/-- The right edge power: `Z^{1 + 1/Lg} ≤ Z·3e^{-Lg/2}·e^{Lg}` once `2 log Z ≤ Lg²`. -/
theorem vk_rpow_right_le {Z Lg : ℝ} (hZ : 0 < Z) (hLg : 0 < Lg) (h : 2 * Real.log Z ≤ Lg ^ 2) :
    Z ^ (1 + 1 / Lg) ≤ Z * (3 * Real.exp (-(Lg / 2))) * Real.exp Lg := by
  rw [Real.rpow_add hZ, Real.rpow_one, Real.rpow_def_of_pos hZ]
  have hexp : Real.exp (Real.log Z * (1 / Lg)) ≤ Real.exp (Lg / 2) := by
    apply Real.exp_le_exp.mpr
    rw [mul_one_div, div_le_iff₀ hLg]
    nlinarith
  have hcomb : 3 * Real.exp (-(Lg / 2)) * Real.exp Lg = 3 * Real.exp (Lg / 2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have he := Real.exp_pos (Lg / 2)
  calc Z * Real.exp (Real.log Z * (1 / Lg)) ≤ Z * Real.exp (Lg / 2) :=
        mul_le_mul_of_nonneg_left hexp hZ.le
    _ ≤ Z * (3 * Real.exp (Lg / 2)) := mul_le_mul_of_nonneg_left (by linarith) hZ.le
    _ = Z * (3 * Real.exp (-(Lg / 2))) * Real.exp Lg := by rw [mul_assoc Z, hcomb]

/-- The left edge power: `Z^{1-u} ≤ Z·3e^{-s}` once `N ≤ Z` and `s ≤ u log N`. -/
theorem vk_rpow_left_le {Z N u s : ℝ} (hN : 0 < N) (hNZ : N ≤ Z) (hu : 0 ≤ u)
    (hs : s ≤ u * Real.log N) : Z ^ (1 - u) ≤ Z * (3 * Real.exp (-s)) := by
  have hZ : 0 < Z := lt_of_lt_of_le hN hNZ
  rw [sub_eq_add_neg, Real.rpow_add hZ, Real.rpow_one]
  have h1 : Z ^ (-u) ≤ N ^ (-u) := Real.rpow_le_rpow_of_nonpos hN hNZ (by linarith)
  have h2 : N ^ (-u) ≤ Real.exp (-s) := by
    rw [Real.rpow_def_of_pos hN]
    apply Real.exp_le_exp.mpr
    linarith
  have h3 : Real.exp (-s) ≤ 3 * Real.exp (-s) := by linarith [Real.exp_pos (-s)]
  exact mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hZ.le

/-- The five-term coefficient against `(1 + W)·10¹⁰(1 + C)L²`. -/
theorem vk_coeff_le {S W ci wd M Cr L Lg : ℝ} (hS0 : 0 ≤ S) (hS : S ≤ 8 * Lg ^ 2) (hW0 : 0 ≤ W)
    (hci0 : 0 ≤ ci) (hci : ci ≤ 12 * 10 ^ 8 * L) (hwd : wd ≤ 1) (hM0 : 0 ≤ M)
    (hM : M ≤ 6 * 10 ^ 8 * Cr * L ^ 2) (hCr : 0 ≤ Cr) (hLg0 : 0 ≤ Lg) (hLgL : Lg ≤ L)
    (hL1 : 1 ≤ L) :
    2 * S * W + ci * (4 + 2 * W) + 2 * wd * (W + 1) + M * (4 + 2 * W) + 2 * wd * M * W
      ≤ (1 + W) * (10 ^ 10 * (1 + Cr) * L ^ 2) := by
  have h1 : 2 * S * W ≤ 2 * S * (1 + W) := by nlinarith
  have h2 : ci * (4 + 2 * W) ≤ 4 * ci * (1 + W) := by nlinarith
  have h3 : 2 * wd * (W + 1) ≤ 2 * (1 + W) := by nlinarith
  have h4 : M * (4 + 2 * W) ≤ 4 * M * (1 + W) := by nlinarith
  have h5 : 2 * wd * M * W ≤ 2 * M * (1 + W) := by
    have := mul_le_mul_of_nonneg_right hwd (mul_nonneg hM0 hW0)
    nlinarith
  have hLg2 : Lg ^ 2 ≤ L ^ 2 := by nlinarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hCL : 0 ≤ Cr * L ^ 2 := mul_nonneg hCr (sq_nonneg L)
  have hP : 2 * S + 4 * ci + 2 + 6 * M ≤ 10 ^ 10 * (1 + Cr) * L ^ 2 := by nlinarith
  calc 2 * S * W + ci * (4 + 2 * W) + 2 * wd * (W + 1) + M * (4 + 2 * W) + 2 * wd * M * W
      ≤ 2 * S * (1 + W) + 4 * ci * (1 + W) + 2 * (1 + W) + 4 * M * (1 + W)
          + 2 * M * (1 + W) := by linarith
    _ = (1 + W) * (2 * S + 4 * ci + 2 + 6 * M) := by ring
    _ ≤ (1 + W) * (10 ^ 10 * (1 + Cr) * L ^ 2) := mul_le_mul_of_nonneg_left hP (by linarith)

/-- The smoothing price against the edge factor: `(1 + W)·3e^{-s} ≤ 3(1 + 9Cm)e^{-2s/3}`. -/
theorem vk_width_factor_le {W Cm s : ℝ} (hs : 0 ≤ s)
    (hW : W ≤ Cm * (9 * Real.exp (s / 3))) :
    (1 + W) * (3 * Real.exp (-s)) ≤ 3 * (1 + 9 * Cm) * Real.exp (-(2 * s / 3)) := by
  have he1 : Real.exp (-s) ≤ Real.exp (-(2 * s / 3)) := Real.exp_le_exp.mpr (by linarith)
  have he2 : Real.exp (s / 3) * Real.exp (-s) = Real.exp (-(2 * s / 3)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE0 := Real.exp_pos (-s)
  have hE1 := Real.exp_pos (-(2 * s / 3))
  calc (1 + W) * (3 * Real.exp (-s))
      ≤ (1 + Cm * (9 * Real.exp (s / 3))) * (3 * Real.exp (-s)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 3 * Real.exp (-s) + 27 * Cm * (Real.exp (s / 3) * Real.exp (-s)) := by ring
    _ ≤ 3 * Real.exp (-(2 * s / 3)) + 27 * Cm * Real.exp (-(2 * s / 3)) := by
        rw [he2]; linarith
    _ = 3 * (1 + 9 * Cm) * Real.exp (-(2 * s / 3)) := by ring

/-- **The contour data on the Vinogradov–Korobov rectangle.** -/
theorem vk_cheb_data {C δ K₀ T c : ℝ}
    (hzf : ∀ (s : ℂ) (K : ℝ), K₀ ≤ K → |s.im| ≤ K →
      1 - vkUniformRegWidth δ K ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0)
    (hreg : ∀ (s : ℂ) (K : ℝ), K₀ ≤ K → |s.im| ≤ K →
      1 - vkUniformRegWidth δ K ≤ s.re → s.re ≤ 9 / 8 →
      ‖zetaLogDerivReg s‖ ≤ C * Real.log K / RHTower.vkHadamardWidth (K + 1))
    (hK : K₀ ≤ T) (hT0 : 0 < T) (hT8 : 8 ≤ Real.log T)
    (hcu : 1 - vkUniformRegWidth δ T ≤ c) (hc1 : c < 1) :
    (∀ s ∈ Set.uIcc c (chebRightTwo T) ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0)
    ∧ (∀ y ∈ Set.uIcc (-T) T, riemannZeta ((c : ℂ) + (y : ℝ) * Complex.I) ≠ 0)
    ∧ (∀ y ∈ Set.Icc (-T) T, ‖zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ C * Real.log T / RHTower.vkHadamardWidth (T + 1))
    ∧ (∀ x ∈ Set.uIoc c (chebRightTwo T),
        ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
          ≤ C * Real.log T / RHTower.vkHadamardWidth (T + 1))
    ∧ (∀ x ∈ Set.uIoc c (chebRightTwo T),
        ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖
          ≤ C * Real.log T / RHTower.vkHadamardWidth (T + 1)) := by
  have hcd : c ≤ chebRightTwo T := le_of_lt (lt_trans hc1 (one_lt_chebRightTwo hT8))
  have hd98 := chebRightTwo_le hT8
  have hTT : (-T : ℝ) ≤ T := by linarith
  have hcre : ∀ y : ℝ, ((c : ℂ) + (y : ℝ) * Complex.I).re = c := by intro y; simp
  have hcim : ∀ y : ℝ, ((c : ℂ) + (y : ℝ) * Complex.I).im = y := by intro y; simp
  have hxre : ∀ x v : ℝ, ((x : ℂ) + ((v : ℝ) : ℂ) * Complex.I).re = x := by intro x v; simp
  have hxim : ∀ x v : ℝ, ((x : ℂ) + ((v : ℝ) : ℂ) * Complex.I).im = v := by intro x v; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hne
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hcd, Set.uIcc_of_le hTT] at hs
    exact hzf s T hK (abs_le.mpr ⟨hs.2.1, hs.2.2⟩) (le_trans hcu hs.1.1) hne
  · intro y hy
    rw [Set.uIcc_of_le hTT] at hy
    refine hzf _ T hK ?_ ?_ ?_
    · rw [hcim]; exact abs_le.mpr ⟨hy.1, hy.2⟩
    · rw [hcre]; exact hcu
    · intro h
      have hh := hcre y
      rw [h] at hh
      simp only [Complex.one_re] at hh
      linarith
  · intro y hy
    refine hreg _ T hK ?_ ?_ ?_
    · rw [hcim]; exact abs_le.mpr ⟨hy.1, hy.2⟩
    · rw [hcre]; exact hcu
    · rw [hcre]; linarith
  · intro x hx
    rw [Set.uIoc_of_le hcd] at hx
    refine hreg _ T hK ?_ ?_ ?_
    · rw [hxim, abs_of_nonneg hT0.le]
    · rw [hxre]; linarith [hx.1]
    · rw [hxre]; linarith [hx.2]
  · intro x hx
    rw [Set.uIoc_of_le hcd] at hx
    refine hreg _ T hK ?_ ?_ ?_
    · rw [hxim, abs_neg, abs_of_nonneg hT0.le]
    · rw [hxre]; linarith [hx.1]
    · rw [hxre]; linarith [hx.2]


/-- **The smoothed Chebyshev sum at Vinogradov–Korobov strength.**  With `T = vkHeight N`,
`H = vkWidth N`, `s = vkSaving N` and left edge `1 - vkUniformRegWidth δ T`:

```text
‖2π ∑ Λ(n) w(n) - (mass)·(bracket)‖ ≤ B (log N)² (N + H + 1) e^{-2s/3}.
``` -/
theorem exists_norm_tsum_vonMangoldt_vk_rate :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N (vkWidth N) (n : ℝ) : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (vkWidth N) x : ℝ) : ℂ)) 1
              * (((2 * Real.arctan (vkHeight N / (chebRightTwo (vkHeight N) - 1))
                    - 2 * Real.arctan (vkHeight N
                      / ((1 - vkUniformRegWidth δ (vkHeight N)) - 1)) : ℝ)) : ℂ)‖
        ≤ B * Real.log N ^ 2 * (N + vkWidth N + 1) * Real.exp (-(2 * vkSaving N / 3)) := by
  obtain ⟨Cm, hCm, hdec⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨C, δ, K₀, hC0, hδ, hK₀3, -, hzf, hreg⟩ := exists_bound_zetaLogDerivReg_vk_uniform
  refine ⟨δ, 10 ^ 10 * (1 + C) * (3 * (1 + 9 * Cm)), hδ, by positivity, ?_⟩
  filter_upwards [eventually_vk_conditions hδ (Real.log K₀)] with N hcond
  obtain ⟨hN3, hL3, hLgK, hLg8, hLg2, hLgL, hw0, hwinv, hu0, hu8, hui, hsu⟩ := hcond
  have hsave : vkSaving N = Real.log (vkHeight N) / 2 := vkSaving_eq N
  have hH : vkWidth N = N * Real.exp (-(vkSaving N / 6)) := rfl
  have hT0 : 0 < vkHeight N := Real.exp_pos _
  set s := vkSaving N with hsdef
  set T := vkHeight N with hTdef
  set H := vkWidth N with hHdef
  set u := vkUniformRegWidth δ T with hudef
  clear_value s T H u
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have hT1 : 1 ≤ T := by
    have := Real.add_one_le_exp (Real.log T)
    rw [Real.exp_log hT0] at this; linarith
  have hK₀T : K₀ ≤ T := by
    have h1 := Real.exp_le_exp.mpr hLgK
    rwa [Real.exp_log (by linarith), Real.exp_log hT0] at h1
  have hs0 : 0 ≤ s := by rw [hsave]; linarith
  have hsL : s ≤ Real.log N / 2 := by rw [hsave]; linarith
  -- the smoothing width
  have hρ1 : 1 ≤ Real.exp (s / 6) := Real.one_le_exp (by linarith)
  have hHpos : 0 < H := by rw [hH]; positivity
  have hH1 : 1 ≤ H := by
    rw [hH]
    have h1 : Real.exp (-Real.log N) ≤ Real.exp (-(s / 6)) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log hN0] at h1
    calc (1 : ℝ) = N * N⁻¹ := (mul_inv_cancel₀ hN0.ne').symm
      _ ≤ N * Real.exp (-(s / 6)) := mul_le_mul_of_nonneg_left h1 hN0.le
  have hHN : H ≤ N := by
    rw [hH]
    exact mul_le_of_le_one_right hN0.le (Real.exp_le_one_iff.mpr (by linarith))
  have hNH : N / H = Real.exp (s / 6) := by
    rw [hH, ← div_div, div_self hN0.ne', one_div, ← Real.exp_neg, neg_neg]
  have hρsq : (Real.exp (s / 6) + 2) ^ (2 : ℕ) ≤ 9 * Real.exp (s / 3) := by
    have h2 : Real.exp (s / 6) ^ 2 = Real.exp (s / 3) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    nlinarith [hρ1, h2]
  have hWle : Cm / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) ≤ Cm * (9 * Real.exp (s / 3)) :=
    width_price_le_gen hH1 hN0.le (le_of_eq hNH) hCm hρsq
  -- the abscissae
  have hc1 : 1 - u < 1 := by linarith
  have hchalf : 1 / 2 ≤ 1 - u := by linarith
  have hc0 : 0 < 1 - u := by linarith
  have hd1 := one_lt_chebRightTwo hLg8
  have hinvLg : 1 / Real.log T ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hwd : chebRightTwo T - (1 - u) = u + 1 / Real.log T := by rw [chebRightTwo]; ring
  have hwd0 : 0 ≤ chebRightTwo T - (1 - u) := by linarith
  have hwd1 : chebRightTwo T - (1 - u) ≤ 1 := by rw [hwd]; linarith
  obtain ⟨hzfrect, hzfline, hregline, hregtop, hregbot⟩ :=
    vk_cheb_data (c := 1 - u) hzf hreg hK₀T hT0 hLg8 (by rw [hudef]) hc1
  -- the edge bound
  have hM0 : 0 ≤ C * Real.log T / RHTower.vkHadamardWidth (T + 1) := by
    have : 0 ≤ Real.log T := by linarith
    positivity
  have hMb : C * Real.log T / RHTower.vkHadamardWidth (T + 1)
      ≤ 6 * 10 ^ 8 * C * Real.log N ^ 2 := by
    rw [mul_div_assoc]
    have h1 : Real.log T / RHTower.vkHadamardWidth (T + 1)
        ≤ Real.log N * (6 * 10 ^ 8 * Real.log N) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hLgL hwinv (by positivity) (by linarith)
    calc C * (Real.log T / RHTower.vkHadamardWidth (T + 1))
        ≤ C * (Real.log N * (6 * 10 ^ 8 * Real.log N)) := mul_le_mul_of_nonneg_left h1 hC0.le
      _ = 6 * 10 ^ 8 * C * Real.log N ^ 2 := by ring
  -- the contour
  set W := Cm / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) with hWdef
  have hW0 : 0 ≤ W := by positivity
  have hbase := norm_tsum_vonMangoldt_sub_full_main_le_explicit
    (Cc := W * (N + H + 1) ^ (1 - u)) (Cd := W * (N + H + 1) ^ chebRightTwo T)
    hN0 hHpos hc0 hc1 hd1 hT1 hM0 hM0 hzfrect hzfline hregline hregtop hregbot
    (fun z hz hzc => hdec N H hN0 hHpos (1 - u) z hz hzc)
    (fun z hz hzd => hdec N H hN0 hHpos (chebRightTwo T) z hz hzd)
  -- the edge powers
  have hZ0 : 0 < N + H + 1 := by linarith
  have hlogZ : Real.log (N + H + 1) ≤ 2 * Real.log N := by
    have h0 : 2 * N + 1 ≤ N ^ 2 := by nlinarith only [hN3]
    have h1 : N + H + 1 ≤ N ^ 2 := by linarith only [h0, hHN]
    have h2 := Real.log_le_log hZ0 h1
    rw [Real.log_pow] at h2; push_cast at h2; linarith only [h2]
  have hLgsq : 4 * Real.log N ≤ Real.log T ^ 2 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ Real.log N by linarith only [hL1])
    have h1 := pow_le_pow_left₀ (by positivity) hLg2 2
    rw [mul_pow, hsq] at h1
    linarith only [h1]
  have hZd := vk_rpow_right_le hZ0 (by linarith : (0 : ℝ) < Real.log T) (by linarith)
  rw [Real.exp_log hT0, ← hsave] at hZd
  have hsu' : s ≤ u * Real.log N := by linarith
  have hZc := vk_rpow_left_le (Z := N + H + 1) hN0 (by linarith) hu0.le hsu'
  have hYc := vk_rpow_left_le (Z := N + H) hN0 (by linarith) hu0.le hsu'
  have hS0 : (0 : ℝ) ≤ ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(chebRightTwo T)) :=
    tsum_nonneg fun n => mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hTE : 1 / T ≤ 3 * Real.exp (-s) := by
    have h1 : Real.exp (-Real.log T) ≤ Real.exp (-s) :=
      Real.exp_le_exp.mpr (by linarith only [hsave, hs0])
    rw [Real.exp_neg, Real.exp_log hT0] at h1
    rw [one_div]; linarith only [h1, Real.exp_pos (-s)]
  have hci0 : 0 ≤ (1 - (1 - u))⁻¹ := by rw [sub_sub_cancel]; exact (inv_pos.mpr hu0).le
  have hshaped := cheb_kappa_one_terms_shaped
    (S := ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(chebRightTwo T)))
    (W := W) (Y := N + H) (Z := N + H + 1) (E := 3 * Real.exp (-s)) (T := T)
    (Mm := ‖mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖)
    (ci := (1 - (1 - u))⁻¹) (wd := chebRightTwo T - (1 - u))
    (M := C * Real.log T / RHTower.vkHadamardWidth (T + 1)) (c := 1 - u)
    hS0 hW0 hci0 hwd0 hM0 hT1 (by positivity) (by linarith) (by linarith) hchalf
    (norm_mellin_smoothWeight_one_le hN0.le hHpos) hTE (Real.rpow_nonneg hZ0.le _) hZd hZc hYc
  -- the coefficient
  have hciu : (1 - (1 - u))⁻¹ ≤ 12 * 10 ^ 8 * Real.log N := by
    rw [sub_sub_cancel, ← one_div]; exact hui
  have hcoef := vk_coeff_le hS0 (tsum_vonMangoldt_chebRightTwo_le hLg8) hW0 hci0 hciu hwd1 hM0
    hMb hC0.le (by linarith) hLgL hL1
  have hfac := vk_width_factor_le hs0 hWle
  have hZE0 : 0 ≤ (N + H + 1) * (3 * Real.exp (-s)) := by positivity
  have hstep := mul_le_mul_of_nonneg_right hcoef hZE0
  have hfin : (1 + W) * (10 ^ 10 * (1 + C) * Real.log N ^ 2) * ((N + H + 1) * (3 * Real.exp (-s)))
      ≤ 10 ^ 10 * (1 + C) * (3 * (1 + 9 * Cm)) * Real.log N ^ 2 * (N + H + 1)
          * Real.exp (-(2 * s / 3)) := by
    have hK0 : 0 ≤ 10 ^ 10 * (1 + C) * Real.log N ^ 2 * (N + H + 1) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hfac hK0
    calc (1 + W) * (10 ^ 10 * (1 + C) * Real.log N ^ 2) * ((N + H + 1) * (3 * Real.exp (-s)))
        = 10 ^ 10 * (1 + C) * Real.log N ^ 2 * (N + H + 1) * ((1 + W) * (3 * Real.exp (-s))) := by
          ring
      _ ≤ 10 ^ 10 * (1 + C) * Real.log N ^ 2 * (N + H + 1)
            * (3 * (1 + 9 * Cm) * Real.exp (-(2 * s / 3))) := h1
      _ = _ := by ring
  exact hbase.trans (hshaped.trans (hstep.trans hfin))

end

end RHTower.Sieve

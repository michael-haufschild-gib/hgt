import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovInvZeta
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovPrimeNumberTheorem
import GaloisForLFunctions.RHTower.Sieve.PerronSharpSubstitution
import GaloisForLFunctions.RHTower.Sieve.SmoothVsSharp

/-!
# The Möbius sum at Vinogradov–Korobov strength

The contour of `∑ μ(n) w(n) = (2πi)⁻¹ ∫ M̃(s)/ζ(s) ds` is run on the rectangle with left edge
`c = 1 - min(δ, w(T+1))/4`, right edge `d = 1 + 1/log T`, height `T = vkHeight N`; there is no
main term.  On the left and horizontal edges `‖1/ζ‖ ≤ C(log(T+1))^7(1 + 2/w(T+1))^7 ≪ (log N)^{14}`,
on the right edge `‖1/ζ‖ ≤ e^{11/2}(1 + log T)`.  With the edge powers of the prime number theorem
contour, every term is `≪ (log N)^{14}(N + H + 1)e^{-2s/3}`, the smoothing costs `H + 1`, and
`(log N)^{14} ≤ s^{28}` is absorbed:

```text
|∑_{n≤N} μ(n)| ≤ B · N · exp(-c (log N)^{3/5} (log log N)^{-5/3}),      c = 1/(288·10⁸).
```

The corpus Möbius rate had exponent `1/3`.
-/

namespace RHTower.Sieve

open Complex Filter Topology Asymptotics GaloisForLFunctions.HTGeometry

noncomputable section

/-- `L^k e^{-s/6} ≤ (2k)!·12^{2k}·e^{-s/12}` once `√L ≤ s`. -/
theorem vk_log_pow_absorb (k : ℕ) {L s : ℝ} (hL : 0 ≤ L) (hs : Real.sqrt L ≤ s) :
    L ^ k * Real.exp (-(s / 6))
      ≤ ((2 * k).factorial * 12 ^ (2 * k) : ℝ) * Real.exp (-(s / 12)) := by
  have hs0 : 0 ≤ s := le_trans (Real.sqrt_nonneg L) hs
  have hLk : L ^ k ≤ s ^ (2 * k) := by
    have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg L) hs (2 * k)
    have h2 : Real.sqrt L ^ (2 * k) = L ^ k := by rw [pow_mul, Real.sq_sqrt hL]
    linarith
  have hfact := Real.pow_div_factorial_le_exp (s / 12) (by positivity) (2 * k)
  have hF : (0 : ℝ) < (2 * k).factorial := by exact_mod_cast Nat.factorial_pos _
  have hsk : s ^ (2 * k) ≤ ((2 * k).factorial * 12 ^ (2 * k) : ℝ) * Real.exp (s / 12) := by
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at hfact
    calc s ^ (2 * k) ≤ Real.exp (s / 12) * (12 ^ (2 * k) * (2 * k).factorial) := hfact
      _ = _ := by ring
  have hsplit : Real.exp (s / 12) * Real.exp (-(s / 6)) = Real.exp (-(s / 12)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE := Real.exp_pos (-(s / 6))
  calc L ^ k * Real.exp (-(s / 6)) ≤ s ^ (2 * k) * Real.exp (-(s / 6)) :=
        mul_le_mul_of_nonneg_right hLk hE.le
    _ ≤ ((2 * k).factorial * 12 ^ (2 * k) : ℝ) * Real.exp (s / 12) * Real.exp (-(s / 6)) :=
        mul_le_mul_of_nonneg_right hsk hE.le
    _ = _ := by rw [mul_assoc, hsplit]

/-- The four Möbius contour terms against one shape. -/
theorem vk_moebius_terms_le {Md V W W' Z Y E T d c Zd Zc Yc : ℝ}
    (hMd : 0 ≤ Md) (hV : 0 ≤ V) (hW : 0 ≤ W) (hW' : 0 ≤ W') (hE : 0 ≤ E) (hY0 : 0 ≤ Y)
    (hYZ : Y ≤ Z) (hT1 : 1 ≤ T) (hc : 1 / 2 ≤ c) (hwd : d - c ≤ 1)
    (hZd0 : 0 ≤ Zd) (hZd : Zd ≤ Z * E * T) (hZc : Zc ≤ Z * E) (hYc : Yc ≤ Y * E) :
    2 * (Md * (W * Zd)) / T + V * (W' * Zd) / T ^ (0 + 1) * (d - c)
        + V * (W' * Zd) / T ^ (0 + 1) * (d - c) + V * (2 * (Yc / c) + 2 * (W * Zc))
      ≤ (2 * Md * W + 2 * V * W' + V * (4 + 2 * W)) * (Z * E) := by
  have hT0 : 0 < T := by linarith
  have hZ0 : 0 ≤ Z := le_trans hY0 hYZ
  have hZE : 0 ≤ Z * E := mul_nonneg hZ0 hE
  have hZdT : Zd / T ≤ Z * E := by
    rw [div_le_iff₀ hT0]; linarith
  have hpow : T ^ (0 + 1) = T := by norm_num
  have h1 : 2 * (Md * (W * Zd)) / T ≤ 2 * Md * W * (Z * E) := by
    have : 2 * (Md * (W * Zd)) / T = 2 * Md * W * (Zd / T) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hZdT (by positivity)
  have h2 : V * (W' * Zd) / T ^ (0 + 1) * (d - c) ≤ V * W' * (Z * E) := by
    rw [hpow]
    have : V * (W' * Zd) / T * (d - c) = V * W' * (Zd / T) * (d - c) := by ring
    rw [this]
    have hq : 0 ≤ V * W' * (Zd / T) := by positivity
    calc V * W' * (Zd / T) * (d - c) ≤ V * W' * (Zd / T) * 1 :=
          mul_le_mul_of_nonneg_left hwd hq
      _ = V * W' * (Zd / T) := by ring
      _ ≤ V * W' * (Z * E) := mul_le_mul_of_nonneg_left hZdT (by positivity)
  have hc0 : 0 < c := by linarith
  have hYc' : Yc / c ≤ 2 * (Z * E) := by
    rw [div_le_iff₀ hc0]
    have : Y * E ≤ Z * E := mul_le_mul_of_nonneg_right hYZ hE
    nlinarith
  have h4 : V * (2 * (Yc / c) + 2 * (W * Zc)) ≤ V * (4 + 2 * W) * (Z * E) := by
    have : 2 * (Yc / c) + 2 * (W * Zc) ≤ (4 + 2 * W) * (Z * E) := by
      have hWZ : W * Zc ≤ W * (Z * E) := mul_le_mul_of_nonneg_left hZc hW
      nlinarith
    calc V * (2 * (Yc / c) + 2 * (W * Zc)) ≤ V * ((4 + 2 * W) * (Z * E)) :=
          mul_le_mul_of_nonneg_left this hV
      _ = _ := by ring
  calc 2 * (Md * (W * Zd)) / T + V * (W' * Zd) / T ^ (0 + 1) * (d - c)
        + V * (W' * Zd) / T ^ (0 + 1) * (d - c) + V * (2 * (Yc / c) + 2 * (W * Zc))
      ≤ 2 * Md * W * (Z * E) + V * W' * (Z * E) + V * W' * (Z * E)
          + V * (4 + 2 * W) * (Z * E) := by linarith
    _ = _ := by ring


/-- The smoothing width `H = N e^{-s/6}` and its prices, for `0 ≤ s ≤ log N`. -/
theorem vk_width_facts {N H s Cm C' : ℝ} (hN3 : 3 ≤ N) (hs0 : 0 ≤ s) (hsL : s ≤ Real.log N)
    (hH : H = N * Real.exp (-(s / 6))) (hCm : 0 ≤ Cm) (hC' : 0 ≤ C') :
    1 ≤ H ∧ H ≤ N
      ∧ Cm / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) ≤ Cm * (9 * Real.exp (s / 3))
      ∧ C' / H ^ (1 : ℕ) * (N + H + 1) ^ (1 : ℕ) ≤ C' * (3 * Real.exp (s / 3))
      ∧ H + 1 ≤ 2 * ((N + H + 1) * Real.exp (-(s / 6))) := by
  have hN0 : 0 < N := by linarith
  have hρ1 : 1 ≤ Real.exp (s / 6) := Real.one_le_exp (by linarith)
  have hHpos : 0 < H := by rw [hH]; positivity
  have hNe : 1 ≤ N * Real.exp (-(s / 6)) := by
    have h1 : Real.exp (-Real.log N) ≤ Real.exp (-(s / 6)) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log hN0] at h1
    calc (1 : ℝ) = N * N⁻¹ := (mul_inv_cancel₀ hN0.ne').symm
      _ ≤ N * Real.exp (-(s / 6)) := mul_le_mul_of_nonneg_left h1 hN0.le
  have hH1 : 1 ≤ H := by rw [hH]; exact hNe
  have hHN : H ≤ N := by
    rw [hH]
    exact mul_le_of_le_one_right hN0.le (Real.exp_le_one_iff.mpr (by linarith))
  have hNH : N / H = Real.exp (s / 6) := by
    rw [hH, ← div_div, div_self hN0.ne', one_div, ← Real.exp_neg, neg_neg]
  have h63 : Real.exp (s / 6) ≤ Real.exp (s / 3) := Real.exp_le_exp.mpr (by linarith)
  have hρsq : (Real.exp (s / 6) + 2) ^ (2 : ℕ) ≤ 9 * Real.exp (s / 3) := by
    have h2 : Real.exp (s / 6) ^ 2 = Real.exp (s / 3) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    nlinarith [hρ1, h2]
  refine ⟨hH1, hHN, width_price_le_gen hH1 hN0.le (le_of_eq hNH) hCm hρsq, ?_, ?_⟩
  · rw [pow_one, pow_one, div_mul_eq_mul_div, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC'
    have h1 : (N + H + 1) / H = N / H + 1 + 1 / H := by field_simp
    have h2 : 1 / H ≤ 1 := by rw [div_le_one hHpos]; exact hH1
    rw [h1, hNH]
    linarith
  · have h3 : N * Real.exp (-(s / 6)) ≤ (N + H + 1) * Real.exp (-(s / 6)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    rw [← hH] at hNe h3
    linarith

/-- **The `1/ζ` contour data on the Vinogradov–Korobov rectangle.** -/
theorem vk_moebius_invZeta_data {Ci δ K₀ T c d : ℝ}
    (hzf : ∀ (s : ℂ) (K : ℝ), K₀ ≤ K → |s.im| ≤ K →
      1 - min δ (RHTower.vkHadamardWidth (K + 1)) / 4 ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0)
    (hinv : ∀ (s : ℂ) (K : ℝ), K₀ ≤ K → |s.im| ≤ K →
      1 - min δ (RHTower.vkHadamardWidth (K + 1)) / 4 ≤ s.re → s.re ≤ 2 →
      ‖invZeta s‖ ≤ Ci * Real.log (K + 1) ^ 7 * (1 + 2 / RHTower.vkHadamardWidth (K + 1)) ^ 7)
    (hK : K₀ ≤ T) (hT0 : 0 < T) (hc : 1 - min δ (RHTower.vkHadamardWidth (T + 1)) / 4 = c)
    (hcd : c ≤ d) (hd2 : d ≤ 2) :
    (∀ z ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, z ≠ 1 → riemannZeta z ≠ 0)
    ∧ (∀ x ∈ Set.Ioc c d, ‖invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
        ≤ Ci * Real.log (T + 1) ^ 7 * (1 + 2 / RHTower.vkHadamardWidth (T + 1)) ^ 7)
    ∧ (∀ x ∈ Set.Ioc c d, ‖invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖
        ≤ Ci * Real.log (T + 1) ^ 7 * (1 + 2 / RHTower.vkHadamardWidth (T + 1)) ^ 7)
    ∧ (∀ y ∈ Set.Icc (-T) T, ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ Ci * Real.log (T + 1) ^ 7 * (1 + 2 / RHTower.vkHadamardWidth (T + 1)) ^ 7) := by
  have hTT : (-T : ℝ) ≤ T := by linarith
  have hxre : ∀ x v : ℝ, ((x : ℂ) + ((v : ℝ) : ℂ) * Complex.I).re = x := by intro x v; simp
  have hxim : ∀ x v : ℝ, ((x : ℂ) + ((v : ℝ) : ℂ) * Complex.I).im = v := by intro x v; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz hne
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hcd, Set.uIcc_of_le hTT] at hz
    exact hzf z T hK (abs_le.mpr ⟨hz.2.1, hz.2.2⟩) (by rw [hc]; exact hz.1.1) hne
  · intro x hx
    refine hinv _ T hK ?_ ?_ ?_
    · rw [hxim, abs_of_pos hT0]
    · rw [hxre, hc]; exact hx.1.le
    · rw [hxre]; linarith [hx.2]
  · intro x hx
    refine hinv _ T hK ?_ ?_ ?_
    · rw [hxim, abs_neg, abs_of_pos hT0]
    · rw [hxre, hc]; exact hx.1.le
    · rw [hxre]; linarith [hx.2]
  · intro y hy
    refine hinv _ T hK ?_ ?_ ?_
    · rw [hxim]; exact abs_le.mpr ⟨hy.1, hy.2⟩
    · rw [hxre, hc]
    · rw [hxre]; linarith

/-- **The Möbius contour against the edge shape.** -/
theorem vk_moebius_contour_le {N H T c d Md V Cm C' E : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hd1 : 1 < d) (hc0 : 0 < c) (hcd : c ≤ d) (hT1 : 1 ≤ T) (hMd0 : 0 ≤ Md) (hV0 : 0 ≤ V)
    (hCm : 0 ≤ Cm) (hC' : 0 ≤ C') (hE : 0 ≤ E) (hc : 1 / 2 ≤ c) (hc1 : c ≤ 1) (hwd : d - c ≤ 1)
    (hzfr : ∀ z ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, z ≠ 1 → riemannZeta z ≠ 0)
    (hFd : ∀ y : ℝ, ‖invZeta ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Md)
    (hFt : ∀ x ∈ Set.Ioc c d, ‖invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ V)
    (hFb : ∀ x ∈ Set.Ioc c d, ‖invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ V)
    (hFc : ∀ y ∈ Set.Icc (-T) T, ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ V)
    (hdec1 : ∀ σ : ℝ, ∀ s : ℂ, 0 < s.re → s.re ≤ σ →
      |s.im| ^ (1 + 1)
        * ‖mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖
        ≤ Cm / H ^ (1 + 1) * (N + H + 1) ^ (1 + 1 : ℕ) * (N + H + 1) ^ σ)
    (hdec0 : ∀ σ : ℝ, ∀ s : ℂ, 0 < s.re → s.re ≤ σ →
      |s.im| ^ (0 + 1)
        * ‖mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖
        ≤ C' / H ^ (0 + 1) * (N + H + 1) ^ (0 + 1 : ℕ) * (N + H + 1) ^ σ)
    (hZd : (N + H + 1) ^ d ≤ (N + H + 1) * E * T) (hZc : (N + H + 1) ^ c ≤ (N + H + 1) * E)
    (hYc : (N + H) ^ c ≤ (N + H) * E) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ)
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ (2 * Md * (Cm / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ))
          + 2 * V * (C' / H ^ (1 : ℕ) * (N + H + 1) ^ (1 : ℕ))
          + V * (4 + 2 * (Cm / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ)))) * ((N + H + 1) * E) := by
  have hFccont := continuousOn_invZeta_left_line hc1 hd1.le hzfr
  have hbase := norm_tsum_moebius_smoothWeight_le_sharp
    (C₁ := Cm / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) * (N + H + 1) ^ d)
    (C₂ := C' / H ^ (1 : ℕ) * (N + H + 1) ^ (1 : ℕ) * (N + H + 1) ^ d)
    (C₃ := Cm / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) * (N + H + 1) ^ c)
    hN hH 0 hd1 hc0 hcd hT1 hMd0 hV0 hV0 hzfr hFd hFt hFb hFc hFccont
    (fun z hz hzd => hdec1 d z hz hzd) (fun z hz hzd => hdec0 d z hz hzd)
    (fun z hz hzc => hdec1 c z hz hzc)
  have hZ0 : 0 < N + H + 1 := by linarith
  have hshaped := vk_moebius_terms_le (Md := Md) (V := V)
    (W := Cm / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ)) (W' := C' / H ^ (1 : ℕ) * (N + H + 1) ^ (1 : ℕ))
    (Z := N + H + 1) (Y := N + H) (E := E) (T := T) (d := d) (c := c) hMd0 hV0
    (by positivity) (by positivity) hE (by linarith) (by linarith) hT1 hc hwd
    (Real.rpow_nonneg hZ0.le _) hZd hZc hYc
  calc _ ≤ _ := hbase
    _ = _ := by ring
    _ ≤ _ := hshaped

/-- The Möbius coefficient against `K L^{14} e^{s/3}`. -/
theorem vk_moebius_coeff_le {Md V W W' L Cm C' Vb E3 : ℝ} (hCm : 0 ≤ Cm)
    (hVb : 0 ≤ Vb) (hL1 : 1 ≤ L) (hE31 : 1 ≤ E3) (hW0 : 0 ≤ W) (hW'0 : 0 ≤ W')
    (hMd : Md ≤ 2 * Real.exp (22 / 4) * L) (hV : V ≤ Vb * L ^ 14)
    (hW : W ≤ Cm * (9 * E3)) (hW' : W' ≤ C' * (3 * E3)) :
    2 * Md * W + 2 * V * W' + V * (4 + 2 * W)
      ≤ (36 * Real.exp (22 / 4) * Cm + Vb * (6 * C' + 4 + 18 * Cm)) * L ^ 14 * E3 := by
  have hL14 : L ≤ L ^ 14 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 14 := pow_le_pow_right₀ hL1 (by norm_num)
  have hE0 : 0 ≤ E3 := by linarith
  have hEe := Real.exp_pos (22 / 4)
  have hA : 2 * Md * W ≤ 36 * Real.exp (22 / 4) * Cm * L ^ 14 * E3 := by
    have h1 := mul_le_mul hMd hW hW0 (by positivity)
    have h2 : 36 * Real.exp (22 / 4) * Cm * L * E3 ≤ 36 * Real.exp (22 / 4) * Cm * L ^ 14 * E3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL14 (by positivity)) hE0
    calc 2 * Md * W = 2 * (Md * W) := by ring
      _ ≤ 2 * (2 * Real.exp (22 / 4) * L * (Cm * (9 * E3))) := by linarith only [h1]
      _ = 36 * Real.exp (22 / 4) * Cm * L * E3 := by ring
      _ ≤ _ := h2
  have hB : 2 * V * W' ≤ 6 * C' * Vb * L ^ 14 * E3 := by
    have h1 := mul_le_mul hV hW' hW'0 (by positivity)
    calc 2 * V * W' = 2 * (V * W') := by ring
      _ ≤ 2 * (Vb * L ^ 14 * (C' * (3 * E3))) := by linarith only [h1]
      _ = _ := by ring
  have hC : V * (4 + 2 * W) ≤ Vb * L ^ 14 * ((4 + 18 * Cm) * E3) := by
    have h4 : 4 + 2 * W ≤ (4 + 18 * Cm) * E3 := by
      have : (4 + 18 * Cm) * E3 = 4 * E3 + 2 * (Cm * (9 * E3)) := by ring
      rw [this]; linarith only [hW, hE31]
    exact mul_le_mul hV h4 (by linarith only [hW0]) (by positivity)
  have hKe : (36 * Real.exp (22 / 4) * Cm + Vb * (6 * C' + 4 + 18 * Cm)) * L ^ 14 * E3
      = 36 * Real.exp (22 / 4) * Cm * L ^ 14 * E3 + 6 * C' * Vb * L ^ 14 * E3
        + Vb * L ^ 14 * ((4 + 18 * Cm) * E3) := by ring
  linarith only [hA, hB, hC, hKe]

/-- The scalar, the smoothing and the collapse: `‖P‖ ≤ (3K + 2) L^{14} Z e^{-s/6}`. -/
theorem vk_moebius_final_le {A P : ℂ} {K L Z H s : ℝ} (hK : 0 ≤ K) (hL1 : 1 ≤ L) (hZ : 0 ≤ Z)
    (hs : 0 ≤ s)
    (hsmooth : ‖(2 * Real.pi : ℝ) • A‖ ≤ 3 * K * L ^ 14 * Z * Real.exp (-(2 * s / 3)))
    (htr : ‖A - P‖ ≤ H + 1) (hHZ : H + 1 ≤ 2 * (Z * Real.exp (-(s / 6)))) :
    ‖P‖ ≤ (3 * K + 2) * L ^ 14 * Z * Real.exp (-(s / 6)) := by
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  have hscal : ‖A‖ ≤ ‖(2 * Real.pi : ℝ) • A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact le_mul_of_one_le_left (norm_nonneg A) hπ1
  have hPA : ‖P‖ ≤ ‖A‖ + ‖A - P‖ := by
    have := norm_sub_norm_le P A
    rw [norm_sub_rev] at this
    linarith only [this]
  have hE23 : Real.exp (-(2 * s / 3)) ≤ Real.exp (-(s / 6)) :=
    Real.exp_le_exp.mpr (by linarith only [hs])
  have hQ0 : 0 ≤ Z * Real.exp (-(s / 6)) := by positivity
  have h1 : 3 * K * L ^ 14 * Z * Real.exp (-(2 * s / 3))
      ≤ 3 * K * L ^ 14 * (Z * Real.exp (-(s / 6))) := by
    rw [show 3 * K * L ^ 14 * Z * Real.exp (-(2 * s / 3))
      = 3 * K * L ^ 14 * (Z * Real.exp (-(2 * s / 3))) by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE23 hZ) (by positivity)
  have hL141 : 1 ≤ L ^ 14 := one_le_pow₀ hL1
  have h2 : 2 * (Z * Real.exp (-(s / 6))) ≤ 2 * L ^ 14 * (Z * Real.exp (-(s / 6))) := by
    have := mul_le_mul_of_nonneg_right hL141 hQ0
    linarith only [this]
  have hgoal : (3 * K + 2) * L ^ 14 * Z * Real.exp (-(s / 6))
      = 3 * K * L ^ 14 * (Z * Real.exp (-(s / 6))) + 2 * L ^ 14 * (Z * Real.exp (-(s / 6))) := by
    ring
  rw [hgoal]
  linarith only [hsmooth, hscal, hPA, htr, hHZ, h1, h2]

/-- **The Möbius sum against the contour shape.**  With `H = vkWidth N`, `s = vkSaving N`:
`‖∑_{n≤N} μ(n)‖ ≤ B (log N)^{14} (N + H + 1) e^{-s/6}`. -/
theorem exists_norm_sum_moebius_vk_shape :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)‖
        ≤ B * Real.log N ^ 14 * (N + vkWidth N + 1) * Real.exp (-(vkSaving N / 6)) := by
  obtain ⟨Cm, hCm, hdec1⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨C', hC', hdec0⟩ := exists_bound_mellin_smoothWeight_uniform_upto 0
  obtain ⟨Ci, δ, K₀, hCi, hδ, hK₀3, -, hzf, hinv⟩ := exists_bound_invZeta_vk_uniform
  obtain ⟨Vb, hVbdef⟩ : ∃ Vb, Vb = Ci * 2 ^ 7 * (13 * 10 ^ 8) ^ 7 := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = 36 * Real.exp (22 / 4) * Cm + Vb * (6 * C' + 4 + 18 * Cm) :=
    ⟨_, rfl⟩
  have hVb0 : 0 ≤ Vb := by rw [hVbdef]; positivity
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  refine ⟨3 * K + 2, by positivity, ?_⟩
  filter_upwards [eventually_vk_conditions hδ (Real.log K₀)] with N hcond
  obtain ⟨hN3, hL3, hLgK, hLg8, hLg2, hLgL, hw0, hwinv, hu0, hu8, hui, hsu⟩ := hcond
  have hsave : vkSaving N = Real.log (vkHeight N) / 2 := vkSaving_eq N
  have hH : vkWidth N = N * Real.exp (-(vkSaving N / 6)) := rfl
  have hT0 : 0 < vkHeight N := Real.exp_pos _
  have hu : vkUniformRegWidth δ (vkHeight N)
      = min δ (RHTower.vkHadamardWidth (vkHeight N + 1)) / 2 := rfl
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
  obtain ⟨hH1, hHN, hWle, hW'le, hHZ⟩ :=
    vk_width_facts hN3 hs0 (by rw [hsave]; linarith) hH hCm hC'
  have hHpos : 0 < H := by linarith
  -- the abscissae
  have hd1 := one_lt_chebRightTwo hLg8
  have hd98 := chebRightTwo_le hLg8
  have hinvLg : 1 / Real.log T ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hcd : 1 - u / 2 ≤ chebRightTwo T := by linarith
  have hwd1 : chebRightTwo T - (1 - u / 2) ≤ 1 := by rw [chebRightTwo]; linarith
  have hc2 : 1 - min δ (RHTower.vkHadamardWidth (T + 1)) / 4 = 1 - u / 2 := by rw [hu]; ring
  obtain ⟨hzfr, hFt, hFb, hFc⟩ := vk_moebius_invZeta_data hzf hinv hK₀T hT0 hc2 hcd (by linarith)
  have hFd : ∀ y : ℝ, ‖invZeta ((chebRightTwo T : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ Real.exp (22 / 4) * (1 + Real.log T) := by
    intro y
    have h := norm_invZeta_right_le (d := chebRightTwo T) (y := y) hd1
    rwa [show chebRightTwo T - 1 = 1 / Real.log T by rw [chebRightTwo]; ring,
      one_div_one_div] at h
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
  have hsu' : s ≤ u / 2 * Real.log N := by linarith
  have hZc := vk_rpow_left_le (Z := N + H + 1) hN0 (by linarith) (by linarith) hsu'
  have hYc := vk_rpow_left_le (Z := N + H) hN0 (by linarith) (by linarith) hsu'
  -- the edge sizes
  have hw0' : 0 < RHTower.vkHadamardWidth (T + 1) := hw0
  have hV0 : 0 ≤ Ci * Real.log (T + 1) ^ 7 * (1 + 2 / RHTower.vkHadamardWidth (T + 1)) ^ 7 := by
    have h2w : 0 ≤ 2 / RHTower.vkHadamardWidth (T + 1) := div_nonneg (by norm_num) hw0'.le
    have hlog0 : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
    exact mul_nonneg (mul_nonneg hCi.le (pow_nonneg hlog0 7)) (pow_nonneg (by linarith) 7)
  have hMd0 : 0 ≤ Real.exp (22 / 4) * (1 + Real.log T) := by
    have : 0 ≤ Real.log T := by linarith
    positivity
  have hsmooth0 := vk_moebius_contour_le hN0 hHpos hd1 (by linarith) hcd hT1 hMd0 hV0 hCm hC'
    (by positivity : (0 : ℝ) ≤ 3 * Real.exp (-s)) (by linarith) (by linarith) hwd1 hzfr hFd hFt
    hFb hFc
    (hdec1 N H hN0 hHpos) (hdec0 N H hN0 hHpos) hZd hZc hYc
  have hMdb : Real.exp (22 / 4) * (1 + Real.log T) ≤ 2 * Real.exp (22 / 4) * Real.log N := by
    have h1 : 1 + Real.log T ≤ 2 * Real.log N := by linarith only [hLgL, hL1]
    calc Real.exp (22 / 4) * (1 + Real.log T) ≤ Real.exp (22 / 4) * (2 * Real.log N) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 2 * Real.exp (22 / 4) * Real.log N := by ring
  have hlogT1 : Real.log (T + 1) ≤ 2 * Real.log N := by
    have h2T : Real.log (T + 1) ≤ Real.log (2 * T) :=
      Real.log_le_log (by linarith only [hT1]) (by linarith only [hT1])
    rw [Real.log_mul (by norm_num) hT0.ne'] at h2T
    have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith only [this]
    linarith only [h2T, hlog2, hLgL, hLg8]
  have hVb' : Ci * Real.log (T + 1) ^ 7 * (1 + 2 / RHTower.vkHadamardWidth (T + 1)) ^ 7
      ≤ Vb * Real.log N ^ 14 := by
    have hlog0 : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith only [hT1])
    have h1 : Real.log (T + 1) ^ 7 ≤ (2 * Real.log N) ^ 7 := pow_le_pow_left₀ hlog0 hlogT1 7
    have h2w : 0 ≤ 2 / RHTower.vkHadamardWidth (T + 1) := div_nonneg (by norm_num) hw0'.le
    have hw2 : 2 / RHTower.vkHadamardWidth (T + 1) ≤ 12 * 10 ^ 8 * Real.log N := by
      have : 2 / RHTower.vkHadamardWidth (T + 1) = 2 * (1 / RHTower.vkHadamardWidth (T + 1)) := by
        ring
      rw [this]; linarith only [hwinv]
    have hb0 : (0 : ℝ) ≤ 1 + 2 / RHTower.vkHadamardWidth (T + 1) := by linarith only [h2w]
    have hb : 1 + 2 / RHTower.vkHadamardWidth (T + 1) ≤ 13 * 10 ^ 8 * Real.log N := by
      linarith only [hw2, hL1]
    have h2 := pow_le_pow_left₀ hb0 hb 7
    have hp0 := pow_nonneg hb0 7
    have hq0 : (0 : ℝ) ≤ Ci * (2 * Real.log N) ^ 7 := by positivity
    have h3 := mul_le_mul (mul_le_mul_of_nonneg_left h1 hCi.le) h2 hp0 hq0
    have h4 : Ci * (2 * Real.log N) ^ 7 * (13 * 10 ^ 8 * Real.log N) ^ 7
        = Vb * Real.log N ^ 14 := by rw [hVbdef]; ring
    linarith only [h3, h4]
  have hE31 : 1 ≤ Real.exp (s / 3) := Real.one_le_exp (by linarith only [hs0])
  have hcoef := vk_moebius_coeff_le hCm hVb0 hL1 hE31 (by positivity) (by positivity)
    hMdb hVb' hWle hW'le
  rw [← hKdef] at hcoef
  have hZE0 : 0 ≤ (N + H + 1) * (3 * Real.exp (-s)) := by positivity
  have hstep := mul_le_mul_of_nonneg_right hcoef hZE0
  have hcollapse : K * Real.log N ^ 14 * Real.exp (s / 3) * ((N + H + 1) * (3 * Real.exp (-s)))
      = 3 * K * Real.log N ^ 14 * (N + H + 1) * Real.exp (-(2 * s / 3)) := by
    have : Real.exp (s / 3) * Real.exp (-s) = Real.exp (-(2 * s / 3)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc K * Real.log N ^ 14 * Real.exp (s / 3) * ((N + H + 1) * (3 * Real.exp (-s)))
        = 3 * K * Real.log N ^ 14 * (N + H + 1) * (Real.exp (s / 3) * Real.exp (-s)) := by ring
      _ = _ := by rw [this]
  exact vk_moebius_final_le hK0 hL1 hZ0.le hs0
    (hsmooth0.trans (hstep.trans (le_of_eq hcollapse)))
    (norm_tsum_smoothWeight_sub_sum_le hN0 hHpos) hHZ


/-- **The Möbius sum at Vinogradov–Korobov strength**:

```text
|∑_{n≤N} μ(n)| ≤ B · N · exp(-κ·(log N)^{3/5}(log log N)^{-5/3}/24),      κ = 1/(12·10⁸).
``` -/
theorem exists_abs_sum_moebius_le_vk_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      |∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℝ)|
        ≤ B * N * Real.exp (-(vkKappa * vkScale N / 24)) := by
  obtain ⟨B, hB, hshape⟩ := exists_norm_sum_moebius_vk_shape
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ, F = ((2 * 14).factorial * 12 ^ (2 * 14) : ℝ) := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by rw [hFdef]; positivity
  refine ⟨3 * F * B, by positivity, ?_⟩
  filter_upwards [hshape, eventually_vk_conditions one_pos 0] with N hN hcond
  obtain ⟨hN3, hL3, -, -, hLg2, -, -, -, -, -, -, -⟩ := hcond
  have hN0 : 0 < N := by linarith
  have hsave : vkSaving N = Real.log (vkHeight N) / 2 := vkSaving_eq N
  have hsq : Real.sqrt (Real.log N) ≤ vkSaving N := by rw [hsave]; linarith
  have habs := vk_log_pow_absorb 14 (by linarith : (0 : ℝ) ≤ Real.log N) hsq
  rw [← hFdef] at habs
  have hs0 : 0 ≤ vkSaving N := le_trans (Real.sqrt_nonneg _) hsq
  have hH0 : 0 ≤ vkWidth N := by unfold vkWidth; positivity
  have hHN : vkWidth N ≤ N := by
    unfold vkWidth
    exact mul_le_of_le_one_right hN0.le (Real.exp_le_one_iff.mpr (by linarith))
  have hZ3 : N + vkWidth N + 1 ≤ 3 * N := by linarith
  have hexp : Real.exp (-(vkSaving N / 12)) = Real.exp (-(vkKappa * vkScale N / 24)) := by
    rw [vkSaving]; congr 1; ring
  have hcast : (((∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℝ)) : ℝ) : ℂ)
      = ∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ) := by
    push_cast; rfl
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs] at hN
  have hstep : B * Real.log N ^ 14 * (N + vkWidth N + 1) * Real.exp (-(vkSaving N / 6))
      ≤ B * (N + vkWidth N + 1) * (F * Real.exp (-(vkSaving N / 12))) := by
    have h1 := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ B * (N + vkWidth N + 1))
    calc B * Real.log N ^ 14 * (N + vkWidth N + 1) * Real.exp (-(vkSaving N / 6))
        = B * (N + vkWidth N + 1) * (Real.log N ^ 14 * Real.exp (-(vkSaving N / 6))) := by ring
      _ ≤ _ := h1
  have hstep2 : B * (N + vkWidth N + 1) * (F * Real.exp (-(vkSaving N / 12)))
      ≤ 3 * F * B * N * Real.exp (-(vkKappa * vkScale N / 24)) := by
    rw [hexp]
    have hE := Real.exp_pos (-(vkKappa * vkScale N / 24))
    have h1 := mul_le_mul_of_nonneg_left hZ3 hB
    have h2 := mul_le_mul_of_nonneg_right h1
      (by positivity : 0 ≤ F * Real.exp (-(vkKappa * vkScale N / 24)))
    calc B * (N + vkWidth N + 1) * (F * Real.exp (-(vkKappa * vkScale N / 24)))
        ≤ B * (3 * N) * (F * Real.exp (-(vkKappa * vkScale N / 24))) := h2
      _ = 3 * F * B * N * Real.exp (-(vkKappa * vkScale N / 24)) := by ring
  linarith [hN, hstep, hstep2]

/-- **The Möbius sum at Vinogradov–Korobov strength**, in `IsBigO` form:

```text
∑_{n≤x} μ(n)  =O[atTop]  x · exp(-c·(log x)^{3/5}·(log log x)^{-5/3}).
``` -/
theorem sum_moebius_isBigO_vinogradovKorobov :
    ∃ c > 0, (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (ArithmeticFunction.moebius n : ℝ))
      =O[atTop] fun x : ℝ =>
        x * Real.exp (-c * (Real.log x ^ ((3 : ℝ) / 5)
          * Real.log (Real.log x) ^ (-((5 : ℝ) / 3)))) := by
  obtain ⟨B, hB, hrate⟩ := exists_abs_sum_moebius_le_vk_rate
  refine ⟨vkKappa / 24, by have := vkKappa_pos; positivity, Asymptotics.IsBigO.of_bound B ?_⟩
  filter_upwards [hrate, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  have hcongr : Real.exp (-(vkKappa * vkScale N / 24))
      = Real.exp (-(vkKappa / 24) * (Real.log N ^ ((3 : ℝ) / 5)
          * Real.log (Real.log N) ^ (-((5 : ℝ) / 3)))) := by
    rw [vkScale]; congr 1; ring
  have hgnorm : ‖N * Real.exp (-(vkKappa / 24) * (Real.log N ^ ((3 : ℝ) / 5)
        * Real.log (Real.log N) ^ (-((5 : ℝ) / 3))))‖
      = N * Real.exp (-(vkKappa / 24) * (Real.log N ^ ((3 : ℝ) / 5)
        * Real.log (Real.log N) ^ (-((5 : ℝ) / 3)))) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [Real.norm_eq_abs, hgnorm]
  rw [hcongr] at hN
  linarith [hN]

end

end RHTower.Sieve

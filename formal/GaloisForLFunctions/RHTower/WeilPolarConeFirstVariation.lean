import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# First variation of the polar Weil cone at the polar near-null vectors

Let `Λ + w` and `Λ − w` both be Weil-positive on polar-constrained tests (`WeilPositive`), with
`Σ |w(n)| n^{−2} < ∞`. Put `L_c = 1 − α_c(τ_c + τ_{−c})`, `α_c = 1/(2 cosh(c/2))`, and let
`G_w(s) = Σ_{n ≥ 2} w(n) n^{−1/2} (Φ(s + log n) + Φ(s − log n))` be the Riemann-kernel transform of
`w` (`weightKernelTransform`).

**Theorem** (`integral_mul_polarShift_weightKernelTransform_eq_zero`). For every shift `c ≥ 0` and
every real polar `C²` compactly supported `h`, `∫ h · L_c G_w = 0`.

The polar second difference `u = L_c(Φχ_L)` is a polar near-null vector: its zero side is
`≤ 9 (5/4) S E_L²` (`norm_W_polarRiemannDifference_le`). Two-sided polar positivity gives
`|T_w(f)| ≤ Re W(f, f)` on polar tests (`abs_atomPairing_le_of_weilPositive`). Along `f = u + εh` the
first variation `T_w(u, h)` is therefore `O(E_L²/ε + ε)`, so its limit `T_w(L_cΦ, h) = ∫ h · L_c G_w`
vanishes.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## Two-sided polar positivity -/

/-- The level-`a` atom sum of a real test equals its atom pairing. -/
theorem atomPairing_eq_sum_of_support (w : ℕ → ℝ) {F : ℝ → ℝ} {a : ℝ}
    (hF : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFs : tsupport (fun u => (F u : ℂ)) ⊆ Icc (-a) a) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) (Real.log n) +
          EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) (-Real.log n)).re =
      atomPairing w (crossCorr F F) := by
  obtain ⟨-, -, hks, -, -⟩ := weilTest_self_data hF hFs
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  have hk : ∀ y, EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) y =
      ((crossCorr F F y : ℝ) : ℂ) := fun y => weilTest_ofReal_eq F y
  have hvan : ∀ n : ℕ, 2 ≤ n → N < n →
      crossCorr F F (Real.log n) = 0 ∧ crossCorr F F (-Real.log n) = 0 := by
    intro n hn2 hn
    have hn' : Real.exp (2 * a) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * a))
      have h2 : ((N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn'
    have hlog : 2 * a < Real.log n := by rw [Real.lt_log_iff_exp_lt hnpos]; exact hn'
    have hout : ∀ y : ℝ, 2 * a < |y| → crossCorr F F y = 0 := by
      intro y hy
      have h0 : EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) y = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
        have := hks hmem
        rw [mem_Icc] at this
        rcases le_or_gt 0 y with h0 | h0
        · rw [abs_of_nonneg h0] at hy; linarith [this.2]
        · rw [abs_of_neg h0] at hy; linarith [this.1]
      rw [hk] at h0; exact_mod_cast h0
    have hl0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    exact ⟨hout _ (by rw [abs_of_pos hl0]; exact hlog),
      hout _ (by rw [abs_neg, abs_of_pos hl0]; exact hlog)⟩
  unfold atomPairing
  rw [tsum_eq_sum (s := Finset.Icc 2 N) (fun n hn => ?_)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Finset.mem_Icc.mp hn).1, hk, hk, ← Complex.ofReal_add, Complex.ofReal_re]
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    by_cases h2 : 2 ≤ n
    · have h : N < n := by rcases hn with h | h <;> omega
      rw [(hvan n h2 h).1, (hvan n h2 h).2, add_zero, mul_zero]
    · rw [if_neg h2, zero_mul]

/-- **Two-sided polar bound.** If `Λ ± w` are Weil-positive on polar tests, then
`|T_w(F)| ≤ Re W(F, F)` for every real polar `C²` test `F` supported in `[−a, a]`. -/
theorem abs_atomPairing_le_of_weilPositive {w : ℕ → ℝ}
    (hp : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) {F : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hF : ContDiff ℝ 2 fun u => (F u : ℂ))
    (hFs : tsupport (fun u => (F u : ℂ)) ⊆ Icc (-a) a)
    (hp1 : paperFT (fun u => (F u : ℂ)) (I / 2) = 0)
    (hp2 : paperFT (fun u => (F u : ℂ)) (-(I / 2)) = 0) :
    |atomPairing w (crossCorr F F)| ≤
      (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re := by
  have hWf := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hF hFs hp1 hp2
  have hre : (∫ τ : ℝ, ‖paperFT (fun u => (F u : ℂ)) τ‖ ^ 2 *
      weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊Real.exp (2 * a)⌋₊
        (τ / (2 * π))) = 2 * π * (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re := by
    rw [hWf, Complex.ofReal_re]; field_simp
  have hsum := atomPairing_eq_sum_of_support w hF hFs
  have h1 := hp a ha _ hF hFs hp1 hp2
  have h2 := hm a ha _ hF hFs hp1 hp2
  rw [integral_weilAtomSymbol_eq_sub hF hFs, hre] at h1 h2
  simp only [add_sub_cancel_left] at h1
  have e2 : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) - w n - ArithmeticFunction.vonMangoldt n) /
      Real.sqrt n = -(w n / Real.sqrt n) := fun n => by ring
  simp only [e2, neg_mul, Finset.sum_neg_distrib] at h2
  rw [hsum] at h1 h2
  have hπ : 0 < π := Real.pi_pos
  rw [abs_le]; constructor <;> nlinarith

/-! ## General perturbations `D + εH` -/

theorem crossCorr_add_smul {D H : ℝ → ℝ} (hD : Continuous D) (hDc : HasCompactSupport D)
    (hH : Continuous H) (hHc : HasCompactSupport H) (ε y : ℝ) :
    crossCorr (fun u => D u + ε * H u) (fun u => D u + ε * H u) y =
      crossCorr D D y + ε * (crossCorr D H y + crossCorr H D y) + ε ^ 2 * crossCorr H H y := by
  have i1 := integrable_translate_prod hD hDc hD y
  have i2 := (integrable_translate_prod hD hDc hH y).const_mul ε
  have i3 := (integrable_translate_prod hH hHc hD y).const_mul ε
  have i4 := (integrable_translate_prod hH hHc hH y).const_mul (ε ^ 2)
  have i23 : Integrable fun t => ε * (D t * H (t - y)) + ε * (H t * D (t - y)) := i2.add i3
  have i123 : Integrable fun t => D t * D (t - y) + (ε * (D t * H (t - y)) + ε * (H t * D (t - y))) :=
    i1.add i23
  unfold crossCorr
  have e : (fun t => (D t + ε * H t) * (D (t - y) + ε * H (t - y))) =
      fun t => D t * D (t - y) + (ε * (D t * H (t - y)) + ε * (H t * D (t - y))) +
        ε ^ 2 * (H t * H (t - y)) := by
    funext t; ring
  rw [e, integral_add i123 i4, integral_add i1 i23, integral_add i2 i3, integral_const_mul,
    integral_const_mul, integral_const_mul]
  ring

/-- **Expansion of the pairing along `D + εH`.** -/
theorem atomPairing_add_smul_expand (w : ℕ → ℝ) {D H : ℝ → ℝ} (hD : Continuous D)
    (hDc : HasCompactSupport D) (hH : Continuous H) (hHc : HasCompactSupport H) (ε : ℝ) :
    atomPairing w (crossCorr (fun u => D u + ε * H u) (fun u => D u + ε * H u)) =
      atomPairing w (crossCorr D D) + 2 * ε * atomPairing w (crossCorr D H) +
        ε ^ 2 * atomPairing w (crossCorr H H) := by
  obtain ⟨R₁, hR₁0, hR₁⟩ := exists_vanish_of_hasCompactSupport hDc
  obtain ⟨R₂, hR₂0, hR₂⟩ := exists_vanish_of_hasCompactSupport hHc
  set R₀ := 2 * (R₁ + R₂) with hR₀
  have hvan : ∀ {X Y : ℝ → ℝ} {r₁ r₂ : ℝ}, (∀ t, r₁ < |t| → X t = 0) → (∀ t, r₂ < |t| → Y t = 0) →
      r₁ + r₂ ≤ R₀ → ∀ y, R₀ < |y| → crossCorr X Y y = 0 := fun hX hY hle y hy =>
    crossCorr_eq_zero hX hY (by linarith)
  have vDD := hvan hR₁ hR₁ (by rw [hR₀]; linarith)
  have vDH := hvan hR₁ hR₂ (by rw [hR₀]; linarith)
  have vHD := hvan hR₂ hR₁ (by rw [hR₀]; linarith)
  have vHH := hvan hR₂ hR₂ (by rw [hR₀]; linarith)
  have hmid : ∀ y, R₀ < |y| → crossCorr D H y + crossCorr H D y = 0 := fun y hy => by
    rw [vDH y hy, vHD y hy, add_zero]
  rw [show crossCorr (fun u => D u + ε * H u) (fun u => D u + ε * H u) = fun y =>
      crossCorr D D y + ε * (crossCorr D H y + crossCorr H D y) + ε ^ 2 * crossCorr H H y from
      funext (crossCorr_add_smul hD hDc hH hHc ε)]
  rw [atomPairing_add_smul w vDD hmid vHH, atomPairing_add w vDH vHD]
  have hswap : atomPairing w (crossCorr H D) = atomPairing w (crossCorr D H) := by
    rw [show crossCorr H D = fun y => crossCorr D H (-y) from funext fun y => crossCorr_swap y,
      atomPairing_reflect]
  rw [hswap]; ring

/-! ## The polar near-null vector -/

/-- The polar second difference of the truncated kernel is small at every zero: `≤ 3 E_L`. -/
theorem polarRiemannDifference_zero_bound (L : ℝ) {c : ℝ} (hc : 0 ≤ c) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (ρ : zetaZeroConfig.carrier) :
    (1 + |(ρ : ℂ).im|) * ‖paperFT (polarRiemannDifference L c) (gammaOf ρ)‖ ≤
        3 * truncatedRiemannTailEnergy L ∧
      (1 + |(ρ : ℂ).im|) * ‖paperFT (polarRiemannDifference L c) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        3 * truncatedRiemannTailEnergy L := by
  have hmem := ρ.2
  have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    have h : IsNontrivialZero (ρ : ℂ) := hmem
    exact ⟨h.2.1, h.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
  have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  obtain ⟨hv1, hv2⟩ := truncatedRiemannKernel_zero_bound L hΛ ρ
  have hd : 0 ≤ 1 + |(ρ : ℂ).im| := by positivity
  constructor
  · rw [paperFT_polarRiemannDifference, norm_mul]
    have hm := norm_polarMultiplier_le hc hIm
    calc (1 + |(ρ : ℂ).im|) * (‖_‖ * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖)
        = ‖1 - (polarWeight c : ℂ) * Complex.exp (I * gammaOf ρ * c) -
            (polarWeight c : ℂ) * Complex.exp (I * gammaOf ρ * ((-c : ℝ) : ℂ))‖ *
          ((1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖) := by ring
      _ ≤ 3 * truncatedRiemannTailEnergy L := mul_le_mul hm hv1 (by positivity) (by norm_num)
  · rw [paperFT_polarRiemannDifference, norm_mul]
    have hm := norm_polarMultiplier_le hc hIm'
    calc (1 + |(ρ : ℂ).im|) * (‖_‖ *
          ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖)
        = ‖1 - (polarWeight c : ℂ) * Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * c) -
            (polarWeight c : ℂ) *
              Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * ((-c : ℝ) : ℂ))‖ *
          ((1 + |(ρ : ℂ).im|) *
            ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖) := by ring
      _ ≤ 3 * truncatedRiemannTailEnergy L := mul_le_mul hm hv2 (by positivity) (by norm_num)

theorem continuous_polarRiemannDifferenceReal (L c : ℝ) :
    Continuous (polarRiemannDifferenceReal L c) := by
  have hU := continuous_truncatedRiemannKernelReal L
  unfold polarRiemannDifferenceReal
  exact (hU.sub (continuous_const.mul (hU.comp (continuous_id.sub continuous_const)))).sub
    (continuous_const.mul (hU.comp (continuous_id.sub continuous_const)))

theorem hasCompactSupport_polarRiemannDifferenceReal (L c : ℝ) :
    HasCompactSupport (polarRiemannDifferenceReal L c) := by
  have hU := hasCompactSupport_truncatedRiemannKernelReal L
  unfold polarRiemannDifferenceReal
  exact (hU.sub (hU.comp_homeomorph (Homeomorph.subRight c)).mul_left).sub
    (hU.comp_homeomorph (Homeomorph.subRight (-c))).mul_left

/-- The zero side of `L_c(Φχ_L) + εH` for a real `C²` compactly supported `H`. -/
theorem norm_W_polarPerturbed_le (L : ℝ) {c : ℝ} (hc : 0 ≤ c) (ε : ℝ) {H : ℝ → ℝ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) :
    ‖zetaZeroConfig.W (fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ))
        (fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ))‖ ≤
      (5 / 4) * zetaInvSqSum * (3 * truncatedRiemannTailEnergy L + |ε| * testEnergy H) ^ 2 := by
  obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hE0 := truncatedRiemannTailEnergy_nonneg L
  have hH0 := testEnergy_nonneg H
  have hfun : (fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ)) =
      fun u => polarRiemannDifference L c u + (ε : ℂ) * (H u : ℂ) := by
    funext u; rw [polarRiemannDifference_eq]; push_cast; ring
  have hlin : ∀ z : ℂ, paperFT (fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ)) z =
      paperFT (polarRiemannDifference L c) z + (ε : ℂ) * paperFT (fun u => (H u : ℂ)) z := by
    intro z
    rw [hfun]
    unfold paperFT
    have hPc : Continuous (polarRiemannDifference L c) := (contDiff_polarRiemannDifference L c).continuous
    have hPs : HasCompactSupport (polarRiemannDifference L c) := by
      rw [polarRiemannDifference_eq]
      exact (hasCompactSupport_polarRiemannDifferenceReal L c).comp_left Complex.ofReal_zero
    have h0 : Integrable fun u : ℝ => polarRiemannDifference L c u * Complex.exp (I * z * u) :=
      (hPc.mul (by fun_prop)).integrable_of_hasCompactSupport hPs.mul_right
    have h1 := (integrable_ofReal_mul_cexp_of_hasCompactSupport hH.continuous hHc z).const_mul (ε : ℂ)
    rw [← integral_const_mul, ← integral_add h0 h1]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only; ring
  refine norm_W_le_of_zero_bound (by positivity) fun ρ => ?_
  obtain ⟨hu1, hu2⟩ := polarRiemannDifference_zero_bound L hc hΛ' ρ
  obtain ⟨hh1, hh2⟩ := test_zero_bound hH hHc ρ
  have hd : 0 ≤ 1 + |(ρ : ℂ).im| := by positivity
  constructor
  · rw [hlin]
    have := norm_add_le (paperFT (polarRiemannDifference L c) (gammaOf ρ))
      ((ε : ℂ) * paperFT (fun u => (H u : ℂ)) (gammaOf ρ))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
    nlinarith [abs_nonneg ε]
  · rw [hlin]
    have := norm_add_le (paperFT (polarRiemannDifference L c) ((starRingEnd ℂ) (gammaOf ρ)))
      ((ε : ℂ) * paperFT (fun u => (H u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
    nlinarith [abs_nonneg ε]

/-! ## Limits and Fubini -/

/-- `L_c g(y) = g(y) − α_c (g(y − c) + g(y + c))`. -/
def polarShift (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  g y - polarWeight c * g (y - c) - polarWeight c * g (y + c)

theorem abs_polarShift_le_of_decay {c K : ℝ} (hc : 0 ≤ c) {g : ℝ → ℝ}
    (hg : ∀ y, |g y| ≤ K * Real.exp (-(2 * |y|))) (y : ℝ) :
    |polarShift c g y| ≤ (K * (1 + 2 * polarWeight c * Real.exp (2 * c))) * Real.exp (-(2 * |y|)) := by
  have hα := polarWeight_pos c
  have hK : 0 ≤ K := by
    have := hg 0; have := Real.exp_pos (-(2 * |(0:ℝ)|)); nlinarith [abs_nonneg (g 0)]
  have hshift : ∀ s : ℝ, |s| ≤ c → Real.exp (-(2 * |y + s|)) ≤ Real.exp (2 * c) * Real.exp (-(2 * |y|)) := by
    intro s hs
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have := abs_sub_abs_le_abs_sub y (-s)
    rw [show y - -s = y + s by ring, abs_neg] at this
    linarith
  have e1 := hg (y - c)
  have e2 := hg (y + c)
  have s1 := hshift (-c) (by rw [abs_neg, abs_of_nonneg hc])
  have s2 := hshift c (by rw [abs_of_nonneg hc])
  rw [show y + -c = y - c by ring] at s1
  unfold polarShift
  calc |g y - polarWeight c * g (y - c) - polarWeight c * g (y + c)|
      ≤ |g y| + polarWeight c * |g (y - c)| + polarWeight c * |g (y + c)| := by
        have := abs_sub (g y - polarWeight c * g (y - c)) (polarWeight c * g (y + c))
        have := abs_sub (g y) (polarWeight c * g (y - c))
        rw [abs_mul, abs_of_pos hα] at *
        linarith
    _ ≤ K * Real.exp (-(2 * |y|)) + polarWeight c * (K * (Real.exp (2 * c) * Real.exp (-(2 * |y|)))) +
          polarWeight c * (K * (Real.exp (2 * c) * Real.exp (-(2 * |y|)))) := by
        gcongr
        · exact hg y
        · exact e1.trans (mul_le_mul_of_nonneg_left s1 hK)
        · exact e2.trans (mul_le_mul_of_nonneg_left s2 hK)
    _ = _ := by ring

/-- Pointwise decay of the Φ-correlation and of the truncation defect. -/
theorem exists_crossCorr_decay {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ y, |crossCorr riemannKernelReal H y| ≤ K * Real.exp (-(2 * |y|))) ∧
      ∀ L y, |crossCorr (truncatedRiemannKernelReal L) H y - crossCorr riemannKernelReal H y| ≤
        (K * Real.exp (-(2 * (L - 1)))) * Real.exp (-(2 * |y|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  obtain ⟨R, hR0, hR⟩ := exists_vanish_of_hasCompactSupport hHc
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, |H t| ≤ M := by
    obtain ⟨M, hM⟩ := hH.bounded_above_of_compact_support hHc
    exact ⟨M, fun t => by rw [← Real.norm_eq_abs]; exact hM t⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨M * C * (2 * R) * Real.exp (2 * R), by positivity, fun y => ?_, fun L y => ?_⟩
  · refine abs_integral_mul_translate_le hC0 hM0 hR0 (fun t => ?_) hM hR y
    rw [abs_of_pos (riemannKernelReal_pos t)]
    refine (hC t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
    nlinarith [abs_nonneg t]
  · have heq : crossCorr (truncatedRiemannKernelReal L) H y - crossCorr riemannKernelReal H y =
        ∫ t, (truncatedRiemannKernelReal L t - riemannKernelReal t) * H (t - y) := by
      simp only [crossCorr]
      rw [← integral_sub (integrable_mul_translate_right (continuous_truncatedRiemannKernelReal L)
        hH hHc y) (integrable_mul_translate_right continuous_riemannKernelReal hH hHc y)]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only; ring
    rw [heq]
    have := abs_integral_mul_translate_le
      (Z := fun t => truncatedRiemannKernelReal L t - riemannKernelReal t)
      (A := C * Real.exp (-(2 * (L - 1)))) (by positivity) hM0 hR0 (fun t => ?_) hM hR y
    · calc _ ≤ _ := this
        _ = _ := by ring
    · obtain ⟨h1, h2⟩ := riemannKernelReal_sub_truncated_le hC L t
      rw [abs_sub_comm, abs_of_nonneg h1]
      exact h2

/-- The correlation of the polar second difference is the polar shift of the correlation. -/
theorem crossCorr_polarRiemannDifferenceReal (L c : ℝ) {H : ℝ → ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) (y : ℝ) :
    crossCorr (polarRiemannDifferenceReal L c) H y =
      polarShift c (crossCorr (truncatedRiemannKernelReal L) H) y := by
  set U := truncatedRiemannKernelReal L
  have hU := continuous_truncatedRiemannKernelReal L
  have hUc := hasCompactSupport_truncatedRiemannKernelReal L
  have i0 := integrable_mul_translate_right hU hH hHc y
  have i1 : Integrable fun t => polarWeight c * (U (t - c) * H (t - y)) :=
    (integrable_mul_translate_right (hU.comp (continuous_id.sub continuous_const)) hH hHc y).const_mul _
  have i2 : Integrable fun t => polarWeight c * (U (t - -c) * H (t - y)) :=
    (integrable_mul_translate_right (hU.comp (continuous_id.sub continuous_const)) hH hHc y).const_mul _
  have s1 : ∫ t, U (t - c) * H (t - y) = crossCorr U H (y - c) := by
    unfold crossCorr
    rw [← integral_add_right_eq_self (μ := volume) (fun t => U (t - c) * H (t - y)) c]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only; rw [show t + c - c = t by ring, show t + c - y = t - (y - c) by ring]
  have s2 : ∫ t, U (t - -c) * H (t - y) = crossCorr U H (y + c) := by
    unfold crossCorr
    rw [← integral_add_right_eq_self (μ := volume) (fun t => U (t - -c) * H (t - y)) (-c)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only; rw [show t + -c - -c = t by ring, show t + -c - y = t - (y + c) by ring]
  have hA : Integrable fun t => U t * H (t - y) - polarWeight c * (U (t - c) * H (t - y)) :=
    i0.sub i1
  have e : crossCorr (polarRiemannDifferenceReal L c) H y =
      (∫ t, U t * H (t - y)) - (∫ t, polarWeight c * (U (t - c) * H (t - y))) -
        ∫ t, polarWeight c * (U (t - -c) * H (t - y)) := by
    rw [← integral_sub i0 i1, ← integral_sub hA i2]
    unfold crossCorr polarRiemannDifferenceReal
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [U]; ring
  rw [e, integral_const_mul, integral_const_mul, s1, s2]
  rfl

theorem summable_atomPairing_polarShift_compact (w : ℕ → ℝ) {c : ℝ} {g : ℝ → ℝ} {R : ℝ}
    (hg : ∀ y, R < |y| → g y = 0) :
    Summable fun n : ℕ => (if 2 ≤ n then w n / Real.sqrt n else 0) *
      (polarShift c g (Real.log n) + polarShift c g (-Real.log n)) := by
  refine summable_atomPairing w (R := R + |c|) fun y hy => ?_
  unfold polarShift
  have h1 : R < |y| := by linarith [abs_nonneg c]
  have h2 : R < |y - c| := by have := abs_sub_abs_le_abs_sub y c; linarith
  have h3 : R < |y + c| := by
    have := abs_sub_abs_le_abs_sub y (-c); rw [show y - -c = y + c by ring, abs_neg] at this; linarith
  rw [hg y h1, hg _ h2, hg _ h3]; ring

/-- **The truncation limit of the first variation.** -/
theorem exists_abs_atomPairing_polarShift_sub_le {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) {c : ℝ} (hc : 0 ≤ c) {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |atomPairing w (crossCorr (polarRiemannDifferenceReal L c) H) -
        atomPairing w (polarShift c (crossCorr riemannKernelReal H))| ≤
        K * Real.exp (-(2 * (L - 1))) := by
  obtain ⟨K, hK0, hΦ, hD⟩ := exists_crossCorr_decay hH hHc
  set Sw := ∑' n : ℕ, |w n| / (n : ℝ) ^ 2
  have hSw0 : 0 ≤ Sw := tsum_nonneg fun _ => by positivity
  set B := 1 + 2 * polarWeight c * Real.exp (2 * c)
  have hB : 0 ≤ B := by have := polarWeight_pos c; positivity
  refine ⟨2 * (K * B) * Sw, by positivity, fun L => ?_⟩
  obtain ⟨R, hR0, hR⟩ := exists_vanish_of_hasCompactSupport hHc
  have hU : ∀ t, |L| < |t| → truncatedRiemannKernelReal L t = 0 := fun t ht =>
    truncatedRiemannKernelReal_eq_zero (lt_of_le_of_lt (le_abs_self L) ht)
  have hcomp : ∀ y, |L| + R < |y| → crossCorr (truncatedRiemannKernelReal L) H y = 0 :=
    fun y hy => crossCorr_eq_zero hU hR hy
  have hs1 := summable_atomPairing_polarShift_compact w (c := c) hcomp
  obtain ⟨hs2, -⟩ := summable_atomPairing_of_decay hw2 (abs_polarShift_le_of_decay hc hΦ)
  have hdiff : ∀ y, |polarShift c (fun y => crossCorr (truncatedRiemannKernelReal L) H y -
      crossCorr riemannKernelReal H y) y| ≤
      ((K * Real.exp (-(2 * (L - 1)))) * B) * Real.exp (-(2 * |y|)) :=
    abs_polarShift_le_of_decay hc (hD L)
  obtain ⟨-, hbound⟩ := summable_atomPairing_of_decay hw2 hdiff
  have heq : atomPairing w (crossCorr (polarRiemannDifferenceReal L c) H) -
      atomPairing w (polarShift c (crossCorr riemannKernelReal H)) =
      atomPairing w (polarShift c (fun y => crossCorr (truncatedRiemannKernelReal L) H y -
        crossCorr riemannKernelReal H y)) := by
    rw [show crossCorr (polarRiemannDifferenceReal L c) H =
        polarShift c (crossCorr (truncatedRiemannKernelReal L) H) from
        funext (crossCorr_polarRiemannDifferenceReal L c hH hHc)]
    unfold atomPairing
    rw [← hs1.tsum_sub hs2]
    refine tsum_congr fun n => ?_
    unfold polarShift; ring
  rw [heq]
  calc _ ≤ 2 * ((K * Real.exp (-(2 * (L - 1)))) * B) * Sw := hbound
    _ = _ := by ring

/-- **Fubini for the polar shift.** `T_w(L_c Φ, H) = ∫ H · L_c G_w`. -/
theorem atomPairing_polarShift_eq_integral {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) (c : ℝ) {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    atomPairing w (polarShift c (crossCorr riemannKernelReal H)) =
      ∫ s, H s * polarShift c (weightKernelTransform w) s := by
  obtain ⟨K, hK0, hΦ, -⟩ := exists_crossCorr_decay hH hHc
  have hGc := continuous_weightKernelTransform hw2
  set g := crossCorr riemannKernelReal H
  have hshift : ∀ s : ℝ, (fun y => g (y - s)) = crossCorr riemannKernelReal (fun t => H (t + s)) := by
    intro s; funext y
    simp only [g, crossCorr]
    congr 1; funext t; rw [show t - (y - s) = t - y + s by ring]
  have hHs : ∀ s : ℝ, Continuous fun t => H (t + s) := fun s => hH.comp (continuous_id.add continuous_const)
  have hHsc : ∀ s : ℝ, HasCompactSupport fun t => H (t + s) := fun s =>
    hHc.comp_homeomorph (Homeomorph.addRight s)
  have hdec : ∀ s : ℝ, ∀ y, |g (y - s)| ≤ (K * Real.exp (2 * |s|)) * Real.exp (-(2 * |y|)) := by
    intro s y
    refine (hΦ (y - s)).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK0
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have := abs_sub_abs_le_abs_sub y s
    linarith
  obtain ⟨s0, -⟩ := summable_atomPairing_of_decay hw2 (g := g) (K := K) hΦ
  obtain ⟨s1, -⟩ := summable_atomPairing_of_decay hw2 (hdec c)
  obtain ⟨s2, -⟩ := summable_atomPairing_of_decay hw2 (hdec (-c))
  have hsplit : atomPairing w (polarShift c g) = atomPairing w g -
      polarWeight c * atomPairing w (fun y => g (y - c)) -
      polarWeight c * atomPairing w (fun y => g (y - -c)) := by
    unfold atomPairing
    rw [← tsum_mul_left, ← tsum_mul_left, ← s0.tsum_sub (s1.mul_left _),
      ← (s0.sub (s1.mul_left _)).tsum_sub (s2.mul_left _)]
    refine tsum_congr fun n => ?_
    simp only [polarShift, show ∀ y : ℝ, y - -c = y + c from fun y => by ring]
    ring
  have hF : ∀ s : ℝ, atomPairing w (fun y => g (y - s)) =
      ∫ t, H t * weightKernelTransform w (t - s) := by
    intro s
    rw [hshift s, atomPairing_riemannKernel_eq_integral hw2 (hHs s) (hHsc s)]
    rw [← integral_sub_right_eq_self (μ := volume) (fun t => H (t + s) * weightKernelTransform w t) s]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only; rw [show t - s + s = t by ring]
  have hi : ∀ s : ℝ, Integrable fun t => H t * weightKernelTransform w (t - s) := fun s =>
    (hH.mul (hGc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      hHc.mul_right
  have i0 : Integrable fun t => H t * weightKernelTransform w t :=
    (hH.mul hGc).integrable_of_hasCompactSupport hHc.mul_right
  have i1 : Integrable fun t => polarWeight c * (H t * weightKernelTransform w (t - c)) :=
    (hi c).const_mul _
  have i2 : Integrable fun t => polarWeight c * (H t * weightKernelTransform w (t - -c)) :=
    (hi (-c)).const_mul _
  have i01 : Integrable fun t => H t * weightKernelTransform w t -
      polarWeight c * (H t * weightKernelTransform w (t - c)) := i0.sub i1
  have hR : ∫ s, H s * polarShift c (weightKernelTransform w) s =
      (∫ t, H t * weightKernelTransform w t) -
        (∫ t, polarWeight c * (H t * weightKernelTransform w (t - c))) -
        ∫ t, polarWeight c * (H t * weightKernelTransform w (t - -c)) := by
    rw [← integral_sub i0 i1, ← integral_sub i01 i2]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [polarShift, show t - -c = t + c by ring]
    ring
  rw [hsplit, atomPairing_riemannKernel_eq_integral hw2 hH hHc, hF c, hF (-c), hR,
    integral_const_mul, integral_const_mul]

/-! ## The first variation vanishes -/

theorem paperFT_polarPerturbed (L c ε : ℝ) {H : ℝ → ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) (z : ℂ) :
    paperFT (fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ)) z =
      paperFT (polarRiemannDifference L c) z + (ε : ℂ) * paperFT (fun u => (H u : ℂ)) z := by
  have hfun : (fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ)) =
      fun u => polarRiemannDifference L c u + (ε : ℂ) * (H u : ℂ) := by
    funext u; rw [polarRiemannDifference_eq]; push_cast; ring
  rw [hfun]
  unfold paperFT
  have hPc : Continuous (polarRiemannDifference L c) := (contDiff_polarRiemannDifference L c).continuous
  have hPs : HasCompactSupport (polarRiemannDifference L c) := by
    rw [polarRiemannDifference_eq]
    exact (hasCompactSupport_polarRiemannDifferenceReal L c).comp_left Complex.ofReal_zero
  have h0 : Integrable fun u : ℝ => polarRiemannDifference L c u * Complex.exp (I * z * u) :=
    (hPc.mul (by fun_prop)).integrable_of_hasCompactSupport hPs.mul_right
  have h1 := (integrable_ofReal_mul_cexp_of_hasCompactSupport hH hHc z).const_mul (ε : ℂ)
  rw [← integral_const_mul, ← integral_add h0 h1]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only; ring

/-- The zero side of the perturbed polar vector bounds its atom pairing (two-sided positivity). -/
theorem abs_atomPairing_polarPerturbed_le {w : ℕ → ℝ}
    (hp : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) (L : ℝ) {c : ℝ}
    (hc : 0 ≤ c) (ε : ℝ) {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H)
    (hH1 : paperFT (fun u => (H u : ℂ)) (I / 2) = 0)
    (hH2 : paperFT (fun u => (H u : ℂ)) (-(I / 2)) = 0) :
    |atomPairing w (crossCorr (fun u => polarRiemannDifferenceReal L c u + ε * H u)
        (fun u => polarRiemannDifferenceReal L c u + ε * H u))| ≤
      (5 / 4) * zetaInvSqSum * (3 * truncatedRiemannTailEnergy L + |ε| * testEnergy H) ^ 2 := by
  obtain ⟨R, hR0, hR⟩ := exists_vanish_of_hasCompactSupport hHc
  set a := |L| + c + R with ha
  have ha0 : 0 ≤ a := by positivity
  have hF : ContDiff ℝ 2 fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ) := by
    have hfun : (fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ)) =
        fun u => polarRiemannDifference L c u + (ε : ℂ) * (H u : ℂ) := by
      funext u; rw [polarRiemannDifference_eq]; push_cast; ring
    rw [hfun]
    exact (contDiff_polarRiemannDifference L c).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hH))
  have hFs : tsupport (fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ)) ⊆
      Icc (-a) a := by
    refine tsupport_subset_of_vanish fun u hu => ?_
    have hD : polarRiemannDifferenceReal L c u = 0 := by
      have h := image_eq_zero_of_notMem_tsupport (f := polarRiemannDifference L c) (x := u)
        (fun hmem => by
          have := tsupport_polarRiemannDifference (L := L) hc hmem
          rw [mem_Icc] at this
          rcases le_or_gt 0 u with h0 | h0
          · rw [abs_of_nonneg h0] at hu; linarith [this.2, le_abs_self L]
          · rw [abs_of_neg h0] at hu; linarith [this.1, le_abs_self L])
      rw [polarRiemannDifference_eq] at h
      have h' : ((polarRiemannDifferenceReal L c u : ℝ) : ℂ) = 0 := h
      exact Complex.ofReal_eq_zero.mp h'
    have hHu : H u = 0 := hR u (by linarith [abs_nonneg L])
    rw [hD, hHu]; simp
  have hp1 : paperFT (fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ)) (I / 2) = 0 := by
    rw [paperFT_polarPerturbed L c ε hH.continuous hHc, (paperFT_polarRiemannDifference_pole L c).1,
      hH1, mul_zero, add_zero]
  have hp2 : paperFT (fun u => ((polarRiemannDifferenceReal L c u + ε * H u : ℝ) : ℂ))
      (-(I / 2)) = 0 := by
    rw [paperFT_polarPerturbed L c ε hH.continuous hHc, (paperFT_polarRiemannDifference_pole L c).2,
      hH2, mul_zero, add_zero]
  exact (abs_atomPairing_le_of_weilPositive hp hm ha0 hF hFs hp1 hp2).trans
    ((Complex.re_le_norm _).trans (norm_W_polarPerturbed_le L hc ε hH hHc))

/-- **The first variation at the polar near-null vector vanishes.** If `Λ ± w` are Weil-positive
on polar tests, then `T_w(L_cΦ, H) = 0` for every real polar `C²` compactly supported `H`. -/
theorem atomPairing_polarShift_eq_zero {w : ℕ → ℝ}
    (hp : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n)
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) {c : ℝ} (hc : 0 ≤ c) {H : ℝ → ℝ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H)
    (hH1 : paperFT (fun u => (H u : ℂ)) (I / 2) = 0)
    (hH2 : paperFT (fun u => (H u : ℂ)) (-(I / 2)) = 0) :
    atomPairing w (polarShift c (crossCorr riemannKernelReal H)) = 0 := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_atomPairing_polarShift_sub_le hw2 hc hH.continuous hHc
  set T := atomPairing w (polarShift c (crossCorr riemannKernelReal H)) with hT
  by_contra hT0
  set τ := |T| with hτ
  have hτ0 : 0 < τ := abs_pos.mpr hT0
  set EH := testEnergy H with hEH
  set q := (5 / 4) * zetaInvSqSum with hq
  have hq0 : 0 ≤ q := by have := zetaInvSqSum_nonneg; rw [hq]; positivity
  set T2 := atomPairing w (crossCorr H H) with hT2
  set M₂ := q * (2 * EH ^ 2) + |T2| with hM₂
  have hM₂0 : 0 ≤ M₂ := by positivity
  set ε := τ / (2 * M₂ + 2) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨L₁, hL₁⟩ := exists_nearRadicalEnergy_le (ε := ε * τ / 108) (by positivity)
  obtain ⟨L₂, hL₂⟩ := exists_forall_mul_exp_le hK0 (δ := τ / 8) (by positivity)
  set L := max L₁ L₂
  have hEL : q * truncatedRiemannTailEnergy L ^ 2 ≤ ε * τ / 108 := hL₁ L (le_max_left _ _)
  have hdiff := (hK L).trans (hL₂ L (le_max_right _ _))
  set D := polarRiemannDifferenceReal L c
  have hDc := continuous_polarRiemannDifferenceReal L c
  have hDs := hasCompactSupport_polarRiemannDifferenceReal L c
  set T0 := atomPairing w (crossCorr D D) with hT0def
  set T1 := atomPairing w (crossCorr D H) with hT1
  set EL := truncatedRiemannTailEnergy L with hELdef
  have hE0 : 0 ≤ EL := truncatedRiemannTailEnergy_nonneg L
  -- the two applications of two-sided positivity
  have b0' := abs_atomPairing_polarPerturbed_le hp hm L hc 0 hH hHc hH1 hH2
  rw [atomPairing_add_smul_expand w hDc hDs hH.continuous hHc 0] at b0'
  have b0 : |T0| ≤ q * (3 * EL) ^ 2 := by
    have e1 : T0 + 2 * 0 * T1 + (0 : ℝ) ^ 2 * T2 = T0 := by ring
    have e2 : (3 * EL + |(0 : ℝ)| * EH) = 3 * EL := by simp
    have := b0'
    rw [e1, e2] at this
    exact this
  have b1' := abs_atomPairing_polarPerturbed_le hp hm L hc ε hH hHc hH1 hH2
  rw [atomPairing_add_smul_expand w hDc hDs hH.continuous hHc ε, abs_of_pos hεpos] at b1'
  have b1 : |T0 + 2 * ε * T1 + ε ^ 2 * T2| ≤ q * (3 * EL + ε * EH) ^ 2 := b1'
  -- first-order bound
  have hsq : (3 * EL + ε * EH) ^ 2 ≤ 2 * (9 * EL ^ 2) + 2 * (ε ^ 2 * EH ^ 2) := by
    nlinarith [sq_nonneg (3 * EL - ε * EH)]
  have hb1 : q * (3 * EL + ε * EH) ^ 2 ≤ 18 * (q * EL ^ 2) + ε ^ 2 * (q * (2 * EH ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left hsq hq0
    have e : q * (2 * (9 * EL ^ 2) + 2 * (ε ^ 2 * EH ^ 2)) =
        18 * (q * EL ^ 2) + ε ^ 2 * (q * (2 * EH ^ 2)) := by ring
    linarith
  have hb0 : q * (3 * EL) ^ 2 = 9 * (q * EL ^ 2) := by ring
  have hT1b : 2 * ε * |T1| ≤ 27 * (q * EL ^ 2) + ε ^ 2 * M₂ := by
    have key : 2 * ε * T1 = (T0 + 2 * ε * T1 + ε ^ 2 * T2) - T0 - ε ^ 2 * T2 := by ring
    have hT2' : |ε ^ 2 * T2| = ε ^ 2 * |T2| := by rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have htri : |2 * ε * T1| ≤ |T0 + 2 * ε * T1 + ε ^ 2 * T2| + |T0| + |ε ^ 2 * T2| := by
      have h1 := abs_sub (T0 + 2 * ε * T1 + ε ^ 2 * T2 - T0) (ε ^ 2 * T2)
      have h2 := abs_sub (T0 + 2 * ε * T1 + ε ^ 2 * T2) T0
      rw [← key] at h1
      linarith
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ε), hT2'] at htri
    rw [hM₂]
    nlinarith
  have hT1' : |T1| ≤ τ / 8 + ε * M₂ / 2 := by
    have h1 : 27 * (q * EL ^ 2) ≤ ε * τ / 4 := by linarith
    have : 2 * ε * |T1| ≤ 2 * ε * (τ / 8 + ε * M₂ / 2) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hεM : ε * M₂ ≤ τ / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have e : τ / 2 * (2 * M₂ + 2) = τ * M₂ + τ := by ring
    linarith
  have htri : |T| - |T1| ≤ |T - T1| := abs_sub_abs_le_abs_sub T T1
  have hdiff' : |T1 - T| ≤ τ / 8 := hdiff
  rw [abs_sub_comm] at htri
  linarith

/-- **Two-sided polar positivity annihilates `L_c G_w` against polar tests.** -/
theorem integral_mul_polarShift_weightKernelTransform_eq_zero {w : ℕ → ℝ}
    (hp : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n)
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) {c : ℝ} (hc : 0 ≤ c) {H : ℝ → ℝ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H)
    (hH1 : paperFT (fun u => (H u : ℂ)) (I / 2) = 0)
    (hH2 : paperFT (fun u => (H u : ℂ)) (-(I / 2)) = 0) :
    ∫ s, H s * polarShift c (weightKernelTransform w) s = 0 := by
  rw [← atomPairing_polarShift_eq_integral hw2 c hH.continuous hHc]
  exact atomPairing_polarShift_eq_zero hp hm hw2 hc hH hHc hH1 hH2

end

end RHTower

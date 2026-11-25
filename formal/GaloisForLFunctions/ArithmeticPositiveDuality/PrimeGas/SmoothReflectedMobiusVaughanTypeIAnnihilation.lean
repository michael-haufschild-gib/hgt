import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HamburgerConductorRigidityAndSubdiagonalMobiusGaussianDuality

/-!
# Smooth Outer-Weighted Reflected-Möbius Duality, Unconditional Sub-Horizon Vaughan Type-I Annihilation Without Continuum Subtraction, and Pure Type-II Vacuum Concentration on `Ω_open`

With a sharp outer Möbius cutoff `1 ≤ d ≤ D`, decomposing `subdiagMoebiusGaussian` via Vaughan's
identity leaves a boundary jump `D^s / s` on the Type-I divisor convolution, yielding a disjunctive
forcing law `max ‖Type I‖ ‖Type II‖ > ((1 / 4) (|Im s| / 7)^{1/2 - Re s} - 1 / 16) / 2` on
`Ω_open = {s : ℂ | 3001 / 24000 ≤ Re s ∧ Re s < 1 / 2 ∧ 184 < |Im s|}`.

This module replaces the sharp outer cutoff on `d` by the canonical Gaussian Mellin weight
`smoothAFECutoff ((d : ℝ) / Y)` at sub-horizon direct scale `x = |Im s|^{-(1 + η)}` and outer scale
`Y = |Im s|^{3 + η}` (`η ≥ 1` arbitrarily large), establishing four unconditional results across
every point of `Ω_open`:

1. **General two-line smooth AFE on arbitrary `[a, b]` and uniform negative-even `ζ` bounds
   (`tsum_smoothAFECutoff_eq_zeta_add_residue_add_mellinAt_neg`,
   `exists_norm_riemannZeta_one_sub_even_le`):**
   For any `w ≠ 1`, `X > 0`, and `a < 0 < b` enclosing `0` and `1 - Re w`, the smoothed Dirichlet
   series `∑_{m ≥ 1} m^{-w} W(m / X)` equals `ζ(w) + smoothAFEZetaShiftedPoleResidue w X +
   smoothAFEZetaMellinAt a w X`. Together with the `2r`-step `zetaChi` recurrence and Spira's lower
   bound on `0 < Re u < 1 / 2`, this bounds `‖ζ(1 - s - 2r - i v)‖ ≤ C_r (1 + |Im s|)^{2r} (1 + |v|)^{2r}`
   uniformly across `3001 / 24000 ≤ Re s < 1 / 2`.

2. **Exact smooth outer-weighted reflected-Möbius cross-height sieve identity
   (`smoothOuter_poleCleared_reflected_moebius_crossHeight_eq`):**
   Weighting `crossHeight_gaussian_two_tsum_eq` at `(d x, 2 d x)` by `μ(d) d^{-(1 - s)} W(d / Y)`
   over all `d ≥ 1` cancels `smoothAFEZetaShiftedPoleResidue` identically term-by-term, isolates the
   two-mode dual vacuum `W(1 / Y) I(s, x, 0) - W(2 / Y) I(s, x, 1)`, and bounds all dual modes
   `k ≥ 3` by `‖smoothOuterSieveCoeff Y k‖ ≤ 2 K_B k^{1 + B} Y^{-B}` via Möbius inversion and
   `‖W(d / Y) - 1‖ ≤ K_B (d / Y)^B`.

3. **Unconditional sub-horizon annihilation of both the short Möbius head and the entire smooth
   Vaughan Type-I bilinear sum without continuum pole subtraction
   (`smoothOuterMoebiusDirect_eq_vaughan_decomposition`,
   `exists_smoothOuter_vaughanTypeI_and_head_annihilation_on_remaining_strip`):**
   For every `η ≥ 1` and every `B_dec > 0`, at `x = |Im s|^{-(1 + η)}` and `Y = |Im s|^{3 + η}`, both
   `smoothOuterVaughanHead` and `smoothOuterVaughanTypeI` (with **no** continuum pole counterterm
   subtracted) are `O_{η, B_dec}(|Im s|^{-B_dec})` uniformly across all `s ∈ Ω_open` and all Vaughan
   cutoffs `U, V` with `U * V ≤ |Im s|^{η - 1 / 2}`. Specifically, in the Mellin-expanded Type-I
   fibre over `m ≥ 1`, the shifted `ζ`-pole residue at `z₁ = s + z₂` acquires two opposite-height
   Gaussian factors `exp((s + z₂)^2 + z₂^2)` whose real part is bounded above by
   `(σ + 2r₂)^2 + (2r₂)^2 - |Im s|^2 / 4 - v₂^2 / 4`, crushing the boundary continuum pole
   super-exponentially while `|Im s| * b * x ≤ |Im s|^{-1 / 2}` and `|Im s| * b / Y ≤ |Im s|^{-5 / 2}`
   suppress both discrete regimes.

4. **Pure Vaughan Type-II cross-height duality and `HasStrictPrimeGasWitness` production on `Ω_open`
   (`exists_pure_vaughanTypeII_crossHeight_duality_on_remaining_strip`,
   `strict_primeGas_witness_of_pure_vaughanTypeII_domination_on_remaining_strip`):**
   Eliminating both Type-0 and Type-I unconditionally concentrates the entire amplified Spira dual
   vacuum `(1 - 2^{-(1 - s)}) zetaChi(s)` (`> (1 / 4) (|Im s| / 7)^{1/2 - Re s}`) against the pure
   Vaughan Type-II convolution `((μ - μ_{≤ U}) * typeIIShort V)` up to `O_η(|Im s|^{-1 / 4})` across
   arbitrarily deep logarithmic factorization ratios `(η - 1 / 2) / (3 + η) → 1`.
-/

noncomputable section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate Topology ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.ArithmeticPositiveDuality
open _root_.RHTower

/-! ### Part 1: Two-Line Smooth AFE on Arbitrary `[a, b]` and Uniform Negative-Even `ζ` Bounds -/

section Part1TwoLineSmoothAFEAndNegativeZeta

/-- Uniform positive bound `‖smoothAFECutoff u‖ ≤ M_cut` across all `u > 0`, obtained by combining
`‖smoothAFECutoff u - 1‖ ≤ K₀ u` on `(0, 1]` with `‖smoothAFECutoff u‖ ≤ K₁ u⁻¹` on `[1, ∞)`. -/
lemma exists_norm_smoothAFECutoff_uniform_le :
    ∃ M_cut : ℝ, 1 ≤ M_cut ∧ ∀ {u : ℝ}, 0 < u → ‖smoothAFECutoff u‖ ≤ M_cut := by
  obtain ⟨K₀, hK₀, h0⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow (δ := 1) one_pos
  obtain ⟨K₁, hK₁, h1⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  refine ⟨max 1 (max (K₀ + 1) K₁), le_max_left _ _, fun {u} hu => ?_⟩
  rcases le_or_gt u 1 with hu1 | hu1
  · have hb := h0 hu
    rw [Real.rpow_one] at hb
    have htri : ‖smoothAFECutoff u‖ ≤ ‖smoothAFECutoff u - 1‖ + 1 := by
      have h := norm_add_le (smoothAFECutoff u - 1) 1
      simpa using h
    have hle : ‖smoothAFECutoff u‖ ≤ K₀ + 1 := by nlinarith
    exact hle.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hb := h1 hu
    have hrp : u ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1.le (by norm_num)
    have hle : ‖smoothAFECutoff u‖ ≤ K₁ :=
      hb.trans (mul_le_of_le_one_right hK₁ hrp)
    exact hle.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Elementary polynomial-vs-Gaussian domination: for every `M ≥ 0`, `τ ^ M * exp (-τ ^ 2 / 4)` is
uniformly bounded across all `τ ≥ 1`. -/
lemma exists_rpow_mul_exp_neg_quarter_sq_le (M : ℝ) :
    ∃ K_exp : ℝ, 0 < K_exp ∧ ∀ {τ : ℝ}, 1 ≤ τ →
      τ ^ M * Real.exp (-τ ^ (2 : ℕ) / 4) ≤ K_exp := by
  set N : ℕ := Nat.ceil (max M 0)
  have hMN : M ≤ (2 * N : ℕ) := by
    have h1 : M ≤ (N : ℝ) := (le_max_left M 0).trans (Nat.le_ceil _)
    have h2 : (N : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast Nat.le_mul_of_pos_left N two_pos
    exact h1.trans h2
  set K_exp : ℝ := (4 * ((N + 1 : ℕ) : ℝ)) ^ N + 1
  refine ⟨K_exp, by dsimp only [K_exp]; positivity, fun {τ} hτ1 => ?_⟩
  have hτ_pos : 0 < τ := zero_lt_one.trans_le hτ1
  have hrp : τ ^ M ≤ τ ^ (2 * N) := by
    calc τ ^ M ≤ τ ^ (((2 * N : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hτ1 hMN
      _ = τ ^ (2 * N) := Real.rpow_natCast τ (2 * N)
  set c_N : ℝ := 4 * ((N + 1 : ℕ) : ℝ)
  have hcN_pos : 0 < c_N := by dsimp only [c_N]; positivity
  have hu_exp : τ ^ (2 : ℕ) / c_N ≤ Real.exp (τ ^ (2 : ℕ) / c_N) := by
    linarith [Real.add_one_le_exp (τ ^ (2 : ℕ) / c_N)]
  have hpow_exp : (τ ^ (2 : ℕ) / c_N) ^ N ≤ Real.exp (τ ^ (2 : ℕ) / 4) := by
    calc (τ ^ (2 : ℕ) / c_N) ^ N
        ≤ (Real.exp (τ ^ (2 : ℕ) / c_N)) ^ N :=
          pow_le_pow_left₀ (by positivity) hu_exp N
      _ = Real.exp ((N : ℝ) * (τ ^ (2 : ℕ) / c_N)) := (Real.exp_nat_mul _ N).symm
      _ ≤ Real.exp (τ ^ (2 : ℕ) / 4) := by
          refine Real.exp_le_exp.mpr ?_
          dsimp only [c_N]
          rw [show (N : ℝ) * (τ ^ (2 : ℕ) / (4 * ((N + 1 : ℕ) : ℝ))) =
            (τ ^ (2 : ℕ) / 4) * ((N : ℝ) / ((N + 1 : ℕ) : ℝ)) by ring]
          refine mul_le_of_le_one_right (by positivity) ?_
          rw [div_le_one (by positivity)]
          exact_mod_cast Nat.le_succ N
  have hmul_le : τ ^ (2 * N) * Real.exp (-τ ^ (2 : ℕ) / 4) ≤ c_N ^ N := by
    have hrew : τ ^ (2 * N) = c_N ^ N * (τ ^ (2 : ℕ) / c_N) ^ N := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero N hcN_pos.ne'), ← pow_mul]
    rw [hrew, mul_assoc]
    refine mul_le_of_le_one_right (pow_nonneg hcN_pos.le N) ?_
    calc (τ ^ (2 : ℕ) / c_N) ^ N * Real.exp (-τ ^ (2 : ℕ) / 4)
        ≤ Real.exp (τ ^ (2 : ℕ) / 4) * Real.exp (-τ ^ (2 : ℕ) / 4) :=
          mul_le_mul_of_nonneg_right hpow_exp (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc τ ^ M * Real.exp (-τ ^ (2 : ℕ) / 4)
      ≤ τ ^ (2 * N) * Real.exp (-τ ^ (2 : ℕ) / 4) :=
        mul_le_mul_of_nonneg_right hrp (Real.exp_nonneg _)
    _ ≤ c_N ^ N := hmul_le
    _ ≤ K_exp := by dsimp only [K_exp]; linarith

private lemma tendsto_smoothAFEZetaMellinIntegrand_horizontal_ab
    {X a b : ℝ} (hX : 0 < X) (hab : a < b) (w : ℂ) {ε : ℝ} (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in a..b,
        smoothAFEZetaMellinIntegrand w X ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
  set M_ab : ℝ := max (|a|) (|b|) + 1
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_riemannZeta_strip (|w.re| + M_ab)
  set X_bd : ℝ := max (X ^ a) (X ^ b)
  set E_bd : ℝ := Real.exp (M_ab ^ (2 : ℕ))
  set K : ℝ := C * X_bd * E_bd
  refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
    (M := fun T => K * ((|w.im| + T) ^ N * Real.exp (-(T ^ (2 : ℕ)))))
    (hgt := fun T => ε * T) ?_
    (by simpa using (tendsto_shifted_pow_mul_exp_neg_sq |w.im| N).const_mul K)
  filter_upwards [eventually_ge_atTop (|w.im| + 2)] with T hT u hu
  rw [Set.uIoc_of_le hab.le] at hu
  have hT1 : 1 ≤ T := by linarith [abs_nonneg w.im]
  have hT_pos : 0 < T := zero_lt_one.trans_le hT1
  have habsv : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_pos hT_pos]
  set z : ℂ := (u : ℂ) + ((ε * T : ℝ) : ℂ) * I
  have hu_abs : |u| ≤ M_ab := by
    rw [abs_le]
    have ha_le : -M_ab ≤ a := by dsimp only [M_ab]; linarith [neg_abs_le a, le_max_left (|a|) (|b|)]
    have hb_le : b ≤ M_ab := by dsimp only [M_ab]; linarith [le_abs_self b, le_max_right (|a|) (|b|)]
    exact ⟨ha_le.trans hu.1.le, hu.2.trans hb_le⟩
  have hwz_re : |(w + z).re| ≤ |w.re| + M_ab := by
    rw [Complex.add_re, show z.re = u by simp [z]]
    linarith [abs_add_le w.re u]
  have hwz_im_ge : 1 ≤ |(w + z).im| := by
    rw [Complex.add_im, show z.im = ε * T by simp [z]]
    have htri : |ε * T| - |w.im| ≤ |w.im + ε * T| := by
      have h := abs_sub_abs_le_abs_sub (ε * T) (-w.im)
      simpa [abs_neg, sub_neg_eq_add, add_comm] using h
    linarith
  have hwz_im_le : |(w + z).im| ≤ |w.im| + T := by
    rw [Complex.add_im, show z.im = ε * T by simp [z]]
    exact (abs_add_le w.im (ε * T)).trans_eq (by rw [habsv])
  have hzeta : ‖riemannZeta (w + z)‖ ≤ C * (|w.im| + T) ^ N := by
    have hrec : ((((w + z).re : ℝ)) : ℂ) + (((w + z).im : ℝ) : ℂ) * I = w + z :=
      Complex.re_add_im _
    have hbase := hC (w + z).re (w + z).im hwz_re hwz_im_ge
    rw [hrec] at hbase
    exact hbase.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hwz_im_le N) hC0)
  have hpow : ‖(X : ℂ) ^ z‖ ≤ X_bd := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, show z.re = u by simp [z]]
    rcases le_total 1 X with h1X | h1X
    · exact (Real.rpow_le_rpow_of_exponent_le h1X hu.2).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hX h1X hu.1.le).trans (le_max_left _ _)
  have hker : ‖smoothAFEGaussianKernel z‖ ≤ E_bd * Real.exp (-(T ^ (2 : ℕ))) := by
    rw [smoothAFEGaussianKernel, norm_div, Complex.norm_exp]
    have hz_sq : (z ^ 2).re = u ^ (2 : ℕ) - T ^ (2 : ℕ) := by
      dsimp only [z]
      simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have hε2 : ε * ε = 1 := by have := sq_abs ε; rw [hε] at this; nlinarith
      nlinarith
    have hznorm1 : 1 ≤ ‖z‖ := by
      calc (1 : ℝ) ≤ T := hT1
        _ = |z.im| := by simp [z, habsv]
        _ ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hu2 : u ^ (2 : ℕ) ≤ M_ab ^ (2 : ℕ) := by
      rw [ ← sq_abs u ]
      exact pow_le_pow_left₀ (abs_nonneg u) hu_abs 2
    rw [hz_sq]
    exact (div_le_self (Real.exp_nonneg _) hznorm1).trans
      (by dsimp only [E_bd]; rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith))
  rw [smoothAFEZetaMellinIntegrand, norm_mul, norm_mul]
  have hX_nn : 0 ≤ X_bd := (Real.rpow_nonneg hX.le a).trans (le_max_left _ _)
  calc ‖riemannZeta (w + z)‖ * ‖(X : ℂ) ^ z‖ * ‖smoothAFEGaussianKernel z‖
      ≤ (C * (|w.im| + T) ^ N) * X_bd * (E_bd * Real.exp (-(T ^ (2 : ℕ)))) := by
        refine mul_le_mul (mul_le_mul hzeta hpow (norm_nonneg _) (by positivity))
          hker (norm_nonneg _) ?_
        exact mul_nonneg (by positivity) hX_nn
    _ = K * ((|w.im| + T) ^ N * Real.exp (-(T ^ (2 : ℕ)))) := by dsimp only [K]; ring

/-- **General two-line smooth AFE on arbitrary `[a, b]` (`a < 0 < b`, `w.re + a < 1 < w.re + b`):**
shifting `smoothAFEZetaMellinIntegrand w X` from `Re z = b` (`1 < w.re + b`) across `z = 0` and
`z = 1 - w` to `Re z = a` (`w.re + a < 1`) expresses `∑_{m ≥ 1} m^{-w} W(m / X)` as
`ζ(w) + smoothAFEZetaShiftedPoleResidue w X + smoothAFEZetaMellinAt a w X`. -/
theorem tsum_smoothAFECutoff_eq_zeta_add_residue_add_mellinAt_neg
    {w : ℂ} (hw1 : w ≠ 1) {X a b : ℝ} (hX : 0 < X)
    (ha0 : a < 0) (h0b : 0 < b) (hwa : w.re + a < 1) (hwb : 1 < w.re + b) :
    (∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-w) * smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X)) =
      riemannZeta w + smoothAFEZetaShiftedPoleResidue w X + smoothAFEZetaMellinAt a w X := by
  have hcast :
      (∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-w) * smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X)) =
        ∑' n : ℕ, ((n : ℂ) + 1) ^ (-w) * smoothAFECutoff (((n : ℝ) + 1) / X) :=
    tsum_congr fun n => by push_cast; rfl
  rw [hcast, ← smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff hX h0b hwb]
  have hab : a < b := ha0.trans h0b
  set F : ℂ → ℂ := smoothAFEZetaMellinIntegrand w X
  have hright := tendsto_smoothAFEZetaMellinIntegrand_vertical_general hX (s := w) h0b.ne' (by linarith)
  have hleft := tendsto_smoothAFEZetaMellinIntegrand_vertical_general hX (s := w) ha0.ne (by linarith)
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in a..b, F ((u : ℂ) + (T : ℂ) * I)) atTop (𝓝 0) := by
    refine (tendsto_smoothAFEZetaMellinIntegrand_horizontal_ab hX hab w (ε := 1) (by norm_num)).congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    dsimp only [F]; congr 1; push_cast; ring
  have hbot : Tendsto (fun T : ℝ => ∫ u : ℝ in a..b, F ((u : ℂ) - (T : ℂ) * I)) atTop (𝓝 0) := by
    refine (tendsto_smoothAFEZetaMellinIntegrand_horizontal_ab hX hab w (ε := -1) (by norm_num)).congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    dsimp only [F]; congr 1; push_cast; ring
  have hcomb := ((hbot.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  have hev : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in a..b, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in a..b, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, F ((b : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, F ((a : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * (riemannZeta w + smoothAFEZetaShiftedPoleResidue w X) := by
    filter_upwards [eventually_gt_atTop (|w.im| + 1)] with T hT
    have hT_pos : 0 < T := lt_of_le_of_lt (abs_nonneg w.im) (by linarith)
    have habs := abs_lt.mp (by linarith : |w.im| < T)
    have hbox := rectIntegral_smoothAFEZetaMellinIntegrand_horizontal_box
      (s := w) (x := X) (a := a) (b := b) (T := T) hX hw1 ha0 h0b hT_pos
      (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
    simpa [rectIntegral, F] using! hbox
  have hinf := tendsto_nhds_unique (hcomb.congr' hev) tendsto_const_nhds
  set R_int : ℂ := ∫ v : ℝ, F ((b : ℂ) + (v : ℂ) * I)
  set L_int : ℂ := ∫ v : ℝ, F ((a : ℂ) + (v : ℂ) * I)
  have hcancel : R_int - L_int =
      (2 * Real.pi : ℂ) * (riemannZeta w + smoothAFEZetaShiftedPoleResidue w X) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [R_int, L_int, smul_eq_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hinf
  have hinv : (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (2 * Real.pi : ℂ) = 1 := by
    push_cast; field_simp [Real.pi_ne_zero]
  unfold smoothAFEZetaMellinAt
  rw [Complex.real_smul, Complex.real_smul]
  have hmul := congrArg (fun z : ℂ => (((1 / (2 * Real.pi) : ℝ) : ℂ)) * z) hcancel
  rw [mul_sub, ← mul_assoc, hinv, one_mul] at hmul
  dsimp only [R_int, L_int, F] at hmul
  linear_combination hmul

/-- Uniform constant upper bound on `‖zetaChi (1 - s - v * I)‖` across `3001 / 24000 ≤ s.re < 1 / 2`
and `v : ℝ`, combining compactness on `[1/2, 20999/24000] × [-185, 185]` with Spira's lower bound
`1 ≤ ‖zetaChi (s + v * I)‖` above height `184`. -/
private lemma exists_norm_zetaChi_one_sub_le :
    ∃ M_chi : ℝ, 1 ≤ M_chi ∧ ∀ (s : ℂ) (v : ℝ), 3001 / 24000 ≤ s.re → s.re < 1 / 2 →
      ‖zetaChi (1 - s - (v : ℂ) * I)‖ ≤ M_chi := by
  set φ : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * I
  set K_set : Set ℂ := φ '' (Set.Icc (1 / 2 : ℝ) (20999 / 24000) ×ˢ Set.Icc (-185 : ℝ) 185)
  have hφ_cont : Continuous φ := by dsimp only [φ]; fun_prop
  have hK_comp : IsCompact K_set := (isCompact_Icc.prod isCompact_Icc).image hφ_cont
  have hchi_cont : ContinuousOn zetaChi K_set := by
    rintro z ⟨⟨x, y⟩, ⟨⟨hx_lo, hx_hi⟩, _⟩, rfl⟩
    refine (zetaChi_analyticAt ?_).continuousAt.continuousWithinAt
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    dsimp only [φ]; simp; linarith
  obtain ⟨M₀, hM₀⟩ := hK_comp.exists_bound_of_continuousOn hchi_cont
  refine ⟨max 1 M₀, le_max_left _ _, fun s v hlo hhi => ?_⟩
  set u₀ : ℂ := s + (v : ℂ) * I
  have hu₀_re : u₀.re = s.re := by simp [u₀]
  have h1u₀_eq : 1 - u₀ = 1 - s - (v : ℂ) * I := by dsimp only [u₀]; ring
  rcases le_or_gt (|u₀.im|) 184 with him_le | him_gt
  · have hmem : 1 - s - (v : ℂ) * I ∈ K_set := by
      refine ⟨(1 - s.re, -u₀.im), ⟨⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
      · have habs := abs_le.mp him_le
        exact ⟨by linarith, by linarith⟩
      · (apply Complex.ext <;> simp [φ, u₀]); ring
    exact (hM₀ _ hmem).trans (le_max_right _ _)
  · obtain ⟨_, _, hge⟩ := norm_zetaChi_ge_rpow_above_oneHundredEightyFour
      (s := u₀) (by linarith) (by linarith) him_gt
    have hrp_ge1 : 1 ≤ (|u₀.im| / 7) ^ (1 / 2 - u₀.re) :=
      Real.one_le_rpow (by linarith) (by linarith)
    have hu₀_ge1 : 1 ≤ ‖zetaChi u₀‖ := hrp_ge1.trans hge
    have hG1 : Complex.Gammaℝ u₀ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hG2 : Complex.Gammaℝ (1 - u₀) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simp [hu₀_re]; linarith)
    have hprod : zetaChi (1 - u₀) * zetaChi u₀ = 1 := by
      unfold zetaChi
      rw [sub_sub_cancel, div_mul_div_comm, mul_comm (Complex.Gammaℝ u₀),
        div_self (mul_ne_zero hG2 hG1)]
    have hn_prod : ‖zetaChi (1 - u₀)‖ * ‖zetaChi u₀‖ = 1 := by
      rw [← norm_mul, hprod, norm_one]
    have hle1 : ‖zetaChi (1 - u₀)‖ ≤ 1 := by
      nlinarith [norm_nonneg (zetaChi (1 - u₀))]
    rw [← h1u₀_eq]
    exact hle1.trans (le_max_left _ _)

/-- **Uniform factored bound on `‖riemannZeta (1 - s - 2r - i v)‖` across `3001 / 24000 ≤ Re s < 1 / 2`:**
combining `zeta_eq_zetaChi_mul`, `zetaChi_sub_two_mul`, and `exists_norm_zetaChi_one_sub_le` bounds
`‖ζ(1 - s - 2r - i v)‖` by `C_z * (1 + |Im s|)^{2r} * (1 + |v|)^{2r}` for every `r ≥ 1`. -/
theorem exists_norm_riemannZeta_one_sub_even_le {r : ℕ} (hr : 1 ≤ r) :
    ∃ C_z : ℝ, 0 < C_z ∧ ∀ (s : ℂ) (v : ℝ), 3001 / 24000 ≤ s.re → s.re < 1 / 2 →
      ‖riemannZeta (1 - s - ((2 * r : ℕ) : ℂ) - (v : ℂ) * I)‖ ≤
        C_z * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r) := by
  obtain ⟨M_chi, hM_chi1, hM_chi⟩ := exists_norm_zetaChi_one_sub_le
  set K_lin : ℝ := ((2 * r + 2 : ℕ) : ℝ) ^ (2 * r)
  set K_pi : ℝ := (1 / (4 * Real.pi ^ 2)) ^ r
  set S_maj : ℝ := smoothAFEZetaMajorant 2
  have hS_nn : 0 ≤ S_maj := tsum_nonneg fun _ => by positivity
  refine ⟨K_pi * K_lin * M_chi * (S_maj + 1) + 1, by positivity, fun s v hlo hhi => ?_⟩
  set w : ℂ := 1 - s - ((2 * r : ℕ) : ℂ) - (v : ℂ) * I
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hw_re : w.re = 1 - s.re - 2 * (r : ℝ) := by dsimp only [w]; simp
  have hw_neg : w.re < 0 := by linarith
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw_neg; simp at hw_neg
  have hw1 : w ≠ 1 := fun h => by rw [h] at hw_neg; norm_num at hw_neg
  have h1w_re : 2 < (1 - w).re := by simp [hw_re]; linarith
  have hG_ne : Complex.Gammaℝ (1 - w) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [zeta_eq_zetaChi_mul hw0 hw1 hG_ne, norm_mul]
  -- Bound `‖riemannZeta (1 - w)‖ ≤ S_maj`.
  have hζ_1w : ‖riemannZeta (1 - w)‖ ≤ S_maj := by
    have hrew : 1 - w = (s + ((2 * r : ℕ) : ℂ) - 2) + (((2 : ℝ) : ℂ) + (v : ℂ) * I) := by
      dsimp only [w]; push_cast; ring
    have hmaj := norm_riemannZeta_vertical_le_smoothAFEZetaMajorant
      (s := s + ((2 * r : ℕ) : ℂ) - 2) (c := 2) (by simp; linarith) v
    rw [← hrew] at hmaj
    refine hmaj.trans (Summable.tsum_le_tsum (fun n => ?_)
      (summable_smoothAFEZetaMajorant (by simp; linarith))
      (summable_smoothAFEZetaMajorant (by norm_num)))
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact one_div_le_one_div_of_le (by positivity)
      (Real.rpow_le_rpow_of_exponent_le hn1 (by simp; linarith))
  -- Bound `‖zetaChi w‖` via `zetaChi_sub_two_mul` at `z = 1 - s - v * I`.
  set z : ℂ := 1 - s - (v : ℂ) * I
  have hz0 : 0 < z.re := by simp [z]; linarith
  have hz1 : z.re < 1 := by simp [z]; linarith
  have hchi_eq : zetaChi w =
      ((-1 : ℂ) ^ r / (4 * (Real.pi : ℂ) ^ 2) ^ r) *
        (∏ j ∈ Finset.range (2 * r), (z - ((j + 1 : ℕ) : ℂ))) * zetaChi z := by
    have hw_eq : w = z - ((2 * r : ℕ) : ℂ) := by dsimp only [w, z]; ring
    rw [hw_eq, zetaChi_sub_two_mul hz0 hz1 r]
  rw [hchi_eq, norm_mul, norm_mul]
  have hnorm_pref : ‖(-1 : ℂ) ^ r / (4 * (Real.pi : ℂ) ^ 2) ^ r‖ = K_pi := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow, norm_mul,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    dsimp only [K_pi]
    rw [show ‖(4 : ℂ)‖ = 4 by norm_num, div_pow, one_pow]
  have hprod_le : ‖∏ j ∈ Finset.range (2 * r), (z - ((j + 1 : ℕ) : ℂ))‖ ≤
      K_lin * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r) := by
    rw [norm_prod]
    have hfac : ∀ j ∈ Finset.range (2 * r),
        ‖z - ((j + 1 : ℕ) : ℂ)‖ ≤ ((2 * r + 2 : ℕ) : ℝ) * (1 + |s.im|) * (1 + |v|) := by
      intro j hj
      have hj_lt : j < 2 * r := Finset.mem_range.mp hj
      have h1 := Complex.norm_le_abs_re_add_abs_im (z - ((j + 1 : ℕ) : ℂ))
      have hre_j : |(z - ((j + 1 : ℕ) : ℂ)).re| ≤ ((2 * r + 2 : ℕ) : ℝ) := by
        rw [Complex.sub_re, show z.re = 1 - s.re by simp [z], Complex.natCast_re, abs_le]
        have hj_le : (j + 1 : ℝ) ≤ (2 * r : ℝ) := by exact_mod_cast hj_lt
        constructor <;> push_cast <;> linarith
      have him_j : |(z - ((j + 1 : ℕ) : ℂ)).im| ≤ |s.im| + |v| := by
        have him_eq : (z - ((j + 1 : ℕ) : ℂ)).im = -(s.im + v) := by simp [z]; ring
        rw [him_eq, abs_neg]
        exact abs_add_le _ _
      have hM1 : (1 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)
      nlinarith [abs_nonneg s.im, abs_nonneg v, mul_nonneg (abs_nonneg s.im) (abs_nonneg v)]
    calc (∏ j ∈ Finset.range (2 * r), ‖z - ((j + 1 : ℕ) : ℂ)‖)
        ≤ ∏ _j ∈ Finset.range (2 * r), (((2 * r + 2 : ℕ) : ℝ) * (1 + |s.im|) * (1 + |v|)) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfac
      _ = K_lin * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r) := by
          rw [Finset.prod_const, Finset.card_range, mul_pow, mul_pow]
  have hchi_z : ‖zetaChi z‖ ≤ M_chi := hM_chi s v hlo hhi
  rw [hnorm_pref]
  have hchi_full : K_pi * ‖∏ j ∈ Finset.range (2 * r), (z - ((j + 1 : ℕ) : ℂ))‖ * ‖zetaChi z‖ ≤
      (K_pi * K_lin * M_chi) * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r) := by
    calc K_pi * ‖∏ j ∈ Finset.range (2 * r), (z - ((j + 1 : ℕ) : ℂ))‖ * ‖zetaChi z‖
        ≤ K_pi * (K_lin * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r)) * M_chi :=
          mul_le_mul (mul_le_mul_of_nonneg_left hprod_le (by positivity))
            hchi_z (norm_nonneg _) (by positivity)
      _ = (K_pi * K_lin * M_chi) * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r) := by ring
  have hζ_le1 : ‖riemannZeta (1 - w)‖ ≤ S_maj + 1 := by linarith
  calc (K_pi * ‖∏ j ∈ Finset.range (2 * r), (z - ((j + 1 : ℕ) : ℂ))‖ * ‖zetaChi z‖) *
        ‖riemannZeta (1 - w)‖
      ≤ ((K_pi * K_lin * M_chi) * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r)) * (S_maj + 1) :=
        mul_le_mul hchi_full hζ_le1 (norm_nonneg _) (by positivity)
    _ ≤ (K_pi * K_lin * M_chi * (S_maj + 1) + 1) * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r) := by
        have hpos : 0 ≤ (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r) := by positivity
        nlinarith

end Part1TwoLineSmoothAFEAndNegativeZeta


/-! ### Part 2: Smooth Outer-Weighted Reflected-Möbius Cross-Height Sieve Identity -/

section Part2SmoothOuterMobiusSieveIdentity

/-- Smooth outer-weighted pole-cleared Möbius Dirichlet series
`(1 - 2^{-z}) ∑_{d ≥ 1} μ(d) d^{-z} W(d / Y)`. -/
def smoothOuterMoebiusSeries (Y : ℝ) (z : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (-z)) *
    ∑' d : ℕ, (ArithmeticFunction.moebius (d + 1) : ℂ) *
      ((d + 1 : ℕ) : ℂ) ^ (-z) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)

/-- Pole-cleared direct Gaussian sum at divisor `d ≥ 1`:
`∑_{n ≥ 1} n^{-s} (W(n / (d x)) - 2^{-(1 - s)} W(n / (2 d x)))`. -/
def smoothOuterDirectPairSum (s : ℂ) (x : ℝ) (d : ℕ) : ℂ :=
  ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
    (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)) -
      (2 : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))))

/-- Smooth outer-weighted dual sieve coefficient at `k ≥ 1`:
`∑_{d ∣ k} μ(d) W(d / Y) - 1_{2 ∣ k} ∑_{d ∣ k / 2} μ(d) W(d / Y)`. -/
def smoothOuterSieveCoeff (Y : ℝ) (k : ℕ) : ℂ :=
  (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℂ) * smoothAFECutoff ((d : ℝ) / Y)) -
    (if 2 ∣ k then
      ∑ d ∈ (k / 2).divisors, (ArithmeticFunction.moebius d : ℂ) * smoothAFECutoff ((d : ℝ) / Y)
    else 0)

private lemma norm_moebius_intCast_le_one' (d : ℕ) :
    ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
  by_cases h : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast
    rw [norm_pow, norm_neg, norm_one, one_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    simp

private lemma sum_divisors_moebius_eq_zero_of_two_le {m : ℕ} (hm2 : 2 ≤ m) :
    (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ)) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    if_neg (by omega : m ≠ 1)] at h
  have hc := congrArg (Int.cast : ℤ → ℂ) h
  push_cast at hc
  exact hc

lemma smoothOuterSieveCoeff_one (Y : ℝ) :
    smoothOuterSieveCoeff Y 1 = smoothAFECutoff (1 / Y) := by
  unfold smoothOuterSieveCoeff
  have hndvd : ¬ (2 ∣ (1 : ℕ)) := by omega
  rw [Nat.divisors_one, if_neg hndvd, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one]
  simp

lemma smoothOuterSieveCoeff_two (Y : ℝ) :
    smoothOuterSieveCoeff Y 2 = -smoothAFECutoff (2 / Y) := by
  unfold smoothOuterSieveCoeff
  have hdiv2 : (2 : ℕ).divisors = {1, 2} := by decide
  rw [hdiv2, if_pos (dvd_refl 2), Nat.div_self two_pos, Nat.divisors_one,
    Finset.sum_pair (by omega : (1 : ℕ) ≠ 2), Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  push_cast; ring

/-- For every `k ≥ 3` and `B > 0`, Möbius inversion `∑_{d ∣ m} μ(d) = 0` (`m ≥ 2`) allows
subtracting `1` from `smoothAFECutoff (d / Y)`, giving
`‖smoothOuterSieveCoeff Y k‖ ≤ 2 K_B k^{1 + B} Y^{-B}`. -/
lemma norm_smoothOuterSieveCoeff_le_rpow_of_three_le
    {B K_B : ℝ} (hB : 0 < B) (hKB0 : 0 ≤ K_B)
    (hKB : ∀ {u : ℝ}, 0 < u → ‖smoothAFECutoff u - 1‖ ≤ K_B * u ^ B)
    {Y : ℝ} (hY : 0 < Y) {k : ℕ} (hk3 : 3 ≤ k) :
    ‖smoothOuterSieveCoeff Y k‖ ≤ 2 * K_B * (k : ℝ) ^ (1 + B) * Y ^ (-B) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hdiv_bd : ∀ {m : ℕ}, 2 ≤ m → m ≤ k →
      ‖∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * smoothAFECutoff ((d : ℝ) / Y)‖ ≤
        K_B * (k : ℝ) ^ (1 + B) * Y ^ (-B) := by
    intro m hm2 hmk
    have hm_pos : 0 < m := by omega
    have h0 := sum_divisors_moebius_eq_zero_of_two_le hm2
    have hsub_eq :
        (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * smoothAFECutoff ((d : ℝ) / Y)) =
          ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * (smoothAFECutoff ((d : ℝ) / Y) - 1) := by
      simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, h0, sub_zero]
    rw [hsub_eq]
    have hsub_Icc : m.divisors ⊆ Finset.Icc 1 m := fun d hd => by
      have hdv := Nat.dvd_of_mem_divisors hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdv hm_pos, Nat.le_of_dvd hm_pos hdv⟩
    have hcard : (m.divisors.card : ℝ) ≤ (k : ℝ) := by
      have hc1 : m.divisors.card ≤ (Finset.Icc 1 m).card := Finset.card_le_card hsub_Icc
      rw [Nat.card_Icc, Nat.add_sub_cancel_right] at hc1
      exact_mod_cast hc1.trans hmk
    have hpt : ∀ d ∈ m.divisors,
        ‖(ArithmeticFunction.moebius d : ℂ) * (smoothAFECutoff ((d : ℝ) / Y) - 1)‖ ≤
          K_B * ((k : ℝ) / Y) ^ B := by
      intro d hd
      have hd_Icc := hsub_Icc hd
      obtain ⟨hd1, hdm⟩ := Finset.mem_Icc.mp hd_Icc
      have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hdk : (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast hdm.trans hmk
      rw [norm_mul]
      have hW := (hKB (div_pos hd_pos hY)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hdk hY.le) hB.le) hKB0)
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_intCast_le_one' d)).trans hW
    calc ‖∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * (smoothAFECutoff ((d : ℝ) / Y) - 1)‖
        ≤ ∑ d ∈ m.divisors, ‖(ArithmeticFunction.moebius d : ℂ) * (smoothAFECutoff ((d : ℝ) / Y) - 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _d ∈ m.divisors, K_B * ((k : ℝ) / Y) ^ B := Finset.sum_le_sum hpt
      _ = (m.divisors.card : ℝ) * (K_B * ((k : ℝ) / Y) ^ B) := by simp
      _ ≤ (k : ℝ) * (K_B * ((k : ℝ) / Y) ^ B) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = K_B * ((k : ℝ) ^ (1 : ℝ) * (k : ℝ) ^ B) * Y ^ (-B) := by
          rw [Real.rpow_one, Real.div_rpow hk_pos.le hY.le, div_eq_mul_inv, ← Real.rpow_neg hY.le]
          ring
      _ = K_B * (k : ℝ) ^ (1 + B) * Y ^ (-B) := by rw [← Real.rpow_add hk_pos]
  unfold smoothOuterSieveCoeff
  refine (norm_sub_le _ _).trans ?_
  have h1 := hdiv_bd (by omega) le_rfl
  have h2 : ‖if 2 ∣ k then
      ∑ d ∈ (k / 2).divisors, (ArithmeticFunction.moebius d : ℂ) * smoothAFECutoff ((d : ℝ) / Y)
      else 0‖ ≤ K_B * (k : ℝ) ^ (1 + B) * Y ^ (-B) := by
    split_ifs with h2k
    · exact hdiv_bd (by omega) (Nat.div_le_self k 2)
    · rw [norm_zero]; positivity
  linarith

private lemma norm_smoothAFECutoff_div_le {A K : ℝ}
    (hK : ∀ {u : ℝ}, 0 < u → ‖smoothAFECutoff u‖ ≤ K * u ^ (-A))
    {u y : ℝ} (hu : 0 < u) (hy : 0 < y) :
    ‖smoothAFECutoff (u / y)‖ ≤ K * ((u ^ A)⁻¹ * y ^ A) := by
  have h := hK (div_pos hu hy)
  rwa [Real.div_rpow hu.le hy.le, Real.rpow_neg hu.le, Real.rpow_neg hy.le, div_inv_eq_mul] at h

/-- Uniform bound on `‖smoothOuterDirectPairSum s x d‖` (`d ≥ 1`, `A ≥ 2`) for summability and
head truncation. -/
lemma norm_smoothOuterDirectPairSum_le
    {A K_cut : ℝ} (hA2 : 2 ≤ A) (hK_cut0 : 0 ≤ K_cut)
    (hK_cut : ∀ {u : ℝ}, 0 < u → ‖smoothAFECutoff u‖ ≤ K_cut * u ^ (-A))
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    {x : ℝ} (hx : 0 < x) {d : ℕ} (hd1 : 1 ≤ d) :
    ‖smoothOuterDirectPairSum s x d‖ ≤
      (1 + (2 : ℝ) ^ A) * K_cut * smoothAFEZetaMajorant 2 * ((d : ℝ) * x) ^ A := by
  have hA_pos : 0 < A := by linarith
  have hsA : 1 < s.re + A := by linarith
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hdx : 0 < (d : ℝ) * x := mul_pos hd_pos hx
  have h2dx : 0 < 2 * (d : ℝ) * x := by positivity
  have h2_le1 : ‖(2 : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos, show (-(1 - s)).re = -(1 - s.re) by simp]
    exact Real.rpow_le_one_of_one_le_of_nonpos one_lt_two.le (by linarith)
  have hsingle : ∀ {y : ℝ}, 0 < y →
      ‖∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / y)‖ ≤
        K_cut * smoothAFEZetaMajorant 2 * y ^ A := by
    intro y hy
    have hsum_maj := (summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left (K_cut * y ^ A)
    have hpt : ∀ n : ℕ,
        ‖((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / y)‖ ≤
          (K_cut * y ^ A) * (1 / (n + 1 : ℝ) ^ (2 : ℝ)) := by
      intro n
      have hn_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      rw [norm_mul, show ((n + 1 : ℕ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hn_pos, Complex.neg_re]
      have hW := norm_smoothAFECutoff_div_le hK_cut hn_pos hy
      calc ((n + 1 : ℕ) : ℝ) ^ (-s.re) * ‖smoothAFECutoff (((n + 1 : ℕ) : ℝ) / y)‖
          ≤ ((n + 1 : ℕ) : ℝ) ^ (-s.re) * (K_cut * ((((n + 1 : ℕ) : ℝ) ^ A)⁻¹ * y ^ A)) :=
            mul_le_mul_of_nonneg_left hW (by positivity)
        _ = (K_cut * y ^ A) * (((n + 1 : ℕ) : ℝ) ^ (-s.re) * ((n + 1 : ℕ) : ℝ) ^ (-A)) := by
            rw [Real.rpow_neg hn_pos.le A]; ring
        _ = (K_cut * y ^ A) * ((n + 1 : ℕ) : ℝ) ^ (-(s.re + A)) := by
            rw [← Real.rpow_add hn_pos]; congr 2; ring
        _ ≤ (K_cut * y ^ A) * ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by positivity)
        _ = (K_cut * y ^ A) * (1 / (n + 1 : ℝ) ^ (2 : ℝ)) := by
            rw [Real.rpow_neg hn_pos.le, one_div]; push_cast; rfl
    have hs_dir := summable_smoothAFE_direct hA_pos hy hsA
    calc ‖∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / y)‖
        ≤ ∑' n : ℕ, ‖((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / y)‖ :=
          norm_tsum_le_tsum_norm hs_dir.norm
      _ ≤ ∑' n : ℕ, (K_cut * y ^ A) * (1 / (n + 1 : ℝ) ^ (2 : ℝ)) :=
          Summable.tsum_le_tsum hpt hs_dir.norm hsum_maj
      _ = K_cut * smoothAFEZetaMajorant 2 * y ^ A := by
          rw [tsum_mul_left]; unfold smoothAFEZetaMajorant; ring
  have hs1 := summable_smoothAFE_direct hA_pos hdx hsA
  have hs2 := (summable_smoothAFE_direct hA_pos h2dx hsA).mul_left ((2 : ℂ) ^ (-(1 - s)))
  have hsplit : smoothOuterDirectPairSum s x d =
      (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x))) -
        (2 : ℂ) ^ (-(1 - s)) *
          ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x)) := by
    unfold smoothOuterDirectPairSum
    rw [← tsum_mul_left, ← hs1.tsum_sub hs2]
    exact tsum_congr fun _ => by ring
  rw [hsplit]
  have ht := norm_sub_le
    (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((d : ℝ) * x)))
    ((2 : ℂ) ^ (-(1 - s)) *
      ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x)))
  rw [norm_mul] at ht
  have hb1 := hsingle hdx
  have hb2 :
      ‖∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * (d : ℝ) * x))‖ ≤
        (2 : ℝ) ^ A * (K_cut * smoothAFEZetaMajorant 2 * ((d : ℝ) * x) ^ A) :=
    (hsingle h2dx).trans_eq
      (by rw [mul_assoc (2 : ℝ) (d : ℝ) x, Real.mul_rpow two_pos.le hdx.le]; ring)
  have hm2 := (mul_le_of_le_one_left (norm_nonneg _) h2_le1).trans hb2
  have hcomb_lin :
      K_cut * smoothAFEZetaMajorant 2 * ((d : ℝ) * x) ^ A +
        (2 : ℝ) ^ A * (K_cut * smoothAFEZetaMajorant 2 * ((d : ℝ) * x) ^ A) =
      (1 + (2 : ℝ) ^ A) * K_cut * smoothAFEZetaMajorant 2 * ((d : ℝ) * x) ^ A := by ring
  linarith

private lemma tsum_dvd_shift_eq {q : ℕ} (hq : 1 ≤ q) (f : ℕ → ℂ) :
    (∑' m : ℕ, f (q * (m + 1) - 1)) =
      ∑' k : ℕ, if q ∣ (k + 1) then f k else 0 := by
  set g : ℕ → ℂ := fun k => if q ∣ (k + 1) then f k else 0
  set ι : ℕ → ℕ := fun m => q * (m + 1) - 1
  have hι_add1 : ∀ m : ℕ, ι m + 1 = q * (m + 1) := fun m =>
    Nat.sub_add_cancel (Nat.mul_pos hq (Nat.succ_pos m))
  have hι_inj : Function.Injective ι := fun m₁ m₂ heq => by
    have h1 : ι m₁ + 1 = ι m₂ + 1 := congrArg (· + 1) heq
    rw [hι_add1, hι_add1] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left hq h1
    omega
  have hcomp : (fun m : ℕ => f (q * (m + 1) - 1)) = fun m : ℕ => g (ι m) := by
    funext m; dsimp only [g]; rw [hι_add1 m, if_pos (dvd_mul_right q (m + 1))]
  rw [hcomp]
  refine Function.Injective.tsum_eq hι_inj fun k hk => ?_
  rw [Function.mem_support] at hk
  have hdvd : q ∣ (k + 1) := by
    by_contra hnd; exact hk (by dsimp only [g]; exact if_neg hnd)
  obtain ⟨c, hc⟩ := hdvd
  have hc_pos : 1 ≤ c := by
    by_contra hc0; have h0 : c = 0 := by omega
    rw [h0, mul_zero] at hc; omega
  refine ⟨c - 1, ?_⟩
  dsimp only [ι]; rw [Nat.sub_add_cancel hc_pos, ← hc]; omega

/-- **Exact smooth outer-weighted reflected-Möbius cross-height sieve identity:**
for all `x > 0`, `Y > 0`, and `0 < Re s < 1 / 2`, weighting `crossHeight_gaussian_two_tsum_eq`
at `(d x, 2 d x)` by `μ(d) d^{-(1 - s)} W(d / Y)` over all `d ≥ 1` cancels the `s = 1` pole
residue identically and separates the two-mode dual vacuum from the `k ≥ 3` smooth sieve tail. -/
theorem smoothOuter_poleCleared_reflected_moebius_crossHeight_eq
    {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    riemannZeta s * smoothOuterMoebiusSeries Y (1 - s) =
      (∑' d : ℕ, (ArithmeticFunction.moebius (d + 1) : ℂ) *
          ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
          smoothOuterDirectPairSum s x (d + 1)) -
        (smoothAFECutoff (1 / Y) * smoothAFEZetaDualCoefficientGeneral s x 0 -
          smoothAFECutoff (2 / Y) * smoothAFEZetaDualCoefficientGeneral s x 1) -
        ∑' j : ℕ, smoothOuterSieveCoeff Y (j + 3) *
          smoothAFEZetaDualCoefficientGeneral s x (j + 2) := by
  -- Deep `r = 1` dual bound gives `‖I(s, x, k)‖ ≤ C_d1 * (k + 1)^{s.re - 3}`.
  obtain ⟨K_d1, hK_d1_pos, hK_d1⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := s.re / 2) (by linarith) (by linarith) (r := 1) le_rfl
  set C_d1 : ℝ := K_d1 * x ^ (-2 * ((1 : ℕ) : ℝ)) * (1 + |s.im|) ^ (2 * ((1 : ℕ) : ℝ) + 1 / 2 - s.re)
  have hI_le : ∀ k : ℕ, ‖smoothAFEZetaDualCoefficientGeneral s x k‖ ≤
      C_d1 * (k + 1 : ℝ) ^ (-(2 * ((1 : ℕ) : ℝ) + 1 - s.re)) :=
    fun k => (hK_d1 s x (by linarith) hhi hx).1 k
  have hsum_du : Summable (fun k : ℕ => smoothAFEZetaDualCoefficientGeneral s x k) := by
    refine Summable.of_norm_bounded
      ((summable_smoothAFEZetaMajorant (p := 2 * ((1 : ℕ) : ℝ) + 1 - s.re) (by push_cast; linarith)).mul_left C_d1)
      fun k => ?_
    rw [one_div, ← Real.rpow_neg (by positivity)]
    exact hI_le k
  -- Single-scale rescaled cross-height identity for `q ≥ 1`.
  have hscale_q : ∀ {q : ℕ}, 1 ≤ q →
      (q : ℂ) ^ (-(1 - s)) * riemannZeta s =
        (q : ℂ) ^ (-(1 - s)) *
            (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / ((q : ℝ) * x)))) -
          (∑' k : ℕ, if q ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
          smoothAFEZetaShiftedPoleResidue s x := by
    intro q hq
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hfe := crossHeight_gaussian_two_tsum_eq unitPoleFreeCrossHeightDatum_riemannZeta (mul_pos hq_pos hx) hs0 hhi
    unfold crossHeightGaussianTwoSeries at hfe
    simp only [one_mul, Complex.ofReal_one, Complex.one_cpow, div_one] at hfe
    have hmul := congrArg (fun z : ℂ => (q : ℂ) ^ (-(1 - s)) * z) hfe
    rw [mul_sub, mul_sub, smoothAFEZetaShiftedPoleResidue_mul_scale hq hx s] at hmul
    have hdu_congr :
        (q : ℂ) ^ (-(1 - s)) * (∑' m : ℕ, smoothAFEZetaDualCoefficientGeneral s ((q : ℝ) * x) m) =
          ∑' k : ℕ, if q ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0 := by
      rw [← tsum_mul_left,
        tsum_congr (fun m => smoothAFEZetaDualCoefficientGeneral_mul_scale hq hx hs0 hhi m)]
      exact tsum_dvd_shift_eq hq _
    rwa [hdu_congr] at hmul
  -- Termwise identity for each `d : ℕ` (`q = d + 1` minus `2^{-(1 - s)}` times `q = 2 * (d + 1)`).
  set w_d : ℕ → ℂ := fun d =>
    (ArithmeticFunction.moebius (d + 1) : ℂ) *
      ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)
  set g_du : ℕ → ℕ → ℂ := fun d k =>
    (ArithmeticFunction.moebius (d + 1) : ℂ) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
      ((if (d + 1) ∣ (k + 1) then (1 : ℂ) else 0) -
        (if 2 * (d + 1) ∣ (k + 1) then (1 : ℂ) else 0)) *
      smoothAFEZetaDualCoefficientGeneral s x k
  have hterm_d : ∀ d : ℕ,
      w_d d * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s) =
        w_d d * smoothOuterDirectPairSum s x (d + 1) - ∑' k : ℕ, g_du d k := by
    intro d
    have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
    have h2d1 : 1 ≤ 2 * (d + 1) := by omega
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
    have h2d_cpow : ((2 * (d + 1) : ℕ) : ℂ) ^ (-(1 - s)) =
        (2 : ℂ) ^ (-(1 - s)) * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) := by
      rw [show ((2 * (d + 1) : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg two_pos.le hd_pos.le (-(1 - s))]
      push_cast; rfl
    have h1 := hscale_q hd1
    have h2 := hscale_q h2d1
    rw [h2d_cpow, show ((2 * (d + 1) : ℕ) : ℝ) * x = 2 * ((d + 1 : ℕ) : ℝ) * x by push_cast; ring] at h2
    have hs_dir1 := summable_smoothAFE_direct (A := 2) (by norm_num) (mul_pos hd_pos hx) (by linarith)
    have hs_dir2 := (summable_smoothAFE_direct (A := 2) (by norm_num)
      (show 0 < 2 * ((d + 1 : ℕ) : ℝ) * x by positivity) (by linarith)).mul_left ((2 : ℂ) ^ (-(1 - s)))
    have hdir_sub :
        (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) * x)))) -
          (2 : ℂ) ^ (-(1 - s)) *
            (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
              smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * ((d + 1 : ℕ) : ℝ) * x)))) =
          smoothOuterDirectPairSum s x (d + 1) := by
      unfold smoothOuterDirectPairSum
      rw [← tsum_mul_left, ← hs_dir1.tsum_sub hs_dir2]
      exact tsum_congr fun _ => by ring
    have hdu1 : Summable (fun k : ℕ =>
        if (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) :=
      Summable.of_norm_bounded hsum_du.norm fun k => by split_ifs <;> simp
    have hdu2 : Summable (fun k : ℕ =>
        if 2 * (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) :=
      Summable.of_norm_bounded hsum_du.norm fun k => by split_ifs <;> simp
    have hdu_sub :
        (ArithmeticFunction.moebius (d + 1) : ℂ) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
          ((∑' k : ℕ, if (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
            (∑' k : ℕ, if 2 * (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0)) =
          ∑' k : ℕ, g_du d k := by
      rw [← hdu1.tsum_sub hdu2, ← tsum_mul_left]
      refine tsum_congr fun k => ?_
      dsimp only [g_du]; split_ifs <;> ring
    have hdiff : ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s) =
        ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * riemannZeta s -
          (2 : ℂ) ^ (-(1 - s)) * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * riemannZeta s := by ring
    dsimp only [w_d]
    calc (ArithmeticFunction.moebius (d + 1) : ℂ) * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
            smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s)
        = (ArithmeticFunction.moebius (d + 1) : ℂ) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
            (((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s)) := by ring
      _ = (ArithmeticFunction.moebius (d + 1) : ℂ) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
            (((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
                ((∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
                    smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) * x)))) -
                  (2 : ℂ) ^ (-(1 - s)) *
                    (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (-s) *
                      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / (2 * ((d + 1 : ℕ) : ℝ) * x))))) -
              ((∑' k : ℕ, if (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0) -
                (∑' k : ℕ, if 2 * (d + 1) ∣ (k + 1) then smoothAFEZetaDualCoefficientGeneral s x k else 0))) := by
          rw [hdiff, h1, h2]; ring
      _ = (ArithmeticFunction.moebius (d + 1) : ℂ) * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
            smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) * smoothOuterDirectPairSum s x (d + 1) -
          ∑' k : ℕ, g_du d k := by rw [hdir_sub, mul_sub, ← hdu_sub]; ring
  -- Summability of `w_d`, `w_d * smoothOuterDirectPairSum`, and uncurried `g_du` on `ℕ × ℕ`.
  obtain ⟨K₄, hK₄0, hK₄⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 4) (by norm_num)
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) (by norm_num)
  have hw_sum : Summable w_d := by
    refine Summable.of_norm_bounded
      ((summable_smoothAFEZetaMajorant (p := 4) (by norm_num)).mul_left (K₄ * Y ^ (4 : ℝ)))
      fun d => ?_
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos d
    have hd1_le : ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
      rw [show ((d + 1 : ℕ) : ℂ) = (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hd_pos]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_pos d) (by simp; linarith)
    have hW := norm_smoothAFECutoff_div_le hK₄ hd_pos hY
    dsimp only [w_d]
    rw [norm_mul, norm_mul]
    calc ‖(ArithmeticFunction.moebius (d + 1) : ℂ)‖ * ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ *
            ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖
        ≤ 1 * 1 * (K₄ * ((((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ * Y ^ (4 : ℝ))) :=
          mul_le_mul (mul_le_mul (norm_moebius_intCast_le_one' _) hd1_le (norm_nonneg _) zero_le_one)
            hW (norm_nonneg _) (by positivity)
      _ = (K₄ * Y ^ (4 : ℝ)) * (1 / (d + 1 : ℝ) ^ (4 : ℝ)) := by push_cast; ring
  have hdir_sum : Summable (fun d : ℕ => w_d d * smoothOuterDirectPairSum s x (d + 1)) := by
    set C_p : ℝ := (1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2 * x ^ (2 : ℝ)
    refine Summable.of_norm_bounded
      ((summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left (K₄ * Y ^ (4 : ℝ) * C_p))
      fun d => ?_
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos d
    have hd1_le : ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
      rw [show ((d + 1 : ℕ) : ℂ) = (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hd_pos]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_pos d) (by simp; linarith)
    have hW := norm_smoothAFECutoff_div_le hK₄ hd_pos hY
    have hp := norm_smoothOuterDirectPairSum_le (le_refl 2) hK₂0 hK₂ hs0 hhi hx (Nat.succ_pos d)
    rw [Real.mul_rpow hd_pos.le hx.le] at hp
    have hp' : ‖smoothOuterDirectPairSum s x (d + 1)‖ ≤ C_p * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
      dsimp only [C_p]; linarith
    dsimp only [w_d]
    rw [norm_mul, norm_mul, norm_mul]
    have hwd_le : ‖(ArithmeticFunction.moebius (d + 1) : ℂ)‖ * ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ *
        ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ ≤
        K₄ * Y ^ (4 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ := by
      calc ‖(ArithmeticFunction.moebius (d + 1) : ℂ)‖ * ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ *
              ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖
          ≤ 1 * 1 * (K₄ * ((((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ * Y ^ (4 : ℝ))) :=
            mul_le_mul (mul_le_mul (norm_moebius_intCast_le_one' _) hd1_le (norm_nonneg _) zero_le_one)
              hW (norm_nonneg _) (by positivity)
        _ = K₄ * Y ^ (4 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ := by ring
    have hrpow_cancel : (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) =
        1 / (d + 1 : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_neg hd_pos.le, ← Real.rpow_add hd_pos,
        show (-4 : ℝ) + 2 = -2 by norm_num, Real.rpow_neg hd_pos.le, one_div]
      push_cast; rfl
    calc ‖(ArithmeticFunction.moebius (d + 1) : ℂ)‖ * ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ *
            ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ * ‖smoothOuterDirectPairSum s x (d + 1)‖
        ≤ (K₄ * Y ^ (4 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹) *
            (C_p * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) :=
          mul_le_mul hwd_le hp' (norm_nonneg _) (by positivity)
      _ = (K₄ * Y ^ (4 : ℝ) * C_p) * ((((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) := by ring
      _ = (K₄ * Y ^ (4 : ℝ) * C_p) * (1 / (d + 1 : ℝ) ^ (2 : ℝ)) := by rw [hrpow_cancel]
  -- Product majorant `A_d d * B_k k` for `g_du` on `ℕ × ℕ`.
  set A_d : ℕ → ℝ := fun d => K₄ * Y ^ (4 : ℝ) * (1 / (d + 1 : ℝ) ^ (4 : ℝ))
  set B_k : ℕ → ℝ := fun k => 2 * ‖smoothAFEZetaDualCoefficientGeneral s x k‖
  have hA_sum : Summable A_d :=
    (summable_smoothAFEZetaMajorant (p := 4) (by norm_num)).mul_left (K₄ * Y ^ (4 : ℝ))
  have hB_sum : Summable B_k := hsum_du.norm.mul_left 2
  have hg_maj : ∀ d k : ℕ, ‖g_du d k‖ ≤ A_d d * B_k k := fun d k => by
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos d
    have hW := norm_smoothAFECutoff_div_le hK₄ hd_pos hY
    have hite : ‖(if (d + 1) ∣ (k + 1) then (1 : ℂ) else 0) -
        (if 2 * (d + 1) ∣ (k + 1) then (1 : ℂ) else 0)‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖if (d + 1) ∣ (k + 1) then (1 : ℂ) else 0‖ ≤ 1 := by split_ifs <;> simp
      have h2 : ‖if 2 * (d + 1) ∣ (k + 1) then (1 : ℂ) else 0‖ ≤ 1 := by split_ifs <;> simp
      linarith
    dsimp only [g_du, A_d, B_k]
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖(ArithmeticFunction.moebius (d + 1) : ℂ)‖ *
            ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ *
            ‖(if (d + 1) ∣ (k + 1) then (1 : ℂ) else 0) -
              (if 2 * (d + 1) ∣ (k + 1) then (1 : ℂ) else 0)‖ *
            ‖smoothAFEZetaDualCoefficientGeneral s x k‖
        ≤ 1 * (K₄ * ((((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ * Y ^ (4 : ℝ))) * 2 *
            ‖smoothAFEZetaDualCoefficientGeneral s x k‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul
              (mul_le_mul (norm_moebius_intCast_le_one' _) hW (norm_nonneg _) zero_le_one)
              hite (norm_nonneg _) (by positivity))
            (norm_nonneg _)
      _ = (K₄ * Y ^ (4 : ℝ) * (1 / (d + 1 : ℝ) ^ (4 : ℝ))) *
            (2 * ‖smoothAFEZetaDualCoefficientGeneral s x k‖) := by push_cast; ring
  have hg_uncurry : Summable (Function.uncurry g_du) :=
    Summable.of_norm_bounded
      (hA_sum.mul_of_nonneg hB_sum (fun _ => by dsimp only [A_d]; positivity)
        (fun _ => by dsimp only [B_k]; positivity))
      fun p => hg_maj p.1 p.2
  have hg_row : ∀ d : ℕ, Summable (fun k : ℕ => g_du d k) := fun d =>
    Summable.of_norm_bounded (hB_sum.mul_left (A_d d)) (fun k => hg_maj d k)
  have hg_col : ∀ k : ℕ, Summable (fun d : ℕ => g_du d k) := fun k =>
    Summable.of_norm_bounded (hA_sum.mul_right (B_k k)) (fun d => hg_maj d k)
  have hg_d_sum : Summable (fun d : ℕ => ∑' k : ℕ, g_du d k) := by
    refine Summable.of_norm_bounded (hA_sum.mul_right (∑' k : ℕ, B_k k)) fun d => ?_
    calc ‖∑' k : ℕ, g_du d k‖
        ≤ ∑' k : ℕ, ‖g_du d k‖ := norm_tsum_le_tsum_norm (hg_row d).norm
      _ ≤ ∑' k : ℕ, A_d d * B_k k :=
          Summable.tsum_le_tsum (fun k => hg_maj d k) (hg_row d).norm (hB_sum.mul_left (A_d d))
      _ = A_d d * ∑' k : ℕ, B_k k := tsum_mul_left
  -- Identify `∑' d, g_du d k` with `smoothOuterSieveCoeff Y (k + 1) * I(s, x, k)`.
  have hcol_eq : ∀ k : ℕ,
      (∑' d : ℕ, g_du d k) =
        smoothOuterSieveCoeff Y (k + 1) * smoothAFEZetaDualCoefficientGeneral s x k := by
    intro k
    have hfin : ∀ d : ℕ, k + 1 ≤ d → g_du d k = 0 := fun d hkd => by
      have hnd1 : ¬ ((d + 1) ∣ (k + 1)) := fun h => by
        have := Nat.le_of_dvd (Nat.succ_pos k) h; omega
      have hnd2 : ¬ (2 * (d + 1) ∣ (k + 1)) := fun h => by
        have := Nat.le_of_dvd (Nat.succ_pos k) h; omega
      dsimp only [g_du]; rw [if_neg hnd1, if_neg hnd2]; ring
    rw [tsum_eq_sum (s := Finset.range (k + 1)) fun d hd =>
      hfin d (Nat.le_of_not_lt (Finset.mem_range.not.mp hd))]
    dsimp only [g_du]
    rw [← Finset.sum_mul]
    congr 1
    -- Split `range (k + 1)` into the two indicator sums and match `(k + 1).divisors` and `((k + 1) / 2).divisors`.
    unfold smoothOuterSieveCoeff
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    · have h1 :
          (∑ d ∈ Finset.range (k + 1),
            (ArithmeticFunction.moebius (d + 1) : ℂ) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
              (if (d + 1) ∣ (k + 1) then (1 : ℂ) else 0)) =
          ∑ q ∈ Finset.Icc 1 (k + 1),
            if q ∣ (k + 1) then
              (ArithmeticFunction.moebius q : ℂ) * smoothAFECutoff ((q : ℝ) / Y)
            else 0 := by
        refine Finset.sum_bij (fun d _ => d + 1)
          (fun d hd => Finset.mem_Icc.mpr ⟨Nat.succ_pos d, by have := Finset.mem_range.mp hd; omega⟩)
          (fun _ _ _ _ h => by omega)
          (fun q hq => ⟨q - 1, Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hq; omega),
            by have := Finset.mem_Icc.mp hq; omega⟩)
          (fun d _ => by split_ifs <;> ring)
      rw [h1, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext q
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      exact ⟨fun ⟨⟨_, _⟩, hdv⟩ => ⟨hdv, Nat.succ_ne_zero k⟩,
        fun ⟨hdv, _⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hdv (Nat.succ_pos k),
          Nat.le_of_dvd (Nat.succ_pos k) hdv⟩, hdv⟩⟩
    · by_cases h2k : 2 ∣ (k + 1)
      · rw [if_pos h2k]
        have hm_pos : 0 < (k + 1) / 2 := by obtain ⟨c, hc⟩ := h2k; omega
        have h2 :
            (∑ d ∈ Finset.range (k + 1),
              (ArithmeticFunction.moebius (d + 1) : ℂ) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
                (if 2 * (d + 1) ∣ (k + 1) then (1 : ℂ) else 0)) =
            ∑ q ∈ Finset.Icc 1 (k + 1),
              if q ∣ ((k + 1) / 2) then
                (ArithmeticFunction.moebius q : ℂ) * smoothAFECutoff ((q : ℝ) / Y)
              else 0 := by
          refine Finset.sum_bij (fun d _ => d + 1)
            (fun d hd => Finset.mem_Icc.mpr ⟨Nat.succ_pos d, by have := Finset.mem_range.mp hd; omega⟩)
            (fun _ _ _ _ h => by omega)
            (fun q hq => ⟨q - 1, Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hq; omega),
              by have := Finset.mem_Icc.mp hq; omega⟩)
            (fun d _ => ?_)
          have hdvd_iff : (2 * (d + 1) ∣ (k + 1)) ↔ ((d + 1) ∣ ((k + 1) / 2)) := by
            obtain ⟨c, hc⟩ := h2k
            rw [hc, Nat.mul_div_cancel_left c two_pos]
            exact mul_dvd_mul_iff_left (by omega : (2 : ℕ) ≠ 0)
          by_cases hd : (d + 1) ∣ ((k + 1) / 2)
          · rw [if_pos (hdvd_iff.mpr hd), if_pos hd, mul_one]
          · rw [if_neg (mt hdvd_iff.mp hd), if_neg hd, mul_zero]
        rw [h2, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext q
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        exact ⟨fun ⟨_, hdv⟩ => ⟨hdv, hm_pos.ne'⟩,
          fun ⟨hdv, _⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hdv hm_pos,
            (Nat.le_of_dvd hm_pos hdv).trans (Nat.div_le_self _ 2)⟩, hdv⟩⟩
      · rw [if_neg h2k]
        refine Finset.sum_eq_zero fun d _ => ?_
        have hnd : ¬ (2 * (d + 1) ∣ (k + 1)) := fun h => h2k (dvd_of_mul_right_dvd h)
        rw [if_neg hnd, mul_zero]
  -- Sum `hterm_d` over `d : ℕ`, swap `(d, k)` via `tsum_comm'`, and peel off `k = 0, 1`.
  have hsum_lhs :
      (∑' d : ℕ, w_d d * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s)) =
        riemannZeta s * smoothOuterMoebiusSeries Y (1 - s) := by
    rw [tsum_mul_right]
    unfold smoothOuterMoebiusSeries
    dsimp only [w_d]; ring
  have hsum_all :
      (∑' d : ℕ, w_d d * ((1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s)) =
        ∑' d : ℕ, (w_d d * smoothOuterDirectPairSum s x (d + 1) - ∑' k : ℕ, g_du d k) :=
    tsum_congr hterm_d
  rw [hsum_lhs, hdir_sum.tsum_sub hg_d_sum,
    (hg_uncurry.tsum_comm' hg_row hg_col).symm, tsum_congr hcol_eq] at hsum_all
  have hcol_sum : Summable (fun k : ℕ =>
      smoothOuterSieveCoeff Y (k + 1) * smoothAFEZetaDualCoefficientGeneral s x k) := by
    refine Summable.of_norm_bounded (hB_sum.mul_left (∑' d : ℕ, A_d d)) fun k => ?_
    rw [← hcol_eq k]
    calc ‖∑' d : ℕ, g_du d k‖
        ≤ ∑' d : ℕ, ‖g_du d k‖ := norm_tsum_le_tsum_norm (hg_col k).norm
      _ ≤ ∑' d : ℕ, A_d d * B_k k :=
          Summable.tsum_le_tsum (fun d => hg_maj d k) (hg_col k).norm (hA_sum.mul_right (B_k k))
      _ = (∑' d : ℕ, A_d d) * B_k k := tsum_mul_right
  have hsplit2 := hcol_sum.sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsplit2
  simp only [zero_add, Nat.reduceAdd, smoothOuterSieveCoeff_one, smoothOuterSieveCoeff_two,
    neg_mul] at hsplit2
  have htail_eq :
      (∑' j : ℕ, smoothOuterSieveCoeff Y (j + 2 + 1) * smoothAFEZetaDualCoefficientGeneral s x (j + 2)) =
        ∑' j : ℕ, smoothOuterSieveCoeff Y (j + 3) * smoothAFEZetaDualCoefficientGeneral s x (j + 2) :=
    tsum_congr fun j => by rw [show j + 2 + 1 = j + 3 by omega]
  rw [htail_eq] at hsplit2
  rw [← hsplit2] at hsum_all
  dsimp only [w_d] at hsum_all
  linear_combination hsum_all

end Part2SmoothOuterMobiusSieveIdentity


/-! ### Part 3: Smooth Vaughan Decomposition and Unconditional Sub-Horizon Type-I Annihilation Across `Ω_open` -/

section Part3SubHorizonVaughanTypeIAnnihilation

/-- Full smooth outer-weighted reflected-Möbius direct Gaussian series over `d ≥ 1`. -/
def smoothOuterMoebiusDirect (s : ℂ) (x Y : ℝ) : ℂ :=
  ∑' d : ℕ, (ArithmeticFunction.moebius (d + 1) : ℂ) *
    ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
    smoothOuterDirectPairSum s x (d + 1)

/-- Short Möbius Type-0 head (`truncAF μ U + truncAF μ V`) of `smoothOuterMoebiusDirect`. -/
def smoothOuterVaughanHead (U V : ℕ) (s : ℂ) (x Y : ℝ) : ℂ :=
  ∑' d : ℕ,
    ((((_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U +
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) (d + 1) : ℝ) : ℂ)) *
      ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
      smoothOuterDirectPairSum s x (d + 1)

/-- Complete smooth outer-weighted Vaughan Type-I bilinear sum (`-(ζ * truncAF μ U * truncAF μ V)`),
with **no** continuum pole counterterm subtracted. -/
def smoothOuterVaughanTypeI (U V : ℕ) (s : ℂ) (x Y : ℝ) : ℂ :=
  ∑' d : ℕ,
    (-((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) (d + 1) : ℝ) : ℂ)) *
      ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
      smoothOuterDirectPairSum s x (d + 1)

/-- Complete smooth outer-weighted Vaughan Type-II bilinear sum
(`((μ - truncAF μ U) * typeIIShort V)`). -/
def smoothOuterVaughanTypeII (U V : ℕ) (s : ℂ) (x Y : ℝ) : ℂ :=
  ∑' d : ℕ,
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ) *
      ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
      smoothOuterDirectPairSum s x (d + 1)

private lemma summable_smoothOuter_arith_weight
    (g : ℕ → ℝ) {C_g : ℝ} (hCg0 : 0 ≤ C_g)
    (hg : ∀ n : ℕ, 1 ≤ n → |g n| ≤ C_g * (n : ℝ) ^ (2 : ℕ))
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y) :
    Summable (fun d : ℕ => ((g (d + 1) : ℝ) : ℂ) *
      ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
      smoothOuterDirectPairSum s x (d + 1)) := by
  obtain ⟨K₆, hK₆0, hK₆⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 6) (by norm_num)
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) (by norm_num)
  set C_p : ℝ := (1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2 * x ^ (2 : ℝ)
  refine Summable.of_norm_bounded
    ((summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left (C_g * K₆ * Y ^ (6 : ℝ) * C_p))
    fun d => ?_
  have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
  have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
  have hd_cpow : ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
    rw [show ((d + 1 : ℕ) : ℂ) = (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hd_pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by simp; linarith)
  have hW := norm_smoothAFECutoff_div_le hK₆ hd_pos hY
  have hp := norm_smoothOuterDirectPairSum_le (le_refl 2) hK₂0 hK₂ hs0 hhi hx hd1
  rw [Real.mul_rpow hd_pos.le hx.le] at hp
  have hp' : ‖smoothOuterDirectPairSum s x (d + 1)‖ ≤ C_p * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
    dsimp only [C_p]; linarith
  have hg_d : ‖((g (d + 1) : ℝ) : ℂ)‖ ≤ C_g * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two]
    exact hg (d + 1) hd1
  rw [norm_mul, norm_mul, norm_mul]
  have hrpow_cancel :
      ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (6 : ℝ))⁻¹ * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) =
        1 / (d + 1 : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_neg hd_pos.le, ← Real.rpow_add hd_pos, ← Real.rpow_add hd_pos,
      show (2 : ℝ) + (-6 : ℝ) + 2 = -2 by norm_num, Real.rpow_neg hd_pos.le, one_div]
    push_cast; rfl
  calc ‖((g (d + 1) : ℝ) : ℂ)‖ * ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ *
          ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ * ‖smoothOuterDirectPairSum s x (d + 1)‖
      ≤ (C_g * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) * 1 *
          (K₆ * ((((d + 1 : ℕ) : ℝ) ^ (6 : ℝ))⁻¹ * Y ^ (6 : ℝ))) *
          (C_p * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) :=
        mul_le_mul
          (mul_le_mul
            (mul_le_mul hg_d hd_cpow (norm_nonneg _) (by positivity))
            hW (norm_nonneg _) (by positivity))
          hp' (norm_nonneg _) (by positivity)
    _ = (C_g * K₆ * Y ^ (6 : ℝ) * C_p) *
          (((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (6 : ℝ))⁻¹ * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) := by
        ring
    _ = (C_g * K₆ * Y ^ (6 : ℝ) * C_p) * (1 / (d + 1 : ℝ) ^ (2 : ℝ)) := by rw [hrpow_cancel]

private lemma abs_truncAF_moebius_le_one' (N n : ℕ) :
    |_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) N n| ≤ 1 := by
  rw [_root_.RHTower.Sieve.truncAF_apply]
  split_ifs with h
  · have hc : ‖(((ArithmeticFunction.moebius : ArithmeticFunction ℝ) n : ℝ) : ℂ)‖ ≤ 1 := by
      rw [ArithmeticFunction.intCoe_apply, Complex.ofReal_intCast]
      exact norm_moebius_intCast_le_one' n
    rwa [Complex.norm_real, Real.norm_eq_abs] at hc
  · norm_num

private lemma card_divisorsAntidiagonal_le_self {n : ℕ} (hn : 1 ≤ n) :
    n.divisorsAntidiagonal.card ≤ n := by
  have hinj : Set.InjOn Prod.fst (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ (rfl : a₁ = a₂)
    have hp₁ := (Nat.mem_divisorsAntidiagonal.mp h₁).1
    have hp₂ := (Nat.mem_divisorsAntidiagonal.mp h₂).1
    have ha₁ : 0 < a₁ := by
      by_contra h0; have hz : a₁ = 0 := by omega
      rw [hz, zero_mul] at hp₁; omega
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left ha₁ (hp₁.trans hp₂.symm))
  have hmaps : Set.MapsTo Prod.fst (n.divisorsAntidiagonal : Set (ℕ × ℕ)) (n.divisors : Set ℕ) :=
    fun p hp => Nat.mem_divisors.mpr ⟨⟨p.2, (Nat.mem_divisorsAntidiagonal.mp hp).1.symm⟩, by omega⟩
  exact (Finset.card_le_card_of_injOn Prod.fst hmaps hinj).trans (Nat.card_divisors_le_self n)

private lemma abs_conv_le_sq_of_linear_and_const
    {f₁ f₂ : ArithmeticFunction ℝ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hf₁ : ∀ k : ℕ, 1 ≤ k → |f₁ k| ≤ C₁ * (k : ℝ))
    (hf₂ : ∀ k : ℕ, 1 ≤ k → |f₂ k| ≤ C₂) :
    ∀ n : ℕ, 1 ≤ n → |(f₁ * f₂) n| ≤ (C₁ * C₂) * (n : ℝ) ^ (2 : ℕ) := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  have hpt : ∀ p ∈ n.divisorsAntidiagonal, |f₁ p.1 * f₂ p.2| ≤ (C₁ * C₂) * (n : ℝ) := by
    intro p hp
    have hprod := Nat.mem_divisorsAntidiagonal.mp hp
    have hp1 : 1 ≤ p.1 := by
      by_contra h0; have hz : p.1 = 0 := by omega
      rw [hz, zero_mul] at hprod; omega
    have hp2 : 1 ≤ p.2 := by
      by_contra h0; have hz : p.2 = 0 := by omega
      rw [hz, mul_zero] at hprod; omega
    have hp1_le : (p.1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hn ⟨p.2, hprod.1.symm⟩
    rw [abs_mul]
    calc |f₁ p.1| * |f₂ p.2|
        ≤ (C₁ * (p.1 : ℝ)) * C₂ := mul_le_mul (hf₁ p.1 hp1) (hf₂ p.2 hp2) (abs_nonneg _) (by positivity)
      _ ≤ (C₁ * (n : ℝ)) * C₂ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1_le hC₁) hC₂
      _ = (C₁ * C₂) * (n : ℝ) := by ring
  have hcard : (n.divisorsAntidiagonal.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast card_divisorsAntidiagonal_le_self hn
  calc |∑ p ∈ n.divisorsAntidiagonal, f₁ p.1 * f₂ p.2|
      ≤ ∑ p ∈ n.divisorsAntidiagonal, |f₁ p.1 * f₂ p.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (C₁ * C₂) * (n : ℝ) := Finset.sum_le_sum hpt
    _ = (n.divisorsAntidiagonal.card : ℝ) * ((C₁ * C₂) * (n : ℝ)) := by simp
    _ ≤ (n : ℝ) * ((C₁ * C₂) * (n : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (C₁ * C₂) * (n : ℝ) ^ (2 : ℕ) := by ring

/-- **Exact Vaughan decomposition of `smoothOuterMoebiusDirect`:**
for all `U, V : ℕ`, `x > 0`, `Y > 0`, and `0 < Re s < 1 / 2`, `smoothOuterMoebiusDirect` splits
into `smoothOuterVaughanHead + smoothOuterVaughanTypeI + smoothOuterVaughanTypeII`. -/
theorem smoothOuterMoebiusDirect_eq_vaughan_decomposition
    (U V : ℕ) {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    smoothOuterMoebiusDirect s x Y =
      smoothOuterVaughanHead U V s x Y + smoothOuterVaughanTypeI U V s x Y +
        smoothOuterVaughanTypeII U V s x Y := by
  have hHead_bd : ∀ n : ℕ, 1 ≤ n →
      |(_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U +
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) n| ≤
        2 * (n : ℝ) ^ (2 : ℕ) := fun n hn => by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := one_le_pow₀ (by exact_mod_cast hn)
    have h1 := abs_truncAF_moebius_le_one' U n
    have h2 := abs_truncAF_moebius_le_one' V n
    have ht := abs_add_le
      (_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U n)
      (_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V n)
    simp only [ArithmeticFunction.add_apply]
    linarith
  have hzmU_lin : ∀ k : ℕ, 1 ≤ k →
      |((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) k| ≤
        1 * (k : ℝ) := fun k hk => by
    rw [ArithmeticFunction.coe_zeta_mul_apply, one_mul]
    have hcard : (k.divisors.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.card_divisors_le_self k
    calc |∑ d ∈ k.divisors, _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U d|
        ≤ ∑ d ∈ k.divisors, |_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U d| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ k.divisors, (1 : ℝ) := Finset.sum_le_sum fun d _ => abs_truncAF_moebius_le_one' U d
      _ = (k.divisors.card : ℝ) := by simp
      _ ≤ (k : ℝ) := hcard
  have hTypeI_bd : ∀ n : ℕ, 1 ≤ n →
      |-(((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) n)| ≤
        (1 * 1) * (n : ℝ) ^ (2 : ℕ) := fun n hn => by
    rw [abs_neg]
    exact abs_conv_le_sq_of_linear_and_const zero_le_one zero_le_one hzmU_lin
      (fun k _ => abs_truncAF_moebius_le_one' V k) n hn
  have hShort_lin : ∀ k : ℕ, 1 ≤ k → |_root_.RHTower.Sieve.typeIIShort V k| ≤ 2 * (k : ℝ) := fun k hk => by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hsub : _root_.RHTower.Sieve.typeIIShort V k =
        (1 : ArithmeticFunction ℝ) k -
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) k := rfl
    rw [hsub]
    have h1_le : |(1 : ArithmeticFunction ℝ) k| ≤ 1 := by
      rw [ArithmeticFunction.one_apply]; split_ifs <;> norm_num
    have h2_le : |((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) k| ≤ (k : ℝ) := by
      rw [ArithmeticFunction.coe_zeta_mul_apply]
      have hcard : (k.divisors.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.card_divisors_le_self k
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun d _ => abs_truncAF_moebius_le_one' V d).trans (by simpa using hcard))
    have ht := abs_sub ((1 : ArithmeticFunction ℝ) k)
      (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) k)
    linarith
  have hLong_const : ∀ k : ℕ, 1 ≤ k →
      |((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) k| ≤ 2 := fun k _ => by
    change |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) k -
      _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U k| ≤ 2
    have hm1 : |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) k| ≤ 1 := by
      have hc : ‖(((ArithmeticFunction.moebius : ArithmeticFunction ℝ) k : ℝ) : ℂ)‖ ≤ 1 := by
        rw [ArithmeticFunction.intCoe_apply, Complex.ofReal_intCast]
        exact norm_moebius_intCast_le_one' k
      rwa [Complex.norm_real, Real.norm_eq_abs] at hc
    have ht := abs_sub ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) k)
      (_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U k)
    linarith [abs_truncAF_moebius_le_one' U k]
  have hTypeII_bd : ∀ n : ℕ, 1 ≤ n →
      |(((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
          _root_.RHTower.Sieve.typeIIShort V) n| ≤
        (2 * 2) * (n : ℝ) ^ (2 : ℕ) := fun n hn => by
    rw [mul_comm]
    exact abs_conv_le_sq_of_linear_and_const zero_le_two zero_le_two hShort_lin hLong_const n hn
  have hs_H := summable_smoothOuter_arith_weight _ zero_le_two hHead_bd hs0 hhi hx hY
  have hs_I := (summable_smoothOuter_arith_weight _ (by positivity) hTypeI_bd hs0 hhi hx hY).congr
    fun d => by rw [Complex.ofReal_neg]
  have hs_II := summable_smoothOuter_arith_weight _ (by positivity) hTypeII_bd hs0 hhi hx hY
  unfold smoothOuterMoebiusDirect smoothOuterVaughanHead smoothOuterVaughanTypeI smoothOuterVaughanTypeII
  rw [← hs_H.tsum_add hs_I, ← (hs_H.add hs_I).tsum_add hs_II]
  refine tsum_congr fun d => ?_
  have hv := congrArg (fun g : ArithmeticFunction ℝ => g (d + 1))
    (GaloisForLFunctions.BezoutValuationIncidence.moebius_vaughan_identity U V)
  change (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (d + 1) =
    (_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U +
      _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) (d + 1) -
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
      _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) (d + 1) +
    (((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
      _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
      _root_.RHTower.Sieve.typeIIShort V) (d + 1) at hv
  have hm_cast : (ArithmeticFunction.moebius (d + 1) : ℂ) =
      (((ArithmeticFunction.moebius : ArithmeticFunction ℝ) (d + 1) : ℝ) : ℂ) := by
    rw [ArithmeticFunction.intCoe_apply]
    exact (Complex.ofReal_intCast (ArithmeticFunction.moebius (d + 1))).symm
  rw [hm_cast, hv]
  push_cast; ring

private lemma summable_and_tsum_finset_sum {α : Type*} [DecidableEq α] (S : Finset α)
    (h : α → ℕ → ℂ) (hs : ∀ b ∈ S, Summable (h b)) :
    Summable (fun d : ℕ => ∑ b ∈ S, h b d) ∧
      (∑' d : ℕ, ∑ b ∈ S, h b d) = ∑ b ∈ S, ∑' d : ℕ, h b d := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hs_a : Summable (h a) := hs a (Finset.mem_insert_self a t)
    obtain ⟨hs_t, heq_t⟩ := ih fun b hb => hs b (Finset.mem_insert_of_mem hb)
    refine ⟨by simpa only [Finset.sum_insert ha] using hs_a.add hs_t, ?_⟩
    simp_rw [Finset.sum_insert ha]
    rw [hs_a.tsum_add hs_t, heq_t]

/-- Exact finite-divisor fibre decomposition of `smoothOuterVaughanTypeI`:
writing `f_UV = truncAF μ U * truncAF μ V` (supported on `1 ≤ b ≤ U * V`),
`smoothOuterVaughanTypeI` sums `-f_UV(b)` times the `m ≥ 1` fibre at divisor `b`. -/
private lemma smoothOuterVaughanTypeI_eq_sum_fibres
    (U V : ℕ) {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    smoothOuterVaughanTypeI U V s x Y =
      ∑ b ∈ Finset.Icc 1 (U * V),
        (-(((_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ)) *
          ((b : ℂ) ^ (-(1 - s)) *
            ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
              smoothAFECutoff (((b * (m + 1) : ℕ) : ℝ) / Y) *
              smoothOuterDirectPairSum s x (b * (m + 1))) := by
  set f_UV : ArithmeticFunction ℝ :=
    _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
      _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V
  have hf_zero_gt : ∀ {b : ℕ}, U * V < b → f_UV b = 0 := fun {b} hgt => by
    dsimp only [f_UV]
    rw [ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
    by_cases hU : p.1 ≤ U
    · have hV : V < p.2 := by
        by_contra hle; push Not at hle
        exact hgt.not_ge (hprod ▸ Nat.mul_le_mul hU hle)
      rw [_root_.RHTower.Sieve.truncAF_apply_of_gt hV, mul_zero]
    · rw [_root_.RHTower.Sieve.truncAF_apply_of_gt (lt_of_not_ge hU), zero_mul]
  set W_base : ℕ → ℂ := fun q =>
    (q : ℂ) ^ (-(1 - s)) * smoothAFECutoff ((q : ℝ) / Y) * smoothOuterDirectPairSum s x q
  have hW_sum : Summable (fun d : ℕ => W_base (d + 1)) := by
    simpa only [W_base, Complex.ofReal_one, one_mul] using
      summable_smoothOuter_arith_weight (fun _ => 1) zero_le_one
        (fun n hn => by rw [abs_one, one_mul]; exact one_le_pow₀ (by exact_mod_cast hn))
        hs0 hhi hx hY
  have hconv_eq : ∀ d : ℕ,
      (-((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) (d + 1) : ℝ) : ℂ)) *
        W_base (d + 1) =
        ∑ b ∈ Finset.Icc 1 (U * V),
          if b ∣ (d + 1) then (-((f_UV b : ℝ) : ℂ)) * W_base (d + 1) else 0 := by
    intro d
    rw [mul_assoc (ArithmeticFunction.zeta : ArithmeticFunction ℝ),
      show _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V = f_UV from rfl,
      ArithmeticFunction.coe_zeta_mul_apply]
    have hdiv_sum :
        (∑ b ∈ (d + 1).divisors, f_UV b) =
          ∑ b ∈ Finset.Icc 1 (U * V), if b ∣ (d + 1) then f_UV b else 0 := by
      rw [← Finset.sum_filter]
      symm
      refine Finset.sum_subset_zero_on_sdiff
        (fun b hb => by
          obtain ⟨_, hdv⟩ := Finset.mem_filter.mp hb
          exact Nat.mem_divisors.mpr ⟨hdv, Nat.succ_ne_zero d⟩)
        (fun b hb => by
          obtain ⟨hdiv, hnot⟩ := Finset.mem_sdiff.mp hb
          have hdv := (Nat.mem_divisors.mp hdiv).1
          have hb1 : 1 ≤ b := Nat.pos_of_dvd_of_pos hdv (Nat.succ_pos d)
          have hgt : U * V < b := by
            by_contra hle; push Not at hle
            exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb1, hle⟩, hdv⟩)
          exact hf_zero_gt hgt)
        (fun _ _ => rfl)
    rw [hdiv_sum]
    push_cast
    rw [show ∀ z : ℂ, -z * W_base (d + 1) = ((-1 : ℂ) * z) * W_base (d + 1) from fun _ => by ring,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> push_cast <;> ring
  unfold smoothOuterVaughanTypeI
  have hlhs_eq :
      (∑' d : ℕ,
        (-((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) (d + 1) : ℝ) : ℂ)) *
          ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
          smoothOuterDirectPairSum s x (d + 1)) =
      ∑' d : ℕ, ∑ b ∈ Finset.Icc 1 (U * V),
        if b ∣ (d + 1) then (-((f_UV b : ℝ) : ℂ)) * W_base (d + 1) else 0 := by
    refine tsum_congr fun d => ?_
    rw [← hconv_eq d]
    dsimp only [W_base]; ring
  rw [hlhs_eq]
  have hs_fib : ∀ b ∈ Finset.Icc 1 (U * V),
      Summable (fun d : ℕ => if b ∣ (d + 1) then (-((f_UV b : ℝ) : ℂ)) * W_base (d + 1) else 0) := by
    intro b _
    refine Summable.of_norm_bounded (hW_sum.norm.mul_left ‖(-((f_UV b : ℝ) : ℂ))‖) fun d => ?_
    split_ifs
    · rw [norm_mul]
    · rw [norm_zero]; positivity
  rw [(summable_and_tsum_finset_sum (Finset.Icc 1 (U * V)) _ hs_fib).2]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hshift := tsum_dvd_shift_eq hb1 (fun d => (-((f_UV b : ℝ) : ℂ)) * W_base (d + 1))
  rw [← hshift]
  have hcongr_m :
      (∑' m : ℕ, (-((f_UV b : ℝ) : ℂ)) * W_base (b * (m + 1) - 1 + 1)) =
        (-((f_UV b : ℝ) : ℂ)) *
          ((b : ℂ) ^ (-(1 - s)) *
            ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
              smoothAFECutoff (((b * (m + 1) : ℕ) : ℝ) / Y) *
              smoothOuterDirectPairSum s x (b * (m + 1))) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    have hbm1 : b * (m + 1) - 1 + 1 = b * (m + 1) :=
      Nat.sub_add_cancel (Nat.mul_pos hb1 (Nat.succ_pos m))
    have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have hcpow : ((b * (m + 1) : ℕ) : ℂ) ^ (-(1 - s)) =
        (b : ℂ) ^ (-(1 - s)) * ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) := by
      rw [show ((b * (m + 1) : ℕ) : ℂ) = ((b : ℝ) : ℂ) * (((m + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg hb_pos.le hm_pos.le (-(1 - s))]
      push_cast; rfl
    dsimp only [W_base]
    rw [hbm1, hcpow]; ring
  exact hcongr_m

/-- Exact Mellin-Fubini identity for a single Type-I divisor fibre over `m ≥ 1`. -/
private lemma smoothOuterVaughanTypeI_fibre_eq_integral
    {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    {x Y : ℝ} (hx : 0 < x) (hY1 : 1 ≤ Y)
    {b : ℕ} (hb1 : 1 ≤ b) (hbY : (b : ℝ) ≤ Y) :
    let c₂ : ℝ := ((2 * r₂ : ℕ) : ℝ)
    let a₁ : ℝ := -((2 * r₁ : ℕ) : ℝ)
    let X₂ : ℝ := Y / (b : ℝ)
    (∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
        smoothAFECutoff (((b * (m + 1) : ℕ) : ℝ) / Y) *
        smoothOuterDirectPairSum s x (b * (m + 1))) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v₂ : ℝ,
          (riemannZeta (s + ((c₂ : ℂ) + (v₂ : ℂ) * I)) *
            (1 - (2 : ℂ) ^ (-(1 - s - ((c₂ : ℂ) + (v₂ : ℂ) * I)))) *
            (((b : ℝ) * x : ℝ) : ℂ) ^ ((c₂ : ℂ) + (v₂ : ℂ) * I) *
            smoothAFEGaussianKernel ((c₂ : ℂ) + (v₂ : ℂ) * I)) *
            (riemannZeta (1 - s - ((c₂ : ℂ) + (v₂ : ℂ) * I)) +
              smoothAFEZetaShiftedPoleResidue (1 - s - ((c₂ : ℂ) + (v₂ : ℂ) * I)) X₂ +
              smoothAFEZetaMellinAt a₁ (1 - s - ((c₂ : ℂ) + (v₂ : ℂ) * I)) X₂) := by
  dsimp only
  set c₂ : ℝ := ((2 * r₂ : ℕ) : ℝ)
  set a₁ : ℝ := -((2 * r₁ : ℕ) : ℝ)
  have hc₂_ge2 : (2 : ℝ) ≤ c₂ := by dsimp only [c₂]; exact_mod_cast Nat.mul_le_mul_left 2 hr₂
  have hc₂_pos : 0 < c₂ := by linarith
  have ha₁_lt0 : a₁ < 0 := by
    dsimp only [a₁]
    have : (0 : ℝ) < ((2 * r₁ : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos two_pos hr₁
    linarith
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hY_pos : 0 < Y := zero_lt_one.trans_le hY1
  set X₂ : ℝ := Y / (b : ℝ)
  have hX₂_ge1 : 1 ≤ X₂ := (one_le_div hb_pos).mpr hbY
  have hX₂_pos : 0 < X₂ := zero_lt_one.trans_le hX₂_ge1
  have hbx_pos : 0 < (b : ℝ) * x := mul_pos hb_pos hx
  have hsc₂ : 1 < s.re + c₂ := by linarith
  set Φ : ℝ → ℂ := fun v₂ =>
    let z₂ : ℂ := (c₂ : ℂ) + (v₂ : ℂ) * I
    riemannZeta (s + z₂) * (1 - (2 : ℂ) ^ (-(1 - s - z₂))) *
      (((b : ℝ) * x : ℝ) : ℂ) ^ z₂ * smoothAFEGaussianKernel z₂
  set H_term : ℕ → ℝ → ℂ := fun m v₂ =>
    let z₂ : ℂ := (c₂ : ℂ) + (v₂ : ℂ) * I
    Φ v₂ * (((m + 1 : ℕ) : ℂ) ^ (-(1 - s - z₂)) * smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X₂))
  have hm_int_eq : ∀ m : ℕ,
      ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((b * (m + 1) : ℕ) : ℝ) / Y) *
          smoothOuterDirectPairSum s x (b * (m + 1)) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) * ∫ v₂ : ℝ, H_term m v₂ := by
    intro m
    set y_m : ℝ := ((b * (m + 1) : ℕ) : ℝ) * x
    have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have hym_pos : 0 < y_m := by dsimp only [y_m]; positivity
    have h2ym_pos : 0 < 2 * y_m := mul_pos two_pos hym_pos
    have hs1 := (summable_smoothAFE_direct hc₂_pos hym_pos hsc₂).congr fun n => by push_cast; rfl
    have hs2 := ((summable_smoothAFE_direct hc₂_pos h2ym_pos hsc₂).mul_left ((2 : ℂ) ^ (-(1 - s)))).congr
      fun n => by push_cast; rfl
    have hpair_eq : smoothOuterDirectPairSum s x (b * (m + 1)) =
        smoothAFEZetaMellinAt c₂ s y_m - (2 : ℂ) ^ (-(1 - s)) * smoothAFEZetaMellinAt c₂ s (2 * y_m) := by
      rw [smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff hym_pos hc₂_pos hsc₂,
        smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff h2ym_pos hc₂_pos hsc₂]
      unfold smoothOuterDirectPairSum
      rw [← tsum_mul_left, ← hs1.tsum_sub hs2]
      refine tsum_congr fun n => ?_
      dsimp only [y_m]
      push_cast; ring
    have hdiv_X₂ : ((b * (m + 1) : ℕ) : ℝ) / Y = ((m + 1 : ℕ) : ℝ) / X₂ := by
      dsimp only [X₂]; push_cast; field_simp [hb_pos.ne']
    rw [hpair_eq, hdiv_X₂]
    unfold smoothAFEZetaMellinAt
    rw [Complex.real_smul, Complex.real_smul]
    have hi1 := smoothAFEZetaMellinIntegrand_verticalIntegrable (s := s) hym_pos hc₂_pos hsc₂
    rw [Complex.VerticalIntegrable] at hi1
    have hi2 := (smoothAFEZetaMellinIntegrand_verticalIntegrable (s := s) h2ym_pos hc₂_pos hsc₂).const_mul
      ((2 : ℂ) ^ (-(1 - s)))
    have hpull :
        ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X₂) *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
              (∫ t : ℝ, smoothAFEZetaMellinIntegrand s y_m ((c₂ : ℂ) + (t : ℂ) * I)) -
            (2 : ℂ) ^ (-(1 - s)) *
              ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
                ∫ t : ℝ, smoothAFEZetaMellinIntegrand s (2 * y_m) ((c₂ : ℂ) + (t : ℂ) * I))) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X₂) *
            ((∫ t : ℝ, smoothAFEZetaMellinIntegrand s y_m ((c₂ : ℂ) + (t : ℂ) * I)) -
              ∫ t : ℝ, (2 : ℂ) ^ (-(1 - s)) *
                smoothAFEZetaMellinIntegrand s (2 * y_m) ((c₂ : ℂ) + (t : ℂ) * I))) := by
      rw [MeasureTheory.integral_const_mul]; ring
    rw [hpull, ← integral_sub hi1 hi2, ← MeasureTheory.integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v₂ => ?_)
    dsimp only [H_term, Φ]
    set z₂ : ℂ := (c₂ : ℂ) + (v₂ : ℂ) * I
    unfold smoothAFEZetaMellinIntegrand
    have hym_cpow : (y_m : ℂ) ^ z₂ = (((b : ℝ) * x : ℝ) : ℂ) ^ z₂ * ((m + 1 : ℕ) : ℂ) ^ z₂ := by
      have hy_eq : (y_m : ℂ) = (((b : ℝ) * x : ℝ) : ℂ) * (((m + 1 : ℕ) : ℝ) : ℂ) := by
        dsimp only [y_m]; push_cast; ring
      rw [hy_eq, Complex.mul_cpow_ofReal_nonneg hbx_pos.le hm_pos.le z₂]
      push_cast; rfl
    have h2ym_cpow : ((2 * y_m : ℝ) : ℂ) ^ z₂ = (2 : ℂ) ^ z₂ * (y_m : ℂ) ^ z₂ := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg two_pos.le hym_pos.le z₂]
      norm_num
    have h2_comb : (2 : ℂ) ^ (-(1 - s)) * (2 : ℂ) ^ z₂ = (2 : ℂ) ^ (-(1 - s - z₂)) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      congr 1; ring
    have hm_comb : ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) * ((m + 1 : ℕ) : ℂ) ^ z₂ =
        ((m + 1 : ℕ) : ℂ) ^ (-(1 - s - z₂)) := by
      have hm_ne0 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      rw [← Complex.cpow_add _ _ hm_ne0]
      congr 1; ring
    rw [h2ym_cpow, hym_cpow]
    calc ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X₂) *
            (riemannZeta (s + z₂) * ((((b : ℝ) * x : ℝ) : ℂ) ^ z₂ * ((m + 1 : ℕ) : ℂ) ^ z₂) *
                smoothAFEGaussianKernel z₂ -
              (2 : ℂ) ^ (-(1 - s)) *
                (riemannZeta (s + z₂) *
                  ((2 : ℂ) ^ z₂ * ((((b : ℝ) * x : ℝ) : ℂ) ^ z₂ * ((m + 1 : ℕ) : ℂ) ^ z₂)) *
                  smoothAFEGaussianKernel z₂))
        = riemannZeta (s + z₂) * (1 - (2 : ℂ) ^ (-(1 - s)) * (2 : ℂ) ^ z₂) *
            (((b : ℝ) * x : ℝ) : ℂ) ^ z₂ * smoothAFEGaussianKernel z₂ *
            ((((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) * ((m + 1 : ℕ) : ℂ) ^ z₂) *
              smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X₂)) := by ring
      _ = riemannZeta (s + z₂) * (1 - (2 : ℂ) ^ (-(1 - s - z₂))) *
            (((b : ℝ) * x : ℝ) : ℂ) ^ z₂ * smoothAFEGaussianKernel z₂ *
            (((m + 1 : ℕ) : ℂ) ^ (-(1 - s - z₂)) * smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X₂)) := by
          rw [h2_comb, hm_comb]
  have hΦ_bd : ∀ v₂ : ℝ,
      ‖Φ v₂‖ ≤ (smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
        ((b : ℝ) * x) ^ (2 * r₂) * (Real.exp (c₂ ^ (2 : ℕ)) / c₂)) * Real.exp (-(v₂ ^ (2 : ℕ))) := by
    intro v₂
    dsimp only [Φ]
    set z₂ : ℂ := (c₂ : ℂ) + (v₂ : ℂ) * I
    have hζ_le : ‖riemannZeta (s + z₂)‖ ≤ smoothAFEZetaMajorant 2 := by
      have hmaj := norm_riemannZeta_vertical_le_smoothAFEZetaMajorant (s := s) (c := c₂) hsc₂ v₂
      exact hmaj.trans (Summable.tsum_le_tsum
        (fun n => one_div_le_one_div_of_le (by positivity)
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos n) (by linarith)))
        (summable_smoothAFEZetaMajorant hsc₂) (summable_smoothAFEZetaMajorant (by norm_num)))
    have h12_le : ‖1 - (2 : ℂ) ^ (-(1 - s - z₂))‖ ≤ 1 + (2 : ℝ) ^ (2 * r₂) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
      have hre_le : (-(1 - s - z₂)).re ≤ ((2 * r₂ : ℕ) : ℝ) := by
        dsimp only [z₂, c₂]; simp; linarith
      have hrp := (Real.rpow_le_rpow_of_exponent_le one_lt_two.le hre_le).trans_eq
        (Real.rpow_natCast 2 (2 * r₂))
      linarith
    have hbx_eq : ‖(((b : ℝ) * x : ℝ) : ℂ) ^ z₂‖ = ((b : ℝ) * x) ^ (2 * r₂) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hbx_pos, show z₂.re = c₂ by simp [z₂]]
      dsimp only [c₂]; exact Real.rpow_natCast _ (2 * r₂)
    have hker := norm_smoothAFEGaussianKernel_vertical_le hc₂_pos v₂
    rw [norm_mul, norm_mul, norm_mul, hbx_eq]
    calc ‖riemannZeta (s + z₂)‖ * ‖1 - (2 : ℂ) ^ (-(1 - s - z₂))‖ *
            ((b : ℝ) * x) ^ (2 * r₂) * ‖smoothAFEGaussianKernel z₂‖
        ≤ smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
            ((b : ℝ) * x) ^ (2 * r₂) * ((Real.exp (c₂ ^ (2 : ℕ)) / c₂) * Real.exp (-(v₂ ^ (2 : ℕ)))) := by
          refine mul_le_mul
            (mul_le_mul_of_nonneg_right
              (mul_le_mul hζ_le h12_le (norm_nonneg _) (tsum_nonneg fun _ => by positivity))
              (by positivity))
            hker (norm_nonneg _) ?_
          exact mul_nonneg (mul_nonneg (tsum_nonneg fun _ => by positivity) (by positivity)) (by positivity)
      _ = (smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
            ((b : ℝ) * x) ^ (2 * r₂) * (Real.exp (c₂ ^ (2 : ℕ)) / c₂)) * Real.exp (-(v₂ ^ (2 : ℕ))) := by ring
  obtain ⟨K_m, hKm0, hKm⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := c₂ + 3) (by linarith)
  set C_Φ : ℝ := smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
    ((b : ℝ) * x) ^ (2 * r₂) * (Real.exp (c₂ ^ (2 : ℕ)) / c₂)
  have hCΦ_nn : 0 ≤ C_Φ := by
    dsimp only [C_Φ]
    exact mul_nonneg (mul_nonneg (mul_nonneg (tsum_nonneg fun _ => by positivity) (by positivity))
      (by positivity)) (by positivity)
  have hΦ_cont : Continuous Φ := by
    haveI : NeZero (((b : ℝ) * x : ℝ) : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hbx_pos.ne'⟩
    haveI : NeZero (2 : ℂ) := ⟨by norm_num⟩
    have hpath : Continuous (fun v₂ : ℝ => (c₂ : ℂ) + (v₂ : ℂ) * I) := by fun_prop
    have hz : Continuous (fun v₂ : ℝ => riemannZeta (s + ((c₂ : ℂ) + (v₂ : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]; intro v₂
      refine (differentiableAt_riemannZeta ?_).continuousAt.comp (by fun_prop)
      intro heq; have hre := congrArg Complex.re heq; simp at hre; linarith
    have h2 : Continuous (fun v₂ : ℝ => 1 - (2 : ℂ) ^ (-(1 - s - ((c₂ : ℂ) + (v₂ : ℂ) * I)))) :=
      continuous_const.sub ((continuous_const_cpow (2 : ℂ)).comp (by fun_prop))
    have hbx_c : Continuous (fun v₂ : ℝ => (((b : ℝ) * x : ℝ) : ℂ) ^ ((c₂ : ℂ) + (v₂ : ℂ) * I)) :=
      (continuous_const_cpow _).comp hpath
    have hker_c : Continuous (fun v₂ : ℝ => smoothAFEGaussianKernel ((c₂ : ℂ) + (v₂ : ℂ) * I)) := by
      unfold smoothAFEGaussianKernel
      exact (Complex.continuous_exp.comp (hpath.pow 2)).div hpath fun v₂ h0 => by
        have := congrArg Complex.re h0; simp at this; exact hc₂_pos.ne' this
    exact ((hz.mul h2).mul hbx_c).mul hker_c
  have hH_pt : ∀ (m : ℕ) (v₂ : ℝ),
      ‖H_term m v₂‖ ≤ (C_Φ * K_m * X₂ ^ (c₂ + 3)) *
        (1 / (m + 1 : ℝ) ^ (2 : ℝ)) * Real.exp (-(v₂ ^ (2 : ℕ))) := by
    intro m v₂
    have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have hW := norm_smoothAFECutoff_div_le hKm hm_pos hX₂_pos
    dsimp only [H_term]
    rw [norm_mul (Φ v₂), norm_mul (((m + 1 : ℕ) : ℂ) ^ _),
      show ((m + 1 : ℕ) : ℂ) = (((m + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hm_pos,
      show (-(1 - s - ((c₂ : ℂ) + (v₂ : ℂ) * I))).re = s.re - 1 + c₂ by simp; ring]
    have hm_tail : ((m + 1 : ℕ) : ℝ) ^ (s.re - 1 + c₂) * ‖smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X₂)‖ ≤
        (K_m * X₂ ^ (c₂ + 3)) * (1 / (m + 1 : ℝ) ^ (2 : ℝ)) := by
      calc ((m + 1 : ℕ) : ℝ) ^ (s.re - 1 + c₂) * ‖smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X₂)‖
          ≤ ((m + 1 : ℕ) : ℝ) ^ (s.re - 1 + c₂) * (K_m * ((((m + 1 : ℕ) : ℝ) ^ (c₂ + 3))⁻¹ * X₂ ^ (c₂ + 3))) :=
            mul_le_mul_of_nonneg_left hW (by positivity)
        _ = (K_m * X₂ ^ (c₂ + 3)) * (((m + 1 : ℕ) : ℝ) ^ (s.re - 1 + c₂) * ((m + 1 : ℕ) : ℝ) ^ (-(c₂ + 3))) := by
            rw [Real.rpow_neg hm_pos.le]; ring
        _ = (K_m * X₂ ^ (c₂ + 3)) * ((m + 1 : ℕ) : ℝ) ^ (s.re - 4) := by
            rw [← Real.rpow_add hm_pos]; congr 2; ring
        _ ≤ (K_m * X₂ ^ (c₂ + 3)) * ((m + 1 : ℕ) : ℝ) ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)) (by positivity)
        _ = (K_m * X₂ ^ (c₂ + 3)) * (1 / (m + 1 : ℝ) ^ (2 : ℝ)) := by
            rw [Real.rpow_neg hm_pos.le, one_div]; push_cast; rfl
    calc ‖Φ v₂‖ * (((m + 1 : ℕ) : ℝ) ^ (s.re - 1 + c₂) * ‖smoothAFECutoff (((m + 1 : ℕ) : ℝ) / X₂)‖)
        ≤ (C_Φ * Real.exp (-(v₂ ^ (2 : ℕ)))) * ((K_m * X₂ ^ (c₂ + 3)) * (1 / (m + 1 : ℝ) ^ (2 : ℝ))) :=
          mul_le_mul (hΦ_bd v₂) hm_tail (by positivity) (by positivity)
      _ = (C_Φ * K_m * X₂ ^ (c₂ + 3)) * (1 / (m + 1 : ℝ) ^ (2 : ℝ)) * Real.exp (-(v₂ ^ (2 : ℕ))) := by ring
  have hH_int : ∀ m : ℕ, Integrable (H_term m) := fun m => by
    have hm_ne0 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    letI : NeZero ((m + 1 : ℕ) : ℂ) := ⟨hm_ne0⟩
    have hcont : Continuous (H_term m) :=
      hΦ_cont.mul (((continuous_const_cpow ((m + 1 : ℕ) : ℂ)).comp (by fun_prop)).mul continuous_const)
    exact Integrable.mono'
      ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
        ((C_Φ * K_m * X₂ ^ (c₂ + 3)) * (1 / (m + 1 : ℝ) ^ (2 : ℝ))))
      hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v₂ => by simpa [one_mul] using hH_pt m v₂)
  have hH_sum_norm : Summable (fun m : ℕ => ∫ v₂ : ℝ, ‖H_term m v₂‖) := by
    set G₀ : ℝ := ∫ v₂ : ℝ, Real.exp (-(v₂ ^ (2 : ℕ)))
    have hgauss := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_)
      ((summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left
        (C_Φ * K_m * X₂ ^ (c₂ + 3) * G₀))
    have hdom := hgauss.const_mul ((C_Φ * K_m * X₂ ^ (c₂ + 3)) * (1 / (m + 1 : ℝ) ^ (2 : ℝ)))
    calc ∫ v₂ : ℝ, ‖H_term m v₂‖
        ≤ ∫ v₂ : ℝ, ((C_Φ * K_m * X₂ ^ (c₂ + 3)) * (1 / (m + 1 : ℝ) ^ (2 : ℝ))) * Real.exp (-(v₂ ^ (2 : ℕ))) :=
          integral_mono_ae (hH_int m).norm
            (by simpa [one_mul] using hdom) (Filter.Eventually.of_forall (hH_pt m))
      _ = (C_Φ * K_m * X₂ ^ (c₂ + 3) * G₀) * (1 / (m + 1 : ℝ) ^ (2 : ℝ)) := by
          rw [MeasureTheory.integral_const_mul]; dsimp only [G₀]; ring
  rw [tsum_congr hm_int_eq, tsum_mul_left,
    MeasureTheory.integral_tsum_of_summable_integral_norm hH_int hH_sum_norm]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v₂ => ?_)
  dsimp only [H_term, Φ]
  rw [tsum_mul_left]
  congr 1
  set w₂ : ℂ := 1 - s - ((c₂ : ℂ) + (v₂ : ℂ) * I)
  have hw₂_re : w₂.re = 1 - s.re - c₂ := by dsimp only [w₂]; simp
  have hw₂_ne1 : w₂ ≠ 1 := fun h => by rw [h] at hw₂_re; simp at hw₂_re; linarith
  exact tsum_smoothAFECutoff_eq_zeta_add_residue_add_mellinAt_neg hw₂_ne1 hX₂_pos
    ha₁_lt0 (by linarith : 0 < c₂ + 2) (by linarith) (by linarith)

private lemma norm_smoothOuterVaughanTypeI_phi_le
    {r₂ : ℕ} (hr₂ : 1 ≤ r₂) {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    {x : ℝ} (hx : 0 < x) {b : ℕ} (hb1 : 1 ≤ b) (v : ℝ) :
    let c₂ : ℝ := ((2 * r₂ : ℕ) : ℝ)
    let z₂ : ℂ := (c₂ : ℂ) + (v : ℂ) * I
    ‖riemannZeta (s + z₂) * (1 - (2 : ℂ) ^ (-(1 - s - z₂))) *
        (((b : ℝ) * x : ℝ) : ℂ) ^ z₂ * smoothAFEGaussianKernel z₂‖ ≤
      (smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
        ((b : ℝ) * x) ^ (2 * r₂) * (Real.exp (((2 * r₂ : ℕ) : ℝ) ^ (2 : ℕ)) / ((2 * r₂ : ℕ) : ℝ))) *
        Real.exp (-v ^ (2 : ℕ)) := by
  dsimp only
  have hc₂_ge2 : (2 : ℝ) ≤ ((2 * r₂ : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul_left 2 hr₂
  have hc₂_pos : (0 : ℝ) < ((2 * r₂ : ℕ) : ℝ) := by linarith
  have hsc₂ : 1 < s.re + ((2 * r₂ : ℕ) : ℝ) := by linarith
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hbx_pos : 0 < (b : ℝ) * x := mul_pos hb_pos hx
  have hSmaj_nn : 0 ≤ smoothAFEZetaMajorant 2 := tsum_nonneg fun _ => by positivity
  set z₂ : ℂ := (((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I
  have hζ_le : ‖riemannZeta (s + z₂)‖ ≤ smoothAFEZetaMajorant 2 := by
    have hmaj := norm_riemannZeta_vertical_le_smoothAFEZetaMajorant
      (s := s) (c := ((2 * r₂ : ℕ) : ℝ)) hsc₂ v
    exact hmaj.trans (Summable.tsum_le_tsum
      (fun n => one_div_le_one_div_of_le (by positivity)
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos n) (by linarith)))
      (summable_smoothAFEZetaMajorant hsc₂) (summable_smoothAFEZetaMajorant (by norm_num)))
  have h12_le : ‖1 - (2 : ℂ) ^ (-(1 - s - z₂))‖ ≤ 1 + (2 : ℝ) ^ (2 * r₂) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
    have hre_le : (-(1 - s - z₂)).re ≤ ((2 * r₂ : ℕ) : ℝ) := by
      dsimp only [z₂]; simp; linarith
    linarith [(Real.rpow_le_rpow_of_exponent_le one_lt_two.le hre_le).trans_eq
      (Real.rpow_natCast 2 (2 * r₂))]
  have hbx_eq : ‖(((b : ℝ) * x : ℝ) : ℂ) ^ z₂‖ = ((b : ℝ) * x) ^ (2 * r₂) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hbx_pos, show z₂.re = ((2 * r₂ : ℕ) : ℝ) by simp [z₂]]
    exact Real.rpow_natCast _ (2 * r₂)
  have hker := norm_smoothAFEGaussianKernel_vertical_le hc₂_pos v
  rw [norm_mul, norm_mul, norm_mul, hbx_eq]
  calc ‖riemannZeta (s + z₂)‖ * ‖1 - (2 : ℂ) ^ (-(1 - s - z₂))‖ *
          ((b : ℝ) * x) ^ (2 * r₂) * ‖smoothAFEGaussianKernel z₂‖
      ≤ smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
          ((b : ℝ) * x) ^ (2 * r₂) *
          ((Real.exp (((2 * r₂ : ℕ) : ℝ) ^ (2 : ℕ)) / ((2 * r₂ : ℕ) : ℝ)) * Real.exp (-v ^ (2 : ℕ))) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right
            (mul_le_mul hζ_le h12_le (norm_nonneg _) hSmaj_nn) (by positivity))
          hker (norm_nonneg _)
          (mul_nonneg (mul_nonneg hSmaj_nn (by positivity)) (by positivity))
    _ = (smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
          ((b : ℝ) * x) ^ (2 * r₂) *
          (Real.exp (((2 * r₂ : ℕ) : ℝ) ^ (2 : ℕ)) / ((2 * r₂ : ℕ) : ℝ))) *
          Real.exp (-v ^ (2 : ℕ)) := by ring

private lemma norm_smoothOuterVaughanTypeI_shiftedPole_piece_le
    {r₂ : ℕ} (hr₂ : 1 ≤ r₂) {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    {x Y : ℝ} (hx : 0 < x) (hY1 : 1 ≤ Y)
    {b : ℕ} (hb1 : 1 ≤ b) (hbY : (b : ℝ) ≤ Y) (v : ℝ) :
    let c₂ : ℝ := ((2 * r₂ : ℕ) : ℝ)
    let z₂ : ℂ := (c₂ : ℂ) + (v : ℂ) * I
    ‖(riemannZeta (s + z₂) * (1 - (2 : ℂ) ^ (-(1 - s - z₂))) *
        (((b : ℝ) * x : ℝ) : ℂ) ^ z₂ * smoothAFEGaussianKernel z₂) *
      smoothAFEZetaShiftedPoleResidue (1 - s - z₂) (Y / (b : ℝ))‖ ≤
      (smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
        Real.exp ((1 + ((2 * r₂ : ℕ) : ℝ)) ^ (2 : ℕ) + ((2 * r₂ : ℕ) : ℝ) ^ (2 : ℕ)) *
        Y ^ ((2 * r₂ + 1 : ℕ) : ℝ) * ((b : ℝ) * x) ^ (2 * r₂) * Real.exp (-s.im ^ (2 : ℕ) / 4)) *
        Real.exp (-(1 / 4 : ℝ) * v ^ (2 : ℕ)) := by
  dsimp only
  set c₂ : ℝ := ((2 * r₂ : ℕ) : ℝ)
  have hc₂_ge2 : (2 : ℝ) ≤ c₂ := by dsimp only [c₂]; exact_mod_cast Nat.mul_le_mul_left 2 hr₂
  have hc₂_pos : 0 < c₂ := by linarith
  have hsc₂ : 1 < s.re + c₂ := by linarith
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hY_pos : 0 < Y := zero_lt_one.trans_le hY1
  have hbx_pos : 0 < (b : ℝ) * x := mul_pos hb_pos hx
  set X₂ : ℝ := Y / (b : ℝ)
  have hX₂_ge1 : 1 ≤ X₂ := (one_le_div hb_pos).mpr hbY
  have hX₂_pos : 0 < X₂ := zero_lt_one.trans_le hX₂_ge1
  set z₂ : ℂ := (c₂ : ℂ) + (v : ℂ) * I
  unfold smoothAFEZetaShiftedPoleResidue smoothAFEGaussianKernel
  have h1w₂ : 1 - (1 - s - z₂) = s + z₂ := by ring
  rw [h1w₂]
  have hSmaj_nn : 0 ≤ smoothAFEZetaMajorant 2 := tsum_nonneg fun _ => by positivity
  have hζ_le : ‖riemannZeta (s + z₂)‖ ≤ smoothAFEZetaMajorant 2 := by
    have hmaj := norm_riemannZeta_vertical_le_smoothAFEZetaMajorant (s := s) (c := c₂) hsc₂ v
    exact hmaj.trans (Summable.tsum_le_tsum
      (fun n => one_div_le_one_div_of_le (by positivity)
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos n) (by linarith)))
      (summable_smoothAFEZetaMajorant hsc₂) (summable_smoothAFEZetaMajorant (by norm_num)))
  have h12_le : ‖1 - (2 : ℂ) ^ (-(1 - s - z₂))‖ ≤ 1 + (2 : ℝ) ^ (2 * r₂) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
    have hre_le : (-(1 - s - z₂)).re ≤ ((2 * r₂ : ℕ) : ℝ) := by
      dsimp only [z₂, c₂]; simp; linarith
    linarith [(Real.rpow_le_rpow_of_exponent_le one_lt_two.le hre_le).trans_eq
      (Real.rpow_natCast 2 (2 * r₂))]
  have hbx_eq : ‖(((b : ℝ) * x : ℝ) : ℂ) ^ z₂‖ = ((b : ℝ) * x) ^ (2 * r₂) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hbx_pos, show z₂.re = c₂ by simp [z₂]]
    dsimp only [c₂]; exact Real.rpow_natCast _ (2 * r₂)
  have hX₂_le : ‖(X₂ : ℂ) ^ (s + z₂)‖ ≤ Y ^ ((2 * r₂ + 1 : ℕ) : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX₂_pos]
    have hre_le : (s + z₂).re ≤ ((2 * r₂ + 1 : ℕ) : ℝ) := by
      dsimp only [z₂, c₂]; simp; linarith
    have hX₂_Y : X₂ ≤ Y := div_le_self hY_pos.le (by exact_mod_cast hb1)
    exact (Real.rpow_le_rpow_of_exponent_le hX₂_ge1 hre_le).trans
      (Real.rpow_le_rpow hX₂_pos.le hX₂_Y (by positivity))
  have hz₂_ge1 : 1 ≤ ‖z₂‖ := by
    calc (1 : ℝ) ≤ c₂ := by linarith
      _ ≤ |z₂.re| := by simp [z₂, abs_of_pos hc₂_pos]
      _ ≤ ‖z₂‖ := Complex.abs_re_le_norm z₂
  have hsz₂_ge1 : 1 ≤ ‖s + z₂‖ := by
    calc (1 : ℝ) ≤ s.re + c₂ := hsc₂.le
      _ ≤ |(s + z₂).re| := by simp [z₂, abs_of_pos (zero_lt_one.trans hsc₂)]
      _ ≤ ‖s + z₂‖ := Complex.abs_re_le_norm (s + z₂)
  have hexp_prod :
      (‖Complex.exp (z₂ ^ 2)‖ / ‖z₂‖) * (‖Complex.exp ((s + z₂) ^ (2 : ℕ))‖ / ‖s + z₂‖) ≤
        Real.exp ((1 + c₂) ^ (2 : ℕ) + c₂ ^ (2 : ℕ)) *
          Real.exp (-s.im ^ (2 : ℕ) / 4) * Real.exp (-(1 / 4 : ℝ) * v ^ (2 : ℕ)) := by
    have hd1 : ‖Complex.exp (z₂ ^ 2)‖ / ‖z₂‖ ≤ ‖Complex.exp (z₂ ^ 2)‖ :=
      div_le_self (norm_nonneg _) hz₂_ge1
    have hd2 : ‖Complex.exp ((s + z₂) ^ (2 : ℕ))‖ / ‖s + z₂‖ ≤ ‖Complex.exp ((s + z₂) ^ (2 : ℕ))‖ :=
      div_le_self (norm_nonneg _) hsz₂_ge1
    refine (mul_le_mul hd1 hd2 (by positivity) (by positivity)).trans ?_
    rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hre1 : (z₂ ^ 2).re = c₂ ^ (2 : ℕ) - v ^ (2 : ℕ) := by
      dsimp only [z₂]; simp [pow_two]
    have hre2 : ((s + z₂) ^ (2 : ℕ)).re = (s.re + c₂) ^ (2 : ℕ) - (s.im + v) ^ (2 : ℕ) := by
      dsimp only [z₂]; simp [pow_two]
    rw [hre1, hre2]
    have hre_le : (s.re + c₂) ^ (2 : ℕ) ≤ (1 + c₂) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have him_q : (1 / 4 : ℝ) * s.im ^ (2 : ℕ) + (1 / 4 : ℝ) * v ^ (2 : ℕ) ≤
        (s.im + v) ^ (2 : ℕ) + v ^ (2 : ℕ) := by
      nlinarith [sq_nonneg ((3 : ℝ) * s.im + 4 * v), sq_nonneg v]
    linarith
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_div, norm_div, norm_mul, hbx_eq]
  calc ‖riemannZeta (s + z₂)‖ * ‖1 - (2 : ℂ) ^ (-(1 - s - z₂))‖ *
          ((b : ℝ) * x) ^ (2 * r₂) * (‖Complex.exp (z₂ ^ 2)‖ / ‖z₂‖) *
          (‖(X₂ : ℂ) ^ (s + z₂)‖ * ‖Complex.exp ((s + z₂) ^ (2 : ℕ))‖ / ‖s + z₂‖)
      = (‖riemannZeta (s + z₂)‖ * ‖1 - (2 : ℂ) ^ (-(1 - s - z₂))‖ *
          ((b : ℝ) * x) ^ (2 * r₂) * ‖(X₂ : ℂ) ^ (s + z₂)‖) *
          ((‖Complex.exp (z₂ ^ 2)‖ / ‖z₂‖) * (‖Complex.exp ((s + z₂) ^ (2 : ℕ))‖ / ‖s + z₂‖)) := by ring
    _ ≤ (smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
          ((b : ℝ) * x) ^ (2 * r₂) * Y ^ ((2 * r₂ + 1 : ℕ) : ℝ)) *
          (Real.exp ((1 + c₂) ^ (2 : ℕ) + c₂ ^ (2 : ℕ)) *
            Real.exp (-s.im ^ (2 : ℕ) / 4) * Real.exp (-(1 / 4 : ℝ) * v ^ (2 : ℕ))) :=
        mul_le_mul
          (mul_le_mul
            (mul_le_mul_of_nonneg_right
              (mul_le_mul hζ_le h12_le (norm_nonneg _) hSmaj_nn)
              (by positivity))
            hX₂_le (norm_nonneg _)
            (mul_nonneg (mul_nonneg hSmaj_nn (by positivity)) (by positivity)))
          hexp_prod (by positivity) (by positivity)
    _ = (smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
          Real.exp ((1 + c₂) ^ (2 : ℕ) + c₂ ^ (2 : ℕ)) *
          Y ^ ((2 * r₂ + 1 : ℕ) : ℝ) * ((b : ℝ) * x) ^ (2 * r₂) * Real.exp (-s.im ^ (2 : ℕ) / 4)) *
          Real.exp (-(1 / 4 : ℝ) * v ^ (2 : ℕ)) := by ring

private lemma norm_smoothAFEZetaMellinAt_neg_even_le
    {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) {C_z12 : ℝ} (hCz12_pos : 0 < C_z12)
    (hCz12 : ∀ (s : ℂ) (v : ℝ), 3001 / 24000 ≤ s.re → s.re < 1 / 2 →
      ‖riemannZeta (1 - s - ((2 * (r₁ + r₂) : ℕ) : ℂ) - (v : ℂ) * I)‖ ≤
        C_z12 * (1 + |s.im|) ^ (2 * (r₁ + r₂)) * (1 + |v|) ^ (2 * (r₁ + r₂)))
    {s : ℂ} (hlo : 3001 / 24000 ≤ s.re) (hhi : s.re < 1 / 2)
    {Y : ℝ} {b : ℕ} (hb1 : 1 ≤ b) (hbY : (b : ℝ) ≤ Y) (v₂ : ℝ) :
    let a₁ : ℝ := -((2 * r₁ : ℕ) : ℝ)
    let c₂ : ℝ := ((2 * r₂ : ℕ) : ℝ)
    ‖smoothAFEZetaMellinAt a₁ (1 - s - ((c₂ : ℂ) + (v₂ : ℂ) * I)) (Y / (b : ℝ))‖ ≤
      (1 / (2 * Real.pi)) * C_z12 *
        (Real.exp ((-((2 * r₁ : ℕ) : ℝ)) ^ (2 : ℕ)) / ((2 * r₁ : ℕ) : ℝ)) *
        (∫ v : ℝ, (1 + |v|) ^ (2 * (r₁ + r₂)) * Real.exp (-v ^ (2 : ℕ))) *
        (1 + |s.im|) ^ (2 * r₁ + 2 * r₂) * ((b : ℝ) / Y) ^ (2 * r₁) *
        (1 + |v₂|) ^ (2 * (r₁ + r₂)) := by
  dsimp only
  set a₁ : ℝ := -((2 * r₁ : ℕ) : ℝ)
  set c₂ : ℝ := ((2 * r₂ : ℕ) : ℝ)
  set X₂ : ℝ := Y / (b : ℝ)
  set w₂ : ℂ := 1 - s - ((c₂ : ℂ) + (v₂ : ℂ) * I)
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hY_pos : 0 < Y := hb_pos.trans_le hbY
  have hX₂_pos : 0 < X₂ := zero_lt_one.trans_le ((one_le_div hb_pos).mpr hbY)
  have ha₁_lt0 : a₁ < 0 := by
    dsimp only [a₁]
    have : (0 : ℝ) < ((2 * r₁ : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos two_pos hr₁
    linarith
  have hna₁_pos : 0 < -a₁ := neg_pos.mpr ha₁_lt0
  unfold smoothAFEZetaMellinAt
  rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  set K_in : ℝ := C_z12 * (1 + |s.im|) ^ (2 * r₁ + 2 * r₂) * (1 + |v₂|) ^ (2 * (r₁ + r₂)) *
    ((b : ℝ) / Y) ^ (2 * r₁) * (Real.exp (a₁ ^ (2 : ℕ)) / (-a₁))
  have hin_pt : ∀ v₁ : ℝ,
      ‖smoothAFEZetaMellinIntegrand w₂ X₂ ((a₁ : ℂ) + (v₁ : ℂ) * I)‖ ≤
        K_in * ((1 + |v₁|) ^ (2 * (r₁ + r₂)) * Real.exp (-v₁ ^ (2 : ℕ))) := by
    intro v₁
    unfold smoothAFEZetaMellinIntegrand
    rw [norm_mul, norm_mul]
    have hwz1 : w₂ + ((a₁ : ℂ) + (v₁ : ℂ) * I) =
        1 - s - ((2 * (r₁ + r₂) : ℕ) : ℂ) - ((v₂ - v₁ : ℝ) : ℂ) * I := by
      dsimp only [w₂, c₂, a₁]; push_cast; ring
    have hz_v1 := hwz1 ▸ hCz12 s (v₂ - v₁) hlo hhi
    have hv_sub : (1 + |v₂ - v₁|) ^ (2 * (r₁ + r₂)) ≤
        (1 + |v₂|) ^ (2 * (r₁ + r₂)) * (1 + |v₁|) ^ (2 * (r₁ + r₂)) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have habs_s : |v₂ - v₁| ≤ |v₂| + |v₁| := abs_sub _ _
      nlinarith [abs_nonneg v₂, abs_nonneg v₁]
    have hz_v1' : ‖riemannZeta (w₂ + ((a₁ : ℂ) + (v₁ : ℂ) * I))‖ ≤
        C_z12 * (1 + |s.im|) ^ (2 * r₁ + 2 * r₂) *
          (1 + |v₂|) ^ (2 * (r₁ + r₂)) * (1 + |v₁|) ^ (2 * (r₁ + r₂)) := by
      calc ‖riemannZeta (w₂ + ((a₁ : ℂ) + (v₁ : ℂ) * I))‖
          ≤ C_z12 * (1 + |s.im|) ^ (2 * r₁ + 2 * r₂) * (1 + |v₂ - v₁|) ^ (2 * (r₁ + r₂)) := by
            simpa only [show 2 * (r₁ + r₂) = 2 * r₁ + 2 * r₂ by ring] using hz_v1
        _ ≤ C_z12 * (1 + |s.im|) ^ (2 * r₁ + 2 * r₂) *
              ((1 + |v₂|) ^ (2 * (r₁ + r₂)) * (1 + |v₁|) ^ (2 * (r₁ + r₂))) :=
            mul_le_mul_of_nonneg_left hv_sub (by positivity)
        _ = C_z12 * (1 + |s.im|) ^ (2 * r₁ + 2 * r₂) *
              (1 + |v₂|) ^ (2 * (r₁ + r₂)) * (1 + |v₁|) ^ (2 * (r₁ + r₂)) := by ring
    have hX₂_a₁ : ‖(X₂ : ℂ) ^ ((a₁ : ℂ) + (v₁ : ℂ) * I)‖ = ((b : ℝ) / Y) ^ (2 * r₁) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX₂_pos,
        show (((a₁ : ℂ) + (v₁ : ℂ) * I).re) = a₁ by simp]
      dsimp only [X₂, a₁]
      rw [Real.rpow_neg hX₂_pos.le, Real.rpow_natCast, ← inv_pow, inv_div]
    have hker_a₁ := norm_smoothAFEGaussianKernel_vertical_le_of_ne ha₁_lt0.ne v₁
    rw [abs_of_neg ha₁_lt0] at hker_a₁
    rw [hX₂_a₁]
    calc ‖riemannZeta (w₂ + ((a₁ : ℂ) + (v₁ : ℂ) * I))‖ * ((b : ℝ) / Y) ^ (2 * r₁) *
            ‖smoothAFEGaussianKernel ((a₁ : ℂ) + (v₁ : ℂ) * I)‖
        ≤ (C_z12 * (1 + |s.im|) ^ (2 * r₁ + 2 * r₂) *
            (1 + |v₂|) ^ (2 * (r₁ + r₂)) * (1 + |v₁|) ^ (2 * (r₁ + r₂))) *
            ((b : ℝ) / Y) ^ (2 * r₁) *
            ((Real.exp (a₁ ^ (2 : ℕ)) / (-a₁)) * Real.exp (-v₁ ^ (2 : ℕ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hz_v1' (by positivity))
            hker_a₁ (norm_nonneg _) (by positivity)
      _ = K_in * ((1 + |v₁|) ^ (2 * (r₁ + r₂)) * Real.exp (-v₁ ^ (2 : ℕ))) := by
          dsimp only [K_in]; ring
  have hint_a₁ := norm_integral_le_of_norm_le
    ((integrable_shifted_pow_mul_exp_neg_sq 1 (2 * (r₁ + r₂))).const_mul K_in)
    (Filter.Eventually.of_forall hin_pt)
  rw [MeasureTheory.integral_const_mul] at hint_a₁
  calc (1 / (2 * Real.pi)) * ‖∫ v₁ : ℝ, smoothAFEZetaMellinIntegrand w₂ X₂ ((a₁ : ℂ) + (v₁ : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) *
          (K_in * ∫ v : ℝ, (1 + |v|) ^ (2 * (r₁ + r₂)) * Real.exp (-v ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hint_a₁ (by positivity)
    _ = (1 / (2 * Real.pi)) * C_z12 *
          (Real.exp ((-((2 * r₁ : ℕ) : ℝ)) ^ (2 : ℕ)) / ((2 * r₁ : ℕ) : ℝ)) *
          (∫ v : ℝ, (1 + |v|) ^ (2 * (r₁ + r₂)) * Real.exp (-v ^ (2 : ℕ))) *
          (1 + |s.im|) ^ (2 * r₁ + 2 * r₂) * ((b : ℝ) / Y) ^ (2 * r₁) *
          (1 + |v₂|) ^ (2 * (r₁ + r₂)) := by
        dsimp only [K_in, a₁]; rw [neg_neg]; ring

/-- **Single-fibre Mellin-shifted bound on `smoothOuterVaughanTypeI`:**
combining `smoothOuterVaughanTypeI_fibre_eq_integral` with opposite-height Gaussian cancellation
bounds each Type-I fibre into three pieces with zero continuum pole subtraction. -/
private lemma exists_norm_smoothOuterVaughanTypeI_fibre_le
    {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) :
    ∃ C_fib : ℝ, 0 < C_fib ∧
      ∀ {s : ℂ}, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∀ {x Y : ℝ}, 0 < x → 1 ≤ Y →
          ∀ {b : ℕ}, 1 ≤ b → (b : ℝ) ≤ Y →
            ‖(b : ℂ) ^ (-(1 - s)) *
                ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
                  smoothAFECutoff (((b * (m + 1) : ℕ) : ℝ) / Y) *
                  smoothOuterDirectPairSum s x (b * (m + 1))‖ ≤
              C_fib *
                ((1 + |s.im|) ^ (2 * r₂) * ((b : ℝ) * x) ^ (2 * r₂) +
                  Y ^ ((2 * r₂ + 1 : ℕ) : ℝ) * ((b : ℝ) * x) ^ (2 * r₂) *
                    Real.exp (-s.im ^ (2 : ℕ) / 4) +
                  (1 + |s.im|) ^ (2 * r₁ + 2 * r₂) *
                    ((b : ℝ) / Y) ^ (2 * r₁) * ((b : ℝ) * x) ^ (2 * r₂)) := by
  have hc₂_pos : (0 : ℝ) < ((2 * r₂ : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos two_pos hr₂
  obtain ⟨C_z2, hCz2_pos, hCz2⟩ := exists_norm_riemannZeta_one_sub_even_le hr₂
  obtain ⟨C_z12, hCz12_pos, hCz12⟩ := exists_norm_riemannZeta_one_sub_even_le (r := r₁ + r₂) (by omega)
  have hSmaj_nn : 0 ≤ smoothAFEZetaMajorant 2 := tsum_nonneg fun _ => by positivity
  set g₁ : ℝ → ℝ := fun v => (1 + |v|) ^ (2 * r₂) * Real.exp (-v ^ (2 : ℕ))
  set g₂ : ℝ → ℝ := fun v => Real.exp (-(1 / 4 : ℝ) * v ^ (2 : ℕ))
  set g₃ : ℝ → ℝ := fun v => (1 + |v|) ^ (2 * (r₁ + r₂)) * Real.exp (-v ^ (2 : ℕ))
  have hg₁_int : Integrable g₁ := integrable_shifted_pow_mul_exp_neg_sq 1 (2 * r₂)
  have hg₂_int : Integrable g₂ := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)
  have hg₃_int : Integrable g₃ := integrable_shifted_pow_mul_exp_neg_sq 1 (2 * (r₁ + r₂))
  have hG₁_nn : 0 ≤ ∫ v : ℝ, g₁ v := integral_nonneg fun _ => by dsimp only [g₁]; positivity
  set A_phi : ℝ := smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
    (Real.exp (((2 * r₂ : ℕ) : ℝ) ^ (2 : ℕ)) / ((2 * r₂ : ℕ) : ℝ))
  set A_p2 : ℝ := smoothAFEZetaMajorant 2 * (1 + (2 : ℝ) ^ (2 * r₂)) *
    Real.exp ((1 + ((2 * r₂ : ℕ) : ℝ)) ^ (2 : ℕ) + ((2 * r₂ : ℕ) : ℝ) ^ (2 : ℕ))
  set A_m3 : ℝ := (1 / (2 * Real.pi)) * C_z12 *
    (Real.exp ((-((2 * r₁ : ℕ) : ℝ)) ^ (2 : ℕ)) / ((2 * r₁ : ℕ) : ℝ)) * (∫ v : ℝ, g₃ v)
  set K_p1 : ℝ := (1 / (2 * Real.pi)) * A_phi * C_z2 * (∫ v : ℝ, g₁ v)
  set K_p2 : ℝ := (1 / (2 * Real.pi)) * A_p2 * (∫ v : ℝ, g₂ v)
  set K_p3 : ℝ := (1 / (2 * Real.pi)) * A_phi * A_m3 * (∫ v : ℝ, g₃ v)
  set C_fib : ℝ := max K_p1 (max K_p2 K_p3) + 1
  have hKp1_nn : 0 ≤ K_p1 := by dsimp only [K_p1, A_phi]; positivity
  refine ⟨C_fib, by dsimp only [C_fib]; linarith [le_max_left K_p1 (max K_p2 K_p3)], ?_⟩
  intro s hlo hhi _him x Y hx hY1 b hb1 hbY
  have hs0 : 0 < s.re := by linarith
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hb_pref_le : ‖(b : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
    rw [show (b : ℂ) = ((b : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hb_pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hb1) (by simp; linarith)
  have hfub :
      (∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
          smoothAFECutoff (((b * (m + 1) : ℕ) : ℝ) / Y) *
          smoothOuterDirectPairSum s x (b * (m + 1))) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ,
            (riemannZeta (s + ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)) *
              (1 - (2 : ℂ) ^ (-(1 - s - ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)))) *
              (((b : ℝ) * x : ℝ) : ℂ) ^ ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I) *
              smoothAFEGaussianKernel ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)) *
              (riemannZeta (1 - s - ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)) +
                smoothAFEZetaShiftedPoleResidue
                  (1 - s - ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)) (Y / (b : ℝ)) +
                smoothAFEZetaMellinAt (-((2 * r₁ : ℕ) : ℝ))
                  (1 - s - ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)) (Y / (b : ℝ))) :=
    smoothOuterVaughanTypeI_fibre_eq_integral hr₁ hr₂ hs0 hhi hx hY1 hb1 hbY
  rw [hfub, ← mul_assoc, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  set T₁ : ℝ := (1 + |s.im|) ^ (2 * r₂) * ((b : ℝ) * x) ^ (2 * r₂)
  set T₂ : ℝ := Y ^ ((2 * r₂ + 1 : ℕ) : ℝ) * ((b : ℝ) * x) ^ (2 * r₂) * Real.exp (-s.im ^ (2 : ℕ) / 4)
  set T₃ : ℝ := (1 + |s.im|) ^ (2 * r₁ + 2 * r₂) * ((b : ℝ) / Y) ^ (2 * r₁) * ((b : ℝ) * x) ^ (2 * r₂)
  set c₁ : ℝ := A_phi * C_z2 * T₁
  set c₂_m : ℝ := A_p2 * T₂
  set c₃ : ℝ := A_phi * A_m3 * T₃
  have hpt_sum : ∀ v : ℝ,
      ‖(riemannZeta (s + ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)) *
          (1 - (2 : ℂ) ^ (-(1 - s - ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)))) *
          (((b : ℝ) * x : ℝ) : ℂ) ^ ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I) *
          smoothAFEGaussianKernel ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)) *
        (riemannZeta (1 - s - ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)) +
          smoothAFEZetaShiftedPoleResidue
            (1 - s - ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)) (Y / (b : ℝ)) +
          smoothAFEZetaMellinAt (-((2 * r₁ : ℕ) : ℝ))
            (1 - s - ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I)) (Y / (b : ℝ)))‖ ≤
        c₁ * g₁ v + c₂_m * g₂ v + c₃ * g₃ v := by
    intro v
    rw [mul_add, mul_add]
    refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl) |>.trans
      (add_le_add (add_le_add ?_ ?_) ?_)
    · rw [norm_mul]
      have hphi := norm_smoothOuterVaughanTypeI_phi_le hr₂ hs0 hhi hx hb1 v
      dsimp only at hphi
      have hw : (1 : ℂ) - s - ((((2 * r₂ : ℕ) : ℝ) : ℂ) + (v : ℂ) * I) =
          1 - s - ((2 * r₂ : ℕ) : ℂ) - (v : ℂ) * I := by push_cast; ring
      have hz := hw ▸ hCz2 s v hlo hhi
      exact show _ ≤ c₁ * g₁ v from
        (mul_le_mul hphi hz (norm_nonneg _) (by positivity)).trans_eq
          (by dsimp only [c₁, A_phi, T₁, g₁]; ring)
    · have hp2 := norm_smoothOuterVaughanTypeI_shiftedPole_piece_le hr₂ hs0 hhi hx hY1 hb1 hbY v
      dsimp only at hp2
      exact show _ ≤ c₂_m * g₂ v from
        hp2.trans_eq (by dsimp only [c₂_m, A_p2, T₂, g₂]; ring)
    · rw [norm_mul]
      have hphi := norm_smoothOuterVaughanTypeI_phi_le hr₂ hs0 hhi hx hb1 v
      dsimp only at hphi
      have hm3 := norm_smoothAFEZetaMellinAt_neg_even_le hr₁ hCz12_pos hCz12 hlo hhi hb1 hbY v
      dsimp only at hm3
      exact show _ ≤ c₃ * g₃ v from
        (mul_le_mul hphi hm3 (norm_nonneg _) (by positivity)).trans_eq
          (by dsimp only [c₃, A_phi, A_m3, T₃, g₃]; ring)
  have hi1 : Integrable (fun v : ℝ => c₁ * g₁ v) := hg₁_int.const_mul c₁
  have hi2 : Integrable (fun v : ℝ => c₂_m * g₂ v) := hg₂_int.const_mul c₂_m
  have hi3 : Integrable (fun v : ℝ => c₃ * g₃ v) := hg₃_int.const_mul c₃
  have hi12 : Integrable (fun v : ℝ => c₁ * g₁ v + c₂_m * g₂ v) := hi1.add hi2
  have hi123 : Integrable (fun v : ℝ => c₁ * g₁ v + c₂_m * g₂ v + c₃ * g₃ v) := hi12.add hi3
  have hint_tot := norm_integral_le_of_norm_le hi123 (Filter.Eventually.of_forall hpt_sum)
  have hint_eq : (∫ v : ℝ, c₁ * g₁ v + c₂_m * g₂ v + c₃ * g₃ v) =
      c₁ * (∫ v : ℝ, g₁ v) + c₂_m * (∫ v : ℝ, g₂ v) + c₃ * (∫ v : ℝ, g₃ v) := by
    rw [integral_add hi12 hi3, integral_add hi1 hi2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  have h1_le : K_p1 * T₁ ≤ C_fib * T₁ :=
    mul_le_mul_of_nonneg_right
      (by dsimp only [C_fib]; linarith [le_max_left K_p1 (max K_p2 K_p3)])
      (by dsimp only [T₁]; positivity)
  have h2_le : K_p2 * T₂ ≤ C_fib * T₂ :=
    mul_le_mul_of_nonneg_right
      (by dsimp only [C_fib]; linarith [le_max_right K_p1 (max K_p2 K_p3), le_max_left K_p2 K_p3])
      (by dsimp only [T₂]; positivity)
  have h3_le : K_p3 * T₃ ≤ C_fib * T₃ :=
    mul_le_mul_of_nonneg_right
      (by dsimp only [C_fib]; linarith [le_max_right K_p1 (max K_p2 K_p3), le_max_right K_p2 K_p3])
      (by dsimp only [T₃]; positivity)
  have hstep1 := mul_le_mul (mul_le_mul_of_nonneg_right hb_pref_le (by positivity : 0 ≤ 1 / (2 * Real.pi)))
    hint_tot (norm_nonneg _) (by positivity)
  rw [hint_eq] at hstep1
  have hstep2 : 1 * (1 / (2 * Real.pi)) *
      (c₁ * (∫ v : ℝ, g₁ v) + c₂_m * (∫ v : ℝ, g₂ v) + c₃ * (∫ v : ℝ, g₃ v)) =
      K_p1 * T₁ + K_p2 * T₂ + K_p3 * T₃ := by
    dsimp only [c₁, c₂_m, c₃, K_p1, K_p2, K_p3]
    ring
  rw [hstep2] at hstep1
  have hstep3 : C_fib * T₁ + C_fib * T₂ + C_fib * T₃ = C_fib * (T₁ + T₂ + T₃) := by ring
  linarith

/-- **Unconditional sub-horizon annihilation of both the short Möbius head and the entire smooth
Vaughan Type-I bilinear sum without continuum pole subtraction across ALL of `Ω_open`:**
for every `η ≥ 1` and every `B_dec > 0`, setting `x(s) = |Im s|^{-(1 + η)}` and
`Y(s) = |Im s|^{3 + η}`, there exists `C_ann > 0` such that at **every** point `s ∈ Ω_open`
and for **all** `U, V : ℕ` with `((U * V : ℕ) : ℝ) ≤ |Im s|^{η - 1 / 2}`, both
`smoothOuterVaughanHead` and `smoothOuterVaughanTypeI` are `≤ C_ann * |Im s|^{-B_dec}`. -/
theorem exists_smoothOuter_vaughanTypeI_and_head_annihilation_on_remaining_strip
    {η B_dec : ℝ} (hη1 : 1 ≤ η) (_hB_pos : 0 < B_dec) :
    ∃ C_ann : ℝ, 0 < C_ann ∧
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        let x : ℝ := |s.im| ^ (-(1 + η))
        let Y : ℝ := |s.im| ^ (3 + η)
        ∀ {U V : ℕ}, 1 ≤ U → 1 ≤ V → ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2) →
          ‖smoothOuterVaughanHead U V s x Y‖ ≤ C_ann * |s.im| ^ (-B_dec) ∧
            ‖smoothOuterVaughanTypeI U V s x Y‖ ≤ C_ann * |s.im| ^ (-B_dec) := by
  set A_h : ℕ := max 2 (Nat.ceil ((B_dec + η) / (3 / 2)))
  have hAh2 : (2 : ℝ) ≤ (A_h : ℝ) := by exact_mod_cast le_max_left 2 _
  have hAh_bd : B_dec + η ≤ (3 / 2 : ℝ) * (A_h : ℝ) := by
    have hc : (B_dec + η) / (3 / 2) ≤ (Nat.ceil ((B_dec + η) / (3 / 2)) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil ((B_dec + η) / (3 / 2)) : ℝ) ≤ (A_h : ℝ) := by
      exact_mod_cast le_max_right 2 _
    have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 2)).mp (hc.trans hm)
    linarith
  set r₂ : ℕ := max 1 (Nat.ceil (2 * η + B_dec))
  set r₁ : ℕ := 1
  have hr₂1 : 1 ≤ r₂ := le_max_left 1 _
  have hr₂_bd : 2 * η + B_dec ≤ (r₂ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
  obtain ⟨M_cut, hM_cut1, hM_cut⟩ := exists_norm_smoothAFECutoff_uniform_le
  have hM_cut_pos : 0 < M_cut := zero_lt_one.trans_le hM_cut1
  have hSmaj2_nn : 0 ≤ smoothAFEZetaMajorant 2 := tsum_nonneg fun _ => by positivity
  obtain ⟨K_Ah, hKAh0, hKAh⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := (A_h : ℝ)) (by linarith)
  obtain ⟨C_fib, hCfib_pos, hCfib⟩ := exists_norm_smoothOuterVaughanTypeI_fibre_le (le_refl 1) hr₂1
  set E_p2 : ℝ := 2 * η + (3 + η) * ((2 * r₂ + 1 : ℕ) : ℝ) + B_dec
  obtain ⟨K_exp, hKexp_pos, hKexp⟩ := exists_rpow_mul_exp_neg_quarter_sq_le E_p2
  set C_hd : ℝ := 2 * M_cut * ((1 + (2 : ℝ) ^ (A_h : ℝ)) * K_Ah * smoothAFEZetaMajorant 2) + 1
  set C_I : ℝ := C_fib * ((2 : ℝ) ^ (2 * r₂) + K_exp + (2 : ℝ) ^ (2 + 2 * r₂)) + 1
  refine ⟨max C_hd C_I, lt_of_lt_of_le (by dsimp only [C_I]; positivity) (le_max_right _ _), ?_⟩
  intro s hlo hhi him
  dsimp only
  intro U V hU1 hV1 hUV_bd
  set τ : ℝ := |s.im|
  have hτ1 : 1 ≤ τ := by dsimp only [τ]; linarith
  have hτ_pos : 0 < τ := by dsimp only [τ]; linarith
  set x : ℝ := τ ^ (-(1 + η))
  set Y : ℝ := τ ^ (3 + η)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hτ_pos _
  have hY1 : 1 ≤ Y := Real.one_le_rpow hτ1 (by linarith)
  have hY_pos : 0 < Y := zero_lt_one.trans_le hY1
  have hs0 : 0 < s.re := by linarith
  constructor
  · -- Part A: Bound `smoothOuterVaughanHead U V s x Y` via finite support `d + 1 ≤ max U V ≤ U * V`.
    have hmax_UV : max U V ≤ U * V :=
      max_le (Nat.le_mul_of_pos_right U hV1) (Nat.le_mul_of_pos_left V hU1)
    unfold smoothOuterVaughanHead
    rw [tsum_eq_sum (s := Finset.range (U * V)) fun d hd => by
      have hgt : U * V < d + 1 := by have := Finset.mem_range.not.mp hd; omega
      have hgtU : U < d + 1 := lt_of_le_of_lt (le_max_left U V |>.trans hmax_UV) hgt
      have hgtV : V < d + 1 := lt_of_le_of_lt (le_max_right U V |>.trans hmax_UV) hgt
      rw [ArithmeticFunction.add_apply,
        _root_.RHTower.Sieve.truncAF_apply_of_gt hgtU,
        _root_.RHTower.Sieve.truncAF_apply_of_gt hgtV]
      simp]
    have hpt_hd : ∀ d ∈ Finset.range (U * V),
        ‖((((_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U +
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) (d + 1) : ℝ) : ℂ)) *
          ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
          smoothOuterDirectPairSum s x (d + 1)‖ ≤
          C_hd * τ ^ (-(3 / 2 : ℝ) * (A_h : ℝ)) := by
      intro d hd
      have hd_le_UV : ((d + 1 : ℕ) : ℝ) ≤ τ ^ (η - 1 / 2) := by
        have hnat : d + 1 ≤ U * V := by have := Finset.mem_range.mp hd; omega
        exact (by exact_mod_cast hnat : ((d + 1 : ℕ) : ℝ) ≤ ((U * V : ℕ) : ℝ)).trans hUV_bd
      have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos d
      have hd_dx : ((d + 1 : ℕ) : ℝ) * x ≤ τ ^ (-(3 / 2 : ℝ)) := by
        calc ((d + 1 : ℕ) : ℝ) * x
            ≤ τ ^ (η - 1 / 2) * τ ^ (-(1 + η)) := mul_le_mul_of_nonneg_right hd_le_UV hx_pos.le
          _ = τ ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hτ_pos]; congr 1; ring
      have hdx_Ah : (((d + 1 : ℕ) : ℝ) * x) ^ (A_h : ℝ) ≤ τ ^ (-(3 / 2 : ℝ) * (A_h : ℝ)) :=
        (Real.rpow_le_rpow (mul_pos hd_pos hx_pos).le hd_dx (by linarith)).trans_eq
          (by rw [← Real.rpow_mul hτ_pos.le])
      have hc_le2 :
          ‖((((_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U +
              _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) (d + 1) : ℝ) : ℂ))‖ ≤ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, ArithmeticFunction.add_apply]
        linarith [abs_add_le
          (_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U (d + 1))
          (_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V (d + 1)),
          abs_truncAF_moebius_le_one' U (d + 1), abs_truncAF_moebius_le_one' V (d + 1)]
      have hcpow_le1 : ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
        rw [show ((d + 1 : ℕ) : ℂ) = (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos hd_pos]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_pos d) (by simp; linarith)
      have hW_le : ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ ≤ M_cut :=
        hM_cut (div_pos hd_pos hY_pos)
      have hp_le := (norm_smoothOuterDirectPairSum_le hAh2 hKAh0 hKAh hs0 hhi hx_pos (Nat.succ_pos d)).trans
        (mul_le_mul_of_nonneg_left hdx_Ah
          (mul_nonneg (mul_nonneg (by positivity) hKAh0) (tsum_nonneg fun _ => by positivity)))
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖((((_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U +
              _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) (d + 1) : ℝ) : ℂ))‖ *
            ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ * ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ *
            ‖smoothOuterDirectPairSum s x (d + 1)‖
          ≤ 2 * 1 * M_cut *
              (((1 + (2 : ℝ) ^ (A_h : ℝ)) * K_Ah * smoothAFEZetaMajorant 2) *
                τ ^ (-(3 / 2 : ℝ) * (A_h : ℝ))) :=
            mul_le_mul
              (mul_le_mul (mul_le_mul hc_le2 hcpow_le1 (norm_nonneg _) zero_le_two)
                hW_le (norm_nonneg _) (by positivity))
              hp_le (norm_nonneg _) (by positivity)
        _ ≤ C_hd * τ ^ (-(3 / 2 : ℝ) * (A_h : ℝ)) := by
            have hnn : 0 ≤ τ ^ (-(3 / 2 : ℝ) * (A_h : ℝ)) := Real.rpow_nonneg hτ_pos.le _
            dsimp only [C_hd]; nlinarith
    have hUV_le_η : ((U * V : ℕ) : ℝ) ≤ τ ^ η :=
      hUV_bd.trans (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith))
    calc ‖∑ d ∈ Finset.range (U * V),
            ((((_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U +
                _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) (d + 1) : ℝ) : ℂ)) *
              ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
              smoothOuterDirectPairSum s x (d + 1)‖
        ≤ ∑ _d ∈ Finset.range (U * V), C_hd * τ ^ (-(3 / 2 : ℝ) * (A_h : ℝ)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hpt_hd)
      _ = ((U * V : ℕ) : ℝ) * (C_hd * τ ^ (-(3 / 2 : ℝ) * (A_h : ℝ))) := by simp
      _ ≤ C_hd * (τ ^ η * τ ^ (-(3 / 2 : ℝ) * (A_h : ℝ))) := by
          have : 0 ≤ C_hd * τ ^ (-(3 / 2 : ℝ) * (A_h : ℝ)) := by dsimp only [C_hd]; positivity
          nlinarith
      _ ≤ C_hd * τ ^ (-B_dec) := by
          rw [← Real.rpow_add hτ_pos]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith))
            (by dsimp only [C_hd]; positivity)
      _ ≤ max C_hd C_I * τ ^ (-B_dec) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hτ_pos.le _)
  · -- Part B: Bound `smoothOuterVaughanTypeI U V s x Y` via `smoothOuterVaughanTypeI_eq_sum_fibres`.
    rw [smoothOuterVaughanTypeI_eq_sum_fibres U V hx_pos hY_pos hs0 hhi]
    have hUV_le_η : ((U * V : ℕ) : ℝ) ≤ τ ^ η :=
      hUV_bd.trans (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith))
    have hpt_b : ∀ b ∈ Finset.Icc 1 (U * V),
        ‖(-(((_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
              _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ)) *
            ((b : ℂ) ^ (-(1 - s)) *
              ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
                smoothAFECutoff (((b * (m + 1) : ℕ) : ℝ) / Y) *
                smoothOuterDirectPairSum s x (b * (m + 1)))‖ ≤
          τ ^ η * (C_I * τ ^ (-(2 * η + B_dec))) := by
      intro b hb
      obtain ⟨hb1, hbUV⟩ := Finset.mem_Icc.mp hb
      have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
      have hb_le_bd : (b : ℝ) ≤ τ ^ (η - 1 / 2) :=
        (by exact_mod_cast hbUV : (b : ℝ) ≤ ((U * V : ℕ) : ℝ)).trans hUV_bd
      have hb_le_η : (b : ℝ) ≤ τ ^ η :=
        hb_le_bd.trans (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith))
      have hb_le_Y : (b : ℝ) ≤ Y :=
        hb_le_η.trans (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith))
      have hf_b_le :
          ‖(-(((_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
              _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ))‖ ≤
            τ ^ η := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, ArithmeticFunction.mul_apply]
        have hcard : (b.divisorsAntidiagonal.card : ℝ) ≤ (b : ℝ) := by
          exact_mod_cast card_divisorsAntidiagonal_le_self hb1
        calc |∑ p ∈ b.divisorsAntidiagonal,
                _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
                  _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V p.2|
            ≤ ∑ p ∈ b.divisorsAntidiagonal,
                |_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
                  _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V p.2| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _p ∈ b.divisorsAntidiagonal, (1 : ℝ) := Finset.sum_le_sum fun p _ => by
              rw [abs_mul]
              exact mul_le_one₀ (abs_truncAF_moebius_le_one' U p.1) (abs_nonneg _)
                (abs_truncAF_moebius_le_one' V p.2)
          _ = (b.divisorsAntidiagonal.card : ℝ) := by simp
          _ ≤ τ ^ η := hcard.trans hb_le_η
      have hfib := hCfib hlo hhi him hx_pos hY1 hb1 hb_le_Y
      -- Bound the three fibre pieces at `x = τ^{-(1 + η)}`, `Y = τ^{3 + η}`, `b ≤ τ^{η - 1 / 2}`.
      have hbx_le : (b : ℝ) * x ≤ τ ^ (-(3 / 2 : ℝ)) := by
        calc (b : ℝ) * x ≤ τ ^ (η - 1 / 2) * τ ^ (-(1 + η)) :=
              mul_le_mul_of_nonneg_right hb_le_bd hx_pos.le
          _ = τ ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hτ_pos]; congr 1; ring
      have hbY_le : (b : ℝ) / Y ≤ τ ^ (-3 : ℝ) := by
        calc (b : ℝ) / Y ≤ τ ^ η / τ ^ (3 + η) := div_le_div_of_nonneg_right hb_le_η hY_pos.le
          _ = τ ^ (-3 : ℝ) := by rw [← Real.rpow_sub hτ_pos]; congr 1; ring
      have h1τ_le : 1 + τ ≤ 2 * τ := by linarith
      have hp1 : (1 + τ) ^ (2 * r₂) * ((b : ℝ) * x) ^ (2 * r₂) ≤
          (2 : ℝ) ^ (2 * r₂) * τ ^ (-(2 * η + B_dec)) := by
        have hτbx : (1 + τ) * ((b : ℝ) * x) ≤ 2 * τ ^ (-(1 / 2 : ℝ)) := by
          calc (1 + τ) * ((b : ℝ) * x)
              ≤ (2 * τ) * τ ^ (-(3 / 2 : ℝ)) :=
                mul_le_mul h1τ_le hbx_le (by positivity) (by positivity)
            _ = 2 * (τ ^ (1 : ℝ) * τ ^ (-(3 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
            _ = 2 * τ ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hτ_pos]; norm_num
        rw [← mul_pow]
        calc ((1 + τ) * ((b : ℝ) * x)) ^ (2 * r₂)
            ≤ (2 * τ ^ (-(1 / 2 : ℝ))) ^ (2 * r₂) :=
              pow_le_pow_left₀ (by positivity) hτbx (2 * r₂)
          _ = (2 : ℝ) ^ (2 * r₂) * τ ^ (-(r₂ : ℝ)) := by
              rw [mul_pow, ← Real.rpow_natCast (τ ^ _) (2 * r₂), ← Real.rpow_mul hτ_pos.le]
              congr 2; push_cast; ring
          _ ≤ (2 : ℝ) ^ (2 * r₂) * τ ^ (-(2 * η + B_dec)) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)) (by positivity)
      have hp2 : Y ^ ((2 * r₂ + 1 : ℕ) : ℝ) * ((b : ℝ) * x) ^ (2 * r₂) *
            Real.exp (-s.im ^ (2 : ℕ) / 4) ≤ K_exp * τ ^ (-(2 * η + B_dec)) := by
        have hbx1 : ((b : ℝ) * x) ^ (2 * r₂) ≤ 1 :=
          pow_le_one₀ (by positivity) (hbx_le.trans (Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)))
        have hY_pow : Y ^ ((2 * r₂ + 1 : ℕ) : ℝ) = τ ^ ((3 + η) * ((2 * r₂ + 1 : ℕ) : ℝ)) :=
          (Real.rpow_mul hτ_pos.le _ _).symm
        have hsim_sq : s.im ^ (2 : ℕ) = τ ^ (2 : ℕ) := (sq_abs s.im).symm
        rw [hY_pow, hsim_sq]
        have hexp_split :
            τ ^ ((3 + η) * ((2 * r₂ + 1 : ℕ) : ℝ)) * Real.exp (-τ ^ (2 : ℕ) / 4) =
              (τ ^ E_p2 * Real.exp (-τ ^ (2 : ℕ) / 4)) * τ ^ (-(2 * η + B_dec)) := by
          rw [mul_right_comm, ← Real.rpow_add hτ_pos]
          congr 2; dsimp only [E_p2]; ring
        calc τ ^ ((3 + η) * ((2 * r₂ + 1 : ℕ) : ℝ)) * ((b : ℝ) * x) ^ (2 * r₂) *
                Real.exp (-τ ^ (2 : ℕ) / 4)
            ≤ τ ^ ((3 + η) * ((2 * r₂ + 1 : ℕ) : ℝ)) * 1 * Real.exp (-τ ^ (2 : ℕ) / 4) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbx1 (by positivity)) (Real.exp_nonneg _)
          _ = (τ ^ E_p2 * Real.exp (-τ ^ (2 : ℕ) / 4)) * τ ^ (-(2 * η + B_dec)) := by
              rw [mul_one, hexp_split]
          _ ≤ K_exp * τ ^ (-(2 * η + B_dec)) :=
              mul_le_mul_of_nonneg_right (hKexp hτ1) (Real.rpow_nonneg hτ_pos.le _)
      have hp3 : (1 + τ) ^ (2 * r₁ + 2 * r₂) * ((b : ℝ) / Y) ^ (2 * r₁) * ((b : ℝ) * x) ^ (2 * r₂) ≤
          (2 : ℝ) ^ (2 + 2 * r₂) * τ ^ (-(2 * η + B_dec)) := by
        dsimp only [r₁]
        have hf1 : (1 + τ) ^ 2 * ((b : ℝ) / Y) ^ 2 ≤ (2 : ℝ) ^ 2 * 1 := by
          have h1 : (1 + τ) * ((b : ℝ) / Y) ≤ 2 * τ ^ (-2 : ℝ) := by
            calc (1 + τ) * ((b : ℝ) / Y) ≤ (2 * τ) * τ ^ (-3 : ℝ) :=
                  mul_le_mul h1τ_le hbY_le (by positivity) (by positivity)
              _ = 2 * (τ ^ (1 : ℝ) * τ ^ (-3 : ℝ)) := by rw [Real.rpow_one]; ring
              _ = 2 * τ ^ (-2 : ℝ) := by rw [← Real.rpow_add hτ_pos]; norm_num
          have h2 : τ ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
          rw [← mul_pow]
          exact (pow_le_pow_left₀ (by positivity)
            (h1.trans (show 2 * τ ^ (-2 : ℝ) ≤ 2 by linarith [h2])) 2).trans_eq (by ring)
        rw [pow_add, show 2 * 1 = 2 by rfl]
        calc ((1 + τ) ^ 2 * (1 + τ) ^ (2 * r₂)) * ((b : ℝ) / Y) ^ 2 * ((b : ℝ) * x) ^ (2 * r₂)
            = ((1 + τ) ^ 2 * ((b : ℝ) / Y) ^ 2) * ((1 + τ) ^ (2 * r₂) * ((b : ℝ) * x) ^ (2 * r₂)) := by ring
          _ ≤ ((2 : ℝ) ^ 2 * 1) * ((2 : ℝ) ^ (2 * r₂) * τ ^ (-(2 * η + B_dec))) :=
              mul_le_mul hf1 hp1 (by positivity) (by positivity)
          _ = (2 : ℝ) ^ (2 + 2 * r₂) * τ ^ (-(2 * η + B_dec)) := by rw [pow_add]; ring
      have hfib' :
          ‖(b : ℂ) ^ (-(1 - s)) *
              ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
                smoothAFECutoff (((b * (m + 1) : ℕ) : ℝ) / Y) *
                smoothOuterDirectPairSum s x (b * (m + 1))‖ ≤
            C_I * τ ^ (-(2 * η + B_dec)) := by
        refine hfib.trans ?_
        have hsum_p := add_le_add (add_le_add hp1 hp2) hp3
        have h1 := mul_le_mul_of_nonneg_left hsum_p hCfib_pos.le
        have hnn : 0 ≤ τ ^ (-(2 * η + B_dec)) := Real.rpow_nonneg hτ_pos.le _
        dsimp only [C_I]
        nlinarith
      rw [norm_mul]
      exact mul_le_mul hf_b_le hfib' (norm_nonneg _) (Real.rpow_nonneg hτ_pos.le _)
    have hcard_Icc : ((Finset.Icc 1 (U * V)).card : ℝ) ≤ ((U * V : ℕ) : ℝ) := by
      have hsub : Finset.Icc 1 (U * V) ⊆ (Finset.range (U * V + 1)).erase 0 := fun q hq =>
        Finset.mem_erase.mpr ⟨by have := (Finset.mem_Icc.mp hq).1; omega,
          Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hq).2; omega)⟩
      have hle : (Finset.Icc 1 (U * V)).card ≤ U * V :=
        (Finset.card_le_card hsub).trans_eq
          (by rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]; omega)
      exact_mod_cast hle
    calc ‖∑ b ∈ Finset.Icc 1 (U * V),
            (-(((_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
                _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ)) *
              ((b : ℂ) ^ (-(1 - s)) *
                ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-(1 - s)) *
                  smoothAFECutoff (((b * (m + 1) : ℕ) : ℝ) / Y) *
                  smoothOuterDirectPairSum s x (b * (m + 1)))‖
        ≤ ∑ _b ∈ Finset.Icc 1 (U * V), τ ^ η * (C_I * τ ^ (-(2 * η + B_dec))) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hpt_b)
      _ = ((Finset.Icc 1 (U * V)).card : ℝ) * (τ ^ η * (C_I * τ ^ (-(2 * η + B_dec)))) := by simp
      _ ≤ ((U * V : ℕ) : ℝ) * (τ ^ η * (C_I * τ ^ (-(2 * η + B_dec)))) :=
          mul_le_mul_of_nonneg_right hcard_Icc (by dsimp only [C_I]; positivity)
      _ ≤ τ ^ η * (τ ^ η * (C_I * τ ^ (-(2 * η + B_dec)))) :=
          mul_le_mul_of_nonneg_right hUV_le_η (by dsimp only [C_I]; positivity)
      _ = C_I * (τ ^ η * τ ^ η * τ ^ (-(2 * η + B_dec))) := by ring
      _ = C_I * τ ^ (-B_dec) := by
          rw [← Real.rpow_add hτ_pos, ← Real.rpow_add hτ_pos]
          congr 2; ring
      _ ≤ max C_hd C_I * τ ^ (-B_dec) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hτ_pos.le _)

end Part3SubHorizonVaughanTypeIAnnihilation


/-! ### Part 4: Pure Vaughan Type-II Cross-Height Duality and Pointwise `HasStrictPrimeGasWitness` Production on `Ω_open` -/

section Part4PureVaughanTypeIIDuality

/-- Uniform single-`tsum` bound on the `k ≥ 3` smooth outer sieve dual tail across `Ω_open`. -/
private lemma exists_smoothOuter_dual_sieve_tail_le {η : ℝ} :
    ∃ C_tail : ℝ, 0 ≤ C_tail ∧
      ∀ {s : ℂ}, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ‖∑' j : ℕ, smoothOuterSieveCoeff (|s.im| ^ (3 + η)) (j + 3) *
            smoothAFEZetaDualCoefficientGeneral s (|s.im| ^ (-(1 + η))) (j + 2)‖ ≤
          C_tail * |s.im| ^ (-(1 / 4 : ℝ)) := by
  set r : ℕ := max 4 (Nat.ceil ((7 + 2 * η) / 2))
  have hr4 : 4 ≤ r := le_max_left 4 _
  have hr_bd : 7 + 2 * η ≤ 2 * (r : ℝ) := by
    have hc : (7 + 2 * η) / 2 ≤ (Nat.ceil ((7 + 2 * η) / 2) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil ((7 + 2 * η) / 2) : ℝ) ≤ (r : ℝ) := by exact_mod_cast le_max_right 4 _
    linarith [(div_le_iff₀ two_pos).mp (hc.trans hm)]
  set B_sv : ℝ := 2 * (r : ℝ) - 2
  have hBsv_pos : 0 < B_sv := by
    dsimp only [B_sv]
    have hr4_real : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr4
    linarith
  obtain ⟨K_Bsv, hKBsv0, hKBsv⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow hBsv_pos
  obtain ⟨K_dual, hKdual_pos, hKdual⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := 3001 / 24000) (by norm_num) (by norm_num) (r := r) (by omega)
  set S_32 : ℝ := smoothAFEZetaMajorant (3 / 2)
  have hS32_nn : 0 ≤ S_32 := tsum_nonneg fun _ => by positivity
  set C_tail : ℝ := 2 * K_Bsv * K_dual * (2 : ℝ) ^ (2 * r + 1) * S_32
  refine ⟨C_tail, by dsimp only [C_tail]; positivity, fun {s} hlo hhi him => ?_⟩
  set τ : ℝ := |s.im|
  have hτ1 : 1 ≤ τ := by dsimp only [τ]; linarith
  have hτ_pos : 0 < τ := by dsimp only [τ]; linarith
  set x : ℝ := τ ^ (-(1 + η))
  set Y : ℝ := τ ^ (3 + η)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hτ_pos _
  have hY_pos : 0 < Y := Real.rpow_pos_of_pos hτ_pos _
  set P_fac : ℝ := 2 * K_Bsv * K_dual * Y ^ (-B_sv) * x ^ (-2 * (r : ℝ)) *
    (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
  have hP_nn : 0 ≤ P_fac := by dsimp only [P_fac]; positivity
  have hpt_j : ∀ j : ℕ,
      ‖smoothOuterSieveCoeff Y (j + 3) * smoothAFEZetaDualCoefficientGeneral s x (j + 2)‖ ≤
        P_fac * (1 / (j + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
    intro j
    have hsv := norm_smoothOuterSieveCoeff_le_rpow_of_three_le hBsv_pos hKBsv0 hKBsv hY_pos (by omega : 3 ≤ j + 3)
    have hId := (hKdual s x hlo hhi hx_pos).1 (j + 2)
    rw [show ((j + 2 : ℕ) : ℝ) + 1 = ((j + 3 : ℕ) : ℝ) by push_cast; ring] at hId
    have hk_pos : (0 : ℝ) < ((j + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j + 3)
    have hk_comb : ((j + 3 : ℕ) : ℝ) ^ (1 + B_sv) *
        ((j + 3 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) ≤ 1 / (j + 1 : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hk_pos,
        show 1 + B_sv + -(2 * (r : ℝ) + 1 - s.re) = s.re - 2 by dsimp only [B_sv]; ring]
      have h1 : ((j + 3 : ℕ) : ℝ) ^ (s.re - 2) ≤ ((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ j + 3)) (by linarith)
      have h2 : ((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ (j + 1 : ℝ) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (by exact_mod_cast (by omega : j + 1 ≤ j + 3)) (by norm_num)
      exact (h1.trans h2).trans_eq
        (show (j + 1 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / (j + 1 : ℝ) ^ (3 / 2 : ℝ) by
          rw [Real.rpow_neg (by positivity), one_div])
    rw [norm_mul]
    calc ‖smoothOuterSieveCoeff Y (j + 3)‖ * ‖smoothAFEZetaDualCoefficientGeneral s x (j + 2)‖
        ≤ (2 * K_Bsv * ((j + 3 : ℕ) : ℝ) ^ (1 + B_sv) * Y ^ (-B_sv)) *
            (K_dual * x ^ (-2 * (r : ℝ)) * (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
              ((j + 3 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re))) :=
          mul_le_mul hsv hId (norm_nonneg _) (by positivity)
      _ = P_fac * (((j + 3 : ℕ) : ℝ) ^ (1 + B_sv) *
            ((j + 3 : ℕ) : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re))) := by dsimp only [P_fac]; ring
      _ ≤ P_fac * (1 / (j + 1 : ℝ) ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hk_comb hP_nn
  have hmaj_sum := (summable_smoothAFEZetaMajorant (p := 3 / 2) (by norm_num)).mul_left P_fac
  have hs_du_j : Summable (fun j : ℕ =>
      smoothOuterSieveCoeff Y (j + 3) * smoothAFEZetaDualCoefficientGeneral s x (j + 2)) :=
    Summable.of_norm_bounded hmaj_sum hpt_j
  have hts_le :
      ‖∑' j : ℕ, smoothOuterSieveCoeff Y (j + 3) * smoothAFEZetaDualCoefficientGeneral s x (j + 2)‖ ≤
        P_fac * S_32 :=
    (norm_tsum_le_tsum_norm hs_du_j.norm).trans
      ((Summable.tsum_le_tsum hpt_j hs_du_j.norm hmaj_sum).trans_eq tsum_mul_left)
  have h1τ_pow : (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) ≤
      (2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2) := by
    have hexp_le : (2 * r : ℝ) + 1 / 2 - s.re ≤ ((2 * r + 1 : ℕ) : ℝ) := by push_cast; linarith
    calc (1 + τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
        ≤ (2 * τ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = (2 : ℝ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * τ ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
          Real.mul_rpow two_pos.le hτ_pos.le
      _ ≤ (2 : ℝ) ^ (((2 * r + 1 : ℕ) : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le one_lt_two.le hexp_le)
            (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)) (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2) := by rw [Real.rpow_natCast]
  have hτ_exp :
      Y ^ (-B_sv) * x ^ (-2 * (r : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2) ≤ τ ^ (-(1 / 4 : ℝ)) := by
    dsimp only [Y, x, B_sv]
    rw [← Real.rpow_mul hτ_pos.le, ← Real.rpow_mul hτ_pos.le,
      ← Real.rpow_add hτ_pos, ← Real.rpow_add hτ_pos]
    refine Real.rpow_le_rpow_of_exponent_le hτ1 ?_
    have hid : (3 + η) * -(2 * (r : ℝ) - 2) + -(1 + η) * (-2 * (r : ℝ)) + ((2 * r : ℝ) + 1 / 2) =
        13 / 2 + 2 * η - 2 * (r : ℝ) := by ring
    linarith
  calc ‖∑' j : ℕ, smoothOuterSieveCoeff Y (j + 3) * smoothAFEZetaDualCoefficientGeneral s x (j + 2)‖
      ≤ P_fac * S_32 := hts_le
    _ ≤ (2 * K_Bsv * K_dual * Y ^ (-B_sv) * x ^ (-2 * (r : ℝ)) *
          ((2 : ℝ) ^ (2 * r + 1) * τ ^ ((2 * r : ℝ) + 1 / 2))) * S_32 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1τ_pow (by positivity)) hS32_nn
    _ = C_tail * (Y ^ (-B_sv) * x ^ (-2 * (r : ℝ)) * τ ^ ((2 * r : ℝ) + 1 / 2)) := by
        dsimp only [C_tail]; ring
    _ ≤ C_tail * τ ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hτ_exp (by dsimp only [C_tail]; positivity)

/-- **Pure Vaughan Type-II cross-height duality across ALL of `Ω_open`:**
for every `η ≥ 1`, setting `x(s) = |Im s|^{-(1 + η)}` and `Y(s) = |Im s|^{3 + η}`, there exists
`C_du > 0` such that at **every** point `s ∈ Ω_open` (`3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`)
and for **all** `U, V : ℕ` (`1 ≤ U, V`, `U * V ≤ |Im s|^{η - 1 / 2}`),
`ζ(s) * smoothOuterMoebiusSeries (Y(s)) (1 - s)` equals
`(1 - 2^{-(1 - s)}) zetaChi(s) + smoothOuterVaughanTypeII U V s (x(s)) (Y(s))` within
`≤ C_du * |Im s|^{-1 / 4}`. -/
theorem exists_pure_vaughanTypeII_crossHeight_duality_on_remaining_strip
    {η : ℝ} (hη1 : 1 ≤ η) :
    ∃ C_du : ℝ, 0 < C_du ∧
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        let x : ℝ := |s.im| ^ (-(1 + η))
        let Y : ℝ := |s.im| ^ (3 + η)
        ∀ {U V : ℕ}, 1 ≤ U → 1 ≤ V → ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2) →
          ‖riemannZeta s * smoothOuterMoebiusSeries Y (1 - s) -
              ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + smoothOuterVaughanTypeII U V s x Y)‖ ≤
            C_du * |s.im| ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C_ann, hCann_pos, hCann⟩ :=
    exists_smoothOuter_vaughanTypeI_and_head_annihilation_on_remaining_strip hη1
      (B_dec := 1 / 4) (by norm_num)
  obtain ⟨C_vac, hCvac_pos, hCvac⟩ := exists_norm_smoothAFEZetaDualCoefficientGeneral_zero_add_zetaChi_le
  obtain ⟨C₀_chi, hC₀_chi_pos, hC₀_chi⟩ :=
    exists_norm_zetaChi_leftStrip_rpow_le (σ_min := 3001 / 24000) (by norm_num) (by norm_num)
  obtain ⟨K₁_sub, hK₁_sub0, hK₁_sub⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow (δ := 1) one_pos
  obtain ⟨C_tail, hCtail0, hCtail⟩ := exists_smoothOuter_dual_sieve_tail_le (η := η)
  set C_vac_tot : ℝ := 3 * C_vac + 3 * K₁_sub * (2 * C_vac + 2 * C₀_chi)
  set C_du : ℝ := 2 * C_ann + C_vac_tot + C_tail + 1
  refine ⟨C_du, by dsimp only [C_du, C_vac_tot]; positivity, ?_⟩
  intro s hlo hhi him
  dsimp only
  intro U V hU1 hV1 hUV_bd
  set τ : ℝ := |s.im|
  have hτ1 : 1 ≤ τ := by dsimp only [τ]; linarith
  have hτ_pos : 0 < τ := by dsimp only [τ]; linarith
  set x : ℝ := τ ^ (-(1 + η))
  set Y : ℝ := τ ^ (3 + η)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hτ_pos _
  have hY_pos : 0 < Y := Real.rpow_pos_of_pos hτ_pos _
  have hs0 : 0 < s.re := by linarith
  have h2_le1 : ‖(2 : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos, show (-(1 - s)).re = -(1 - s.re) by simp]
    exact Real.rpow_le_one_of_one_le_of_nonpos one_lt_two.le (by linarith)
  rw [smoothOuter_poleCleared_reflected_moebius_crossHeight_eq hx_pos hY_pos hs0 hhi]
  change ‖(smoothOuterMoebiusDirect s x Y -
        (smoothAFECutoff (1 / Y) * smoothAFEZetaDualCoefficientGeneral s x 0 -
          smoothAFECutoff (2 / Y) * smoothAFEZetaDualCoefficientGeneral s x 1) -
        ∑' j : ℕ, smoothOuterSieveCoeff Y (j + 3) *
          smoothAFEZetaDualCoefficientGeneral s x (j + 2)) -
      ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + smoothOuterVaughanTypeII U V s x Y)‖ ≤
    C_du * τ ^ (-(1 / 4 : ℝ))
  rw [smoothOuterMoebiusDirect_eq_vaughan_decomposition U V hx_pos hY_pos hs0 hhi]
  have hI1_eq :
      (2 : ℂ) ^ (-(1 - s)) * smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 =
        smoothAFEZetaDualCoefficientGeneral s x 1 := by
    simpa only [Nat.cast_ofNat] using
      smoothAFEZetaDualCoefficientGeneral_mul_scale (d := 2) (by omega) hx_pos hs0 hhi 0
  set E_vaug : ℂ := smoothOuterVaughanHead U V s x Y + smoothOuterVaughanTypeI U V s x Y
  set E_vac : ℂ :=
    -((smoothAFECutoff (1 / Y) - 1) * smoothAFEZetaDualCoefficientGeneral s x 0 +
      (smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s)) +
    (2 : ℂ) ^ (-(1 - s)) *
      ((smoothAFECutoff (2 / Y) - 1) * smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 +
        (smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 + zetaChi s))
  set E_du : ℂ := ∑' j : ℕ, smoothOuterSieveCoeff Y (j + 3) *
    smoothAFEZetaDualCoefficientGeneral s x (j + 2)
  have halg :
      (smoothOuterVaughanHead U V s x Y + smoothOuterVaughanTypeI U V s x Y +
          smoothOuterVaughanTypeII U V s x Y -
        (smoothAFECutoff (1 / Y) * smoothAFEZetaDualCoefficientGeneral s x 0 -
          smoothAFECutoff (2 / Y) * smoothAFEZetaDualCoefficientGeneral s x 1) - E_du) -
      ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + smoothOuterVaughanTypeII U V s x Y) =
      E_vaug + E_vac - E_du := by
    dsimp only [E_vaug, E_vac]
    linear_combination -(smoothAFECutoff (2 / Y) * hI1_eq)
  rw [halg]
  obtain ⟨hhd_bd, hI_bd⟩ := hCann s hlo hhi him hU1 hV1 hUV_bd
  have hvaug_bd : ‖E_vaug‖ ≤ 2 * C_ann * τ ^ (-(1 / 4 : ℝ)) := by
    dsimp only [E_vaug]
    linarith [norm_add_le (smoothOuterVaughanHead U V s x Y) (smoothOuterVaughanTypeI U V s x Y)]
  have hvac_bd : ‖E_vac‖ ≤ C_vac_tot * τ ^ (-(1 / 4 : ℝ)) := by
    have hx_le_m2 : x ≤ τ ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
    have hx_le1 : x ≤ 1 := hx_le_m2.trans (Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num))
    have hx_qtr : x ^ (3 / 4 - s.re) ≤ τ ^ (-(1 / 4 : ℝ)) := by
      have h1 : x ^ (3 / 4 - s.re) ≤ x ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hx_pos hx_le1 (by linarith)
      have h2 : x ^ (1 / 4 : ℝ) ≤ (τ ^ (-2 : ℝ)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hx_pos.le hx_le_m2 (by norm_num)
      have h3 : (τ ^ (-2 : ℝ)) ^ (1 / 4 : ℝ) ≤ τ ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_mul hτ_pos.le]
        exact Real.rpow_le_rpow_of_exponent_le hτ1 (by norm_num)
      exact (h1.trans h2).trans h3
    have h2x_qtr : (2 * x) ^ (3 / 4 - s.re) ≤ 2 * τ ^ (-(1 / 4 : ℝ)) := by
      rw [Real.mul_rpow two_pos.le hx_pos.le]
      have h2_le : (2 : ℝ) ^ (3 / 4 - s.re) ≤ 2 :=
        (Real.rpow_le_rpow_of_exponent_le one_lt_two.le (by linarith)).trans_eq (Real.rpow_one 2)
      exact mul_le_mul h2_le hx_qtr (by positivity) zero_le_two
    have hv1 := (hCvac s x hs0 hhi hx_pos).trans (mul_le_mul_of_nonneg_left hx_qtr hCvac_pos.le)
    have hv2 := (hCvac s (2 * x) hs0 hhi (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2x_qtr hCvac_pos.le)
    have hchi_le : ‖zetaChi s‖ ≤ 2 * C₀_chi * τ ^ (1 / 2 : ℝ) := by
      have hs_eq : ((s.re : ℂ) + (s.im : ℂ) * I) = s := Complex.re_add_im s
      have hb := hs_eq ▸ hC₀_chi s.re s.im hlo hhi.le
      have h1 : (1 + |s.im|) ^ (1 / 2 - s.re) ≤ (2 * τ) ^ (1 / 2 : ℝ) :=
        (Real.rpow_le_rpow (by positivity) (by dsimp only [τ]; linarith) (by linarith)).trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
      have h2 : (2 * τ) ^ (1 / 2 : ℝ) ≤ 2 * τ ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow two_pos.le hτ_pos.le]
        exact mul_le_mul_of_nonneg_right
          ((Real.rpow_le_rpow_of_exponent_le one_lt_two.le (by norm_num)).trans_eq (Real.rpow_one 2))
          (by positivity)
      exact hb.trans ((mul_le_mul_of_nonneg_left (h1.trans h2) hC₀_chi_pos.le).trans_eq (by ring))
    have hτ_qtr_half : τ ^ (-(1 / 4 : ℝ)) ≤ τ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hτ1 (by norm_num)
    have hv_half : C_vac * τ ^ (-(1 / 4 : ℝ)) ≤ C_vac * τ ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hτ_qtr_half hCvac_pos.le
    have hv_nn : 0 ≤ C_vac * τ ^ (1 / 2 : ℝ) := by positivity
    have hI_ring :
        C_vac * τ ^ (1 / 2 : ℝ) + C_vac * τ ^ (1 / 2 : ℝ) + 2 * C₀_chi * τ ^ (1 / 2 : ℝ) =
          (2 * C_vac + 2 * C₀_chi) * τ ^ (1 / 2 : ℝ) := by ring
    have hI0_le : ‖smoothAFEZetaDualCoefficientGeneral s x 0‖ ≤
        (2 * C_vac + 2 * C₀_chi) * τ ^ (1 / 2 : ℝ) := by
      have htri : ‖smoothAFEZetaDualCoefficientGeneral s x 0‖ ≤
          ‖smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s‖ + ‖zetaChi s‖ := by
        simpa using norm_sub_le (smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s) (zetaChi s)
      linarith
    have hI20_le : ‖smoothAFEZetaDualCoefficientGeneral s (2 * x) 0‖ ≤
        (2 * C_vac + 2 * C₀_chi) * τ ^ (1 / 2 : ℝ) := by
      have htri : ‖smoothAFEZetaDualCoefficientGeneral s (2 * x) 0‖ ≤
          ‖smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 + zetaChi s‖ + ‖zetaChi s‖ := by
        simpa using norm_sub_le (smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 + zetaChi s) (zetaChi s)
      have hv2_half : C_vac * (2 * τ ^ (-(1 / 4 : ℝ))) ≤ 2 * (C_vac * τ ^ (1 / 2 : ℝ)) := by
        linarith
      linarith
    have hY_m4 : Y⁻¹ ≤ τ ^ (-4 : ℝ) := by
      dsimp only [Y]
      rw [← Real.rpow_neg hτ_pos.le]
      exact Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
    have hW1_sub : ‖smoothAFECutoff (1 / Y) - 1‖ ≤ K₁_sub * τ ^ (-4 : ℝ) := by
      have h : ‖smoothAFECutoff (1 / Y) - 1‖ ≤ K₁_sub * Y⁻¹ :=
        (hK₁_sub (div_pos one_pos hY_pos)).trans_eq (by rw [Real.rpow_one, one_div])
      exact h.trans (mul_le_mul_of_nonneg_left hY_m4 hK₁_sub0)
    have hW2_sub : ‖smoothAFECutoff (2 / Y) - 1‖ ≤ 2 * K₁_sub * τ ^ (-4 : ℝ) := by
      have h : ‖smoothAFECutoff (2 / Y) - 1‖ ≤ K₁_sub * (2 * Y⁻¹) :=
        (hK₁_sub (div_pos two_pos hY_pos)).trans_eq (by rw [Real.rpow_one, div_eq_mul_inv])
      exact h.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY_m4 zero_le_two) hK₁_sub0).trans_eq (by ring))
    have hτ_prod : τ ^ (-4 : ℝ) * τ ^ (1 / 2 : ℝ) ≤ τ ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hτ_pos]
      exact Real.rpow_le_rpow_of_exponent_le hτ1 (by norm_num)
    have hp_w1 : ‖(smoothAFECutoff (1 / Y) - 1) * smoothAFEZetaDualCoefficientGeneral s x 0‖ ≤
        K₁_sub * (2 * C_vac + 2 * C₀_chi) * τ ^ (-(1 / 4 : ℝ)) := by
      rw [norm_mul]
      calc ‖smoothAFECutoff (1 / Y) - 1‖ * ‖smoothAFEZetaDualCoefficientGeneral s x 0‖
          ≤ (K₁_sub * τ ^ (-4 : ℝ)) * ((2 * C_vac + 2 * C₀_chi) * τ ^ (1 / 2 : ℝ)) :=
            mul_le_mul hW1_sub hI0_le (norm_nonneg _) (by positivity)
        _ = K₁_sub * (2 * C_vac + 2 * C₀_chi) * (τ ^ (-4 : ℝ) * τ ^ (1 / 2 : ℝ)) := by ring
        _ ≤ K₁_sub * (2 * C_vac + 2 * C₀_chi) * τ ^ (-(1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hτ_prod (by positivity)
    have hp_w2 : ‖(smoothAFECutoff (2 / Y) - 1) * smoothAFEZetaDualCoefficientGeneral s (2 * x) 0‖ ≤
        2 * K₁_sub * (2 * C_vac + 2 * C₀_chi) * τ ^ (-(1 / 4 : ℝ)) := by
      rw [norm_mul]
      calc ‖smoothAFECutoff (2 / Y) - 1‖ * ‖smoothAFEZetaDualCoefficientGeneral s (2 * x) 0‖
          ≤ (2 * K₁_sub * τ ^ (-4 : ℝ)) * ((2 * C_vac + 2 * C₀_chi) * τ ^ (1 / 2 : ℝ)) :=
            mul_le_mul hW2_sub hI20_le (norm_nonneg _) (by positivity)
        _ = 2 * K₁_sub * (2 * C_vac + 2 * C₀_chi) * (τ ^ (-4 : ℝ) * τ ^ (1 / 2 : ℝ)) := by ring
        _ ≤ 2 * K₁_sub * (2 * C_vac + 2 * C₀_chi) * τ ^ (-(1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hτ_prod (by positivity)
    dsimp only [E_vac, C_vac_tot]
    have ht1 := norm_add_le
      (-((smoothAFECutoff (1 / Y) - 1) * smoothAFEZetaDualCoefficientGeneral s x 0 +
        (smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s)))
      ((2 : ℂ) ^ (-(1 - s)) *
        ((smoothAFECutoff (2 / Y) - 1) * smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 +
          (smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 + zetaChi s)))
    rw [norm_neg, norm_mul] at ht1
    have ht2 := norm_add_le
      ((smoothAFECutoff (1 / Y) - 1) * smoothAFEZetaDualCoefficientGeneral s x 0)
      (smoothAFEZetaDualCoefficientGeneral s x 0 + zetaChi s)
    have ht3 := norm_add_le
      ((smoothAFECutoff (2 / Y) - 1) * smoothAFEZetaDualCoefficientGeneral s (2 * x) 0)
      (smoothAFEZetaDualCoefficientGeneral s (2 * x) 0 + zetaChi s)
    have hm2 := (mul_le_of_le_one_left (norm_nonneg _) h2_le1).trans ht3
    have hvac_ring :
        (K₁_sub * (2 * C_vac + 2 * C₀_chi) * τ ^ (-(1 / 4 : ℝ)) + C_vac * τ ^ (-(1 / 4 : ℝ))) +
          (2 * K₁_sub * (2 * C_vac + 2 * C₀_chi) * τ ^ (-(1 / 4 : ℝ)) + C_vac * (2 * τ ^ (-(1 / 4 : ℝ)))) =
        (3 * C_vac + 3 * K₁_sub * (2 * C_vac + 2 * C₀_chi)) * τ ^ (-(1 / 4 : ℝ)) := by ring
    linarith
  have hdu_bd : ‖E_du‖ ≤ C_tail * τ ^ (-(1 / 4 : ℝ)) := hCtail hlo hhi him
  have ht1 := norm_sub_le (E_vaug + E_vac) E_du
  have ht2 := norm_add_le E_vaug E_vac
  have hnn : 0 ≤ τ ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hτ_pos.le _
  have hdu_ring :
      2 * C_ann * τ ^ (-(1 / 4 : ℝ)) + C_vac_tot * τ ^ (-(1 / 4 : ℝ)) +
        C_tail * τ ^ (-(1 / 4 : ℝ)) ≤ C_du * τ ^ (-(1 / 4 : ℝ)) := by
    dsimp only [C_du]
    have h1 :
        2 * C_ann * τ ^ (-(1 / 4 : ℝ)) + C_vac_tot * τ ^ (-(1 / 4 : ℝ)) +
          C_tail * τ ^ (-(1 / 4 : ℝ)) + τ ^ (-(1 / 4 : ℝ)) =
        (2 * C_ann + C_vac_tot + C_tail + 1) * τ ^ (-(1 / 4 : ℝ)) := by ring
    linarith
  linarith

/-- **Pointwise `HasStrictPrimeGasWitness` production from pure Vaughan Type-II domination on `Ω_open`:**
whenever `smoothOuterVaughanTypeII U V s (|Im s|^{-(1 + η)}) (|Im s|^{3 + η})` falls strictly below
`(1 / 4) * (|Im s| / 7)^{1/2 - Re s} - C_du * |Im s|^{-1 / 4}`, `ζ(s) ≠ 0`, yielding an explicit
`HasStrictPrimeGasWitness` at `s`. Conversely, at any zero `ζ(s) = 0` in `Ω_open`, the pure
Vaughan Type-II sum alone is forced strictly above `(1 / 4) * (|Im s| / 7)^{1/2 - Re s} - C_du * |Im s|^{-1 / 4}`
with zero Vaughan Type-I contribution. -/
theorem strict_primeGas_witness_of_pure_vaughanTypeII_domination_on_remaining_strip
    {η C_du : ℝ}
    (hduality : ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
      let x : ℝ := |s.im| ^ (-(1 + η))
      let Y : ℝ := |s.im| ^ (3 + η)
      ∀ {U V : ℕ}, 1 ≤ U → 1 ≤ V → ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2) →
        ‖riemannZeta s * smoothOuterMoebiusSeries Y (1 - s) -
            ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + smoothOuterVaughanTypeII U V s x Y)‖ ≤
          C_du * |s.im| ^ (-(1 / 4 : ℝ)))
    {s : ℂ} (hlo : 3001 / 24000 ≤ s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|)
    {U V : ℕ} (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hUV_bd : ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2)) :
    (riemannZeta s = 0 →
      (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_du * |s.im| ^ (-(1 / 4 : ℝ)) <
        ‖smoothOuterVaughanTypeII U V s (|s.im| ^ (-(1 + η))) (|s.im| ^ (3 + η))‖) ∧
    (∀ {L_hor : ℝ}, 0 < L_hor →
      ‖smoothOuterVaughanTypeII U V s (|s.im| ^ (-(1 + η))) (|s.im| ^ (3 + η))‖ ≤
        (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_du * |s.im| ^ (-(1 / 4 : ℝ)) →
      HasStrictPrimeGasWitness s (by linarith) L_hor) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  have hpref := one_quarter_lt_norm_one_sub_two_cpow_neg_one_sub hhi
  obtain ⟨_, _, hchi_ge⟩ := norm_zetaChi_ge_rpow_above_oneHundredEightyFour hs0 hhi him
  have hchi_pos : 0 < ‖zetaChi s‖ := lt_of_lt_of_le (by positivity) hchi_ge
  have hvac_gt : (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) <
      ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s‖ := by
    rw [norm_mul]
    calc (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re)
        ≤ (1 / 4 : ℝ) * ‖zetaChi s‖ := mul_le_mul_of_nonneg_left hchi_ge (by norm_num)
      _ < ‖1 - (2 : ℂ) ^ (-(1 - s))‖ * ‖zetaChi s‖ := mul_lt_mul_of_pos_right hpref hchi_pos
  have hforced : riemannZeta s = 0 →
      (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_du * |s.im| ^ (-(1 / 4 : ℝ)) <
        ‖smoothOuterVaughanTypeII U V s (|s.im| ^ (-(1 + η))) (|s.im| ^ (3 + η))‖ := by
    intro hζ0
    have herr := hduality s hlo hhi him hU1 hV1 hUV_bd
    rw [hζ0, zero_mul, zero_sub, norm_neg] at herr
    have htri :
        ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s‖ -
          ‖smoothOuterVaughanTypeII U V s (|s.im| ^ (-(1 + η))) (|s.im| ^ (3 + η))‖ ≤
        ‖(1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s +
          smoothOuterVaughanTypeII U V s (|s.im| ^ (-(1 + η))) (|s.im| ^ (3 + η))‖ := by
      have h := norm_sub_norm_le ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s)
        (-smoothOuterVaughanTypeII U V s (|s.im| ^ (-(1 + η))) (|s.im| ^ (3 + η)))
      rwa [sub_neg_eq_add, norm_neg] at h
    linarith
  refine ⟨hforced, fun {L_hor} hL_hor hdom => ?_⟩
  refine (hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 hs1 hL_hor).mpr fun hζ0 => ?_
  linarith [hforced hζ0]

end Part4PureVaughanTypeIIDuality

#print axioms exists_norm_smoothAFECutoff_uniform_le
#print axioms exists_rpow_mul_exp_neg_quarter_sq_le
#print axioms tsum_smoothAFECutoff_eq_zeta_add_residue_add_mellinAt_neg
#print axioms exists_norm_riemannZeta_one_sub_even_le
#print axioms norm_smoothOuterSieveCoeff_le_rpow_of_three_le
#print axioms smoothOuter_poleCleared_reflected_moebius_crossHeight_eq
#print axioms smoothOuterMoebiusDirect_eq_vaughan_decomposition
#print axioms exists_smoothOuter_vaughanTypeI_and_head_annihilation_on_remaining_strip
#print axioms exists_pure_vaughanTypeII_crossHeight_duality_on_remaining_strip
#print axioms strict_primeGas_witness_of_pure_vaughanTypeII_domination_on_remaining_strip

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end

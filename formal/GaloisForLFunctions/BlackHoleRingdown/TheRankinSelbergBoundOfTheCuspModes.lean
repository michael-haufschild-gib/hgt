import GaloisForLFunctions.BlackHoleRingdown.TheEulerProductOfTheCuspModes

/-!
# The Rankin–Selberg bound for the cusp modes

The Whittaker coefficients of a cusp form of the modular horizon are of size `1` on average
(`mean_square_le`): `Σ_{0 < |n| ≤ N} |ρ(n)|² ≤ A N log N`. Consequently `Σ_n |ρ(n)|² |n|^{-σ}` converges for every
`σ > 1` (`summable_sq`), the L-series `Σ ρ(n)|n|^{-s}` converges absolutely on `Re s > 1` (`summable_abs`), and for
Hecke eigenforms the Euler product holds on the whole half plane `Re s > 1` (`cusp_euler_product_one`).

**Mechanism.** The horocycle mass `m(y) = ∫_{-1/2}^{1/2} |g(x+iy)|² dx = Σ_n |ρ(n)|² y |K_ν(2π|n|y)|²` is
bounded by `sup|g|²` and decays like `y e^{-4πy}`. Its Mellin transform at `σ ∈ (1, 2]` is therefore at most
`sup|g|²/(σ-1) + ∫_1^∞ m`. By Tonelli it is the sum of the modal transforms, and each modal transform is at least
`|ρ(n)|² κ₀ X^σ (2π|n|)^{-σ}`, from the window `2π|n|y ∈ [X, 2X]` where `|K_ν|² ≥ κ₀ > 0`. Hence
`Σ |ρ(n)|² |n|^{-σ} ≤ A/(σ-1)`, and `σ = 1 + 1/log N` gives the mean square.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane ENNReal

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  GaloisForLFunctions.RHTower.Gamma0MaassHecke
open GaloisForLFunctions.HTGeometry (modifiedBesselKOrder eventually_re_modifiedBesselKOrder_pos)
open UpperHalfPlane (ofComplex)

namespace CuspRS

open HeckeCusp CuspL WeylUpper

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-- A window `[X, 2X]` with `X ≥ 1` on which `|K_ν|² ≥ κ₀ > 0`. -/
theorem exists_window (ν : ℂ) :
    ∃ X κ₀ : ℝ, 1 ≤ X ∧ 0 < κ₀ ∧ ∀ x ∈ Icc X (2 * X), κ₀ ≤ ‖modifiedBesselKOrder x ν‖ ^ 2 := by
  obtain ⟨X, hX1, hXpos⟩ := eventually_re_modifiedBesselKOrder_pos ν
  have hcont : ContinuousOn (fun x : ℝ => ‖modifiedBesselKOrder x ν‖ ^ 2) (Icc X (2 * X)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by linarith) hx.1
    exact ((MaassWhittaker.hasDerivAt_besK ν hx0).continuousAt.norm.pow 2).continuousWithinAt
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 (by linarith : X ≤ 2 * X)) hcont
  have hpos : 0 < ‖modifiedBesselKOrder x₀ ν‖ ^ 2 :=
    pow_pos (lt_of_lt_of_le (hXpos x₀ hx₀.1) (Complex.re_le_norm _)) 2
  exact ⟨X, _, hX1, hpos, fun x hx => hmin hx⟩

/-- The horocycle mass decays like `y e^{-4πy}`. -/
theorem slice_le_decay (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ D, 0 ≤ D ∧ ∀ y, 1 ≤ y → slice g y ≤ D * (y * Real.exp (-(4 * Real.pi) * y)) := by
  obtain ⟨b, hbs, hb0, hmode⟩ := CuspL.norm_mode_le hg hρ0 hρ
  set B := ∑' n, b n
  have hbB : ∀ n, b n ≤ B := fun n => hbs.le_tsum n fun m _ => hb0 m
  refine ⟨B * B, mul_nonneg (tsum_nonneg hb0) (tsum_nonneg hb0), fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hE : (Real.sqrt y * Real.exp (-(2 * Real.pi * y))) ^ 2 = y * Real.exp (-(4 * Real.pi) * y) := by
    rw [mul_pow, Real.sq_sqrt hy0.le, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hterm : ∀ n, ‖fourierCoeff g n y‖ ^ 2 ≤ B * b n * (y * Real.exp (-(4 * Real.pi) * y)) := by
    intro n
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hmode n y hy) 2
    rw [mul_pow, hE] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hbB n) (hb0 n) |>.trans_eq (by ring)
  rw [← (hasSum_slice hg hy0).tsum_eq]
  calc ∑' n, ‖fourierCoeff g n y‖ ^ 2 ≤ ∑' n, B * b n * (y * Real.exp (-(4 * Real.pi) * y)) :=
        (hasSum_slice hg hy0).summable.tsum_le_tsum hterm ((hbs.mul_left B).mul_right _)
    _ = B * B * (y * Real.exp (-(4 * Real.pi) * y)) := by
        rw [tsum_mul_right, tsum_mul_left]

/-- The Mellin transform of the horocycle mass at `σ ∈ (1, 2]` is at most `C²/(σ - 1) + T`. -/
theorem lintegral_slice_le (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ C T : ℝ, 0 ≤ C ∧ 0 ≤ T ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (slice g y * y ^ (σ - 2)) ≤
        ENNReal.ofReal (C / (σ - 1) + T) := by
  obtain ⟨Cg, hCg⟩ := exists_bound hg
  obtain ⟨D, hD0, hD⟩ := slice_le_decay hg hρ0 hρ
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg UpperHalfPlane.I)
  have hint : IntegrableOn (fun y : ℝ => D * Real.exp (-(4 * Real.pi - 1) * y)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 (by nlinarith [Real.pi_gt_three])).const_mul D
  set T := ∫ y in Ioi (1 : ℝ), D * Real.exp (-(4 * Real.pi - 1) * y)
  have hT0 : 0 ≤ T := setIntegral_nonneg measurableSet_Ioi fun y _ => by positivity
  refine ⟨Cg ^ 2, T, sq_nonneg _, hT0, fun σ hσ1 hσ2 => ?_⟩
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  rw [ENNReal.ofReal_add (div_nonneg (sq_nonneg _) (by linarith)) hT0]
  gcongr
  · -- the bounded part
    have hr : -1 < σ - 2 := by linarith
    have hii : IntegrableOn (fun y : ℝ => Cg ^ 2 * y ^ (σ - 2)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' hr)).const_mul _
    have hval : ∫ y in Ioc (0 : ℝ) 1, Cg ^ 2 * y ^ (σ - 2) = Cg ^ 2 / (σ - 1) := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr),
        Real.one_rpow, Real.zero_rpow (by linarith)]
      rw [show σ - 2 + 1 = σ - 1 by ring]
      ring
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hii
      ((ae_restrict_mem measurableSet_Ioc).mono fun y hy =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hy.1.le _))]
    refine setLIntegral_mono_ae (hii.aemeasurable.ennreal_ofReal) ?_
    filter_upwards with y hy
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy.1.le _))
    exact (slice_le hCg y)
  · -- the cusp part
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => by positivity)]
    refine setLIntegral_mono_ae (hint.aemeasurable.ennreal_ofReal) ?_
    filter_upwards with y hy
    have hy1 : 1 ≤ y := le_of_lt hy
    refine ENNReal.ofReal_le_ofReal ?_
    have hsl : 0 ≤ slice g y := slice_nonneg y
    have hpow : y ^ (σ - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
    have hye : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    calc slice g y * y ^ (σ - 2) ≤ slice g y := mul_le_of_le_one_right hsl hpow
      _ ≤ D * (y * Real.exp (-(4 * Real.pi) * y)) := hD y hy1
      _ ≤ D * (Real.exp y * Real.exp (-(4 * Real.pi) * y)) := by gcongr
      _ = D * Real.exp (-(4 * Real.pi - 1) * y) := by rw [← Real.exp_add]; congr 2; ring

/-- Each mode contributes at least `|ρ(n)|² κ₀ X^σ (2π|n|)^{-σ}` to the Mellin transform at `σ ≥ 1`. -/
theorem lintegral_mode_ge (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE))
    {X κ₀ : ℝ} (hX : 1 ≤ X) (hκ : ∀ x ∈ Icc X (2 * X), κ₀ ≤ ‖modifiedBesselKOrder x (nu lamE)‖ ^ 2)
    (hκ0 : 0 ≤ κ₀) {σ : ℝ} (hσ : 1 ≤ σ) {n : ℤ} (hn : n ≠ 0) :
    ENNReal.ofReal (‖ρ n‖ ^ 2 * κ₀ * X ^ σ * (2 * Real.pi * |(n : ℝ)|) ^ (-σ)) ≤
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (‖fourierCoeff g n y‖ ^ 2 * y ^ (σ - 2)) := by
  set c := 2 * Real.pi * |(n : ℝ)|
  have hc : 0 < c := by have := abs_pos.2 (Int.cast_ne_zero.2 hn : (n : ℝ) ≠ 0); positivity
  have hX0 : 0 < X := by linarith
  have hsub : Icc (X / c) (2 * X / c) ⊆ Ioi 0 := fun y hy => lt_of_lt_of_le (by positivity) hy.1
  refine le_trans ?_ (lintegral_mono_set hsub)
  have hlow : ∀ y ∈ Icc (X / c) (2 * X / c),
      ‖ρ n‖ ^ 2 * (X / c) ^ (σ - 1) * κ₀ ≤ ‖fourierCoeff g n y‖ ^ 2 * y ^ (σ - 2) := by
    intro y hy
    have hy0 : 0 < y := hsub hy
    rw [hρ n y hy0, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt hy0.le]
    have hcy : c * y ∈ Icc X (2 * X) := by
      constructor
      · have := hy.1; rw [div_le_iff₀ hc] at this; linarith
      · have := hy.2; rw [le_div_iff₀ hc] at this; linarith
    have hK := hκ (c * y) hcy
    have hyp : (X / c) ^ (σ - 1) ≤ y ^ (σ - 1) := Real.rpow_le_rpow (by positivity) hy.1 (by linarith)
    have hyy : y * y ^ (σ - 2) = y ^ (σ - 1) := by
      rw [show σ - 1 = 1 + (σ - 2) by ring, Real.rpow_add hy0, Real.rpow_one]
    calc ‖ρ n‖ ^ 2 * (X / c) ^ (σ - 1) * κ₀ ≤ ‖ρ n‖ ^ 2 * y ^ (σ - 1) *
          ‖modifiedBesselKOrder (c * y) (nu lamE)‖ ^ 2 := by
          gcongr
      _ = ‖ρ n‖ ^ 2 * y * ‖modifiedBesselKOrder (c * y) (nu lamE)‖ ^ 2 * y ^ (σ - 2) := by
          rw [← hyy]; ring
  calc ENNReal.ofReal (‖ρ n‖ ^ 2 * κ₀ * X ^ σ * c ^ (-σ))
      = ∫⁻ y in Icc (X / c) (2 * X / c), ENNReal.ofReal (‖ρ n‖ ^ 2 * (X / c) ^ (σ - 1) * κ₀) := by
        rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show 2 * X / c - X / c = X / c by ring]
        have hcs : 0 < c ^ σ := Real.rpow_pos_of_pos hc σ
        have hXs : 0 < X ^ σ := Real.rpow_pos_of_pos hX0 σ
        rw [Real.div_rpow hX0.le hc.le, Real.rpow_neg hc.le, Real.rpow_sub hX0, Real.rpow_sub hc,
          Real.rpow_one, Real.rpow_one]
        field_simp
    _ ≤ ∫⁻ y in Icc (X / c) (2 * X / c), ENNReal.ofReal (‖fourierCoeff g n y‖ ^ 2 * y ^ (σ - 2)) :=
        lintegral_mono_ae ((ae_restrict_mem measurableSet_Icc).mono fun y hy =>
          ENNReal.ofReal_le_ofReal (hlow y hy))

/-- **The Rankin–Selberg series converges for `σ > 1`, with a pole of order at most one at `σ = 1`.** -/
theorem summable_sq (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      Summable (fun n : ℤ => ‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-σ)) ∧
        ∑' n : ℤ, ‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-σ) ≤ A / (σ - 1) := by
  obtain ⟨X, κ₀, hX1, hκ0, hκ⟩ := exists_window (nu lamE)
  obtain ⟨C, T, hC0, hT0, hL⟩ := lintegral_slice_le hg hρ0 hρ
  have hX0 : 0 < X := by linarith
  set K₂ : ℝ := κ₀ * X * (2 * Real.pi) ^ (-(2 : ℝ))
  have hK₂ : 0 < K₂ := by positivity
  refine ⟨(C + T) / K₂, by positivity, fun σ hσ1 hσ2 => ?_⟩
  set u : ℤ → ℝ := fun n => ‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-σ)
  have hu0 : ∀ n, 0 ≤ u n := fun n => by positivity
  set K₁ : ℝ := κ₀ * X ^ σ * (2 * Real.pi) ^ (-σ)
  have hK₁ : 0 < K₁ := by positivity
  -- the modal lower bounds, summed by Tonelli
  have hmode : ∀ n : ℤ, ENNReal.ofReal (K₁ * u n) ≤
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (‖fourierCoeff g n y‖ ^ 2 * y ^ (σ - 2)) := by
    intro n
    by_cases hn : n = 0
    · simp [u, hn, hρ0]
    refine le_trans (le_of_eq ?_) (lintegral_mode_ge hρ hX1 hκ hκ0.le hσ1.le hn)
    congr 1
    have hn0 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
    simp only [K₁, u]
    rw [Real.mul_rpow (by positivity) hn0.le]
    ring
  have hton : ∑' n : ℤ, ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (‖fourierCoeff g n y‖ ^ 2 * y ^ (σ - 2)) =
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (slice g y * y ^ (σ - 2)) := by
    rw [← lintegral_tsum]
    · refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      have hy0 : 0 < y := hy
      have hs := (hasSum_slice hg hy0).mul_right (y ^ (σ - 2))
      rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable]
    · intro n
      have hcont : ContinuousOn (fun y => ‖fourierCoeff g n y‖ ^ 2 * y ^ (σ - 2)) (Ioi 0) :=
        (((modalSol_fourierCoeff hg n).continuousOn.1).norm.pow 2).mul
          (fun y hy => (Real.continuousAt_rpow_const y _ (Or.inl (ne_of_gt hy))).continuousWithinAt)
      exact (hcont.aemeasurable measurableSet_Ioi).ennreal_ofReal
  have hbound : ENNReal.ofReal K₁ * ∑' n, ENNReal.ofReal (u n) ≤ ENNReal.ofReal (C / (σ - 1) + T) := by
    rw [← ENNReal.tsum_mul_left]
    refine le_trans (ENNReal.tsum_le_tsum fun n => ?_) (le_trans (le_of_eq hton) (hL σ hσ1 hσ2))
    rw [← ENNReal.ofReal_mul hK₁.le]
    exact hmode n
  have hfin : ∑' n, ENNReal.ofReal (u n) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simpa using hK₁)] at hbound
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hbound)
  have hsum : Summable u := by
    have := ENNReal.summable_toReal hfin
    exact this.congr fun n => ENNReal.toReal_ofReal (hu0 n)
  refine ⟨hsum, ?_⟩
  -- the real bound
  have hreal : K₁ * ∑' n, u n ≤ C / (σ - 1) + T := by
    have h := hbound
    rw [← ENNReal.ofReal_tsum_of_nonneg hu0 hsum, ← ENNReal.ofReal_mul hK₁.le] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  have hK12 : K₂ ≤ K₁ := by
    have h1 : X ≤ X ^ σ := by
      calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        _ ≤ X ^ σ := Real.rpow_le_rpow_of_exponent_le hX1 hσ1.le
    have h2 : (2 * Real.pi) ^ (-(2 : ℝ)) ≤ (2 * Real.pi) ^ (-σ) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [Real.pi_gt_three]) (by linarith)
    simp only [K₁, K₂]
    have : κ₀ * X ≤ κ₀ * X ^ σ := mul_le_mul_of_nonneg_left h1 hκ0.le
    calc κ₀ * X * (2 * Real.pi) ^ (-(2 : ℝ)) ≤ κ₀ * X ^ σ * (2 * Real.pi) ^ (-(2 : ℝ)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ κ₀ * X ^ σ * (2 * Real.pi) ^ (-σ) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hS0 : 0 ≤ ∑' n, u n := tsum_nonneg hu0
  have hσ0 : 0 < σ - 1 := by linarith
  have hT' : T ≤ T / (σ - 1) := by
    rw [le_div_iff₀ hσ0]; nlinarith
  calc ∑' n, u n ≤ (C / (σ - 1) + T) / K₂ := by
        rw [le_div_iff₀ hK₂]
        calc (∑' n, u n) * K₂ ≤ (∑' n, u n) * K₁ := mul_le_mul_of_nonneg_left hK12 hS0
          _ = K₁ * ∑' n, u n := by ring
          _ ≤ _ := hreal
    _ ≤ (C / (σ - 1) + T / (σ - 1)) / K₂ := by gcongr
    _ = (C + T) / K₂ / (σ - 1) := by field_simp

/-- **The Rankin–Selberg mean square**: `Σ_{|n| ≤ N} |ρ(n)|² ≤ A N log N` for `N ≥ 3`. -/
theorem mean_square_le (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 3 ≤ N →
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖ρ n‖ ^ 2 ≤ A * N * Real.log N := by
  obtain ⟨A, hA0, hA⟩ := summable_sq hg hρ0 hρ
  refine ⟨Real.exp 1 * A, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hN0]
    have : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    exact this.trans_le (by exact_mod_cast hN)
  set σ := 1 + 1 / Real.log N
  have hl0 : 0 < 1 / Real.log N := one_div_pos.2 (by linarith)
  have hl1 : 1 / Real.log N ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hσ1 : 1 < σ := by simp only [σ]; linarith
  have hσ2 : σ ≤ 2 := by simp only [σ]; linarith
  obtain ⟨hs, hb⟩ := hA σ hσ1 hσ2
  have hNσ : (N : ℝ) ^ σ = Real.exp 1 * N := by
    rw [Real.rpow_add hN0, Real.rpow_one, Real.rpow_def_of_pos hN0, mul_one_div,
      div_self (by linarith : Real.log N ≠ 0)]
    ring
  have hterm : ∀ n ∈ Finset.Icc (-(N : ℤ)) N, ‖ρ n‖ ^ 2 ≤ (N : ℝ) ^ σ * (‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-σ)) := by
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0, hρ0]
    have hnN : |(n : ℝ)| ≤ N := by
      have := Finset.mem_Icc.1 hn
      rw [abs_le]; constructor <;> exact_mod_cast (by omega)
    have hn1 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn0)
    have h : 1 ≤ (N : ℝ) ^ σ * |(n : ℝ)| ^ (-σ) := by
      rw [Real.rpow_neg hn1.le, ← div_eq_mul_inv, one_le_div (by positivity)]
      exact Real.rpow_le_rpow hn1.le hnN (by linarith)
    nlinarith [sq_nonneg ‖ρ n‖]
  calc ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖ρ n‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (N : ℝ) ^ σ * (‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-σ)) :=
        Finset.sum_le_sum hterm
    _ = (N : ℝ) ^ σ * ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-σ) := by
        rw [Finset.mul_sum]
    _ ≤ (N : ℝ) ^ σ * ∑' n : ℤ, ‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-σ) :=
        mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ fun n _ => by positivity) (by positivity)
    _ ≤ (N : ℝ) ^ σ * (A / (σ - 1)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = Real.exp 1 * A * N * Real.log N := by
        rw [hNσ, show σ - 1 = 1 / Real.log N by simp only [σ]; ring]
        field_simp

/-- **Absolute convergence on `Re s > 1`**: `Σ_n |ρ(n)| |n|^{-σ} < ∞` for every `σ > 1`. -/
theorem summable_abs (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℤ => ‖ρ n‖ * |(n : ℝ)| ^ (-σ) := by
  obtain ⟨A, -, hA⟩ := summable_sq hg hρ0 hρ
  set σ' := min σ 2
  have h1 : 1 < σ' := lt_min hσ (by norm_num)
  obtain ⟨hs, -⟩ := hA σ' h1 (min_le_right _ _)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hs.add (Real.summable_abs_int_rpow h1)).mul_left (1 / 2))
  by_cases hn : n = 0
  · simp [hn, hρ0]
    exact Real.rpow_nonneg le_rfl _
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hpow : |(n : ℝ)| ^ (-σ) ≤ |(n : ℝ)| ^ (-σ') :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by simp only [σ', neg_le_neg_iff]; exact min_le_left _ _)
  have hamgm : ‖ρ n‖ ≤ (‖ρ n‖ ^ 2 + 1) / 2 := by nlinarith [sq_nonneg (‖ρ n‖ - 1)]
  calc ‖ρ n‖ * |(n : ℝ)| ^ (-σ) ≤ ((‖ρ n‖ ^ 2 + 1) / 2) * |(n : ℝ)| ^ (-σ') :=
        mul_le_mul hamgm hpow (by positivity) (by positivity)
    _ = 1 / 2 * (‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-σ') + |(n : ℝ)| ^ (-σ')) := by ring

/-- **The Euler product on the half plane `Re s > 1`.** -/
theorem cusp_euler_product_one (hg : g ∈ cuspSpace lamE) (c : ℕ → ℂ)
    (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    lSeries ρ s = (ρ 1 + ρ (-1)) *
      ∏' p : Nat.Primes, (1 - CuspEuler.heckeLam c p * (p : ℂ) ^ (-s) + ((p : ℂ) ^ (-s)) ^ 2)⁻¹ :=
  CuspEuler.cusp_euler_product_of_summable hg c hc hρ0 hρ (summable_abs hg hρ0 hρ hs)

end CuspRS

end GaloisForLFunctions.BlackHoleRingdown

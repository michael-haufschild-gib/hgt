import GaloisForLFunctions.RHTower.Sieve.VinogradovZetaGrowth

/-!
# Vinogradov–Korobov growth of `ζ` at every depth `κ` near `σ = 1`

The corpus bound `norm_riemannZeta_le_vinogradovKorobov` holds for `1 − w(L) ≤ σ`, with
`w(L) = L^{−2/3}(log L)^{−2/3}/100` and `L = log τ`.  Here it is extended to every depth
`w(L) ≤ κ = 1 − σ ≤ 1/(3·2^{24})`:

`‖ζ(σ + iτ)‖ ≤ C · L · exp(864 · κ^{3/2} · L log L)`   (`norm_riemannZeta_le_vinogradovKorobov_general`).

The proof follows the corpus proof step for step.
* Middle dyadic blocks: the prefix bound `12e^{20} Y^{1−δ/4} + 200 Y^{1/2}` combines with
  `δ/4 ≥ ℓ²/(746496 L² log² L)` (`ℓ = log Y`) and `κℓ − ℓ³/A ≤ κ^{3/2}√A`, where
  `√A = 864 L log L`.  This gives `12e^{20} e^{864 κ^{3/2} L log L} + 200`
  (`norm_block_le_middle_general`).
* Large blocks: the derivative test saves `Y^{−1/(3·2^{24})}`, which absorbs `Y^κ`
  (`norm_block_le_large_general`).
* Initial segment `k ≤ e^{L^{2/3}}`: `e^{κ(L^{2/3}+1)}(1 + log N₀)`.  Since `κ ≥ w(L)`, this is at most
  `e^{864 κ^{3/2} L log L}` (`exp_initial_le_vkGeneralGrowth`).
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The growth factor `exp(κ^{3/2} · 864 L log L)`. -/
def vkGeneralGrowth (κ L : ℝ) : ℝ := Real.exp (κ * Real.sqrt κ * (864 * L * Real.log L))

/-- The block constant at depth `κ`: `12 e^{20} E + 2761`. -/
def vkGeneralBlockConstant (κ L : ℝ) : ℝ := 12 * Real.exp 20 * vkGeneralGrowth κ L + 2761

/-- The growth constant `8 + 4(12 e^{20} + 2761)`. -/
def vkGeneralGrowthConstant : ℝ := 8 + 4 * (12 * Real.exp 20 + 2761)

theorem sqrt_vkSaving {L : ℝ} (hL0 : 0 < L) (hl : 0 ≤ Real.log L) :
    Real.sqrt (746496 * L ^ 2 * Real.log L ^ 2) = 864 * L * Real.log L := by
  rw [show (746496 : ℝ) * L ^ 2 * Real.log L ^ 2 = (864 * L * Real.log L) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-- At depth `κ ≥ w(L)` the initial segment factor `e^{κ(L^{2/3}+1)}` is at most the growth factor. -/
theorem exp_initial_le_vkGeneralGrowth {L κ : ℝ} (hL : Real.exp 30 ≤ L)
    (hκ : vinogradovKorobovWidth L ≤ κ) :
    Real.exp (κ * (L ^ ((2 : ℝ) / 3) + 1)) ≤ vkGeneralGrowth κ L := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl := one_le_log_of_exp_thirty_le hL
  have hw0 := vinogradovKorobovWidth_pos hL
  have hwle := vinogradovKorobovWidth_le hL
  have hκ0 : 0 ≤ κ := by linarith
  have hcube := vinogradovKorobovWidth_cube hL
  rw [sqrt_vkSaving hL0 (by linarith)] at hcube
  -- `w · L^{2/3} ≤ 1/100`
  have hwL : vinogradovKorobovWidth L * L ^ ((2 : ℝ) / 3) ≤ 1 / 100 := by
    unfold vinogradovKorobovWidth
    have h1 : L ^ (-(2 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hL0]; norm_num
    have h2 : Real.log L ^ (-(2 : ℝ) / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h3 : 0 ≤ Real.log L ^ (-(2 : ℝ) / 3) := by positivity
    calc 1 / 100 * L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(2 : ℝ) / 3) * L ^ ((2 : ℝ) / 3)
        = 1 / 100 * Real.log L ^ (-(2 : ℝ) / 3) * (L ^ (-(2 : ℝ) / 3) * L ^ ((2 : ℝ) / 3)) := by
          ring
      _ ≤ 1 / 100 * 1 * 1 := by rw [h1]; gcongr
      _ = 1 / 100 := by norm_num
  -- `L^{2/3} + 1 ≤ √w · 864 L log L ≤ √κ · 864 L log L`
  have hsw : Real.sqrt (vinogradovKorobovWidth L) * (864 * L * Real.log L) =
      864 / 1000 / vinogradovKorobovWidth L := by
    rw [eq_div_iff hw0.ne', ← hcube]; ring
  have hkey : L ^ ((2 : ℝ) / 3) + 1 ≤ Real.sqrt κ * (864 * L * Real.log L) := by
    have h1 : L ^ ((2 : ℝ) / 3) + 1 ≤ 864 / 1000 / vinogradovKorobovWidth L := by
      rw [le_div_iff₀ hw0]
      have : (1 : ℝ) / (3 * (2 : ℝ) ^ 24) ≤ 1 / 100 := by norm_num
      nlinarith
    have h2 : Real.sqrt (vinogradovKorobovWidth L) ≤ Real.sqrt κ := Real.sqrt_le_sqrt hκ
    have h3 : 0 ≤ 864 * L * Real.log L := by positivity
    calc L ^ ((2 : ℝ) / 3) + 1 ≤ 864 / 1000 / vinogradovKorobovWidth L := h1
      _ = Real.sqrt (vinogradovKorobovWidth L) * (864 * L * Real.log L) := hsw.symm
      _ ≤ Real.sqrt κ * (864 * L * Real.log L) := mul_le_mul_of_nonneg_right h2 h3
  unfold vkGeneralGrowth
  apply Real.exp_le_exp.mpr
  calc κ * (L ^ ((2 : ℝ) / 3) + 1) ≤ κ * (Real.sqrt κ * (864 * L * Real.log L)) :=
        mul_le_mul_of_nonneg_left hkey hκ0
    _ = κ * Real.sqrt κ * (864 * L * Real.log L) := by ring

/-- `log ⌈e^{L^{2/3}}⌉ ≤ L^{2/3} + 1`. -/
theorem log_vkInitialLength_le {τ : ℝ} (hL : Real.exp 30 ≤ Real.log τ) :
    Real.log (⌈Real.exp (Real.log τ ^ ((2 : ℝ) / 3))⌉₊ : ℝ) ≤ Real.log τ ^ ((2 : ℝ) / 3) + 1 := by
  set L := Real.log τ with hLdef
  set N₀ : ℕ := ⌈Real.exp (L ^ ((2 : ℝ) / 3))⌉₊
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hN₀low : Real.exp (L ^ ((2 : ℝ) / 3)) ≤ N₀ := Nat.le_ceil _
  have hN₀up : (N₀ : ℝ) < Real.exp (L ^ ((2 : ℝ) / 3)) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hN₀1 : 1 ≤ N₀ := by
    have : (1 : ℝ) ≤ N₀ := le_trans (Real.one_le_exp (by positivity)) hN₀low
    exact_mod_cast this
  have h1 : (N₀ : ℝ) ≤ 2 * Real.exp (L ^ ((2 : ℝ) / 3)) := by
    have : (1 : ℝ) ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := Real.one_le_exp (by positivity)
    linarith
  have h2 := Real.log_le_log (by exact_mod_cast hN₀1) h1
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h2
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  linarith

/-- The initial segment at depth `1 − σ`: `‖Σ_{k ≤ N₀} k^{−σ−iτ}‖ ≤ N₀^{1−σ}(1 + log N₀)`. -/
theorem norm_sum_initial_le_general {σ τ : ℝ} {N₀ : ℕ} (hσ1 : σ ≤ 1) :
    ‖∑ k ∈ Finset.Icc 1 N₀, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      Real.exp ((1 - σ) * Real.log N₀) * (1 + Real.log N₀) := by
  have hterm : ∀ k ∈ Finset.Icc 1 N₀, ‖((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      Real.exp ((1 - σ) * Real.log N₀) * (1 / (k : ℝ)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N₀ := (Finset.mem_Icc.mp hk).2
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hk0]
    have hre : (-((σ : ℂ) + (τ : ℂ) * Complex.I)).re = -σ := by simp
    rw [hre]
    have h2 : (k : ℝ) ^ (-σ) = (k : ℝ) ^ (1 - σ) * (1 / (k : ℝ)) := by
      rw [show -σ = (1 - σ) - 1 by ring, Real.rpow_sub hk0, Real.rpow_one]; ring
    have h3 : (k : ℝ) ^ (1 - σ) ≤ Real.exp ((1 - σ) * Real.log N₀) := by
      rw [Real.rpow_def_of_pos hk0, Real.exp_le_exp]
      have := Real.log_le_log hk0 (by exact_mod_cast hkN : (k : ℝ) ≤ N₀)
      nlinarith
    rw [h2]
    gcongr
  calc ‖∑ k ∈ Finset.Icc 1 N₀, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖
      ≤ ∑ k ∈ Finset.Icc 1 N₀, ‖((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 N₀, Real.exp ((1 - σ) * Real.log N₀) * (1 / (k : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = Real.exp ((1 - σ) * Real.log N₀) * (harmonic N₀ : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        push_cast
        simp [one_div]
    _ ≤ Real.exp ((1 - σ) * Real.log N₀) * (1 + Real.log N₀) := by
        gcongr
        exact harmonic_le_one_add_log N₀

theorem vk_general_final_arith {E L C : ℝ} (hE1 : 1 ≤ E) (hL1 : 1 ≤ L) (hC0 : 0 ≤ C)
    (hC : C = 12 * Real.exp 20 + 2761) :
    E * (2 + L) + (3 * L + 1) * (C * E) + 1 + 4 ≤ vkGeneralGrowthConstant * L * E := by
  rw [vkGeneralGrowthConstant, ← hC]
  have h1 : 1 ≤ L * E := by nlinarith
  have h2 : E ≤ L * E := by nlinarith
  have h3 : C * E ≤ C * (L * E) := mul_le_mul_of_nonneg_left h2 hC0
  nlinarith

/-- **Middle blocks at depth `1 − σ`.** -/
theorem norm_block_le_middle_general {τ σ : ℝ} {Y : ℕ} (hL : Real.exp 30 ≤ Real.log τ)
    (hY : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y) (hYτ : (Y : ℝ) ^ 22 ≤ τ)
    (hσ0' : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖∑ n ∈ Finset.Ico (Y + 1) (2 * Y + 1), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
      12 * Real.exp 20 * vkGeneralGrowth (1 - σ) (Real.log τ) + 200 := by
  set L := Real.log τ with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hlogL := one_le_log_of_exp_thirty_le hL
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hY1 : (1 : ℝ) ≤ Y := by
    have : (1 : ℝ) ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := Real.one_le_exp (by positivity)
    linarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hYτ
  set ℓ := Real.log Y with hℓ
  have hℓlow : L ^ ((2 : ℝ) / 3) ≤ ℓ := by
    rw [hℓ, ← Real.log_exp (L ^ ((2 : ℝ) / 3))]
    exact Real.log_le_log (Real.exp_pos _) hY
  have hℓL : 22 * ℓ ≤ L := by
    have := Real.log_le_log (by positivity) hYτ
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.rpow_pos_of_pos hL0 _) hℓlow
  set R := vinogradovBlockOrder L ℓ with hR
  have hR22 : 22 ≤ R := vinogradovBlockOrder_ge hℓ0 hℓL
  -- hypotheses of the dyadic estimate
  have hY38 : 3 ^ 8 ≤ Y := by
    have h1 : (3 : ℝ) ^ 8 ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := by
      have h30 : (30 : ℝ) ≤ L ^ ((2 : ℝ) / 3) := by
        have h100 := hundred_le_rpow_third hL
        rw [rpow_two_thirds_eq_sq hL0]
        have := mul_le_mul h100 h100 (by norm_num) (by linarith)
        linarith
      calc (3 : ℝ) ^ 8 ≤ Real.exp 30 := by
            have h2 : Real.exp 30 = Real.exp 1 ^ 30 := by rw [← Real.exp_nat_mul]; norm_num
            have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
            have : (2.7 : ℝ) ^ 30 ≤ Real.exp 1 ^ 30 := pow_le_pow_left₀ (by norm_num) he 30
            rw [h2]; norm_num at this ⊢; linarith
        _ ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := Real.exp_le_exp.mpr h30
    have : ((3 ^ 8 : ℕ) : ℝ) ≤ Y := by push_cast; linarith
    exact_mod_cast this
  have hroot : (Y : ℝ) ^ ((1 : ℝ) / 8) ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) / 3 := by
    have h3 : (3 : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 8) := by
      have : ((3 : ℝ) ^ 8) ^ ((1 : ℝ) / 8) ≤ (Y : ℝ) ^ ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hY38) (by norm_num)
      have e : ((3 : ℝ) ^ 8) ^ ((1 : ℝ) / 8) = 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith
    have e : (Y : ℝ) ^ ((1 : ℝ) / 4) = (Y : ℝ) ^ ((1 : ℝ) / 8) * (Y : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_add hY0]; norm_num
    rw [e, le_div_iff₀ (by norm_num)]
    have : 0 ≤ (Y : ℝ) ^ ((1 : ℝ) / 8) := by positivity
    nlinarith
  have htR : τ ≤ ((Y : ℝ) ^ ((1 : ℝ) / 4) / 3) ^ (4 * R) := by
    calc τ = Real.exp L := (Real.exp_log hτ0).symm
      _ ≤ Real.exp (R / 2 * ℓ) := by
          apply Real.exp_le_exp.mpr
          have := two_mul_div_le_vinogradovBlockOrder L ℓ
          rw [← hR] at this
          rw [div_le_iff₀ hℓ0] at this
          linarith
      _ = ((Y : ℝ) ^ ((1 : ℝ) / 8)) ^ (4 * R) := by
          rw [hℓ, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le, Real.rpow_def_of_pos hY0]
          congr 1; push_cast; ring
      _ ≤ ((Y : ℝ) ^ ((1 : ℝ) / 4) / 3) ^ (4 * R) :=
          pow_le_pow_left₀ (by positivity) hroot _
  have hthr : (vinogradovWeylThreshold R : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) / 3 := by
    have h1 := vinogradovWeylThreshold_le_pow R (by omega)
    have hRL : (R : ℝ) ≤ 3 * L ^ ((1 : ℝ) / 3) := by
      have h := vinogradovBlockOrder_le hℓ0 hℓL
      rw [← hR] at h
      calc (R : ℝ) ≤ 3 * L / ℓ := h
        _ ≤ 3 * L / L ^ ((2 : ℝ) / 3) := by
            apply div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hL0 _) hℓlow
        _ = 3 * L ^ ((1 : ℝ) / 3) := by
            rw [mul_div_assoc]
            congr 1
            rw [div_eq_iff (Real.rpow_pos_of_pos hL0 _).ne', ← Real.rpow_add hL0]
            norm_num
    have hR18 : ((2 ^ 54 * R ^ 18 : ℕ) : ℝ) ≤ 2 ^ 54 * (3 * L ^ ((1 : ℝ) / 3)) ^ 18 := by
      have e : ((2 ^ 54 * R ^ 18 : ℕ) : ℝ) = (2 : ℝ) ^ 54 * (R : ℝ) ^ 18 := by push_cast; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hRL 18)
        (by positivity)
    have hpoly : (2 : ℝ) ^ 54 * (3 * L ^ ((1 : ℝ) / 3)) ^ 18 * 3 ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) := by
      -- `log` of the left side is at most `L^{2/3}/4 ≤ ℓ/4`
      have hlhs : 0 < (2 : ℝ) ^ 54 * (3 * L ^ ((1 : ℝ) / 3)) ^ 18 * 3 := by positivity
      rw [← Real.exp_log hlhs, ← Real.exp_log (Real.rpow_pos_of_pos hY0 _),
        Real.exp_le_exp, Real.log_rpow hY0, ← hℓ]
      rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) (by positivity),
        Real.log_rpow hL0]
      have hl3 : Real.log 3 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.add_one_le_exp (2 : ℝ); linarith
      have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      have hlogL3 : Real.log L ≤ 3 * L ^ ((1 : ℝ) / 3) := by
        have h := Real.log_le_rpow_div (x := L) (ε := 1 / 3) hL0.le (by norm_num)
        linarith
      have hL13 := hundred_le_rpow_third hL
      set u := L ^ ((1 : ℝ) / 3) with hu
      have hℓu : u * u ≤ ℓ := by rw [← rpow_two_thirds_eq_sq hL0]; exact hℓlow
      have huu : 100 * u ≤ u * u := mul_le_mul_of_nonneg_right hL13 (by linarith)
      push_cast
      linarith [hl2, hl3, hlogL3, hℓu, huu, hL13]
    calc (vinogradovWeylThreshold R : ℝ) ≤ ((2 ^ 54 * R ^ 18 : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ 2 ^ 54 * (3 * L ^ ((1 : ℝ) / 3)) ^ 18 := hR18
      _ ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) / 3 := by rw [le_div_iff₀ (by norm_num)]; exact hpoly
  -- the prefix bound
  set δ := vinogradovDyadicSaving R with hδ
  set Pb : ℝ := 12 * Real.exp 20 * Y * (Y : ℝ) ^ (-(δ / 4)) + 200 * (Y : ℝ) ^ ((1 : ℝ) / 2)
    with hPb
  have hprefix : ∀ m, Y + 1 ≤ m → m ≤ 2 * Y + 1 →
      ‖∑ n ∈ Finset.Ico (Y + 1) m, (n : ℂ) ^ (-(Complex.I * (τ : ℂ)))‖ ≤ Pb := by
    intro m hm1 hm2
    rw [norm_sum_Ico_cpow_eq hm1]
    have h := norm_sum_logPhase_le_dyadic (N := Y) (A := Y) (L := m - 1 - Y) hR22 hY38 hYτ htR hthr
      le_rfl (by omega)
    refine h.trans ?_
    have hLm : ((m - 1 - Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast (by omega : m - 1 - Y ≤ Y)
    have : (0 : ℝ) ≤ 12 * Real.exp 20 * (Y : ℝ) ^ (-(δ / 4)) := by positivity
    rw [hPb]
    nlinarith
  have hσ0 : 0 ≤ σ := by linarith
  have hsig := dirichlet_block_sigma_bound hσ0 τ (Y + 1) (2 * Y + 1) (by omega) (by omega) Pb
    hprefix
  refine hsig.trans ?_
  have hYσ : ((Y + 1 : ℕ) : ℝ) ^ (-σ) ≤ (Y : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hY0 (by push_cast; linarith) (by linarith)
  have hexp : (Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-σ) ≤ vkGeneralGrowth (1 - σ) L := by
    have e : (Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-σ) = Real.exp (ℓ * (1 - σ - δ / 4)) := by
      have e1 : (Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-σ) =
          (Y : ℝ) ^ (1 + -(δ / 4) + -σ) := by
        rw [Real.rpow_add hY0, Real.rpow_add hY0, Real.rpow_one]
      rw [e1, Real.rpow_def_of_pos hY0, hℓ]
      congr 1
      ring
    rw [e, vkGeneralGrowth]
    apply Real.exp_le_exp.mpr
    have hδl := vinogradovDyadicSaving_div_four_ge hL hℓlow hℓL
    rw [← hR, ← hδ] at hδl
    have hA : (0 : ℝ) < 746496 * L ^ 2 * Real.log L ^ 2 := by positivity
    have hcube := mul_sub_cube_div_le (θ := 1 - σ) (by linarith) hℓ0.le hA
    rw [sqrt_vkSaving hL0 (by linarith)] at hcube
    have h2 : ℓ ^ 3 / (746496 * L ^ 2 * Real.log L ^ 2) ≤ ℓ * (δ / 4) := by
      have : ℓ ^ 3 / (746496 * L ^ 2 * Real.log L ^ 2) =
          ℓ * (ℓ ^ 2 / (746496 * L ^ 2 * Real.log L ^ 2)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hδl hℓ0.le
    nlinarith
  have hhalf : (Y : ℝ) ^ ((1 : ℝ) / 2) * (Y : ℝ) ^ (-σ) ≤ 1 := by
    rw [← Real.rpow_add hY0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
  have hPb0 : 0 ≤ Pb := by rw [hPb]; positivity
  calc Pb * ((Y + 1 : ℕ) : ℝ) ^ (-σ) ≤ Pb * (Y : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_left hYσ hPb0
    _ = 12 * Real.exp 20 * ((Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-σ)) +
        200 * ((Y : ℝ) ^ ((1 : ℝ) / 2) * (Y : ℝ) ^ (-σ)) := by rw [hPb]; ring
    _ ≤ 12 * Real.exp 20 * vkGeneralGrowth (1 - σ) L + 200 * 1 := by gcongr
    _ = 12 * Real.exp 20 * vkGeneralGrowth (1 - σ) L + 200 := by ring

/-- **Large blocks at depth `1 − σ ≤ 1/(3·2^{24})`.** -/
theorem norm_block_le_large_general {τ σ : ℝ} {Y : ℕ} (hL : Real.exp 30 ≤ Real.log τ)
    (hY : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y) (hYτ : τ < (Y : ℝ) ^ 22)
    (hYup : 8 * Real.pi * ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ τ)
    (hκ : 1 - σ ≤ 1 / (3 * (2 : ℝ) ^ 24)) :
    ‖∑ n ∈ Finset.Ico (Y + 1) (2 * Y + 1), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
      2560 := by
  set L := Real.log τ with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hYup
  have hY1 : (1 : ℝ) ≤ ((Y + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg Y : (0:ℝ) ≤ Y)]
  have hY0 : (0 : ℝ) < ((Y + 1 : ℕ) : ℝ) := by linarith
  have hfac : Nat.factorial (24 - 1) ≤ Y + 1 := by
    have h200 : (200 : ℝ) ≤ L ^ ((2 : ℝ) / 3) := by
      have h100 := hundred_le_rpow_third hL
      rw [rpow_two_thirds_eq_sq hL0]
      have := mul_le_mul h100 h100 (by norm_num) (by linarith)
      linarith
    have : ((Nat.factorial 23 : ℕ) : ℝ) ≤ ((Y + 1 : ℕ) : ℝ) := by
      calc ((Nat.factorial 23 : ℕ) : ℝ) ≤ Real.exp 200 := factorial_twentythree_le_exp
        _ ≤ Real.exp (L ^ ((2 : ℝ) / 3)) := Real.exp_le_exp.mpr h200
        _ ≤ Y := hY
        _ ≤ ((Y + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hhigh : τ ≤ 2 * Real.pi * 2 ^ 24 * ((Y + 1 : ℕ) : ℝ) ^ (24 - 1) *
      ((Y + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by
    have h1 : τ ≤ ((Y + 1 : ℕ) : ℝ) ^ 22 := by
      have : (Y : ℝ) ^ 22 ≤ ((Y + 1 : ℕ) : ℝ) ^ 22 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast; linarith) 22
      linarith
    have h2 : ((Y + 1 : ℕ) : ℝ) ^ 22 ≤ ((Y + 1 : ℕ) : ℝ) ^ (24 - 1) *
        ((Y + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by
      rw [← Real.rpow_natCast _ (24 - 1), ← Real.rpow_add hY0, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hY1
      norm_num
    have h3 : (1 : ℝ) ≤ 2 * Real.pi * 2 ^ 24 := by
      have hpi := Real.pi_gt_three
      have h24 : (1 : ℝ) ≤ 2 ^ 24 := one_le_pow₀ (by norm_num)
      have : (1 : ℝ) ≤ 2 * Real.pi := by linarith
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 * Real.pi * 2 ^ 24 := mul_le_mul this h24 (by norm_num) (by positivity)
    have h4 : 0 ≤ ((Y + 1 : ℕ) : ℝ) ^ (24 - 1) * ((Y + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by
      positivity
    calc τ ≤ ((Y + 1 : ℕ) : ℝ) ^ (24 - 1) * ((Y + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := h1.trans h2
      _ ≤ 2 * Real.pi * 2 ^ 24 * (((Y + 1 : ℕ) : ℝ) ^ (24 - 1) *
          ((Y + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) := le_mul_of_one_le_left h4 h3
      _ = _ := by ring
  have hσ0 : 0 ≤ σ := by
    have : (1 : ℝ) / (3 * (2 : ℝ) ^ 24) ≤ 1 := by norm_num
    linarith
  have h := dirichlet_block_sigma_saving_of_small_factorial hσ0 hτ0 (N := Y + 1) (M := 2 * Y + 1)
    (by omega) (by omega) (by omega) (by norm_num : 2 ≤ 24) hfac hYup hhigh
  refine h.trans ?_
  have hexp : ((Y + 1 : ℕ) : ℝ) ^ (1 - σ) *
      ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24))) ≤ 1 := by
    rw [← Real.rpow_add hY0]
    apply Real.rpow_le_one_of_one_le_of_nonpos hY1
    have : (1 : ℝ) / (3 * (2 : ℝ) ^ 24) = 1 / (3 * (2 : ℝ) ^ (24 : ℕ)) := by norm_num
    linarith
  calc 2560 * ((Y + 1 : ℕ) : ℝ) ^ (1 - σ) * ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24)))
      = 2560 * (((Y + 1 : ℕ) : ℝ) ^ (1 - σ) *
        ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24))))  := by ring
    _ ≤ 2560 * 1 := by gcongr
    _ = 2560 := by ring


/-- The dyadic part at depth `1 − σ`. -/
theorem vk_dyadic_le_general {τ σ : ℝ} {N₀ J : ℕ} (hτbig : 2 * (8 * Real.pi) ^ 3 ≤ τ)
    (hL : Real.exp 30 ≤ Real.log τ)
    (hN₀ : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ N₀)
    (hJmin : ∀ r < J, (N₀ : ℝ) * 2 ^ r < τ ^ 2)
    (hσ0' : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hκ : 1 - σ ≤ 1 / (3 * (2 : ℝ) ^ 24)) :
    ‖∑ k ∈ Finset.Ioc N₀ (N₀ * 2 ^ J), ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      J * vkGeneralBlockConstant (1 - σ) (Real.log τ) := by
  have hdy := norm_sum_Ioc_dyadic_le N₀
    (fun k : ℕ => ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))) J
  refine hdy.trans ?_
  have hblock : ∀ r ∈ Finset.range J,
      ‖∑ k ∈ Finset.Ioc (N₀ * 2 ^ r) (N₀ * 2 ^ (r + 1)),
        ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤ vkGeneralBlockConstant (1 - σ) (Real.log τ) := by
    intro r hr
    have hrJ := Finset.mem_range.mp hr
    set Y := N₀ * 2 ^ r with hY
    have hY2 : N₀ * 2 ^ (r + 1) = Y * 2 := by rw [hY, pow_succ]; ring
    rw [hY2, block_sum_eq_Ico]
    have hYlow : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y := by
      have : (N₀ : ℝ) ≤ Y := by
        rw [hY]; push_cast
        exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ (by norm_num))
      linarith
    have hYτ2 : (Y : ℝ) < τ ^ 2 := by rw [hY]; push_cast; exact hJmin r hrJ
    unfold vkGeneralBlockConstant
    have hE : 0 ≤ 12 * Real.exp 20 * vkGeneralGrowth (1 - σ) (Real.log τ) := by
      unfold vkGeneralGrowth; positivity
    by_cases hmid : (Y : ℝ) ^ 22 ≤ τ
    · have h := norm_block_le_middle_general hL hYlow hmid hσ0' hσ1
      linarith
    · push Not at hmid
      have hπ : 0 < 8 * Real.pi := by positivity
      have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτbig
      have hYup : 8 * Real.pi * ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ τ := by
        have hY1 : ((Y + 1 : ℕ) : ℝ) ≤ (τ / (8 * Real.pi)) ^ 3 := by
          have h1 : (1 : ℝ) ≤ τ ^ 2 := by
            have h8 : (1 : ℝ) ≤ 8 * Real.pi := by linarith [Real.pi_gt_three]
            have h83 : (1 : ℝ) ≤ (8 * Real.pi) ^ 3 := one_le_pow₀ h8
            have : (1 : ℝ) ≤ τ := le_trans (by linarith) hτbig
            exact one_le_pow₀ this
          have h2 : 2 * τ ^ 2 ≤ (τ / (8 * Real.pi)) ^ 3 := by
            rw [div_pow, le_div_iff₀ (by positivity)]
            have : 2 * (8 * Real.pi) ^ 3 * τ ^ 2 ≤ τ * τ ^ 2 :=
              mul_le_mul_of_nonneg_right hτbig (by positivity)
            nlinarith
          push_cast
          linarith
        have hroot : ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
            ((τ / (8 * Real.pi)) ^ 3) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) hY1 (by norm_num)
        have he : ((τ / (8 * Real.pi)) ^ 3) ^ ((1 : ℝ) / 3) = τ / (8 * Real.pi) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        rw [he] at hroot
        calc 8 * Real.pi * ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ 8 * Real.pi * (τ / (8 * Real.pi)) :=
              mul_le_mul_of_nonneg_left hroot hπ.le
          _ = τ := by field_simp
      have h := norm_block_le_large_general hL hYlow hmid hYup hκ
      linarith
  calc ∑ r ∈ Finset.range J, ‖∑ k ∈ Finset.Ioc (N₀ * 2 ^ r) (N₀ * 2 ^ (r + 1)),
        ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖
      ≤ ∑ _r ∈ Finset.range J, vkGeneralBlockConstant (1 - σ) (Real.log τ) := Finset.sum_le_sum hblock
    _ = J * vkGeneralBlockConstant (1 - σ) (Real.log τ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]



/-- **Vinogradov–Korobov growth at every depth near `1`.** -/
theorem norm_riemannZeta_le_vinogradovKorobov_general {τ σ : ℝ} (hτ : Real.exp (Real.exp 30) ≤ τ)
    (hσw : σ ≤ 1 - vinogradovKorobovWidth (Real.log τ)) (hκ : 1 - σ ≤ 1 / (3 * (2 : ℝ) ^ 24)) :
    ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      vkGeneralGrowthConstant * Real.log τ * vkGeneralGrowth (1 - σ) (Real.log τ) := by
  classical
  have hτ0 : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hτ
  have hL : Real.exp 30 ≤ Real.log τ := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) hτ
  have hL0 : 0 < Real.log τ := lt_of_lt_of_le (Real.exp_pos _) hL
  have hL1 : (1 : ℝ) ≤ Real.log τ := le_trans (Real.one_le_exp (by norm_num)) hL
  have hθ0 := vinogradovKorobovWidth_pos hL
  have hθsmall := vinogradovKorobovWidth_le hL
  have hσ0 : 1 / 2 ≤ σ := by
    have : (1 : ℝ) / (3 * (2 : ℝ) ^ 24) ≤ 1 / 2 := by norm_num
    linarith
  have hσle : σ ≤ 1 := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  have hτbig : 2 * (8 * Real.pi) ^ 3 ≤ τ := by
    have h1 : 2 * (8 * Real.pi) ^ 3 ≤ Real.exp 30 := by
      have hpi := Real.pi_lt_d2
      have h2 : Real.exp 30 = Real.exp 1 ^ 30 := by rw [← Real.exp_nat_mul]; norm_num
      have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h3 : (2 : ℝ) ^ 30 ≤ Real.exp 1 ^ 30 := pow_le_pow_left₀ (by norm_num) he 30
      have h4 : (8 * Real.pi) ^ 3 ≤ (8 * 3.15) ^ 3 := pow_le_pow_left₀ (by positivity)
        (by linarith) 3
      rw [h2]; norm_num at h3 h4 ⊢; linarith
    have h2 : Real.exp 30 ≤ τ := le_trans (Real.exp_le_exp.mpr (by
      have := Real.add_one_le_exp (30 : ℝ); linarith)) hτ
    linarith
  have hτ4 : (4 : ℝ) ≤ τ := by
    have hpi := Real.pi_gt_three
    have h8 : (1 : ℝ) ≤ 8 * Real.pi := by linarith
    have h83 : 8 * Real.pi ≤ (8 * Real.pi) ^ 3 := le_self_pow₀ h8 (by norm_num)
    linarith
  set N₀ : ℕ := ⌈Real.exp (Real.log τ ^ ((2 : ℝ) / 3))⌉₊ with hN₀
  have hN₀low : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ N₀ := Nat.le_ceil _
  have hN₀1 : 1 ≤ N₀ := by
    have : (1 : ℝ) ≤ N₀ := le_trans (Real.one_le_exp (by positivity)) hN₀low
    exact_mod_cast this
  have hN₀τ2 : (N₀ : ℝ) ≤ 2 * τ ^ 2 := by
    have hN₀up : (N₀ : ℝ) < Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h100 := hundred_le_rpow_third hL
    have hL23 : Real.log τ ^ ((2 : ℝ) / 3) ≤ Real.log τ := by
      have e : Real.log τ = Real.log τ ^ ((1 : ℝ) / 3) * Real.log τ ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_add hL0]; norm_num
      have h0 : 0 ≤ Real.log τ ^ ((2 : ℝ) / 3) := by positivity
      have : 1 * Real.log τ ^ ((2 : ℝ) / 3) ≤
          Real.log τ ^ ((1 : ℝ) / 3) * Real.log τ ^ ((2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right (by linarith) h0
      rw [← e] at this; linarith
    have h1 : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ τ := by
      calc Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Real.exp (Real.log τ) := Real.exp_le_exp.mpr hL23
        _ = τ := Real.exp_log hτ0
    nlinarith
  -- the number of blocks
  have hex : ∃ J : ℕ, τ ^ 2 ≤ (N₀ : ℝ) * 2 ^ J := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (τ ^ 2) (by norm_num : (1 : ℝ) < 2)
    refine ⟨J, le_trans hJ.le ?_⟩
    have : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
    have : (0 : ℝ) < 2 ^ J := by positivity
    nlinarith
  set J := Nat.find hex with hJdef
  have hJspec : τ ^ 2 ≤ (N₀ : ℝ) * 2 ^ J := Nat.find_spec hex
  have hJmin : ∀ r < J, (N₀ : ℝ) * 2 ^ r < τ ^ 2 := fun r hr => by
    have := Nat.find_min hex hr
    push Not at this
    exact this
  set X : ℕ := N₀ * 2 ^ J with hXdef
  have hXlow : τ ^ 2 ≤ (X : ℝ) := by rw [hXdef]; push_cast; exact hJspec
  have hXup : (X : ℝ) ≤ 2 * τ ^ 2 := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [hXdef, h0]; push_cast; linarith
    · have h := hJmin (J - 1) (by omega)
      have e2 : (2 : ℝ) ^ J = 2 * 2 ^ (J - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hXdef]; push_cast; rw [e2]
      nlinarith
  have hX1 : 1 ≤ X := le_trans hN₀1 (Nat.le_mul_of_pos_right _ (by positivity))
  have hJbound : (J : ℝ) ≤ 3 * Real.log τ + 1 := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [h0]; push_cast; linarith
    · have h := hJmin (J - 1) (by omega)
      have h2 : (2 : ℝ) ^ (J - 1) < τ ^ 2 := by
        have : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
        have : (0 : ℝ) < 2 ^ (J - 1) := by positivity
        nlinarith
      have hlog := Real.log_lt_log (by positivity) h2
      rw [Real.log_pow, Real.log_pow] at hlog
      have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have hJ1 : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [hJ1] at hlog
      push_cast at hlog
      have hJ0 : (0 : ℝ) ≤ (J : ℝ) - 1 := by
        have : (1 : ℝ) ≤ J := by exact_mod_cast hpos
        linarith
      nlinarith
  -- truncation and the four pieces
  have hwne : (σ : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hre : ((σ : ℂ) + (τ : ℂ) * Complex.I).re = σ := by simp
  have htrunc := norm_riemannZeta_le_partialSum (w := (σ : ℂ) + (τ : ℂ) * Complex.I)
    (by rw [hre]; linarith) hwne hX1
  rw [hre] at htrunc
  have ht1 := vk_tail_one (τ := τ) (σ := σ) (θ := 1 - σ) (X := X)
    (by linarith) (by linarith) (by nlinarith) (by linarith) hX1 hXup
  have ht2 := vk_tail_two (τ := τ) (σ := σ) (X := X) hτ4 hσ0 hσ2 hXlow
  have hsplit := sum_Icc_one_eq_initial_add_dyadic
    (fun k : ℕ => ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))) N₀ J
  have hinit := norm_sum_initial_le_general (τ := τ) (N₀ := N₀) hσle
  have hlogN₀ := log_vkInitialLength_le hL
  rw [← hN₀] at hlogN₀
  have hlogN₀0 : 0 ≤ Real.log N₀ := Real.log_nonneg (by exact_mod_cast hN₀1)
  have hE1 : 1 ≤ vkGeneralGrowth (1 - σ) (Real.log τ) := by
    unfold vkGeneralGrowth
    exact Real.one_le_exp (by
      have := Real.sqrt_nonneg (1 - σ)
      have hlogL : 0 ≤ Real.log (Real.log τ) := Real.log_nonneg hL1
      have : 0 ≤ 1 - σ := by linarith
      positivity)
  have hinit' : Real.exp ((1 - σ) * Real.log N₀) * (1 + Real.log N₀) ≤
      vkGeneralGrowth (1 - σ) (Real.log τ) * (2 + Real.log τ) := by
    have h1 : Real.exp ((1 - σ) * Real.log N₀) ≤ vkGeneralGrowth (1 - σ) (Real.log τ) :=
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlogN₀ (by linarith))).trans
        (exp_initial_le_vkGeneralGrowth hL (by linarith))
    have hL23 : Real.log τ ^ ((2 : ℝ) / 3) ≤ Real.log τ :=
      Real.rpow_le_self_of_one_le hL1 (by norm_num)
    have h2 : 1 + Real.log N₀ ≤ 2 + Real.log τ := by linarith
    exact mul_le_mul h1 h2 (by linarith) (by linarith)
  have hdy := vk_dyadic_le_general (σ := σ) (N₀ := N₀) (J := J) hτbig hL hN₀low hJmin hσ0 hσle hκ
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = vkGeneralGrowth (1 - σ) (Real.log τ) := ⟨_, rfl⟩
  rw [← hEdef] at hinit' hE1
  have hBk : vkGeneralBlockConstant (1 - σ) (Real.log τ) ≤ (12 * Real.exp 20 + 2761) * E := by
    unfold vkGeneralBlockConstant
    rw [← hEdef]
    nlinarith [Real.exp_pos 20]
  have hsum : ‖∑ k ∈ Finset.Icc 1 X, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      E * (2 + Real.log τ) + J * vkGeneralBlockConstant (1 - σ) (Real.log τ) := by
    rw [hXdef, hsplit]
    exact (norm_add_le _ _).trans (add_le_add (hinit.trans hinit') hdy)
  have hB0 : 0 ≤ vkGeneralBlockConstant (1 - σ) (Real.log τ) := by
    unfold vkGeneralBlockConstant vkGeneralGrowth; positivity
  have hJB : (J : ℝ) * vkGeneralBlockConstant (1 - σ) (Real.log τ) ≤
      (3 * Real.log τ + 1) * ((12 * Real.exp 20 + 2761) * E) :=
    mul_le_mul hJbound hBk hB0 (by linarith)
  have hC0 : 0 ≤ 12 * Real.exp 20 + 2761 := by positivity
  have hfirst : ‖∑ k ∈ Finset.Icc 1 X, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      E * (2 + Real.log τ) + (3 * Real.log τ + 1) * ((12 * Real.exp 20 + 2761) * E) := by
    linarith
  calc ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
      ≤ ‖∑ k ∈ Finset.Icc 1 X, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ +
          (X : ℝ) ^ (1 - σ) / ‖(σ : ℂ) + (τ : ℂ) * Complex.I - 1‖ +
          ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ * ((X : ℝ) ^ (-σ) / σ) := htrunc
    _ ≤ (E * (2 + Real.log τ) + (3 * Real.log τ + 1) * ((12 * Real.exp 20 + 2761) * E)) + 1 + 4 :=
        add_le_add (add_le_add hfirst ht1) ht2
    _ ≤ vkGeneralGrowthConstant * Real.log τ * E :=
        vk_general_final_arith hE1 hL1 hC0 rfl
    _ = vkGeneralGrowthConstant * Real.log τ * vkGeneralGrowth (1 - σ) (Real.log τ) := by rw [hEdef]

end

end RHTower.Sieve

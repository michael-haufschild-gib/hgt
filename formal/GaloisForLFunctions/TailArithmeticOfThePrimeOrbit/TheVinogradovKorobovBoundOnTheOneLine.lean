import GaloisForLFunctions.RHTower.Sieve.VinogradovZetaGrowth

/-!
# The Vinogradov–Korobov bound on the `1`-line

For `τ ≥ exp(exp 30)`, `1 ≤ σ ≤ 2`, `L = log τ`:

`‖ζ(σ + iτ)‖ ≤ C (1 + K)`, `K = (746496 (L log L)²)^{1/3}`,

so `‖ζ(σ + iτ)‖ ≪ (log τ · log log τ)^{2/3}` (`norm_riemannZeta_le_vkCube`,
`exists_norm_riemannZeta_le_two_thirds`).

Proof. Vinogradov's dyadic estimate bounds the prefix sums of `n^{−iτ}` on `(Y, 2Y]` by
`12e^{20} Y^{1−δ/4} + 200 Y^{1/2}` with `δ/4 ≥ ℓ²/(746496 L²(log L)²)`, `ℓ = log Y`, whenever
`e^{L^{2/3}} ≤ Y` and `Y^{22} ≤ τ`. At `σ ≥ 1` partial summation turns this into
`12e^{20} exp(−ℓ³/K³) + 200 Y^{−1/2}` (`norm_block_le_middle_one`); past `Y^{22} > τ` the
`24`-th derivative test gives `2560 Y^{−1/(3·2^{24})}` (`norm_block_le_large_one`). Start the dyadic
blocks at `N₁ = ⌈e^K⌉`: then `ℓ ≥ K + r log 2` on the `r`-th block, `ℓ³/K³ ≥ ℓ/K`, and the blocks
sum to `12e^{19}(1 + K/log 2) + O(1)`. The initial segment costs `e^{1/50}(1 + log N₁)`.
-/

open Real Finset

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

open RHTower.Sieve

noncomputable section

/-- **Middle blocks on the `1`-line.** For `σ ≥ 1` the block `(Y, 2Y]` saves
`exp(−(log Y)³/(746496 L²(log L)²))` against its trivial size `1`. -/
theorem norm_block_le_middle_one {τ σ : ℝ} {Y : ℕ} (hL : Real.exp 30 ≤ Real.log τ)
    (hY : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y) (hYτ : (Y : ℝ) ^ 22 ≤ τ) (hσ1 : 1 ≤ σ) :
    ‖∑ n ∈ Finset.Ico (Y + 1) (2 * Y + 1), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
      12 * Real.exp 20 * Real.exp (-(Real.log Y ^ 3 /
          (746496 * Real.log τ ^ 2 * Real.log (Real.log τ) ^ 2))) +
        200 * (Y : ℝ) ^ (-(1 / 2 : ℝ)) := by
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
  have hYσ : ((Y + 1 : ℕ) : ℝ) ^ (-σ) ≤ (Y : ℝ) ^ (-(1 : ℝ)) :=
    calc ((Y + 1 : ℕ) : ℝ) ^ (-σ) ≤ (Y : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos hY0 (by push_cast; linarith) (by linarith)
      _ ≤ (Y : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hPb0 : 0 ≤ Pb := by rw [hPb]; positivity
  have e1 : (Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-(1 : ℝ)) = (Y : ℝ) ^ (-(δ / 4)) := by
    rw [Real.rpow_neg_one]
    field_simp
  have e2 : (Y : ℝ) ^ ((1 : ℝ) / 2) * (Y : ℝ) ^ (-(1 : ℝ)) = (Y : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hY0]
    norm_num
  have hsave : (Y : ℝ) ^ (-(δ / 4)) ≤
      Real.exp (-(ℓ ^ 3 / (746496 * L ^ 2 * Real.log L ^ 2))) := by
    rw [Real.rpow_def_of_pos hY0, ← hℓ]
    apply Real.exp_le_exp.mpr
    have hδl := vinogradovDyadicSaving_div_four_ge hL hℓlow hℓL
    rw [← hR, ← hδ] at hδl
    have h2 : ℓ ^ 3 / (746496 * L ^ 2 * Real.log L ^ 2) ≤ ℓ * (δ / 4) := by
      have : ℓ ^ 3 / (746496 * L ^ 2 * Real.log L ^ 2) =
          ℓ * (ℓ ^ 2 / (746496 * L ^ 2 * Real.log L ^ 2)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hδl hℓ0.le
    linarith
  calc Pb * ((Y + 1 : ℕ) : ℝ) ^ (-σ) ≤ Pb * (Y : ℝ) ^ (-(1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hYσ hPb0
    _ = 12 * Real.exp 20 * ((Y : ℝ) * (Y : ℝ) ^ (-(δ / 4)) * (Y : ℝ) ^ (-(1 : ℝ))) +
        200 * ((Y : ℝ) ^ ((1 : ℝ) / 2) * (Y : ℝ) ^ (-(1 : ℝ))) := by rw [hPb]; ring
    _ = 12 * Real.exp 20 * (Y : ℝ) ^ (-(δ / 4)) + 200 * (Y : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [e1, e2]
    _ ≤ _ := by gcongr

/-- **Large blocks on the `1`-line.** Past `Y^{22} > τ` the `24`-th derivative test gives a power
saving at `σ ≥ 1`. -/
theorem norm_block_le_large_one {τ σ : ℝ} {Y : ℕ} (hL : Real.exp 30 ≤ Real.log τ)
    (hY : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y) (hYτ : τ < (Y : ℝ) ^ 22)
    (hYup : 8 * Real.pi * ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ τ) (hσ1 : 1 ≤ σ) :
    ‖∑ n ∈ Finset.Ico (Y + 1) (2 * Y + 1), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
      2560 * ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24))) := by
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
  have hσ0 : 0 ≤ σ := by linarith
  have h := dirichlet_block_sigma_saving_of_small_factorial hσ0 hτ0 (N := Y + 1) (M := 2 * Y + 1)
    (by omega) (by omega) (by omega) (by norm_num : 2 ≤ 24) hfac hYup hhigh
  refine h.trans ?_
  have hexp : ((Y + 1 : ℕ) : ℝ) ^ (1 - σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
  have hp : 0 ≤ ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24))) := by positivity
  calc 2560 * ((Y + 1 : ℕ) : ℝ) ^ (1 - σ) * ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24)))
      ≤ 2560 * 1 * ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24))) := by gcongr
    _ = _ := by ring


/-- A geometric series of ratio `e^{−x}`: `Σ_{r<J} e^{−xr} ≤ 1 + 1/x`. -/
theorem sum_range_exp_neg_pow_le {x : ℝ} (hx : 0 < x) (J : ℕ) :
    ∑ r ∈ Finset.range J, Real.exp (-x) ^ r ≤ 1 + 1 / x := by
  have hq0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hq1 : Real.exp (-x) < 1 := by
    have := Real.exp_lt_exp.mpr (show -x < 0 by linarith)
    rwa [Real.exp_zero] at this
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hq0 hq1
  rw [← Finset.range_eq_Ico, pow_zero] at hg
  refine hg.trans ?_
  have he : Real.exp (-x) * (1 + x) ≤ 1 := by
    have h1 := Real.add_one_le_exp x
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-x)]
  have hd : 0 < 1 - Real.exp (-x) := by linarith
  rw [div_le_iff₀ hd]
  have e : (1 + 1 / x) * (1 - Real.exp (-x)) = ((1 + x) * (1 - Real.exp (-x))) / x := by
    field_simp
    ring
  rw [e, le_div_iff₀ hx]
  nlinarith

/-- The Vinogradov cube scale `K = (746496 (L log L)²)^{1/3}`, `L = log τ`: a dyadic block of
logarithmic length `ℓ ≥ K` saves `exp(−ℓ³/K³) ≤ exp(−ℓ/K)` on the `1`-line. -/
def vkCubeScale (τ : ℝ) : ℝ :=
  (746496 * (Real.log τ * Real.log (Real.log τ)) ^ 2) ^ ((1 : ℝ) / 3)

theorem vkCubeScale_cube {τ : ℝ} :
    vkCubeScale τ ^ 3 = 746496 * Real.log τ ^ 2 * Real.log (Real.log τ) ^ 2 := by
  unfold vkCubeScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  ring

theorem vkCubeScale_pos {τ : ℝ} (hL : Real.exp 30 ≤ Real.log τ) : 0 < vkCubeScale τ := by
  have hL0 : 0 < Real.log τ := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl := one_le_log_of_exp_thirty_le hL
  unfold vkCubeScale
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The cube scale lies above the Vinogradov length `L^{2/3}`. -/
theorem rpow_two_thirds_le_vkCubeScale {τ : ℝ} (hL : Real.exp 30 ≤ Real.log τ) :
    Real.log τ ^ ((2 : ℝ) / 3) ≤ vkCubeScale τ := by
  have hL0 : 0 < Real.log τ := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl := one_le_log_of_exp_thirty_le hL
  rw [← pow_le_pow_iff_left₀ (by positivity) (vkCubeScale_pos hL).le (by norm_num : (3 : ℕ) ≠ 0),
    vkCubeScale_cube, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
    show (2 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 2 by norm_num, Real.rpow_two]
  have h1 : (1 : ℝ) ≤ 746496 * Real.log (Real.log τ) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (Real.log τ)]

/-- Below `τ²` a block is short enough for the derivative test: `8π(Y+1)^{1/3} ≤ τ`. -/
theorem eightPi_rpow_le_of_lt_sq {τ : ℝ} {Y : ℕ} (hτbig : 2 * (8 * Real.pi) ^ 3 ≤ τ)
    (hYτ2 : (Y : ℝ) < τ ^ 2) : 8 * Real.pi * ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ τ := by
  have hπ : 0 < 8 * Real.pi := by positivity
  have hτ1 : 1 ≤ τ := by
    have h8 : (1 : ℝ) ≤ 8 * Real.pi := by linarith [Real.pi_gt_three]
    have : (1 : ℝ) ≤ (8 * Real.pi) ^ 3 := one_le_pow₀ h8
    linarith
  have hY1 : ((Y + 1 : ℕ) : ℝ) ≤ (τ / (8 * Real.pi)) ^ 3 := by
    have h1 : (1 : ℝ) ≤ τ ^ 2 := one_le_pow₀ hτ1
    have h2 : 2 * τ ^ 2 ≤ (τ / (8 * Real.pi)) ^ 3 := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      have : 2 * (8 * Real.pi) ^ 3 * τ ^ 2 ≤ τ * τ ^ 2 :=
        mul_le_mul_of_nonneg_right hτbig (by positivity)
      nlinarith only [this]
    push_cast
    linarith only [h1, h2, hYτ2]
  have hroot : ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ ((τ / (8 * Real.pi)) ^ 3) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) hY1 (by norm_num)
  have he : ((τ / (8 * Real.pi)) ^ 3) ^ ((1 : ℝ) / 3) = τ / (8 * Real.pi) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  rw [he] at hroot
  calc 8 * Real.pi * ((Y + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ 8 * Real.pi * (τ / (8 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hroot hπ.le
    _ = τ := by field_simp

/-- The three geometric ratios of the block bound. -/
def vkRatioOne (τ : ℝ) : ℝ := Real.exp (-(Real.log 2 / vkCubeScale τ))

/-- The ratio of the square-root remainder. -/
def vkRatioTwo : ℝ := Real.exp (-(Real.log 2 / 2))

/-- The ratio of the derivative-test blocks. -/
def vkRatioThree : ℝ := Real.exp (-(1 / (3 * (2 : ℝ) ^ 24) * Real.log 2))

/-- `exp(−ℓ³/K³) ≤ e^{−1} q₁^r` once `ℓ ≥ K + r log 2`. -/
theorem exp_neg_cube_le {τ ℓ : ℝ} {r : ℕ} (hL : Real.exp 30 ≤ Real.log τ)
    (hℓ : vkCubeScale τ + r * Real.log 2 ≤ ℓ) :
    Real.exp (-(ℓ ^ 3 / (746496 * Real.log τ ^ 2 * Real.log (Real.log τ) ^ 2))) ≤
      Real.exp (-1) * vkRatioOne τ ^ r := by
  set K := vkCubeScale τ with hKdef
  have hK0 : 0 < K := vkCubeScale_pos hL
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← vkCubeScale_cube, ← hKdef, vkRatioOne, ← hKdef, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  set m := ℓ / K with hm
  have hmle : 1 + r * Real.log 2 / K ≤ m := by
    have := div_le_div_of_nonneg_right hℓ hK0.le
    rwa [add_div, div_self hK0.ne'] at this
  have hu : 0 ≤ r * Real.log 2 / K := by positivity
  have hm1 : 1 ≤ m := by linarith only [hmle, hu]
  have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
  have hcube : m ≤ m ^ 3 := by
    have := le_mul_of_one_le_right (by linarith only [hm1] : (0 : ℝ) ≤ m) hm2
    rw [pow_succ']
    linarith only [this]
  have e : ℓ ^ 3 / K ^ 3 = m ^ 3 := by rw [hm, div_pow]
  have e2 : (r : ℝ) * (-(Real.log 2 / K)) = -(r * Real.log 2 / K) := by ring
  rw [e, e2]
  linarith only [hcube, hmle]

/-- **One dyadic block on the `1`-line.** The block `(Y, 2Y]`, `Y = N₁2^r ≥ e^K 2^r`, `Y < τ²`, is
at most `12e^{19}q₁^r + 200q₂^r + 2560q₃^r`. -/
theorem norm_block_le_geometric {τ σ : ℝ} (hL : Real.exp 30 ≤ Real.log τ)
    (hτbig : 2 * (8 * Real.pi) ^ 3 ≤ τ) (hσ1 : 1 ≤ σ) {N₁ : ℕ}
    (hN₁ : Real.exp (vkCubeScale τ) ≤ N₁) {r : ℕ} (hYτ2 : ((N₁ * 2 ^ r : ℕ) : ℝ) < τ ^ 2) :
    ‖∑ n ∈ Finset.Ico (N₁ * 2 ^ r + 1) (2 * (N₁ * 2 ^ r) + 1),
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (τ : ℂ))‖ ≤
      12 * Real.exp 19 * vkRatioOne τ ^ r + 200 * vkRatioTwo ^ r + 2560 * vkRatioThree ^ r := by
  set K := vkCubeScale τ with hKdef
  have hK0 : 0 < K := vkCubeScale_pos hL
  have hKL : Real.log τ ^ ((2 : ℝ) / 3) ≤ K := rpow_two_thirds_le_vkCubeScale hL
  set Y := N₁ * 2 ^ r with hY
  have hYK : Real.exp K * 2 ^ r ≤ (Y : ℝ) := by
    rw [hY]; push_cast
    exact mul_le_mul_of_nonneg_right hN₁ (by positivity)
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (by positivity) hYK
  have hℓ : K + r * Real.log 2 ≤ Real.log Y := by
    have := Real.log_le_log (by positivity) hYK
    rwa [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow] at this
  have hYlow : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Y := by
    have h1 : Real.exp (Real.log τ ^ ((2 : ℝ) / 3)) ≤ Real.exp K := Real.exp_le_exp.mpr hKL
    have h2 : Real.exp K ≤ Real.exp K * 2 ^ r :=
      le_mul_of_one_le_right (Real.exp_pos _).le (one_le_pow₀ (by norm_num))
    linarith only [h1, h2, hYK]
  have hr0 : 0 ≤ (r : ℝ) * Real.log 2 := by positivity
  have hrY : (r : ℝ) * Real.log 2 ≤ Real.log Y := by linarith only [hℓ, hK0]
  have hn₁ : 0 ≤ 12 * Real.exp 19 * vkRatioOne τ ^ r := by unfold vkRatioOne; positivity
  have hn₂ : 0 ≤ 200 * vkRatioTwo ^ r := by unfold vkRatioTwo; positivity
  have hn₃ : 0 ≤ 2560 * vkRatioThree ^ r := by unfold vkRatioThree; positivity
  by_cases hmid : (Y : ℝ) ^ 22 ≤ τ
  · have h := norm_block_le_middle_one hL hYlow hmid hσ1
    have hg₁ := exp_neg_cube_le hL hℓ
    have hg₂ : (Y : ℝ) ^ (-(1 / 2 : ℝ)) ≤ vkRatioTwo ^ r := by
      rw [Real.rpow_def_of_pos hY0, vkRatioTwo, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      linarith only [hrY]
    have he : 12 * Real.exp 20 * (Real.exp (-1) * vkRatioOne τ ^ r) =
        12 * Real.exp 19 * vkRatioOne τ ^ r := by
      rw [show (20 : ℝ) = 19 + 1 by norm_num, Real.exp_add]
      have : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
      linear_combination 12 * Real.exp 19 * vkRatioOne τ ^ r * this
    have h' : 12 * Real.exp 20 * Real.exp (-(Real.log Y ^ 3 /
        (746496 * Real.log τ ^ 2 * Real.log (Real.log τ) ^ 2))) + 200 * (Y : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ 12 * Real.exp 20 * (Real.exp (-1) * vkRatioOne τ ^ r) + 200 * vkRatioTwo ^ r := by
      gcongr
    linarith only [h, h', he, hn₃]
  · push Not at hmid
    have h := norm_block_le_large_one hL hYlow hmid (eightPi_rpow_le_of_lt_sq hτbig hYτ2) hσ1
    have hε : (0 : ℝ) < 1 / (3 * (2 : ℝ) ^ 24) := by positivity
    have hg₃ : ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24))) ≤ vkRatioThree ^ r := by
      calc ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24)))
          ≤ (Y : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24))) :=
            Real.rpow_le_rpow_of_nonpos hY0 (by push_cast; linarith) (by linarith only [hε])
        _ ≤ vkRatioThree ^ r := by
            rw [Real.rpow_def_of_pos hY0, vkRatioThree, ← Real.exp_nat_mul]
            apply Real.exp_le_exp.mpr
            nlinarith only [hrY, hε]
    have h' : 2560 * ((Y + 1 : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ 24))) ≤
        2560 * vkRatioThree ^ r := by gcongr
    linarith only [h, h', hn₁, hn₂]

/-- **The dyadic blocks on the `1`-line** sum to `12e^{19}(1 + K/log 2) + O(1)`. -/
theorem norm_dyadic_le_one {τ σ : ℝ} (hL : Real.exp 30 ≤ Real.log τ)
    (hτbig : 2 * (8 * Real.pi) ^ 3 ≤ τ) (hσ1 : 1 ≤ σ) {N₁ J : ℕ}
    (hN₁ : Real.exp (vkCubeScale τ) ≤ N₁) (hJmin : ∀ r < J, (N₁ : ℝ) * 2 ^ r < τ ^ 2) :
    ‖∑ k ∈ Finset.Ioc N₁ (N₁ * 2 ^ J), ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      12 * Real.exp 19 * (1 + vkCubeScale τ / Real.log 2) + 200 * (1 + 2 / Real.log 2) +
        2560 * (1 + 1 / (1 / (3 * (2 : ℝ) ^ 24) * Real.log 2)) := by
  have hK0 : 0 < vkCubeScale τ := vkCubeScale_pos hL
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hblock : ∀ r ∈ Finset.range J,
      ‖∑ k ∈ Finset.Ioc (N₁ * 2 ^ r) (N₁ * 2 ^ (r + 1)),
        ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
        12 * Real.exp 19 * vkRatioOne τ ^ r + 200 * vkRatioTwo ^ r + 2560 * vkRatioThree ^ r := by
    intro r hr
    have hY2 : N₁ * 2 ^ (r + 1) = (N₁ * 2 ^ r) * 2 := by rw [pow_succ]; ring
    rw [hY2, block_sum_eq_Ico]
    refine norm_block_le_geometric hL hτbig hσ1 hN₁ ?_
    push_cast
    exact hJmin r (Finset.mem_range.mp hr)
  refine (norm_sum_Ioc_dyadic_le N₁ _ J).trans ((Finset.sum_le_sum hblock).trans ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have g1 := sum_range_exp_neg_pow_le (x := Real.log 2 / vkCubeScale τ) (by positivity) J
  have g2 := sum_range_exp_neg_pow_le (x := Real.log 2 / 2) (by positivity) J
  have g3 := sum_range_exp_neg_pow_le (x := 1 / (3 * (2 : ℝ) ^ 24) * Real.log 2) (by positivity) J
  rw [one_div_div] at g1 g2
  rw [vkRatioOne, vkRatioTwo, vkRatioThree]
  gcongr

/-- The constant of the `1`-line bound. -/
def vkOneLineConstant : ℝ :=
  3 * Real.exp (1 / 50) + 12 * Real.exp 19 * (1 + 1 / Real.log 2) +
    200 * (1 + 2 / Real.log 2) + 2560 * (1 + 1 / (1 / (3 * (2 : ℝ) ^ 24) * Real.log 2)) + 5

theorem vkOneLineConstant_pos : 0 < vkOneLineConstant := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold vkOneLineConstant
  positivity

/-- The pieces of the bound collect into `vkOneLineConstant · (1 + K)`. -/
private theorem pieces_le {K ℓ₁ : ℝ} (hK0 : 0 ≤ K) (hℓ₁ : ℓ₁ ≤ K + 1) :
    (Real.exp (1 / 50) * (1 + ℓ₁) +
        (12 * Real.exp 19 * (1 + K / Real.log 2) + 200 * (1 + 2 / Real.log 2) +
          2560 * (1 + 1 / (1 / (3 * (2 : ℝ) ^ 24) * Real.log 2)))) + 1 + 4 ≤
      vkOneLineConstant * (1 + K) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he50 : 0 < Real.exp (1 / 50) := Real.exp_pos _
  have he19 : 0 < Real.exp 19 := Real.exp_pos _
  have hc3 : 0 ≤ 2560 * (1 + 1 / (1 / (3 * (2 : ℝ) ^ 24) * Real.log 2)) := by positivity
  have hc2 : 0 ≤ 200 * (1 + 2 / Real.log 2) := by positivity
  have hinv : 0 ≤ 12 * Real.exp 19 * (1 / Real.log 2) := by positivity
  have h1 : Real.exp (1 / 50) * (1 + ℓ₁) ≤ Real.exp (1 / 50) * (2 + K) :=
    mul_le_mul_of_nonneg_left (by linarith only [hℓ₁]) he50.le
  have eK : 12 * Real.exp 19 * (1 + K / Real.log 2) =
      12 * Real.exp 19 + 12 * Real.exp 19 * (1 / Real.log 2) * K := by
    field_simp
  have hcoef : Real.exp (1 / 50) + 12 * Real.exp 19 * (1 / Real.log 2) ≤ vkOneLineConstant := by
    unfold vkOneLineConstant
    nlinarith only [he50, he19, hc3, hc2, hinv]
  have hconst : 2 * Real.exp (1 / 50) + 12 * Real.exp 19 + 200 * (1 + 2 / Real.log 2) +
      2560 * (1 + 1 / (1 / (3 * (2 : ℝ) ^ 24) * Real.log 2)) + 5 ≤ vkOneLineConstant := by
    unfold vkOneLineConstant
    nlinarith only [he50, he19, hinv]
  have hKmul := mul_le_mul_of_nonneg_right hcoef hK0
  rw [eK]
  nlinarith only [h1, hKmul, hconst]

/-- **The Vinogradov–Korobov bound on the `1`-line.** For `τ ≥ exp(exp 30)` and `1 ≤ σ ≤ 2`,
`‖ζ(σ + iτ)‖ ≤ C(1 + K)` with `K = (746496 (log τ · log log τ)²)^{1/3}`. -/
theorem norm_riemannZeta_le_vkCube {τ σ : ℝ} (hτ : Real.exp (Real.exp 30) ≤ τ) (hσ1 : 1 ≤ σ)
    (hσ2 : σ ≤ 2) :
    ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ vkOneLineConstant * (1 + vkCubeScale τ) := by
  classical
  have hτ0 : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hτ
  have hL : Real.exp 30 ≤ Real.log τ := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) hτ
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
  set K := vkCubeScale τ with hKdef
  have hK0 : 0 < K := vkCubeScale_pos hL
  set N₁ : ℕ := ⌈Real.exp K⌉₊ with hN₁
  have hN₁low : Real.exp K ≤ N₁ := Nat.le_ceil _
  have hN₁1 : 1 ≤ N₁ := by
    have : (1 : ℝ) ≤ N₁ := le_trans (Real.one_le_exp hK0.le) hN₁low
    exact_mod_cast this
  have hlogN₁ : Real.log N₁ ≤ K + 1 := by
    have hup : (N₁ : ℝ) < Real.exp K + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h1 : (N₁ : ℝ) ≤ 2 * Real.exp K := by linarith [Real.one_le_exp hK0.le]
    have h2 := Real.log_le_log (by exact_mod_cast hN₁1) h1
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h2
    have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hex : ∃ J : ℕ, τ ^ 2 ≤ (N₁ : ℝ) * 2 ^ J := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (τ ^ 2) (by norm_num : (1 : ℝ) < 2)
    refine ⟨J, le_trans hJ.le ?_⟩
    have : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁1
    have : (0 : ℝ) < 2 ^ J := by positivity
    nlinarith
  set J := Nat.find hex with hJdef
  have hJspec : τ ^ 2 ≤ (N₁ : ℝ) * 2 ^ J := Nat.find_spec hex
  have hJmin : ∀ r < J, (N₁ : ℝ) * 2 ^ r < τ ^ 2 := fun r hr => by
    have := Nat.find_min hex hr
    push Not at this
    exact this
  set X : ℕ := N₁ * 2 ^ J with hXdef
  have hXlow : τ ^ 2 ≤ (X : ℝ) := by rw [hXdef]; push_cast; exact hJspec
  have hX1 : 1 ≤ X := le_trans hN₁1 (Nat.le_mul_of_pos_right _ (by positivity))
  have hwne : (σ : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hre : ((σ : ℂ) + (τ : ℂ) * Complex.I).re = σ := by simp
  have htrunc := norm_riemannZeta_le_partialSum (w := (σ : ℂ) + (τ : ℂ) * Complex.I)
    (by rw [hre]; linarith) hwne hX1
  rw [hre] at htrunc
  have ht1 : (X : ℝ) ^ (1 - σ) / ‖(σ : ℂ) + (τ : ℂ) * Complex.I - 1‖ ≤ 1 := by
    have h1 : (X : ℝ) ^ (1 - σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hX1) (by linarith)
    have h2 : τ ≤ ‖(σ : ℂ) + (τ : ℂ) * Complex.I - 1‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)
      rw [show ((σ : ℂ) + (τ : ℂ) * Complex.I - 1).im = τ by simp, abs_of_pos hτ0] at this
      exact this
    rw [div_le_one (by linarith)]
    linarith
  have ht2 := vk_tail_two (τ := τ) (σ := σ) (X := X) hτ4 (by linarith) hσ2 hXlow
  have hsplit := sum_Icc_one_eq_initial_add_dyadic
    (fun k : ℕ => ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))) N₁ J
  have hinit := norm_sum_initial_le (σ := σ) (τ := τ) (θ := 0) hN₁1 le_rfl (by simp) (by linarith)
  have hdy := norm_dyadic_le_one hL hτbig hσ1 hN₁low hJmin
  have hsum : ‖∑ k ∈ Finset.Icc 1 X, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      Real.exp (1 / 50) * (1 + Real.log N₁) +
        (12 * Real.exp 19 * (1 + K / Real.log 2) + 200 * (1 + 2 / Real.log 2) +
          2560 * (1 + 1 / (1 / (3 * (2 : ℝ) ^ 24) * Real.log 2))) := by
    rw [hXdef, hsplit]
    exact (norm_add_le _ _).trans (add_le_add hinit hdy)
  calc ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
      ≤ ‖∑ k ∈ Finset.Icc 1 X, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ +
          (X : ℝ) ^ (1 - σ) / ‖(σ : ℂ) + (τ : ℂ) * Complex.I - 1‖ +
          ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ * ((X : ℝ) ^ (-σ) / σ) := htrunc
    _ ≤ (Real.exp (1 / 50) * (1 + Real.log N₁) +
        (12 * Real.exp 19 * (1 + K / Real.log 2) + 200 * (1 + 2 / Real.log 2) +
          2560 * (1 + 1 / (1 / (3 * (2 : ℝ) ^ 24) * Real.log 2)))) + 1 + 4 := by gcongr
    _ ≤ vkOneLineConstant * (1 + K) := pieces_le hK0.le hlogN₁

/-- **`|ζ(σ + iτ)| ≪ (log|τ| · log log|τ|)^{2/3}` on `1 ≤ σ ≤ 2`.** -/
theorem exists_norm_riemannZeta_le_two_thirds :
    ∃ C : ℝ, 0 < C ∧ ∀ τ σ : ℝ, Real.exp (Real.exp 30) ≤ |τ| → 1 ≤ σ → σ ≤ 2 →
      ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        C * (Real.log |τ| * Real.log (Real.log |τ|)) ^ ((2 : ℝ) / 3) := by
  have hC0 := vkOneLineConstant_pos
  refine ⟨vkOneLineConstant * (1 + (746496 : ℝ) ^ ((1 : ℝ) / 3)), by positivity,
    fun τ σ hτ hσ1 hσ2 => ?_⟩
  have hL : Real.exp 30 ≤ Real.log |τ| := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) hτ
  have hl := one_le_log_of_exp_thirty_le hL
  have hL1 : 1 ≤ Real.log |τ| := le_trans (Real.one_le_exp (by norm_num)) hL
  have hu1 : 1 ≤ Real.log |τ| * Real.log (Real.log |τ|) := by nlinarith only [hl, hL1]
  have hu0 : 0 ≤ Real.log |τ| * Real.log (Real.log |τ|) := by linarith only [hu1]
  have hsym : ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ =
      ‖riemannZeta ((σ : ℂ) + ((|τ| : ℝ) : ℂ) * Complex.I)‖ := by
    rcases le_or_gt 0 τ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h]
      have e : (σ : ℂ) + (τ : ℂ) * Complex.I =
          (starRingEnd ℂ) ((σ : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp
      rw [e, riemannZeta_conj, RCLike.norm_conj]
  rw [hsym]
  refine (norm_riemannZeta_le_vkCube hτ hσ1 hσ2).trans ?_
  have hK : vkCubeScale |τ| = (746496 : ℝ) ^ ((1 : ℝ) / 3) *
      (Real.log |τ| * Real.log (Real.log |τ|)) ^ ((2 : ℝ) / 3) := by
    unfold vkCubeScale
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hu0]
    norm_num
  have hpow : 1 ≤ (Real.log |τ| * Real.log (Real.log |τ|)) ^ ((2 : ℝ) / 3) :=
    Real.one_le_rpow hu1 (by norm_num)
  rw [hK, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC0.le
  have : 0 ≤ (746496 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  nlinarith only [this, hpow]

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

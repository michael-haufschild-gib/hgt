import GaloisForLFunctions.RHTower.RobinCriterionRiemann

/-!
# Lagarias's criterion

The Riemann hypothesis holds if and only if `σ(n) ≤ H_n + e^{H_n} log H_n` for all large `n`,
`H_n = 1 + 1/2 + ⋯ + 1/n`.

Since `γ < H_n - log n`, the right side exceeds `e^γ n log log n`, so Robin's inequality implies
Lagarias's.  Conversely `H_L < γ + log(L + 1)` shows that Lagarias's inequality at
`L = lcm(1, …, n)` bounds the Robin defect there by `O(1/(ψ(n) log ψ(n))) ≤ 1/(√n log n)`, which
suffices for RH.
-/

open Filter Topology
open ArithmeticFunction (sigma)
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- `γ + log n < H_n` for `n ≥ 1`. -/
theorem eulerMascheroni_add_log_lt_harmonic {n : ℕ} (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant + Real.log n < harmonic n := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [Real.eulerMascheroniSeq', if_neg (by omega)] at h
  linarith

/-- `H_n < γ + log(n + 1)`. -/
theorem harmonic_lt_eulerMascheroni_add_log (n : ℕ) :
    (harmonic n : ℝ) < Real.eulerMascheroniConstant + Real.log (n + 1) := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  rw [Real.eulerMascheroniSeq] at h
  linarith

/-- **Robin implies Lagarias** for `n ≥ 3`. -/
theorem exp_mul_log_log_le_lagarias {n : ℕ} (hn : 3 ≤ n) :
    Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)
      ≤ harmonic n + Real.exp (harmonic n) * Real.log (harmonic n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hH := eulerMascheroni_add_log_lt_harmonic (by omega : 1 ≤ n)
  have hγ : 0 < Real.eulerMascheroniConstant := by
    have := Real.one_half_lt_eulerMascheroniConstant; linarith
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hll : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlog1
  have hHpos : (0 : ℝ) < harmonic n := by linarith
  have h1 : Real.exp Real.eulerMascheroniConstant * n ≤ Real.exp (harmonic n) := by
    rw [← Real.exp_log hn0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hH.le
  have h2 : Real.log (Real.log n) ≤ Real.log (harmonic n) :=
    Real.log_le_log (by linarith) (by linarith)
  calc Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)
      ≤ Real.exp (harmonic n) * Real.log (Real.log n) := mul_le_mul_of_nonneg_right h1 hll
    _ ≤ Real.exp (harmonic n) * Real.log (harmonic n) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ ≤ harmonic n + Real.exp (harmonic n) * Real.log (harmonic n) := by linarith

theorem exp_eulerMascheroni_lt_two : Real.exp Real.eulerMascheroniConstant < 2 := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := Real.log_two_gt_d9
  calc Real.exp Real.eulerMascheroniConstant < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr (by linarith)
    _ = 2 := Real.exp_log (by norm_num)

/-- **Lagarias's inequality at `L_n` bounds the Robin defect.**  If
`σ(L) ≤ H_L + e^{H_L} log H_L` at `L = lcm(1, …, n)`, `λ = ψ(n) ≥ 8`, and `7/λ ≤ δ log λ`, then
`D(n) ≤ δ`. -/
theorem robinLcmDefect_le_of_lagarias {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hlam8 : 8 ≤ Chebyshev.psi n) (hkey : 7 / Chebyshev.psi n ≤ Real.log (Chebyshev.psi n) * δ)
    (hLag : (sigma 1 (Nat.lcmUpto n) : ℝ)
      ≤ harmonic (Nat.lcmUpto n)
        + Real.exp (harmonic (Nat.lcmUpto n)) * Real.log (harmonic (Nat.lcmUpto n))) :
    robinLcmDefect n ≤ δ := by
  set L := Nat.lcmUpto n with hL
  set lam := Chebyshev.psi n with hlam
  have hlamL : Real.log (L : ℝ) = lam := (Chebyshev.psi_eq_log_lcmUpto n).symm
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.lcmUpto_pos n
  have hLexp : (L : ℝ) = Real.exp lam := by rw [← hlamL, Real.exp_log hL0]
  have hlam0 : 0 < lam := by linarith
  have hloglam : 1 ≤ Real.log lam := by
    rw [Real.le_log_iff_exp_le hlam0]; have := Real.exp_one_lt_d9; linarith
  have hγ0 : 0 < Real.eulerMascheroniConstant := by
    have := Real.one_half_lt_eulerMascheroniConstant; linarith
  have hγ1 := Real.eulerMascheroniConstant_lt_two_thirds
  have heγ := exp_eulerMascheroni_lt_two
  have heγ1 : 1 ≤ Real.exp Real.eulerMascheroniConstant := Real.one_le_exp hγ0.le
  -- size of `L`
  have hcube : lam ^ 3 / 6 ≤ (L : ℝ) := by
    rw [hLexp]
    have := Real.pow_div_factorial_le_exp lam hlam0.le 3
    have e : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rwa [e] at this
  have hL1 : lam * (lam + 1) ≤ (L : ℝ) := by nlinarith
  have hL2 : lam * Real.log lam ≤ (L : ℝ) := by
    have := Real.log_le_sub_one_of_pos hlam0
    nlinarith
  have hL3 : (3 : ℝ) ≤ L := by nlinarith
  -- the harmonic number of `L`
  have hH1 := eulerMascheroni_add_log_lt_harmonic (Nat.lcmUpto_pos n)
  have hH2 := harmonic_lt_eulerMascheroni_add_log L
  rw [← hL] at hH1
  rw [hlamL] at hH1
  set H := (harmonic L : ℝ) with hHdef
  have hlogL1 : Real.log ((L : ℝ) + 1) ≤ lam + 1 / L := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((L : ℝ) + 1) / L by positivity)
    rw [Real.log_div (by positivity) hL0.ne', hlamL] at h1
    have e : ((L : ℝ) + 1) / L - 1 = 1 / L := by field_simp; ring
    linarith
  have hHpos : 1 < H := by linarith
  have hHup : H ≤ lam + 1 := by
    have : 1 / (L : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hL3
    linarith
  have hlogH : Real.log H ≤ Real.log lam + 1 / lam := by
    have h1 : Real.log H ≤ Real.log (lam + 1) := Real.log_le_log (by linarith) hHup
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (lam + 1) / lam by positivity)
    rw [Real.log_div (by linarith) hlam0.ne'] at h2
    have e : (lam + 1) / lam - 1 = 1 / lam := by field_simp; ring
    linarith
  have hlogHpos : 0 < Real.log H := Real.log_pos hHpos
  have hexpH : Real.exp H ≤ Real.exp Real.eulerMascheroniConstant * ((L : ℝ) + 1) := by
    rw [← Real.exp_log (show (0 : ℝ) < (L : ℝ) + 1 by positivity), ← Real.exp_add]
    exact Real.exp_le_exp.mpr hH2.le
  set A := Real.exp Real.eulerMascheroniConstant with hA
  set ℓ := Real.log lam with hℓ
  have hσ : (sigma 1 L : ℝ) ≤ (lam + 1) + A * ((L : ℝ) + 1) * (ℓ + 1 / lam) := by
    have h1 : Real.exp H * Real.log H ≤ A * ((L : ℝ) + 1) * (ℓ + 1 / lam) :=
      mul_le_mul hexpH hlogH hlogHpos.le (by positivity)
    linarith
  have hσpos : (0 : ℝ) < sigma 1 L := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 L (Nat.lcmUpto_ne_zero n)
  -- `σ(L)/L ≤ A ℓ e^δ`
  have hb1 : (lam + 1) / L ≤ 1 / lam := by
    rw [div_le_div_iff₀ hL0 hlam0]; linarith
  have hb2 : A * ℓ / L ≤ 2 / lam := by
    rw [div_le_div_iff₀ hL0 hlam0]
    have : A * ℓ * lam ≤ 2 * (ℓ * lam) := by
      have := mul_le_mul_of_nonneg_right heγ.le (show 0 ≤ ℓ * lam by positivity)
      linarith
    nlinarith
  have hb3 : A * (1 + 1 / L) / lam ≤ 8 / 3 / lam := by
    refine div_le_div_of_nonneg_right ?_ hlam0.le
    have : 1 / (L : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hL3
    have h0 : 0 ≤ 1 + 1 / (L : ℝ) := by positivity
    nlinarith
  have hsplit : ((lam + 1) + A * ((L : ℝ) + 1) * (ℓ + 1 / lam)) / L
      = (lam + 1) / L + A * ℓ + A * ℓ / L + A * (1 + 1 / L) / lam := by
    field_simp
    ring
  have hdiv : (sigma 1 L : ℝ) / L ≤ A * ℓ + 7 / lam := by
    calc (sigma 1 L : ℝ) / L ≤ ((lam + 1) + A * ((L : ℝ) + 1) * (ℓ + 1 / lam)) / L :=
          div_le_div_of_nonneg_right hσ hL0.le
      _ = (lam + 1) / L + A * ℓ + A * ℓ / L + A * (1 + 1 / L) / lam := hsplit
      _ ≤ 1 / lam + A * ℓ + 2 / lam + 8 / 3 / lam := by linarith
      _ ≤ A * ℓ + 7 / lam := by
          have : 0 < 1 / lam := by positivity
          have e : 1 / lam + A * ℓ + 2 / lam + 8 / 3 / lam = A * ℓ + 17 / 3 * (1 / lam) := by
            ring
          have e2 : 7 / lam = 7 * (1 / lam) := by ring
          rw [e, e2]; linarith
  have hfin : (sigma 1 L : ℝ) / L ≤ A * ℓ * Real.exp δ := by
    have h1 : 7 / lam ≤ A * ℓ * δ := by
      have : ℓ * δ ≤ A * ℓ * δ := by
        have := mul_le_mul_of_nonneg_right heγ1 (show 0 ≤ ℓ * δ by positivity)
        linarith
      linarith
    have h2 : A * ℓ * (1 + δ) ≤ A * ℓ * Real.exp δ := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := Real.add_one_le_exp δ; linarith
    nlinarith
  -- conclusion
  have hlogd : Real.log ((sigma 1 L : ℝ) / L) ≤ Real.eulerMascheroniConstant + Real.log ℓ + δ := by
    have h1 := Real.log_le_log (div_pos hσpos hL0) hfin
    rw [Real.log_mul (by positivity) (Real.exp_pos δ).ne', Real.log_mul (Real.exp_pos _).ne'
      (by positivity), Real.log_exp, Real.log_exp] at h1
    exact h1
  unfold robinLcmDefect
  rw [← hL, ← hlam]
  linarith

/-- **Lagarias's criterion.**  The Riemann hypothesis holds if and only if
`σ(n) ≤ H_n + e^{H_n} log H_n` for all large `n`. -/
theorem riemannHypothesis_iff_eventually_lagarias :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop,
      (sigma 1 n : ℝ) ≤ harmonic n + Real.exp (harmonic n) * Real.log (harmonic n) := by
  constructor
  · intro hRH
    filter_upwards [eventually_robin_of_riemannHypothesis hRH, eventually_ge_atTop 3]
      with n hR hn
    exact hR.le.trans (exp_mul_log_log_le_lagarias hn)
  · intro h
    refine riemannHypothesis_of_eventually_robinLcmDefect_le ?_
    have hlcm : Tendsto Nat.lcmUpto atTop atTop :=
      tendsto_atTop_mono' atTop (eventually_ge_atTop 1 |>.mono fun n hn => le_lcmUpto hn)
        tendsto_id
    have hθ := tendsto_natCast_atTop_atTop.eventually eventually_two_fifths_le_theta
    filter_upwards [hlcm.eventually h, hθ, eventually_ge_atTop 1225] with n hLag hθn hn
    have hn0 : (1225 : ℝ) ≤ n := by exact_mod_cast hn
    have hψ : 2 / 5 * (n : ℝ) ≤ Chebyshev.psi n := hθn.trans (Chebyshev.theta_le_psi _)
    have hsn : 35 ≤ Real.sqrt (n : ℝ) := by
      rw [show (35 : ℝ) = Real.sqrt 1225 by rw [show (1225 : ℝ) = 35 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hn0
    have hnn : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt (by positivity)
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hψ8 : 8 ≤ Chebyshev.psi n := by linarith
    have hψ0 : 0 < Chebyshev.psi n := by linarith
    have hlogψ : Real.log n / 2 ≤ Real.log (Chebyshev.psi n) := by
      have h1 : Real.sqrt (n : ℝ) ≤ Chebyshev.psi n := by nlinarith
      have h2 := Real.log_le_log (by linarith) h1
      rw [Real.log_sqrt (by positivity)] at h2
      exact h2
    refine robinLcmDefect_le_of_lagarias (by positivity) hψ8 ?_ hLag
    -- `7/ψ ≤ log ψ/(√n log n)`
    have hD : 0 < Real.sqrt (n : ℝ) * Real.log n := by positivity
    have h1 : 7 / Chebyshev.psi n ≤ 35 / (2 * n) := by
      rw [div_le_div_iff₀ hψ0 (by positivity)]; nlinarith
    have h2 : 35 / (2 * (n : ℝ)) ≤ 1 / (2 * Real.sqrt n) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h3 : 1 / (2 * Real.sqrt (n : ℝ))
        ≤ Real.log (Chebyshev.psi n) * (1 / (Real.sqrt n * Real.log n)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hD]
      nlinarith
    linarith

end

end RHTower

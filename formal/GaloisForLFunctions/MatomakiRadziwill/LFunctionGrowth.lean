import GaloisForLFunctions.MatomakiRadziwill.HurwitzGrowth
import GaloisForLFunctions.RHTower.DirichletLLogStrip

/-!
# Vinogradov–Korobov growth of Dirichlet `L`-functions

For a nonprincipal character `χ` mod `q`, `τ ≥ e^{e^{30}}` and `1 − θ(log τ) ≤ σ ≤ 2`,

`‖L(σ + iτ, χ)‖ ≤ (q³ + 56q + qC) log τ`   (`norm_LFunction_le_vinogradovKorobov`),

`C` the Hurwitz growth constant.  Truncate at `M = qT`, `T = ⌈τ²/q⌉`
(`RHTower.norm_LFunction_sub_character_partial_le`: the tail is at most `56q`), split the partial sum
into residues, `Σ_{m≤qT} χ(m)m^{-s} = Σ_{a≤q} χ(a) q^{-s} Σ_{k<T} (k + a/q)^{-s}`, and bound each
progression by `(a/q)^{-σ} ≤ q²` plus the Hurwitz partial sum (`norm_hurwitzPartial_le`).
-/

open Finset RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- Splitting `[1, qT]` into the progressions `qk + a`, `1 ≤ a ≤ q`, `k < T`. -/
theorem sum_Icc_mul_eq_sum_residues (F : ℕ → ℂ) (q T : ℕ) :
    ∑ m ∈ Finset.Icc 1 (q * T), F m = ∑ a ∈ Finset.Icc 1 q, ∑ k ∈ Finset.range T, F (q * k + a) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h1 : Finset.Icc 1 (q * (T + 1)) = Finset.Ioc 0 (q * T + q) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; constructor <;> intro h <;> constructor <;>
        [omega; nlinarith [h.2]; omega; nlinarith [h.2]]
    have h2 : Finset.Icc 1 (q * T) = Finset.Ioc 0 (q * T) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have hle : q * T ≤ q * T + q := Nat.le_add_right _ _
    rw [h1, ← Finset.sum_Ioc_consecutive F (Nat.zero_le _) hle, ← h2, ih]
    have hmap := Finset.map_add_left_Ioc 0 q (q * T)
    rw [add_zero] at hmap
    rw [← hmap, Finset.sum_map]
    have h3 : Finset.Icc 1 q = Finset.Ioc 0 q := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [← h3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_range_succ]
    rfl

/-- The truncated `L`-series as a sum over `1 ≤ m ≤ M`. -/
theorem dirichletPartialSum_eq_sum_Icc {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) (s : ℂ) :
    RHTower.dirichletPartialSum (fun j => χ (j + 1)) M s =
      ∑ m ∈ Finset.Icc 1 M, χ m * (((m : ℝ) : ℂ)) ^ (-s) := by
  induction M with
  | zero => simp [RHTower.dirichletPartialSum]
  | succ M ih =>
    rw [RHTower.dirichletPartialSum, Finset.sum_range_succ, ← RHTower.dirichletPartialSum, ih,
      Finset.sum_Icc_succ_top (by omega)]
    congr 1
    push_cast
    rfl

/-- `‖x^{-s}‖ = x^{-Re s}` for `x > 0`. -/
theorem norm_ofReal_cpow_neg {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖((x : ℝ) : ℂ) ^ (-s)‖ = x ^ (-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- `Σ_{k<n} g(k+1) = Σ_{1≤k≤n} g(k)`. -/
theorem sum_range_shift_eq_sum_Icc (g : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range n, g (k + 1) = ∑ k ∈ Finset.Icc 1 n, g k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-- One progression `qk + a`, `k < T`: at most `q² + C log τ`. -/
theorem norm_sum_progression_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {τ σ : ℝ}
    (hτ : Real.exp (Real.exp 30) ≤ τ)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) (hσ2 : σ ≤ 2)
    {a T : ℕ} (ha1 : 1 ≤ a) (haq : a ≤ q) (hT1 : 1 ≤ T) (hTτ : ((T - 1 : ℕ) : ℝ) ≤ 2 * τ ^ 2) :
    ‖∑ k ∈ Finset.range T, χ ((q * k + a : ℕ) : ZMod q) *
        ((((q * k + a : ℕ) : ℝ)) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      (q : ℝ) ^ 2 + hurwitzGrowthConstant * Real.log τ := by
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hL : Real.exp 30 ≤ Real.log τ := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) hτ
  have hθ1 : vinogradovKorobovWidth (Real.log τ) ≤ 1 / 100 :=
    (vinogradovKorobovWidth_le hL).trans (by norm_num)
  have hσ0 : (99 / 100 : ℝ) ≤ σ := by linarith
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  set α : ℝ := (a : ℝ) / q with hαdef
  have ha1R : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hα0 : 0 < α := by rw [hαdef]; positivity
  have hα1 : α ≤ 1 := by
    rw [hαdef, div_le_one (by positivity)]; exact_mod_cast haq
  have hterm : ∀ k ∈ Finset.range T, χ ((q * k + a : ℕ) : ZMod q) *
      ((((q * k + a : ℕ) : ℝ)) : ℂ) ^ (-s) =
        χ (a : ZMod q) * ((((q : ℝ)) : ℂ) ^ (-s) * ((((k : ℝ) + α : ℝ)) : ℂ) ^ (-s)) := by
    intro k _
    have hχ' : χ ((q * k + a : ℕ) : ZMod q) = χ (a : ZMod q) := by
      congr 1
      push_cast
      rw [ZMod.natCast_self, zero_mul, zero_add]
    rw [hχ']
    congr 1
    have hcast : (((q * k + a : ℕ) : ℝ)) = (q : ℝ) * ((k : ℝ) + α) := by
      rw [hαdef]; push_cast; field_simp
    rw [hcast, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _)
      (by positivity)]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum, norm_mul, norm_mul]
  have hχa : ‖χ (a : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hqs : ‖((((q : ℝ)) : ℂ)) ^ (-s)‖ ≤ 1 := by
    rw [norm_ofReal_cpow_neg (by positivity), hsre]
    exact Real.rpow_le_one_of_one_le_of_nonpos hqR (by linarith)
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  rw [Finset.sum_range_succ', sum_range_shift_eq_sum_Icc
    (fun k => ((((k : ℝ) + α : ℝ)) : ℂ) ^ (-s)) T']
  have hhur := norm_hurwitzPartial_le hτ hσ1 hα0.le hα1 (K := T') (by
    have : ((T' + 1 - 1 : ℕ) : ℝ) = T' := by congr 1
    rw [this] at hTτ; exact hTτ)
  have hzero : ‖((((((0 : ℕ) : ℝ) + α : ℝ)) : ℂ)) ^ (-s)‖ ≤ (q : ℝ) ^ 2 := by
    rw [Nat.cast_zero, zero_add, norm_ofReal_cpow_neg hα0, hsre]
    have h1 : α ^ (-σ) ≤ (1 / (q : ℝ)) ^ (-σ) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      rw [hαdef]
      exact div_le_div_of_nonneg_right ha1R (by positivity)
    have h2 : (1 / (q : ℝ)) ^ (-σ) = (q : ℝ) ^ σ := by
      rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
    have h3 : (q : ℝ) ^ σ ≤ (q : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hqR hσ2
    rw [Real.rpow_two] at h3
    linarith
  have hsum : ‖∑ k ∈ Finset.Icc 1 T', ((((k : ℝ) + α : ℝ)) : ℂ) ^ (-s) +
      ((((((0 : ℕ) : ℝ) + α : ℝ)) : ℂ)) ^ (-s)‖ ≤ (q : ℝ) ^ 2 + hurwitzGrowthConstant * Real.log τ := by
    refine (norm_add_le _ _).trans ?_
    linarith
  have hn0 : 0 ≤ ‖∑ k ∈ Finset.Icc 1 T', ((((k : ℝ) + α : ℝ)) : ℂ) ^ (-s) +
      ((((((0 : ℕ) : ℝ) + α : ℝ)) : ℂ)) ^ (-s)‖ := norm_nonneg _
  calc ‖χ (a : ZMod q)‖ * (‖((((q : ℝ)) : ℂ)) ^ (-s)‖ *
        ‖∑ k ∈ Finset.Icc 1 T', ((((k : ℝ) + α : ℝ)) : ℂ) ^ (-s) +
          ((((((0 : ℕ) : ℝ) + α : ℝ)) : ℂ)) ^ (-s)‖)
      ≤ 1 * (1 * ((q : ℝ) ^ 2 + hurwitzGrowthConstant * Real.log τ)) := by
        gcongr
    _ = (q : ℝ) ^ 2 + hurwitzGrowthConstant * Real.log τ := by ring

/-- **Vinogradov–Korobov growth of `L(s, χ)`.** For nonprincipal `χ` mod `q`,
`τ ≥ max(e^{e^{30}}, q)` and `1 − θ(log τ) ≤ σ ≤ 2`: `‖L(σ+iτ, χ)‖ ≤ (q³ + 56q + qC) log τ`. -/
theorem norm_LFunction_le_vinogradovKorobov {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {τ σ : ℝ} (hτ : Real.exp (Real.exp 30) ≤ τ) (hτq : (q : ℝ) ≤ τ)
    (hσ1 : 1 - vinogradovKorobovWidth (Real.log τ) ≤ σ) (hσ2 : σ ≤ 2) :
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      ((q : ℝ) ^ 3 + 56 * q + q * hurwitzGrowthConstant) * Real.log τ := by
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hsdef
  have hτ0 : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hτ
  have hτ1 : (1 : ℝ) ≤ τ := le_trans (Real.one_le_exp (Real.exp_pos _).le) hτ
  have hL : Real.exp 30 ≤ Real.log τ := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) hτ
  have hL1 : (1 : ℝ) ≤ Real.log τ := le_trans (Real.one_le_exp (by norm_num)) hL
  have hθ1 : vinogradovKorobovWidth (Real.log τ) ≤ 1 / 100 :=
    (vinogradovKorobovWidth_le hL).trans (by norm_num)
  have hσ0 : (99 / 100 : ℝ) ≤ σ := by linarith
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  -- truncation at `M = qT`, `T = ⌈τ²/q⌉`
  set T : ℕ := ⌈τ ^ 2 / q⌉₊ with hTdef
  have hT : τ ^ 2 / q ≤ T := Nat.le_ceil _
  have hTup : (T : ℝ) < τ ^ 2 / q + 1 := Nat.ceil_lt_add_one (by positivity)
  have hM : τ ^ 2 ≤ ((q * T : ℕ) : ℝ) := by
    push_cast
    rw [div_le_iff₀ (by positivity)] at hT
    linarith
  have hT1 : 1 ≤ T := by
    have h1 : (1 : ℝ) ≤ τ ^ 2 / q := by
      rw [le_div_iff₀ (by positivity), one_mul]
      nlinarith
    have : (1 : ℝ) ≤ T := h1.trans hT
    exact_mod_cast this
  have hTτ : ((T - 1 : ℕ) : ℝ) ≤ 2 * τ ^ 2 := by
    rw [Nat.cast_sub hT1, Nat.cast_one]
    have h1 : τ ^ 2 / q ≤ τ ^ 2 := div_le_self (by positivity) hqR
    nlinarith
  have htail := RHTower.norm_LFunction_sub_character_partial_le hχ (s := s)
    (by rw [hsre]; linarith) (q * T)
  rw [hsre, dirichletPartialSum_eq_sum_Icc] at htail
  have hsnorm : ‖s‖ ≤ 2 + τ := by
    rw [hsdef]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0]
    linarith
  have htail' : 2 * q * (1 + ‖s‖ / σ) * (((q * T : ℕ) : ℝ) + 1) ^ (-σ) ≤ 56 * q := by
    have h1 : 1 + ‖s‖ / σ ≤ 7 * τ := by
      have h2 : ‖s‖ / σ ≤ (2 + τ) / (99 / 100) :=
        div_le_div₀ (by linarith) hsnorm (by norm_num) hσ0
      have h3 : (2 + τ) / (99 / 100) ≤ 6 * τ := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      linarith
    have h2 : (((q * T : ℕ) : ℝ) + 1) ^ (-σ) ≤ (τ ^ 2) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h3 : τ * (τ ^ 2) ^ (-σ) ≤ 1 := by
      rw [← Real.rpow_natCast τ 2, ← Real.rpow_mul hτ0.le]
      calc τ * τ ^ (((2 : ℕ) : ℝ) * -σ) = τ ^ (1 + ((2 : ℕ) : ℝ) * -σ) := by
            rw [Real.rpow_add hτ0, Real.rpow_one]
        _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by push_cast; linarith)
    have h0 : 0 ≤ (((q * T : ℕ) : ℝ) + 1) ^ (-σ) := by positivity
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    calc 2 * q * (1 + ‖s‖ / σ) * (((q * T : ℕ) : ℝ) + 1) ^ (-σ)
        ≤ 2 * q * (7 * τ) * (τ ^ 2) ^ (-σ) := by gcongr
      _ = 14 * q * (τ * (τ ^ 2) ^ (-σ)) := by ring
      _ ≤ 14 * q * 1 := by gcongr
      _ ≤ 56 * q := by linarith
  -- the partial sum, split into progressions
  rw [sum_Icc_mul_eq_sum_residues (fun m => χ m * (((m : ℝ) : ℂ)) ^ (-s)) q T] at htail
  have hpartial : ‖∑ a ∈ Finset.Icc 1 q, ∑ k ∈ Finset.range T,
      χ ((q * k + a : ℕ) : ZMod q) * ((((q * k + a : ℕ) : ℝ)) : ℂ) ^ (-s)‖ ≤
        q * ((q : ℝ) ^ 2 + hurwitzGrowthConstant * Real.log τ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a ∈ Finset.Icc 1 q, ‖∑ k ∈ Finset.range T,
          χ ((q * k + a : ℕ) : ZMod q) * ((((q * k + a : ℕ) : ℝ)) : ℂ) ^ (-s)‖
        ≤ ∑ _a ∈ Finset.Icc 1 q, ((q : ℝ) ^ 2 + hurwitzGrowthConstant * Real.log τ) :=
          Finset.sum_le_sum fun a ha => norm_sum_progression_le χ hτ hσ1 hσ2
            (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2 hT1 hTτ
      _ = q * ((q : ℝ) ^ 2 + hurwitzGrowthConstant * Real.log τ) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          congr 1
  have hC0 : 0 ≤ hurwitzGrowthConstant := by
    unfold hurwitzGrowthConstant; have := hurwitzBlockConstant_nonneg; linarith
  have htri := norm_sub_norm_le (DirichletCharacter.LFunction χ s)
    (∑ a ∈ Finset.Icc 1 q, ∑ k ∈ Finset.range T,
      χ ((q * k + a : ℕ) : ZMod q) * ((((q * k + a : ℕ) : ℝ)) : ℂ) ^ (-s))
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h3 : (q : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 * Real.log τ := le_mul_of_one_le_right (by positivity) hL1
  have h56 : 56 * (q : ℝ) ≤ 56 * q * Real.log τ := le_mul_of_one_le_right (by positivity) hL1
  nlinarith [htail, htail', hpartial, htri]

end

end GaloisForLFunctions.MatomakiRadziwill

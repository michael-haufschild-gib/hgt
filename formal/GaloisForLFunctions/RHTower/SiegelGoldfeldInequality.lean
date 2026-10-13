import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Goldfeld's inequality for Dirichlet series with nonnegative coefficients

Let `F(s) = ∑ a_n n^{-s}` have nonnegative coefficients with `a_1 = 1`, converge absolutely for
`Re s > 1`, and suppose `F(s) − λ/(s − 1) = G(s)` there for an entire function `G` and some
`λ ≥ 0`.  If `|G| ≤ M` on the circle `|s − 2| = 3/2`, then for `7/8 ≤ σ < 1`

`G(σ) − λ/(1 − σ) ≥ 1/2 − 2λ(2 − σ)^K/(1 − σ)`

for every `K` with `4M(3/4)^K ≤ 1/2` (`goldfeld_lower_bound`), and in particular
`G(σ) − λ/(1 − σ) ≥ 1/2 − 2e λ (8M + 8)^{4(1−σ)}/(1 − σ)` (`goldfeld_lower_bound'`).

Proof.  Expand `G` around `2`.  Its `m`-th Taylor coefficient is `(−1)^m(β_m − λ)` with
`β_m = (−1)^m F^{(m)}(2)/m! ≥ 0` (nonnegative coefficients) and `β_0 = F(2) ≥ a_1 = 1`, because the
Taylor coefficients of `λ/(s − 1)` at `2` are `λ(−1)^m`.  So
`G(σ) = ∑_m (2 − σ)^m (β_m − λ)`.  The terms with `m < K` are at least `−λ(2−σ)^m` (and `1 − λ` for
`m = 0`); the Cauchy estimate `|β_m − λ| ≤ M (2/3)^m` bounds the tail by `4M(3/4)^K`.

This is the analytic core of Siegel's theorem `L(1, χ) ≫_ε q^{−ε}`.
-/

open Complex Nat

noncomputable section

namespace RHTower

open scoped ComplexOrder

/-- The value at `2` of a Dirichlet series with nonnegative coefficients and `a_1 = 1` has real
part at least `1`. -/
lemma one_le_re_LSeries_two {a : ℕ → ℂ} (ha : 0 ≤ a) (ha1 : a 1 = 1)
    (hsum : LSeriesSummable a 2) : 1 ≤ (LSeries a 2).re := by
  have hs : HasSum (fun n => (LSeries.term a 2 n).re) (LSeries a 2).re :=
    Complex.hasSum_re hsum.hasSum
  have hnn : ∀ n, 0 ≤ (LSeries.term a 2 n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have han := ha n
      rw [LSeries.term_of_ne_zero hn]
      have hre : (a n).im = 0 := (Complex.nonneg_iff.mp han).2.symm
      have hre' : 0 ≤ (a n).re := (Complex.nonneg_iff.mp han).1
      have hcp : ((n : ℂ) ^ (2 : ℂ)) = ((n : ℝ) ^ 2 : ℝ) := by
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]; push_cast; ring
      rw [hcp, Complex.div_ofReal_re]
      exact div_nonneg hre' (by positivity)
  have h1 : (LSeries.term a 2 1).re = 1 := by
    rw [LSeries.term_of_ne_zero one_ne_zero, ha1]; simp
  calc (1 : ℝ) = (LSeries.term a 2 1).re := h1.symm
    _ ≤ (LSeries a 2).re := le_hasSum hs 1 fun n _ => hnn n

lemma iteratedDeriv_inv_sub_one_two (m : ℕ) :
    iteratedDeriv m (fun s : ℂ => (s - 1)⁻¹) 2 = (-1) ^ m * (m ! : ℂ) := by
  rw [iteratedDeriv_eq_iterate]
  have h := iter_deriv_inv_linear_sub (𝕜 := ℂ) m 1 1
  simp only [one_mul, one_pow, mul_one] at h
  rw [h]
  norm_num

/-- **Goldfeld's inequality.** -/
theorem goldfeld_lower_bound {a : ℕ → ℂ} (ha : 0 ≤ a) (ha1 : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {res M : ℝ} (hres : 0 ≤ res)
    (hF : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + res / (s - 1))
    (hM : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G z‖ ≤ M) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : 4 * M * (3 / 4 : ℝ) ^ K ≤ 1 / 2) {σ : ℝ} (hσ1 : 7 / 8 ≤ σ) (hσ2 : σ < 1) :
    1 / 2 - 2 * res * (2 - σ) ^ K / (1 - σ) ≤ (G σ).re - res / (1 - σ) := by
  -- the open half-plane of absolute convergence contains 2
  set U : Set ℂ := {s | LSeries.abscissaOfAbsConv a < s.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const
    (continuous_coe_real_ereal.comp Complex.continuous_re)
  have h12 : ((1 : ℝ) : EReal) < ((2 : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by norm_num)
  have habs2 : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) :=
    lt_of_le_of_lt (by simpa using habs) h12
  have h2U : (2 : ℂ) ∈ U := by
    simp only [hU, Set.mem_setOf_eq]
    simpa using habs2
  have hV : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hEq : G =ᶠ[nhds 2] fun s => LSeries a s - res * (s - 1)⁻¹ := by
    filter_upwards [hV] with s hs
    rw [hF s hs, div_eq_mul_inv]; ring
  have hcdF : ∀ m : ℕ, ContDiffAt ℂ m (LSeries a) 2 := fun m =>
    ((LSeries_differentiableOn a).contDiffOn hUopen).contDiffAt (hUopen.mem_nhds h2U)
  have hcdI : ∀ m : ℕ, ContDiffAt ℂ m (fun s : ℂ => (s - 1)⁻¹) 2 := fun m =>
    (contDiffAt_id.sub contDiffAt_const).inv (by norm_num)
  -- Taylor coefficients of G at 2
  have hDG : ∀ m : ℕ, iteratedDeriv m G 2
      = iteratedDeriv m (LSeries a) 2 - res * ((-1) ^ m * (m ! : ℂ)) := by
    intro m
    rw [hEq.iteratedDeriv_eq m]
    have : (fun s => LSeries a s - (res : ℂ) * (s - 1)⁻¹)
        = LSeries a - fun s => (res : ℂ) * (s - 1)⁻¹ := rfl
    rw [this, iteratedDeriv_sub (hcdF m) (contDiffAt_const.mul (hcdI m)),
      iteratedDeriv_const_mul (res : ℂ) (hcdI m), iteratedDeriv_inv_sub_one_two]
  set β : ℕ → ℂ := fun m => (m ! : ℂ)⁻¹ * ((-1) ^ m * iteratedDeriv m (LSeries a) 2) with hβ
  have hβnn : ∀ m, 0 ≤ β m := by
    intro m
    have h := LSeries.iteratedDeriv_alternating ha (x := 2) habs2 m
    simp only [Complex.ofReal_ofNat] at h
    have hf : (0 : ℂ) ≤ (m ! : ℂ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      exact Complex.zero_le_real.mpr (by positivity)
    exact mul_nonneg hf h
  have hβ0 : 1 ≤ (β 0).re := by
    simp only [hβ, factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul, iteratedDeriv_zero]
    exact one_le_re_LSeries_two ha ha1 (LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa using habs2))
  -- the Taylor series at σ
  have hT := Complex.hasSum_taylorSeries_of_entire hG 2 (σ : ℂ)
  have hterm : ∀ m : ℕ, (m ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ m • iteratedDeriv m G 2
      = (((2 - σ) ^ m : ℝ) : ℂ) * (β m - res) := by
    intro m
    rw [hDG m, smul_eq_mul, smul_eq_mul]
    have hfac : (m ! : ℂ) ≠ 0 := by exact_mod_cast (factorial_ne_zero m)
    have hsq : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
    simp only [hβ]
    push_cast
    rw [show ((σ : ℂ) - 2) ^ m = (-1) ^ m * (2 - (σ : ℂ)) ^ m by rw [← mul_pow]; ring]
    have hinv : (m ! : ℂ)⁻¹ * (m ! : ℂ) = 1 := inv_mul_cancel₀ hfac
    linear_combination (-(res : ℂ) * (2 - (σ : ℂ)) ^ m * ((-1) ^ m * (-1) ^ m)) * hinv
      + (-(res : ℂ) * (2 - (σ : ℂ)) ^ m) * hsq
  simp_rw [hterm] at hT
  have hTre := Complex.hasSum_re hT
  simp only [Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re] at hTre
  -- Cauchy's estimate
  have hcauchy : ∀ m : ℕ, |(β m).re - res| ≤ M * (2 / 3) ^ m := by
    intro m
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m
      (by norm_num : (0 : ℝ) < 3 / 2) (hG.diffContOnCl) hM
    have hbm : β m - res = (m ! : ℂ)⁻¹ * ((-1) ^ m * iteratedDeriv m G 2) := by
      rw [hDG m]
      have hfac : (m ! : ℂ) ≠ 0 := by exact_mod_cast (factorial_ne_zero m)
      have hsq : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
      simp only [hβ]
      field_simp
      linear_combination (res : ℂ) * (m ! : ℂ) * hsq
    have hre : (β m).re - res = (β m - res).re := by simp
    rw [hre]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [hbm, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv,
      Complex.norm_natCast]
    have hf : (0 : ℝ) < m ! := by exact_mod_cast factorial_pos m
    rw [inv_mul_le_iff₀ hf]
    calc ‖iteratedDeriv m G 2‖ ≤ m ! * M / (3 / 2) ^ m := hc
      _ = m ! * (M * (2 / 3) ^ m) := by
        rw [div_eq_mul_inv, ← inv_pow, show ((3 : ℝ) / 2)⁻¹ = 2 / 3 by norm_num]; ring
  -- split the series at K
  set r : ℕ → ℝ := fun m => (2 - σ) ^ m * ((β m).re - res) with hr
  have hρ0 : 0 ≤ 2 - σ := by linarith
  have hρ : (2 - σ) * (2 / 3) ≤ 3 / 4 := by nlinarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) ((hcauchy 0).trans (by simp))
  have htail_le : ∀ m, -(M * (3 / 4 : ℝ) ^ m) ≤ r m := by
    intro m
    have h1 := hcauchy m
    have h2 : |r m| ≤ M * (3 / 4) ^ m := by
      rw [hr, abs_mul, abs_of_nonneg (pow_nonneg hρ0 m)]
      calc (2 - σ) ^ m * |(β m).re - res| ≤ (2 - σ) ^ m * (M * (2 / 3) ^ m) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg hρ0 m)
        _ = M * ((2 - σ) * (2 / 3)) ^ m := by rw [mul_pow]; ring
        _ ≤ M * (3 / 4) ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hρ m) hM0
    exact (neg_le_neg h2).trans (neg_abs_le _)
  have hhead : ∀ m, 1 ≤ m → -(res * (2 - σ) ^ m) ≤ r m := by
    intro m _
    have := (Complex.nonneg_iff.mp (hβnn m)).1
    rw [hr]
    nlinarith [pow_nonneg hρ0 m]
  have hsplit := (hasSum_nat_add_iff' K).mpr hTre
  have hgeo : HasSum (fun m => -(M * (3 / 4 : ℝ) ^ (m + K))) (-(M * (3 / 4) ^ K * 4)) := by
    have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num)).mul_left
      (M * (3 / 4) ^ K)
    have e : (fun m => -(M * (3 / 4 : ℝ) ^ (m + K)))
        = fun m => -(M * (3 / 4) ^ K * (3 / 4) ^ m) := by
      funext m; rw [pow_add]; ring
    rw [e, show -(M * (3 / 4 : ℝ) ^ K * 4) = -(M * (3 / 4) ^ K * (1 - 3 / 4)⁻¹) by norm_num]
    exact h.neg
  have htail : -(M * (3 / 4) ^ K * 4) ≤ (G σ).re - ∑ m ∈ Finset.range K, r m :=
    hasSum_le (fun m => htail_le (m + K)) hgeo hsplit
  -- the head
  have hgeom_sum : ∑ m ∈ Finset.range K, (2 - σ) ^ m = ((2 - σ) ^ K - 1) / (1 - σ) := by
    rw [geom_sum_eq (by linarith : (2 - σ) ≠ 1)]
    congr 1; ring
  have hhead_sum : 1 - res * ((2 - σ) ^ K - 1) / (1 - σ) ≤ ∑ m ∈ Finset.range K, r m := by
    set ℓ : ℕ → ℝ := fun m => (if m = 0 then 1 else 0) - res * (2 - σ) ^ m with hℓ
    have hle : ∀ m ∈ Finset.range K, ℓ m ≤ r m := by
      intro m _
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [hℓ, hr, if_true, pow_zero, one_mul, mul_one]; linarith
      · have := hhead m hm
        simp only [hℓ, if_neg hm.ne']
        linarith
    have hsumℓ : ∑ m ∈ Finset.range K, ℓ m = 1 - res * ∑ m ∈ Finset.range K, (2 - σ) ^ m := by
      simp only [hℓ, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_ite_eq' (Finset.range K) 0 (fun _ => (1 : ℝ)),
        if_pos (Finset.mem_range.mpr hK1)]
    calc 1 - res * ((2 - σ) ^ K - 1) / (1 - σ)
        = ∑ m ∈ Finset.range K, ℓ m := by rw [hsumℓ, hgeom_sum]; ring
      _ ≤ ∑ m ∈ Finset.range K, r m := Finset.sum_le_sum hle
  have hσ0 : 0 < 1 - σ := by linarith
  have hfin : (G σ).re ≥ 1 / 2 - res * (2 - σ) ^ K / (1 - σ) := by
    have h1 : -(M * (3 / 4) ^ K * 4) ≥ -(1 / 2) := by linarith
    have h2 : res * ((2 - σ) ^ K - 1) / (1 - σ) ≤ res * (2 - σ) ^ K / (1 - σ) := by
      apply div_le_div_of_nonneg_right _ hσ0.le; nlinarith
    linarith
  have hpow1 : 1 ≤ (2 - σ) ^ K := one_le_pow₀ (by linarith)
  have h3 : res / (1 - σ) ≤ res * (2 - σ) ^ K / (1 - σ) := by
    apply div_le_div_of_nonneg_right _ hσ0.le; nlinarith
  have h4 : 2 * res * (2 - σ) ^ K / (1 - σ)
      = res * (2 - σ) ^ K / (1 - σ) + res * (2 - σ) ^ K / (1 - σ) := by ring
  linarith

/-- The exponent `K = ⌈log(8M + 8)/log(4/3)⌉` makes the Cauchy tail at most `1/2`. -/
lemma goldfeld_exponent_spec {M : ℝ} (hM : 0 ≤ M) :
    let K := ⌈Real.log (8 * M + 8) / Real.log (4 / 3)⌉₊
    1 ≤ K ∧ 4 * M * (3 / 4 : ℝ) ^ K ≤ 1 / 2 ∧
      ∀ σ : ℝ, 7 / 8 ≤ σ → σ < 1 →
        (2 - σ) ^ K ≤ Real.exp 1 * (8 * M + 8) ^ (4 * (1 - σ)) := by
  intro K
  have hA : 0 < 8 * M + 8 := by linarith
  have hlogA : Real.log 8 ≤ Real.log (8 * M + 8) := Real.log_le_log (by norm_num) (by linarith)
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hl43 : 1 / 4 ≤ Real.log (4 / 3) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at this ⊢; linarith
  have hl43p : 0 < Real.log (4 / 3) := by linarith
  have hKge : Real.log (8 * M + 8) / Real.log (4 / 3) ≤ K := Nat.le_ceil _
  have hratio : 0 < Real.log (8 * M + 8) / Real.log (4 / 3) := div_pos (by linarith) hl43p
  have hKle : (K : ℝ) ≤ 4 * Real.log (8 * M + 8) + 1 := by
    have h1 : (K : ℝ) < Real.log (8 * M + 8) / Real.log (4 / 3) + 1 :=
      Nat.ceil_lt_add_one hratio.le
    have h2 : Real.log (8 * M + 8) / Real.log (4 / 3) ≤ 4 * Real.log (8 * M + 8) := by
      rw [div_le_iff₀ hl43p]; nlinarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have : (0 : ℝ) < K := lt_of_lt_of_le hratio hKge
    exact_mod_cast this
  · -- (3/4)^K = exp(−K log(4/3)) ≤ 1/(8M+8)
    have hp : (3 / 4 : ℝ) ^ K ≤ (8 * M + 8)⁻¹ := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < (3 / 4) ^ K), Real.log_pow,
        ← Real.exp_log hA, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have : Real.log (3 / 4) = -Real.log (4 / 3) := by
        rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
      rw [this]
      have := (div_le_iff₀ hl43p).mp hKge
      nlinarith
    calc 4 * M * (3 / 4 : ℝ) ^ K ≤ 4 * M * (8 * M + 8)⁻¹ :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ 1 / 2 := by rw [mul_inv_le_iff₀ hA]; linarith
  · intro σ hσ1 hσ2
    have hb : 0 < 2 - σ := by linarith
    rw [← Real.exp_log (pow_pos hb K), Real.log_pow, ← Real.exp_log hA,
      ← Real.exp_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log (2 - σ) ≤ 1 - σ := by
      have := Real.log_le_sub_one_of_pos hb; linarith
    have hlogpos : 0 ≤ Real.log (2 - σ) := Real.log_nonneg (by linarith)
    have hσ0 : 0 ≤ 1 - σ := by linarith
    calc (K : ℝ) * Real.log (2 - σ) ≤ (4 * Real.log (8 * M + 8) + 1) * (1 - σ) :=
          mul_le_mul hKle hlog hlogpos (by linarith)
      _ ≤ 1 + Real.log (8 * M + 8) * (4 * (1 - σ)) := by nlinarith

/-- **Goldfeld's inequality, explicit form.**  Under the hypotheses of `goldfeld_lower_bound`
with `M ≥ 0`, for `7/8 ≤ σ < 1`,
`G(σ) − λ/(1 − σ) ≥ 1/2 − 2e λ (8M + 8)^{4(1−σ)}/(1 − σ)`. -/
theorem goldfeld_lower_bound' {a : ℕ → ℂ} (ha : 0 ≤ a) (ha1 : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {res M : ℝ} (hres : 0 ≤ res) (hM0 : 0 ≤ M)
    (hF : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + res / (s - 1))
    (hM : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G z‖ ≤ M) {σ : ℝ} (hσ1 : 7 / 8 ≤ σ)
    (hσ2 : σ < 1) :
    1 / 2 - 2 * Real.exp 1 * res * (8 * M + 8) ^ (4 * (1 - σ)) / (1 - σ)
      ≤ (G σ).re - res / (1 - σ) := by
  obtain ⟨hK1, hK, hpow⟩ := goldfeld_exponent_spec hM0
  have h := goldfeld_lower_bound ha ha1 habs hG hres hF hM hK1 hK hσ1 hσ2
  have hσ0 : 0 < 1 - σ := by linarith
  have := hpow σ hσ1 hσ2
  have h2 : 2 * res * (2 - σ) ^ ⌈Real.log (8 * M + 8) / Real.log (4 / 3)⌉₊ / (1 - σ)
      ≤ 2 * Real.exp 1 * res * (8 * M + 8) ^ (4 * (1 - σ)) / (1 - σ) := by
    apply div_le_div_of_nonneg_right _ hσ0.le
    nlinarith
  linarith

end RHTower

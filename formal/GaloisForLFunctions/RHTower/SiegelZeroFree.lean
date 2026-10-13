import GaloisForLFunctions.RHTower.SiegelTheorem

/-!
# Siegel's theorem in zero-free form

**Theorem** (`siegel_zero_free`).  For every `ε > 0` there is `c > 0` such that for every
nontrivial quadratic character `χ` modulo `N`, `L(σ, χ) ≠ 0` for all real `σ > 1 − c N^{−ε}`.

Proof.  Put `r = 1/(4 log(N + 3)) ≤ 1/4`.  On `Re z ≥ 1 − 2r`, `|z| ≤ 2`, truncating the Dirichlet
series at `N` gives `|L(z, χ)| ≤ 2(log N + 11)` (`norm_LFunction_le_near_one`: `n^{2r} ≤ e^{1/2}` for
`n ≤ N + 1`).  Cauchy's estimate on circles of radius `r` gives `|L'(σ, χ)| ≤ 8(log N + 11) log(N + 3)`
for `1 − r ≤ σ ≤ 1`.  If `L(β, χ) = 0` with `1 − r ≤ β < 1`, then
`L(1, χ) = L(1, χ) − L(β, χ) ≤ (1 − β) · 8(log N + 11) log(N + 3)`, and Siegel's lower bound
`L(1, χ) ≥ c(ε/2) N^{−ε/2}` gives `1 − β ≫_ε N^{−ε}`.  Zeros with `β < 1 − r` satisfy
`1 − β > r ≫_ε N^{−ε}`.
-/

open DirichletCharacter Complex
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-- The radius `r_N = 1/(4 log(N + 3))`. -/
def siegelRadius (N : ℕ) : ℝ := 1 / (4 * Real.log (N + 3))

lemma one_lt_log_add_three (N : ℕ) : 1 < Real.log ((N : ℝ) + 3) := by
  have h3 : Real.exp 1 < (N : ℝ) + 3 := by
    have := Real.exp_one_lt_d9; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) h3

lemma siegelRadius_pos (N : ℕ) : 0 < siegelRadius N := by
  have := one_lt_log_add_three N
  unfold siegelRadius; positivity

lemma siegelRadius_le (N : ℕ) : siegelRadius N ≤ 1 / 4 := by
  have := one_lt_log_add_three N
  unfold siegelRadius
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- `n^{2r} ≤ e^{1/2}` for `1 ≤ n ≤ N + 3`. -/
lemma rpow_two_siegelRadius_le {N : ℕ} {x : ℝ} (hx1 : 1 ≤ x) (hxN : x ≤ (N : ℝ) + 3) :
    x ^ (2 * siegelRadius N) ≤ Real.exp (1 / 2) := by
  have hl := one_lt_log_add_three N
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log x ≤ Real.log ((N : ℝ) + 3) := Real.log_le_log (by linarith) hxN
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  unfold siegelRadius
  rw [show Real.log x * (2 * (1 / (4 * Real.log ((N : ℝ) + 3))))
    = Real.log x / (2 * Real.log ((N : ℝ) + 3)) by field_simp; ring]
  rw [div_le_iff₀ (by positivity)]
  linarith

lemma exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

variable {N : ℕ} [NeZero N]

/-- `|L(z, χ)| ≤ 2(log N + 11)` on `Re z ≥ 1 − 2r_N`, `|z| ≤ 2`. -/
theorem norm_LFunction_le_near_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {z : ℂ}
    (hz1 : 1 - 2 * siegelRadius N ≤ z.re) (hz2 : ‖z‖ ≤ 2) :
    ‖LFunction χ z‖ ≤ 2 * (Real.log N + 11) := by
  have hr := siegelRadius_le N
  have hre : (1 / 2 : ℝ) ≤ z.re := by linarith
  have hre0 : 0 < z.re := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have h := norm_LFunction_sub_character_partial_le hχ hre0 N
  -- the truncation error
  have herr : 2 * (N : ℝ) * (1 + ‖z‖ / z.re) * ((N : ℝ) + 1) ^ (-z.re) ≤ 10 * Real.exp (1 / 2) := by
    have h1 : 1 + ‖z‖ / z.re ≤ 5 := by
      have : ‖z‖ / z.re ≤ 4 := by
        rw [div_le_iff₀ hre0]; linarith
      linarith
    have h2 : ((N : ℝ) + 1) ^ (-z.re) ≤ ((N : ℝ) + 1) ^ (-(1 - 2 * siegelRadius N)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : ((N : ℝ) + 1) ^ (-(1 - 2 * siegelRadius N))
        = ((N : ℝ) + 1)⁻¹ * ((N : ℝ) + 1) ^ (2 * siegelRadius N) := by
      rw [show -(1 - 2 * siegelRadius N) = -1 + 2 * siegelRadius N by ring,
        Real.rpow_add (by linarith), Real.rpow_neg_one]
    have h4 := rpow_two_siegelRadius_le (N := N) (x := (N : ℝ) + 1) (by linarith) (by linarith)
    have h5 : (N : ℝ) * ((N : ℝ) + 1)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
    have hpow0 : 0 ≤ ((N : ℝ) + 1) ^ (-z.re) := Real.rpow_nonneg (by linarith) _
    calc 2 * (N : ℝ) * (1 + ‖z‖ / z.re) * ((N : ℝ) + 1) ^ (-z.re)
        ≤ 2 * (N : ℝ) * 5 * (((N : ℝ) + 1)⁻¹ * ((N : ℝ) + 1) ^ (2 * siegelRadius N)) := by
          rw [← h3]
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 hpow0
            (by positivity)
      _ = 10 * ((N : ℝ) * ((N : ℝ) + 1)⁻¹) * ((N : ℝ) + 1) ^ (2 * siegelRadius N) := by ring
      _ ≤ 10 * 1 * Real.exp (1 / 2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h5 (by norm_num)) h4
            (Real.rpow_nonneg (by linarith) _) (by norm_num)
      _ = 10 * Real.exp (1 / 2) := by ring
  -- the partial sum
  have hS : ‖dirichletPartialSum (fun j => χ (j + 1)) N z‖ ≤ Real.exp (1 / 2) * (1 + Real.log N) := by
    unfold dirichletPartialSum
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ n ∈ Finset.range N, ‖χ ((n : ZMod N) + 1) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-z)‖
        ≤ Real.exp (1 / 2) * ((n : ℝ) + 1)⁻¹ := by
      intro n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      have hnN : (n : ℝ) + 1 ≤ (N : ℝ) + 3 := by
        have : (n : ℝ) < N := by exact_mod_cast Finset.mem_range.mp hn
        linarith
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
      have hc : ‖χ ((n : ZMod N) + 1)‖ ≤ 1 := χ.norm_le_one _
      have hp : ((n : ℝ) + 1) ^ (-z.re) ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) ^ (2 * siegelRadius N) := by
        calc ((n : ℝ) + 1) ^ (-z.re) ≤ ((n : ℝ) + 1) ^ (-(1 - 2 * siegelRadius N)) :=
              Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
          _ = ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) ^ (2 * siegelRadius N) := by
              rw [show -(1 - 2 * siegelRadius N) = -1 + 2 * siegelRadius N by ring,
                Real.rpow_add (by linarith), Real.rpow_neg_one]
      have h4 := rpow_two_siegelRadius_le (N := N) hn1 hnN
      have hinv : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
      calc ‖χ ((n : ZMod N) + 1)‖ * ((n : ℝ) + 1) ^ (-z.re)
          ≤ 1 * (((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) ^ (2 * siegelRadius N)) :=
            mul_le_mul hc hp (Real.rpow_nonneg (by linarith) _) zero_le_one
        _ ≤ Real.exp (1 / 2) * ((n : ℝ) + 1)⁻¹ := by
            rw [one_mul, mul_comm]; exact mul_le_mul_of_nonneg_right h4 hinv
    have hsum := Finset.sum_le_sum hterm
    refine (le_of_eq_of_le (by push_cast; rfl) hsum).trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have := harmonic_le_one_add_log N
    rw [harmonic] at this
    push_cast at this
    exact this
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have he := exp_half_lt_two
  calc ‖LFunction χ z‖
      ≤ ‖LFunction χ z - dirichletPartialSum (fun j => χ (j + 1)) N z‖
        + ‖dirichletPartialSum (fun j => χ (j + 1)) N z‖ := norm_le_norm_sub_add _ _
    _ ≤ 10 * Real.exp (1 / 2) + Real.exp (1 / 2) * (1 + Real.log N) :=
        add_le_add (h.trans herr) hS
    _ = Real.exp (1 / 2) * (Real.log N + 11) := by ring
    _ ≤ 2 * (Real.log N + 11) := by
        apply mul_le_mul_of_nonneg_right he.le (by linarith)

/-- `|L'(σ, χ)| ≤ 8(log N + 11) log(N + 3)` for `1 − r_N ≤ σ ≤ 1`. -/
theorem norm_deriv_LFunction_le_near_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {σ : ℝ}
    (hσ1 : 1 - siegelRadius N ≤ σ) (hσ2 : σ ≤ 1) :
    ‖deriv (LFunction χ) σ‖ ≤ 8 * (Real.log N + 11) * Real.log ((N : ℝ) + 3) := by
  have hr0 := siegelRadius_pos N
  have hr := siegelRadius_le N
  have hd := (differentiable_LFunction hχ).diffContOnCl (s := Metric.ball (σ : ℂ) (siegelRadius N))
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hd (C := 2 * (Real.log N + 11))
    (fun z hz => by
      have hz' : ‖z - σ‖ = siegelRadius N := by simpa [dist_eq_norm] using hz
      apply norm_LFunction_le_near_one hχ
      · have := Complex.abs_re_le_norm (z - σ)
        rw [hz', Complex.sub_re, Complex.ofReal_re] at this
        linarith [(abs_le.mp this).1]
      · calc ‖z‖ = ‖(z - σ) + σ‖ := by ring_nf
          _ ≤ ‖z - σ‖ + ‖(σ : ℂ)‖ := norm_add_le _ _
          _ ≤ 2 := by
            rw [hz', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            linarith)
  calc ‖deriv (LFunction χ) σ‖ ≤ 2 * (Real.log N + 11) / siegelRadius N := hb
    _ = 8 * (Real.log N + 11) * Real.log ((N : ℝ) + 3) := by
        unfold siegelRadius
        have := one_lt_log_add_three N
        field_simp
        ring

/-- **Siegel's theorem, zero-free form.**  For every `ε > 0` there is `c > 0` such that every
nontrivial quadratic `L(s, χ)` modulo `N` has no real zero `σ > 1 − c N^{−ε}`. -/
theorem siegel_zero_free {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
      ∀ σ : ℝ, 1 - c * (N : ℝ) ^ (-ε) < σ → LFunction χ σ ≠ 0 := by
  obtain ⟨c₀, hc₀, hsiegel⟩ := siegel_LFunction_one (ε := ε / 2) (by positivity)
  -- constants: log(N+3) ≤ K N^{ε/4} with K = (4/ε) 4^{ε/4}
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 / ε * (4 : ℝ) ^ (ε / 4) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hlogK : ∀ M : ℕ, 1 ≤ M → Real.log ((M : ℝ) + 3) ≤ K * (M : ℝ) ^ (ε / 4) := by
    intro M hM
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ (M : ℝ) + 3)
      (by positivity : (0 : ℝ) < ε / 4)
    have h2 : ((M : ℝ) + 3) ^ (ε / 4) ≤ (4 * (M : ℝ)) ^ (ε / 4) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at h2
    calc Real.log ((M : ℝ) + 3) ≤ ((M : ℝ) + 3) ^ (ε / 4) / (ε / 4) := h1
      _ ≤ (4 : ℝ) ^ (ε / 4) * (M : ℝ) ^ (ε / 4) / (ε / 4) :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ = K * (M : ℝ) ^ (ε / 4) := by rw [hK]; field_simp
  refine ⟨min (c₀ / (96 * K ^ 2)) (1 / (4 * K)), by positivity, ?_⟩
  intro N _ χ hq hχ σ hσ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hN0 : (0 : ℝ) < N := by linarith
  have hNε : 0 < (N : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hN0 _
  have hl := one_lt_log_add_three N
  have hlogN := hlogK N NeZero.one_le
  have hNq : (N : ℝ) ^ (ε / 4) ≤ (N : ℝ) ^ (ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rcases le_or_gt 1 σ with h1 | h1
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using h1)
  intro hz
  -- the radius is at least the claimed width
  have hrlow : 1 / (4 * K) * (N : ℝ) ^ (-ε) ≤ siegelRadius N := by
    unfold siegelRadius
    have hpow : (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-ε) ≤ 1 := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hNε]
  rcases lt_or_ge σ (1 - siegelRadius N) with h2 | h2
  · -- far zero: 1 − σ > r
    have hmin : min (c₀ / (96 * K ^ 2)) (1 / (4 * K)) * (N : ℝ) ^ (-ε) ≤ siegelRadius N :=
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hNε.le).trans hrlow
    linarith
  · -- near zero: mean value theorem on [σ, 1]
    set K' : ℝ := 8 * (Real.log N + 11) * Real.log ((N : ℝ) + 3) with hK'
    have hmv : ‖LFunction χ ((1 : ℝ) : ℂ) - LFunction χ (σ : ℂ)‖ ≤ K' * (1 - σ) := by
      have hf : ∀ x ∈ Set.Icc σ 1, HasDerivWithinAt (fun t : ℝ => LFunction χ (t : ℂ))
          (deriv (LFunction χ) (x : ℂ)) (Set.Icc σ 1) x := fun x _ =>
        ((differentiable_LFunction hχ (x : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
      have hbd : ∀ x ∈ Set.Ico σ 1, ‖deriv (LFunction χ) (x : ℂ)‖ ≤ K' := fun x hx =>
        norm_deriv_LFunction_le_near_one hχ (by linarith [hx.1]) hx.2.le
      exact norm_image_sub_le_of_norm_deriv_le_segment' hf hbd 1 ⟨h1.le, le_rfl⟩
    rw [hz, sub_zero] at hmv
    have hL1 := hsiegel N χ hq hχ
    have hre : (LFunction χ 1).re ≤ ‖LFunction χ ((1 : ℝ) : ℂ)‖ := by
      simpa using Complex.re_le_norm (LFunction χ 1)
    -- K' ≤ 96 K² N^{ε/2}
    have hlogle : Real.log N ≤ Real.log ((N : ℝ) + 3) := Real.log_le_log hN0 (by linarith)
    have hK'le : K' ≤ 96 * K ^ 2 * (N : ℝ) ^ (ε / 2) := by
      have hNq2 : (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 4) = (N : ℝ) ^ (ε / 2) := by
        rw [← Real.rpow_add hN0]; ring_nf
      have hu : Real.log ((N : ℝ) + 3) ^ 2 ≤ K ^ 2 * (N : ℝ) ^ (ε / 2) := by
        rw [← hNq2]
        have h0 : 0 ≤ Real.log ((N : ℝ) + 3) := by linarith
        nlinarith [mul_le_mul hlogN hlogN h0 (by positivity)]
      calc K' = 8 * (Real.log N + 11) * Real.log ((N : ℝ) + 3) := hK'
        _ ≤ 8 * (12 * Real.log ((N : ℝ) + 3)) * Real.log ((N : ℝ) + 3) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            nlinarith
        _ = 96 * Real.log ((N : ℝ) + 3) ^ 2 := by ring
        _ ≤ 96 * (K ^ 2 * (N : ℝ) ^ (ε / 2)) := by linarith
        _ = 96 * K ^ 2 * (N : ℝ) ^ (ε / 2) := by ring
    have hσlt : 1 - σ < c₀ / (96 * K ^ 2) * (N : ℝ) ^ (-ε) := by
      have := (mul_le_mul_of_nonneg_right (min_le_left (c₀ / (96 * K ^ 2)) (1 / (4 * K)))
        hNε.le)
      linarith
    have hNsplit : (N : ℝ) ^ (-(ε / 2)) = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-ε) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hNh0 : 0 < (N : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hN0 _
    have hchain : c₀ * (N : ℝ) ^ (-(ε / 2)) ≤ K' * (1 - σ) := (hL1.trans hre).trans hmv
    have h1σ : 0 < 1 - σ := by linarith
    have : c₀ * (N : ℝ) ^ (-(ε / 2)) < c₀ * (N : ℝ) ^ (-(ε / 2)) := by
      calc c₀ * (N : ℝ) ^ (-(ε / 2)) ≤ K' * (1 - σ) := hchain
        _ ≤ 96 * K ^ 2 * (N : ℝ) ^ (ε / 2) * (1 - σ) :=
            mul_le_mul_of_nonneg_right hK'le h1σ.le
        _ < 96 * K ^ 2 * (N : ℝ) ^ (ε / 2) * (c₀ / (96 * K ^ 2) * (N : ℝ) ^ (-ε)) :=
            mul_lt_mul_of_pos_left hσlt (by positivity)
        _ = c₀ * (N : ℝ) ^ (-(ε / 2)) := by
            rw [hNsplit]; field_simp
    exact lt_irrefl _ this

end RHTower

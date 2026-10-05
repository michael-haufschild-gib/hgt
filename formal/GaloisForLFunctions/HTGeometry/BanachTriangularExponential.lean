import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Triangular-array exponential limits in commutative Banach algebras

In a commutative unital complex Banach algebra with `‖1‖ = 1`:

* `‖exp x‖ ≤ e^{‖x‖}`, `‖exp x - 1‖ ≤ e^{‖x‖} - 1` and `‖exp x - 1 - x‖ ≤ ‖x‖² e^{‖x‖}`, by comparing
  the exponential series termwise with the real one;
* telescoping, `‖Π u_i - Π v_i‖ ≤ (Π M_i) Σ ‖u_i - v_i‖` whenever `‖u_i‖, ‖v_i‖ ≤ M_i` and
  `M_i ≥ 1`;
* hence `‖Π (1 + x_i) - exp(Σ x_i)‖ ≤ e^{2 Σ ‖x_i‖} Σ ‖x_i‖²` (as `exp(Σ x_i) = Π exp x_i`).

Consequently, if `Σ_j ‖a_{N,j}‖ ≤ C`, `max_j ‖a_{N,j}‖ → 0` and `Σ_j a_{N,j} → a`, then
`Π_j (1 + z a_{N,j}) → exp(z a)` uniformly for `|z| ≤ R` `(PDF.7)`; in particular
`(1 + z a/N)^N → exp(z a)` `(PDF.1)`.
-/

open Filter Topology NormedSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationDust

variable {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- The rational scalars of a complex Banach algebra. -/
@[reducible] def ratAlgebra : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℂ 𝔸

attribute [local instance] ratAlgebra

/-! ### Norm bounds for the exponential -/

omit [CompleteSpace 𝔸] in
theorem norm_smul_pow_le (x : 𝔸) (n : ℕ) :
    ‖((n.factorial : ℝ)⁻¹) • x ^ n‖ ≤ ‖x‖ ^ n / n.factorial := by
  rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (norm_pow_le x n) (by positivity)

theorem norm_exp_le (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  rw [Real.exp_eq_exp_ℝ]
  exact (exp_series_hasSum_exp' (𝕂 := ℝ) x).norm_le_of_bounded
    (expSeries_div_hasSum_exp ‖x‖) (norm_smul_pow_le x)

theorem norm_exp_sub_one_le (x : 𝔸) : ‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have h1 := (hasSum_nat_add_iff' 1).2 (exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have h2 := (hasSum_nat_add_iff' 1).2 (expSeries_div_hasSum_exp ‖x‖)
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_smul, div_one] at h1 h2
  rw [← Real.exp_eq_exp_ℝ] at h2
  exact h1.norm_le_of_bounded h2 fun n => norm_smul_pow_le x (n + 1)

theorem norm_exp_sub_one_sub_le (x : 𝔸) : ‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  have h1 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℝ) x)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_one, Nat.factorial_one] at h1
  rw [sub_add_eq_sub_sub] at h1
  have h2 := (expSeries_div_hasSum_exp ‖x‖).mul_left (‖x‖ ^ 2)
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.norm_le_of_bounded h2 fun n => (norm_smul_pow_le x (n + 2)).trans ?_
  rw [pow_add, mul_comm (‖x‖ ^ n), mul_div_assoc]
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (by exact_mod_cast Nat.factorial_le (Nat.le_add_right n 2))) (by positivity)

/-! ### Telescoping products -/

omit [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] in
theorem norm_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (u v : ι → 𝔸)
    (M : ι → ℝ) (hM : ∀ i ∈ s, 1 ≤ M i) (hu : ∀ i ∈ s, ‖u i‖ ≤ M i)
    (hv : ∀ i ∈ s, ‖v i‖ ≤ M i) :
    ‖∏ i ∈ s, u i - ∏ i ∈ s, v i‖ ≤ (∏ i ∈ s, M i) * ∑ i ∈ s, ‖u i - v i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hM' : ∀ i ∈ s, 1 ≤ M i := fun i hi => hM i (Finset.mem_insert_of_mem hi)
    have hPM : 1 ≤ ∏ i ∈ s, M i :=
      calc (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := by simp
        _ ≤ ∏ i ∈ s, M i := Finset.prod_le_prod (fun _ _ => zero_le_one) hM'
    have hPu : ‖∏ i ∈ s, u i‖ ≤ ∏ i ∈ s, M i :=
      (Finset.norm_prod_le s u).trans (Finset.prod_le_prod (fun i _ => norm_nonneg _)
        fun i hi => hu i (Finset.mem_insert_of_mem hi))
    have ih' := ih hM' (fun i hi => hu i (Finset.mem_insert_of_mem hi))
      (fun i hi => hv i (Finset.mem_insert_of_mem hi))
    have hMa := hM a (Finset.mem_insert_self a s)
    have hva := hv a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
      show u a * ∏ i ∈ s, u i - v a * ∏ i ∈ s, v i =
        (u a - v a) * ∏ i ∈ s, u i + v a * (∏ i ∈ s, u i - ∏ i ∈ s, v i) by ring]
    calc ‖(u a - v a) * ∏ i ∈ s, u i + v a * (∏ i ∈ s, u i - ∏ i ∈ s, v i)‖
        ≤ ‖u a - v a‖ * ∏ i ∈ s, M i + M a * ((∏ i ∈ s, M i) * ∑ i ∈ s, ‖u i - v i‖) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hPu (norm_nonneg _))
          · exact (norm_mul_le _ _).trans (mul_le_mul hva ih' (norm_nonneg _) (by linarith))
      _ ≤ M a * (∏ i ∈ s, M i) * (‖u a - v a‖ + ∑ i ∈ s, ‖u i - v i‖) := by
          have h1 := mul_le_mul_of_nonneg_right hMa (mul_nonneg (by linarith : (0 : ℝ) ≤
            ∏ i ∈ s, M i) (norm_nonneg (u a - v a)))
          linarith

/-- **The product–exponential comparison**:
`‖Π (1 + x_i) - exp(Σ x_i)‖ ≤ e^{2 Σ ‖x_i‖} Σ ‖x_i‖²`. -/
theorem norm_prod_one_add_sub_exp_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → 𝔸) :
    ‖∏ i ∈ s, (1 + x i) - exp (∑ i ∈ s, x i)‖ ≤
      Real.exp (2 * ∑ i ∈ s, ‖x i‖) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  rw [exp_sum]
  have h := norm_prod_sub_prod_le s (fun i => 1 + x i) (fun i => exp (x i))
    (fun i => Real.exp ‖x i‖) (fun i _ => Real.one_le_exp (norm_nonneg _))
    (fun i _ => (norm_add_le _ _).trans (by
      rw [norm_one, add_comm]; exact Real.add_one_le_exp _))
    (fun i _ => norm_exp_le (x i))
  refine h.trans ?_
  rw [← Real.exp_sum, two_mul, Real.exp_add, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [show 1 + x i - exp (x i) = -(exp (x i) - 1 - x i) by ring, norm_neg, mul_comm]
  refine (norm_exp_sub_one_sub_le (x i)).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 ?_) (by positivity))
  exact Finset.single_le_sum (fun j _ => norm_nonneg (x j)) hi

/-- `‖exp u - exp w‖ ≤ e^{‖w‖} (e^{‖u - w‖} - 1)`. -/
theorem norm_exp_sub_exp_le (u w : 𝔸) :
    ‖exp u - exp w‖ ≤ Real.exp ‖w‖ * (Real.exp ‖u - w‖ - 1) := by
  rw [show exp u = exp w * exp (u - w) by rw [← exp_add, add_sub_cancel],
    show exp w * exp (u - w) - exp w = exp w * (exp (u - w) - 1) by ring]
  exact (norm_mul_le _ _).trans (mul_le_mul (norm_exp_le w) (norm_exp_sub_one_le _)
    (norm_nonneg _) (Real.exp_pos _).le)

/-! ### Lemma 3.1: the triangular-array exponential limit -/

/-- **Lemma 3.1, `(PDF.6)`–`(PDF.7)`**: if `Σ_j ‖a_{N,j}‖ ≤ C`, `max_j ‖a_{N,j}‖ → 0` and
`Σ_j a_{N,j} → a`, then `Π_j (1 + z a_{N,j}) → exp(z a)` uniformly on `|z| ≤ R`. -/
theorem tendstoUniformlyOn_prod_one_add {m : ℕ → ℕ} (a : (N : ℕ) → Fin (m N) → 𝔸) (a₀ : 𝔸)
    {C : ℝ} (hC : ∀ N, ∑ j, ‖a N j‖ ≤ C)
    (hsmall : ∀ ε > 0, ∀ᶠ N in atTop, ∀ j, ‖a N j‖ ≤ ε)
    (hsum : Tendsto (fun N => ∑ j, a N j) atTop (𝓝 a₀)) (R : ℝ) :
    TendstoUniformlyOn (fun N (z : ℂ) => ∏ j, (1 + z • a N j)) (fun z => exp (z • a₀)) atTop
      (Metric.closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set R' := max R 0
  set C' := max C 0
  have hC0 : ∀ N, ∑ j, ‖a N j‖ ≤ C' := fun N => (hC N).trans (le_max_left _ _)
  -- the exponential part
  have hexp : Tendsto (fun N => Real.exp (R' * ‖a₀‖) *
      (Real.exp (R' * ‖∑ j, a N j - a₀‖) - 1)) atTop (𝓝 0) := by
    have h0 := (tendsto_iff_norm_sub_tendsto_zero.1 hsum).const_mul R'
    rw [mul_zero] at h0
    have h := (Real.continuous_exp.continuousAt (x := 0)).tendsto.comp h0
    simp only [Real.exp_zero] at h
    have h2 := (h.sub_const 1).const_mul (Real.exp (R' * ‖a₀‖))
    simp only [sub_self, mul_zero] at h2
    exact h2
  set B := Real.exp (2 * (R' * C')) * R' ^ 2 * C'
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ > 0, B * δ < ε / 2 := by
    refine ⟨ε / 2 / (B + 1), by positivity, ?_⟩
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    have hB : 0 ≤ B := by positivity
    nlinarith
  filter_upwards [hsmall δ hδ, hexp.eventually (gt_mem_nhds (half_pos hε))] with N hN hNexp
  intro z hz
  have hz' : ‖z‖ ≤ R' := (mem_closedBall_zero_iff.1 hz).trans (le_max_left _ _)
  rw [dist_eq_norm, norm_sub_rev, ← sub_add_sub_cancel _ (exp (∑ j, z • a N j))]
  refine (norm_add_le _ _).trans_lt ?_
  have h1 : ‖∏ j, (1 + z • a N j) - exp (∑ j, z • a N j)‖ ≤ B * δ := by
    refine (norm_prod_one_add_sub_exp_le _ _).trans ?_
    have hn : ∀ j, ‖z • a N j‖ ≤ R' * ‖a N j‖ := fun j => by
      rw [norm_smul]; exact mul_le_mul_of_nonneg_right hz' (norm_nonneg _)
    have hs1 : ∑ j, ‖z • a N j‖ ≤ R' * C' := by
      calc ∑ j, ‖z • a N j‖ ≤ ∑ j, R' * ‖a N j‖ := Finset.sum_le_sum fun j _ => hn j
        _ = R' * ∑ j, ‖a N j‖ := by rw [Finset.mul_sum]
        _ ≤ R' * C' := mul_le_mul_of_nonneg_left (hC0 N) (le_max_right _ _)
    have hs2 : ∑ j, ‖z • a N j‖ ^ 2 ≤ R' ^ 2 * C' * δ := by
      calc ∑ j, ‖z • a N j‖ ^ 2 ≤ ∑ j, R' ^ 2 * δ * ‖a N j‖ := Finset.sum_le_sum fun j _ => by
            have h0 := norm_nonneg (z • a N j)
            have h3 := hn j
            have h4 := hN j
            have : ‖z • a N j‖ ≤ R' * δ := h3.trans (mul_le_mul_of_nonneg_left h4
              (le_max_right _ _))
            nlinarith [norm_nonneg (a N j), le_max_right R 0]
        _ = R' ^ 2 * δ * ∑ j, ‖a N j‖ := by rw [Finset.mul_sum]
        _ ≤ R' ^ 2 * δ * C' := mul_le_mul_of_nonneg_left (hC0 N) (by positivity)
        _ = R' ^ 2 * C' * δ := by ring
    calc Real.exp (2 * ∑ j, ‖z • a N j‖) * ∑ j, ‖z • a N j‖ ^ 2
        ≤ Real.exp (2 * (R' * C')) * (R' ^ 2 * C' * δ) :=
          mul_le_mul (Real.exp_le_exp.2 (by linarith)) hs2 (Finset.sum_nonneg fun j _ => by
            positivity) (Real.exp_pos _).le
      _ = B * δ := by ring
  have h2 : ‖exp (∑ j, z • a N j) - exp (z • a₀)‖ ≤
      Real.exp (R' * ‖a₀‖) * (Real.exp (R' * ‖∑ j, a N j - a₀‖) - 1) := by
    refine (norm_exp_sub_exp_le _ _).trans (mul_le_mul (Real.exp_le_exp.2 ?_) (sub_le_sub_right
      (Real.exp_le_exp.2 ?_) 1) (sub_nonneg.2 (Real.one_le_exp (norm_nonneg _)))
      (Real.exp_pos _).le)
    · rw [norm_smul]; exact mul_le_mul_of_nonneg_right hz' (norm_nonneg _)
    · rw [← Finset.smul_sum, ← smul_sub, norm_smul]
      exact mul_le_mul_of_nonneg_right hz' (norm_nonneg _)
  linarith

/-- **`(PDF.1)`**: `(1 + z a/N)^N → exp(z a)` uniformly on `|z| ≤ R`. -/
theorem tendstoUniformlyOn_one_add_div_pow (a : 𝔸) (R : ℝ) :
    TendstoUniformlyOn (fun (N : ℕ) (z : ℂ) => (1 + z • ((N : ℂ)⁻¹ • a)) ^ N)
      (fun z => exp (z • a)) atTop (Metric.closedBall 0 R) := by
  have h := tendstoUniformlyOn_prod_one_add (m := fun N => N) (fun N _ => (N : ℂ)⁻¹ • a) a
    (C := ‖a‖) (fun N => by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_smul,
          norm_inv, Complex.norm_natCast, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul])
    (fun ε hε => by
      filter_upwards [eventually_ge_atTop ⌈‖a‖ / ε⌉₊, eventually_gt_atTop 0] with N hN hN0 j
      rw [norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div, div_le_iff₀ (by
        exact_mod_cast hN0)]
      have := (Nat.ceil_le.1 hN)
      rw [div_le_iff₀ hε] at this
      linarith)
    (tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
        smul_smul, mul_inv_cancel₀ (by exact_mod_cast hN.ne'), one_smul])) R
  refine h.congr (Eventually.of_forall fun N z _ => ?_)
  simp [Finset.prod_const]

end GaloisForLFunctions.HTGeometry.FormationDust

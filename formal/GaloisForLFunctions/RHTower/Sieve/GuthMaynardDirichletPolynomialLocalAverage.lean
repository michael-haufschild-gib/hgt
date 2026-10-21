import GaloisForLFunctions.RHTower.Sieve.GuthMaynardBandKernel

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 11.3: a Dirichlet polynomial is controlled by its local average

For `D(t) = Σ_{N < n ≤ 2N} b_n n^{it}` with `|b_n| ≤ 1` (Guth–Maynard, arXiv 2405.20552, Lemma 11.3):

`|D(t)| ≪ ∫_{|u − t| ⪅ 1} |D(u)| du + O(T^{−A})`.

Proof. `D(t) = Σ_n b_n e(t · log n/2π)` has its frequencies `log n/2π` within distance `1` of
`a = log N/2π` (`log 2 < 2π`), so the unit-scale band kernel reproduces it:
`|D(t)| ≤ ‖K‖_∞ ∫_{−δ}^{δ} |D(t + η)| dη + N ∫_{|ξ| > δ} |K|` (`GuthMaynardBandKernel`). With
`δ = T^ε` the tail is `O_A(T^{−A−1})` by the Schwartz decay of `K`, and `N ≤ T`.

The same kernel gives the shift-uniform square bound
`|D(u − σ)|² ≤ ‖K‖₁ ∫ 3 bandCauchy/(1+η²) |D(u + η)|² dη` for `|σ| ≤ 1`, which is how Lemma 11.3
enters the proofs of Lemmas 11.4 and 11.6 (without truncation error).
-/

open MeasureTheory Set Finset

namespace RHTower.GuthMaynard

noncomputable section

/-- The dyadic Dirichlet polynomial `D(t) = Σ_{N < n ≤ 2N} b_n n^{it}`. -/
def dyadicDirichletPoly (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)

/-- `D` is the exponential sum with frequencies `log n/2π`. -/
theorem dyadicDirichletPoly_eq_finiteFrequencyPoly (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    dyadicDirichletPoly N b t =
      Sieve.finiteFrequencyPoly b (Finset.Ioc N (2 * N)) (fun n => Real.log n / (2 * Real.pi)) t := by
  unfold dyadicDirichletPoly Sieve.finiteFrequencyPoly
  refine sum_congr rfl fun n _ => ?_
  congr 1
  have h : 2 * Real.pi * (t * (Real.log n / (2 * Real.pi))) = t * Real.log n := by
    field_simp
  rw [h]
  push_cast
  ring_nf

/-- The frequencies `log n/2π`, `N < n ≤ 2N`, lie within `1` of `log N/2π`. -/
theorem abs_log_div_two_pi_sub_le {N n : ℕ} (hn : n ∈ Finset.Ioc N (2 * N)) :
    |Real.log n / (2 * Real.pi) - Real.log N / (2 * Real.pi)| ≤ 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
  have hN : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hn1 : (N : ℝ) ≤ n := by exact_mod_cast h1.le
  have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast h2
  have hlog0 : 0 ≤ Real.log n - Real.log N := sub_nonneg.mpr (Real.log_le_log (by linarith) hn1)
  have hlog1 : Real.log n - Real.log N ≤ 1 := by
    rw [← Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))]
    have : (n : ℝ) / N ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    calc Real.log (n / N) ≤ n / N - 1 :=
          Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
      _ ≤ 1 := by linarith
  rw [← sub_div, abs_div, abs_of_nonneg hlog0, abs_of_pos Real.two_pi_pos,
    div_le_one Real.two_pi_pos]
  linarith [Real.pi_gt_three]

/-- The trivial bound `|D(t)| ≤ N`. -/
theorem norm_dyadicDirichletPoly_le {N : ℕ} {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) (t : ℝ) :
    ‖dyadicDirichletPoly N b t‖ ≤ N := by
  unfold dyadicDirichletPoly
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Finset.Ioc N (2 * N), ‖b n * Complex.exp (Complex.I * t * Real.log n)‖
      ≤ ∑ _n ∈ Finset.Ioc N (2 * N), (1 : ℝ) := by
        refine sum_le_sum fun n _ => ?_
        rw [norm_mul, norm_exp_mul_log, mul_one]
        exact hb n
    _ = N := by simp [Nat.card_Ioc, two_mul]

theorem continuous_dyadicDirichletPoly (N : ℕ) (b : ℕ → ℂ) :
    Continuous (dyadicDirichletPoly N b) := by
  unfold dyadicDirichletPoly
  fun_prop

/-- `Σ_{N<n≤2N} |b_n| ≤ N`. -/
theorem sum_norm_le_of_norm_le_one {N : ℕ} {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) :
    ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ N := by
  calc ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ ∑ _n ∈ Finset.Ioc N (2 * N), (1 : ℝ) :=
        sum_le_sum fun n _ => hb n
    _ = N := by simp [Nat.card_Ioc, two_mul]

/-! ### The local form -/

/-- **Lemma 11.3, explicit form.** For `|b_n| ≤ 1` and `δ ≥ 0`:
`|D(t)| ≤ ‖K‖_∞ ∫_{t−δ}^{t+δ} |D(u)| du + N ∫_{|ξ|>δ} |K|`. -/
theorem norm_dyadicDirichletPoly_le_local {N : ℕ} {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) {δ : ℝ}
    (hδ : 0 ≤ δ) (t : ℝ) :
    ‖dyadicDirichletPoly N b t‖ ≤
      bandSup * (∫ u in (t - δ)..(t + δ), ‖dyadicDirichletPoly N b u‖) + N * bandTail δ := by
  have h := norm_finiteFrequencyPoly_le_local b (Finset.Ioc N (2 * N))
    (fun n => Real.log n / (2 * Real.pi)) (a := Real.log N / (2 * Real.pi)) one_pos hδ
    (fun n hn => abs_log_div_two_pi_sub_le hn) t
  simp_rw [← dyadicDirichletPoly_eq_finiteFrequencyPoly] at h
  rw [one_mul, one_mul] at h
  have hshift : ∫ η in -δ..δ, ‖dyadicDirichletPoly N b (t + η)‖ =
      ∫ u in (t - δ)..(t + δ), ‖dyadicDirichletPoly N b u‖ := by
    rw [intervalIntegral.integral_comp_add_left (fun u => ‖dyadicDirichletPoly N b u‖) t,
      sub_eq_add_neg]
  rw [hshift] at h
  refine h.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right (sum_norm_le_of_norm_le_one hb) (bandTail_nonneg δ)

/-- **Shifted square form** (Lemma 11.3 as used in Lemmas 11.4 and 11.6): for `|σ| ≤ 1`,
`|D(u − σ)|² ≤ ‖K‖₁ ∫ 3 bandCauchy/(1 + η²) |D(u + η)|² dη`. -/
theorem norm_dyadicDirichletPoly_sub_sq_le (N : ℕ) (b : ℕ → ℂ) (u σ : ℝ) (hσ : |σ| ≤ 1) :
    ‖dyadicDirichletPoly N b (u - σ)‖ ^ 2 ≤
      bandMass * ∫ η, 3 * bandCauchy / (1 + η ^ 2) * ‖dyadicDirichletPoly N b (u + η)‖ ^ 2 := by
  have h := norm_finiteFrequencyPoly_sub_sq_le b (Finset.Ioc N (2 * N))
    (fun n => Real.log n / (2 * Real.pi)) (a := Real.log N / (2 * Real.pi))
    (fun n hn => abs_log_div_two_pi_sub_le hn) u σ hσ
  simpa only [← dyadicDirichletPoly_eq_finiteFrequencyPoly] using h

/-! ### The paper form -/

/-- The tail `∫_{|ξ| > T^ε} |K|` decays faster than every power of `T`. -/
theorem exists_bandTail_rpow_le {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → bandTail (T ^ ε) ≤ C * T ^ (-A) := by
  set j : ℕ := ⌈A / ε⌉₊
  set B := cglSchwartzFourierDecayBudget bandPlateau (j + 2)
  have hB0 : 0 ≤ B := le_trans (by positivity) (abs_pow_mul_norm_bandProfile_le (j + 2) 0)
  refine ⟨2 * Real.pi * B, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  refine (bandTail_le j hTε).trans ?_
  have hpow : (T ^ ε) ^ j = T ^ (ε * j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
  have hexp : -(ε * j) ≤ -A := by
    have : A / ε ≤ j := Nat.le_ceil _
    rw [div_le_iff₀ hε, mul_comm] at this
    linarith
  rw [hpow, div_eq_mul_inv, ← Real.rpow_neg hT0.le]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT (by linarith))
    (by positivity)

/-- **Guth–Maynard Lemma 11.3** (`|D(t)| ≪ ∫_{|u−t| ⪅ 1} |D(u)| du + O(T^{−A})`): for every
`ε > 0` and every `A` there is `C ≥ 0` such that for all `T ≥ 2`, `N ≤ T`, `|b_n| ≤ 1` and `t`,
`|D(t)| ≤ C ∫_{t − T^ε}^{t + T^ε} |D(u)| du + C T^{−A}`. -/
theorem guthMaynard_lemma113 {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (b : ℕ → ℂ) (T t : ℝ), 2 ≤ T → (N : ℝ) ≤ T → (∀ n, ‖b n‖ ≤ 1) →
      ‖dyadicDirichletPoly N b t‖ ≤
        C * (∫ u in (t - T ^ ε)..(t + T ^ ε), ‖dyadicDirichletPoly N b u‖) + C * T ^ (-A) := by
  obtain ⟨C₁, hC₁, htail⟩ := exists_bandTail_rpow_le hε (A + 1)
  refine ⟨max bandSup C₁, le_trans hC₁ (le_max_right _ _), fun N b T t hT hNT hb => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hδ : 0 ≤ T ^ ε := by positivity
  have h := norm_dyadicDirichletPoly_le_local (N := N) hb hδ t
  have hint : 0 ≤ ∫ u in (t - T ^ ε)..(t + T ^ ε), ‖dyadicDirichletPoly N b u‖ :=
    intervalIntegral.integral_nonneg (by linarith) fun u _ => norm_nonneg _
  have herr : (N : ℝ) * bandTail (T ^ ε) ≤ C₁ * T ^ (-A) := by
    calc (N : ℝ) * bandTail (T ^ ε) ≤ T * (C₁ * T ^ (-(A + 1))) :=
          mul_le_mul hNT (htail T hT1) (bandTail_nonneg _) hT0.le
      _ = C₁ * T ^ (-A) := by
          rw [show -(A + 1) = -A + (-1) by ring, Real.rpow_add hT0, Real.rpow_neg_one]
          field_simp
  have h1 : bandSup * (∫ u in (t - T ^ ε)..(t + T ^ ε), ‖dyadicDirichletPoly N b u‖) ≤
      max bandSup C₁ * (∫ u in (t - T ^ ε)..(t + T ^ ε), ‖dyadicDirichletPoly N b u‖) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hint
  have h2 : C₁ * T ^ (-A) ≤ max bandSup C₁ * T ^ (-A) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  linarith

end

end RHTower.GuthMaynard

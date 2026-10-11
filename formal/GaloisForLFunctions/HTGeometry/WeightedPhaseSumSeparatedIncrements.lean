import Mathlib

/-!
# Weighted phase sums with separated increments

Let `F₀, F₁, …` be real phases whose increments `θ_k = F_{k+1} − F_k` lie in `[δ, 2π − δ]`, and let
`w_k` be real weights. With `σ = 2 sin(δ/2)`,

  `‖Σ_{k ≤ m} w_k e^{iF_k}‖ ≤ |w_m| + 2|w_{m−1}|/σ
      + 2 Σ_{i < m−1} (|w_{i+1} − w_i|/σ + |w_i| |θ_{i+1} − θ_i|/σ²)`

(`norm_sum_weight_mul_phase_le`). The sum is small when the weights have small variation and the
increments vary slowly.

**Proof.** Put `u_k = e^{iF_k}` and `e_k = e^{iθ_k} − 1`. Then `u_{k+1} − u_k = u_k e_k`, so
`w_k u_k = c_k (u_{k+1} − u_k)` with `c_k = w_k/e_k`. Summation by parts against the telescoping
partial sums `u_{i+1} − u_0` gives the bound, using `|e_k| ≥ σ` (`two_sin_half_le_norm_exp_sub_one`)
and `|1/e_{i+1} − 1/e_i| ≤ |θ_{i+1} − θ_i|/σ²`.

Along any nondecreasing sequence of points the Lorentzian weights `1/(1 + (t − u_i)²)` have total
variation at most `3` (`sum_abs_sub_lorentzWeight_le_three`): they rise, cross the peak once and
fall.
-/

open Complex Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `|e^{iθ} − 1| ≥ 2 sin(δ/2)` for `θ ∈ [δ, 2π − δ]`. -/
theorem two_sin_half_le_norm_exp_sub_one {δ θ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi)
    (h1 : δ ≤ θ) (h2 : θ ≤ 2 * Real.pi - δ) :
    2 * Real.sin (δ / 2) ≤ ‖cexp (I * θ) - 1‖ := by
  rw [norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have hs : Real.sin (δ / 2) ≤ Real.sin (θ / 2) := by
    rcases le_total (θ / 2) (Real.pi / 2) with h | h
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h (by linarith)
    · rw [← Real.sin_pi_sub (θ / 2)]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have : Real.sin (θ / 2) ≤ |Real.sin (θ / 2)| := le_abs_self _
  linarith

/-- `0 < 2 sin(δ/2)` for `0 < δ ≤ π`. -/
theorem two_sin_half_pos {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) : 0 < 2 * Real.sin (δ / 2) := by
  have := Real.sin_pos_of_pos_of_lt_pi (x := δ / 2) (by linarith) (by linarith)
  linarith

/-- `|e^{ia} − e^{ib}| ≤ |a − b|`. -/
theorem norm_exp_I_mul_sub_exp_I_mul_le (a b : ℝ) :
    ‖cexp (I * a) - cexp (I * b)‖ ≤ |a - b| := by
  have e : cexp (I * a) - cexp (I * b) = cexp (I * b) * (cexp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, norm_exp_I_mul_ofReal, one_mul, norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_two]
  have := Real.abs_sin_le_abs (x := (a - b) / 2)
  rw [abs_div, abs_two] at this
  linarith

/-- **Weighted phase sums with separated increments.** -/
theorem norm_sum_weight_mul_phase_le {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) (F w : ℕ → ℝ)
    (m : ℕ) (hθ : ∀ k < m, δ ≤ F (k + 1) - F k ∧ F (k + 1) - F k ≤ 2 * Real.pi - δ) :
    ‖∑ k ∈ range (m + 1), (w k : ℂ) * cexp (I * F k)‖ ≤
      |w m| + 2 * |w (m - 1)| / (2 * Real.sin (δ / 2)) +
        2 * ∑ i ∈ range (m - 1), (|w (i + 1) - w i| / (2 * Real.sin (δ / 2)) +
          |w i| * |(F (i + 2) - F (i + 1)) - (F (i + 1) - F i)| /
            (2 * Real.sin (δ / 2)) ^ 2) := by
  set σ := 2 * Real.sin (δ / 2) with hσ
  have hσ0 : 0 < σ := two_sin_half_pos hδ hδπ
  set u : ℕ → ℂ := fun k => cexp (I * F k) with hu
  set θ : ℕ → ℝ := fun k => F (k + 1) - F k with hθdef
  set e : ℕ → ℂ := fun k => cexp (I * θ k) - 1 with he
  set c : ℕ → ℂ := fun k => (w k : ℂ) / e k with hc
  have hnorm_e : ∀ k < m, σ ≤ ‖e k‖ := fun k hk =>
    two_sin_half_le_norm_exp_sub_one hδ hδπ (hθ k hk).1 (hθ k hk).2
  have he0 : ∀ k < m, e k ≠ 0 := fun k hk h => by
    have := hnorm_e k hk; rw [h, norm_zero] at this; linarith
  have hu_norm : ∀ k, ‖u k‖ = 1 := fun k => by rw [hu]; exact norm_exp_I_mul_ofReal _
  -- `u_{k+1} − u_k = u_k e_k`
  have hstep : ∀ k, u (k + 1) - u k = u k * e k := fun k => by
    simp only [hu, he, hθdef]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  -- `w_k u_k = c_k (u_{k+1} − u_k)`
  have hterm : ∀ k < m, (w k : ℂ) * u k = c k * (u (k + 1) - u k) := fun k hk => by
    rw [hstep, hc]
    field_simp [he0 k hk]
  have hsplit : ∑ k ∈ range (m + 1), (w k : ℂ) * u k =
      (w m : ℂ) * u m + ∑ k ∈ range m, c k * (u (k + 1) - u k) := by
    rw [sum_range_succ, add_comm]
    congr 1
    exact sum_congr rfl fun k hk => hterm k (mem_range.mp hk)
  -- summation by parts
  have hparts := sum_range_by_parts c (fun k => u (k + 1) - u k) m
  simp only [smul_eq_mul] at hparts
  have htel : ∀ n, ∑ i ∈ range n, (u (i + 1) - u i) = u n - u 0 := fun n =>
    sum_range_sub u n
  simp only [htel] at hparts
  have hu2 : ∀ n, ‖u n - u 0‖ ≤ 2 := fun n => by
    refine (norm_sub_le _ _).trans ?_
    rw [hu_norm, hu_norm]; norm_num
  -- bounds on `c`
  have hc_le : ∀ k < m, ‖c k‖ ≤ |w k| / σ := fun k hk => by
    rw [hc, norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hσ0 (hnorm_e k hk)
  have hc_diff : ∀ i, i + 1 < m → ‖c (i + 1) - c i‖ ≤
      |w (i + 1) - w i| / σ + |w i| * |θ (i + 1) - θ i| / σ ^ 2 := by
    intro i hi
    have hi0 : i < m := by omega
    have e1 := he0 (i + 1) hi
    have e0 := he0 i hi0
    have hdecomp : c (i + 1) - c i =
        ((w (i + 1) : ℂ) - w i) / e (i + 1) + (w i : ℂ) * (e i - e (i + 1)) / (e i * e (i + 1)) := by
      rw [hc]; field_simp; ring
    rw [hdecomp]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hσ0 (hnorm_e (i + 1) hi)
    · rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hee : ‖e i - e (i + 1)‖ ≤ |θ (i + 1) - θ i| := by
        have : e i - e (i + 1) = cexp (I * θ i) - cexp (I * θ (i + 1)) := by rw [he]; ring
        rw [this, abs_sub_comm]
        exact norm_exp_I_mul_sub_exp_I_mul_le _ _
      have hden : σ ^ 2 ≤ ‖e i‖ * ‖e (i + 1)‖ := by
        rw [sq]
        exact mul_le_mul (hnorm_e i hi0) (hnorm_e (i + 1) hi) hσ0.le (norm_nonneg _)
      have hq : ‖e i - e (i + 1)‖ / (‖e i‖ * ‖e (i + 1)‖) ≤ |θ (i + 1) - θ i| / σ ^ 2 :=
        calc ‖e i - e (i + 1)‖ / (‖e i‖ * ‖e (i + 1)‖)
            ≤ |θ (i + 1) - θ i| / (‖e i‖ * ‖e (i + 1)‖) :=
              div_le_div_of_nonneg_right hee (by positivity)
          _ ≤ |θ (i + 1) - θ i| / σ ^ 2 :=
              div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hq (abs_nonneg (w i))
  -- the boundary term
  have hb : ‖c (m - 1)‖ * ‖u m - u 0‖ ≤ 2 * |w (m - 1)| / σ := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · have hz : u m - u 0 = 0 := by rw [hm, sub_self]
      rw [hz, norm_zero, mul_zero]
      positivity
    · have h1 := hc_le (m - 1) (by omega)
      have h2 := hu2 m
      calc ‖c (m - 1)‖ * ‖u m - u 0‖ ≤ (|w (m - 1)| / σ) * 2 :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = 2 * |w (m - 1)| / σ := by ring
  have hs : ‖∑ i ∈ range (m - 1), (c (i + 1) - c i) * (u (i + 1) - u 0)‖ ≤
      2 * ∑ i ∈ range (m - 1), (|w (i + 1) - w i| / σ +
        |w i| * |(F (i + 2) - F (i + 1)) - (F (i + 1) - F i)| / σ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hi' : i + 1 < m := by have := mem_range.mp hi; omega
    rw [norm_mul]
    have h1 := hc_diff i hi'
    have hθe : θ (i + 1) - θ i = (F (i + 2) - F (i + 1)) - (F (i + 1) - F i) := by
      simp only [hθdef]
    rw [hθe] at h1
    have h2 := hu2 (i + 1)
    have h0 : 0 ≤ |w (i + 1) - w i| / σ +
        |w i| * |(F (i + 2) - F (i + 1)) - (F (i + 1) - F i)| / σ ^ 2 := by positivity
    calc ‖c (i + 1) - c i‖ * ‖u (i + 1) - u 0‖
        ≤ (|w (i + 1) - w i| / σ +
            |w i| * |(F (i + 2) - F (i + 1)) - (F (i + 1) - F i)| / σ ^ 2) * 2 :=
          mul_le_mul h1 h2 (norm_nonneg _) h0
      _ = _ := by ring
  have hwm : ‖(w m : ℂ) * u m‖ = |w m| := by
    rw [norm_mul, hu_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hmain : ‖∑ k ∈ range (m + 1), (w k : ℂ) * u k‖ ≤ |w m| + (‖c (m - 1)‖ * ‖u m - u 0‖ +
      ‖∑ i ∈ range (m - 1), (c (i + 1) - c i) * (u (i + 1) - u 0)‖) := by
    rw [hsplit, hparts]
    refine (norm_add_le _ _).trans ?_
    rw [hwm]
    have := norm_sub_le (c (m - 1) * (u m - u 0))
      (∑ i ∈ range (m - 1), (c (i + 1) - c i) * (u (i + 1) - u 0))
    rw [norm_mul] at this
    linarith
  exact hmain.trans (by linarith)

/-- The Lorentzian weight `1/(1 + (t − v)²)`. -/
def lorentzWeight (t v : ℝ) : ℝ := 1 / (1 + (t - v) ^ 2)

theorem lorentzWeight_nonneg (t v : ℝ) : 0 ≤ lorentzWeight t v := by
  unfold lorentzWeight; positivity

theorem lorentzWeight_le_one (t v : ℝ) : lorentzWeight t v ≤ 1 := by
  unfold lorentzWeight
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (t - v)]

theorem lorentzWeight_mono {t v₁ v₂ : ℝ} (h12 : v₁ ≤ v₂) (h2 : v₂ ≤ t) :
    lorentzWeight t v₁ ≤ lorentzWeight t v₂ := by
  unfold lorentzWeight
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem lorentzWeight_anti {t v₁ v₂ : ℝ} (h1 : t ≤ v₁) (h12 : v₁ ≤ v₂) :
    lorentzWeight t v₂ ≤ lorentzWeight t v₁ := by
  unfold lorentzWeight
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- **Total variation of Lorentzian weights.** Along any nondecreasing sequence of points the
weights `1/(1 + (t − u_i)²)` have total variation at most `3`. -/
theorem sum_abs_sub_lorentzWeight_le_three (t : ℝ) {u : ℕ → ℝ} (hu : Monotone u) (m : ℕ) :
    ∑ i ∈ range m, |lorentzWeight t (u (i + 1)) - lorentzWeight t (u i)| ≤ 3 := by
  set w : ℕ → ℝ := fun i => lorentzWeight t (u i) with hw
  have key : ∀ m : ℕ, (u m ≤ t → ∑ i ∈ range m, |w (i + 1) - w i| = w m - w 0) ∧
      ∑ i ∈ range m, |w (i + 1) - w i| + w m ≤ 3 := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => by simp, ?_⟩
      simp only [range_zero, sum_empty, zero_add, hw]
      linarith [lorentzWeight_le_one t (u 0)]
    | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hw1 : ∀ i, w i ≤ 1 := fun i => lorentzWeight_le_one t (u i)
      have hw0 : ∀ i, 0 ≤ w i := fun i => lorentzWeight_nonneg t (u i)
      have hmono := hu (Nat.le_succ m)
      rw [sum_range_succ]
      by_cases hm1 : u (m + 1) ≤ t
      · have hm : u m ≤ t := le_trans hmono hm1
        have hinc : w m ≤ w (m + 1) := lorentzWeight_mono hmono hm1
        have hS := ih1 hm
        rw [abs_of_nonneg (by linarith), hS]
        refine ⟨fun _ => by ring, ?_⟩
        linarith [hw1 (m + 1), hw0 0]
      · push Not at hm1
        refine ⟨fun h => absurd h (not_le.mpr hm1), ?_⟩
        by_cases hm : t ≤ u m
        · have hdec : w (m + 1) ≤ w m := lorentzWeight_anti hm hmono
          rw [abs_of_nonpos (by linarith)]
          linarith
        · push Not at hm
          have hS := ih1 hm.le
          rw [hS]
          have habs : |w (m + 1) - w m| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith [hw1 m, hw1 (m + 1), hw0 m, hw0 (m + 1)]
          linarith [hw1 m, hw1 (m + 1), hw0 0]
  have := (key m).2
  linarith [lorentzWeight_nonneg t (u m)]


/-- **Lorentzian phase sums with separated, slowly varying increments.** Let `u` be
nondecreasing with phase increments `λ(u_{k+1} − u_k) ∈ [δ, 2π − δ]`, increment variation at
most `η`, and total Lorentzian weight at most `M`. Then
`‖Σ_{i ≤ m} w_i e^{iλu_i}‖ ≤ 1 + 8/σ + 2Mη/σ²`, `σ = 2 sin(δ/2)`. -/
theorem norm_sum_lorentzWeight_phase_le {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi)
    {t lam η M : ℝ} {u : ℕ → ℝ} (hu : Monotone u) (m : ℕ)
    (hθ : ∀ k < m, δ ≤ lam * (u (k + 1) - u k) ∧ lam * (u (k + 1) - u k) ≤ 2 * Real.pi - δ)
    (hη : ∀ k, k + 1 < m →
      |lam * (u (k + 2) - u (k + 1)) - lam * (u (k + 1) - u k)| ≤ η) (hη0 : 0 ≤ η)
    (hmass : ∑ i ∈ range (m + 1), lorentzWeight t (u i) ≤ M) :
    ‖∑ i ∈ range (m + 1), (lorentzWeight t (u i) : ℂ) * cexp (I * ((lam * u i : ℝ) : ℂ))‖ ≤
      1 + 8 / (2 * Real.sin (δ / 2)) + 2 * M * η / (2 * Real.sin (δ / 2)) ^ 2 := by
  have hσ0 : 0 < 2 * Real.sin (δ / 2) := two_sin_half_pos hδ hδπ
  have hθ' : ∀ k < m, δ ≤ lam * u (k + 1) - lam * u k ∧
      lam * u (k + 1) - lam * u k ≤ 2 * Real.pi - δ := by
    intro k hk
    have := hθ k hk
    constructor <;> linarith [this.1, this.2]
  have hmain := norm_sum_weight_mul_phase_le hδ hδπ (fun i => lam * u i)
    (fun i => lorentzWeight t (u i)) m hθ'
  have hw0 : ∀ i, 0 ≤ lorentzWeight t (u i) := fun i => lorentzWeight_nonneg t (u i)
  have hw1 : ∀ i, lorentzWeight t (u i) ≤ 1 := fun i => lorentzWeight_le_one t (u i)
  have hTV := sum_abs_sub_lorentzWeight_le_three t hu (m - 1)
  have hsumw : ∑ i ∈ range (m - 1), lorentzWeight t (u i) ≤ M := by
    refine le_trans ?_ hmass
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
      fun i _ _ => hw0 i
  have h2 : ∑ i ∈ range (m - 1), |lorentzWeight t (u i)| *
      |(lam * u (i + 2) - lam * u (i + 1)) - (lam * u (i + 1) - lam * u i)| ≤ η * M := by
    calc ∑ i ∈ range (m - 1), |lorentzWeight t (u i)| *
          |(lam * u (i + 2) - lam * u (i + 1)) - (lam * u (i + 1) - lam * u i)|
        ≤ ∑ i ∈ range (m - 1), lorentzWeight t (u i) * η := by
          refine sum_le_sum fun i hi => ?_
          have hi' : i + 1 < m := by have := mem_range.mp hi; omega
          rw [abs_of_nonneg (hw0 i)]
          refine mul_le_mul_of_nonneg_left ?_ (hw0 i)
          have e : (lam * u (i + 2) - lam * u (i + 1)) - (lam * u (i + 1) - lam * u i) =
              lam * (u (i + 2) - u (i + 1)) - lam * (u (i + 1) - u i) := by ring
          rw [e]; exact hη i hi'
      _ = η * ∑ i ∈ range (m - 1), lorentzWeight t (u i) := by rw [← sum_mul, mul_comm]
      _ ≤ η * M := mul_le_mul_of_nonneg_left hsumw hη0
  set σ := 2 * Real.sin (δ / 2) with hσ
  have hpair : ∑ i ∈ range (m - 1), (|lorentzWeight t (u (i + 1)) - lorentzWeight t (u i)| / σ +
      |lorentzWeight t (u i)| *
        |(lam * u (i + 2) - lam * u (i + 1)) - (lam * u (i + 1) - lam * u i)| / σ ^ 2) ≤
      3 / σ + η * M / σ ^ 2 := by
    rw [sum_add_distrib, ← sum_div, ← sum_div]
    have h1 : (∑ i ∈ range (m - 1), |lorentzWeight t (u (i + 1)) - lorentzWeight t (u i)|) / σ ≤
        3 / σ := div_le_div_of_nonneg_right hTV hσ0.le
    have h3 := div_le_div_of_nonneg_right h2 (show (0 : ℝ) ≤ σ ^ 2 by positivity)
    linarith
  have hb1 : |lorentzWeight t (u m)| ≤ 1 := by rw [abs_of_nonneg (hw0 m)]; exact hw1 m
  have hb2 : 2 * |lorentzWeight t (u (m - 1))| / σ ≤ 2 / σ := by
    rw [abs_of_nonneg (hw0 _)]
    exact div_le_div_of_nonneg_right (by linarith [hw1 (m - 1)]) hσ0.le
  have e : 1 + 8 / σ + 2 * M * η / σ ^ 2 = 1 + 2 / σ + 2 * (3 / σ + η * M / σ ^ 2) := by ring
  rw [e]
  refine hmain.trans ?_
  linarith
end

end GaloisForLFunctions.HTGeometry

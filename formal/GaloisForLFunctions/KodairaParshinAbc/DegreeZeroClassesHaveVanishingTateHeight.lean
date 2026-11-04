import GaloisForLFunctions.ArithmeticEffectivityTheory.TatesLimitLaw

/-!
# Degree-zero classes have vanishing Tate height

On a curve `Y` over a number field, a metrized class `x̂` of negative degree has heights
`deg u*(x̂) ≤ O([F:ℚ])` on all points `u`, because `-x̂` is ample up to a bounded change of metric.
Applied to `±x̂ - ε M` with `M` ample, a class of degree zero satisfies
`|deg u*(x̂)| ≤ ε deg u*(M) + O_ε([F:ℚ])` for every `ε > 0`.

On an abelian group `M` with Tate's normalization these two statements become exact, and
Tate's limit law of the corpus (`ArithmeticEffectivityTheory.tateLimit`) removes both error terms:

* a function `q` with `q(2x) = 4q(x)` that is bounded above is `≤ 0`
  (`nonpos_of_two_nsmul_of_bounded_above`);
* if `|h_x| ≤ ε h_M + B_ε` for every `ε > 0`, where `h_x, h_M` satisfy Tate's duplication bound,
  then the Tate limit of `h_x` vanishes identically (`tateLimit_eq_zero_of_degree_zero`);
* consequently, if `h₁ - c h₂` has degree zero in this sense, the Tate limits satisfy
  `q₁ = c q₂` exactly (`tateLimit_eq_smul_of_degree_zero`): the comparison `deg u*(L) ≤
  (1/3 + ε) ω² + O(d)` between two heights whose difference has degree zero becomes an identity of
  canonical heights.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.KodairaParshinAbc

open GaloisForLFunctions.ArithmeticEffectivityTheory

variable {M : Type*} [AddCommGroup M]

theorem two_pow_nsmul_eq {q : M → ℝ} (hq : ∀ x, q (2 • x) = 4 * q x) (n : ℕ) (x : M) :
    q ((2 ^ n : ℕ) • x) = 4 ^ n * q x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_comm, ← smul_smul, hq, ih, pow_succ]
    ring

/-- **Negative degree.**  A function with `q(2x) = 4 q(x)` that is bounded above is `≤ 0`. -/
theorem nonpos_of_two_nsmul_of_bounded_above {q : M → ℝ} (hq : ∀ x, q (2 • x) = 4 * q x)
    {B : ℝ} (hB : ∀ x, q x ≤ B) (x : M) : q x ≤ 0 := by
  have hle : ∀ n : ℕ, q x ≤ B * (1 / 4) ^ n := by
    intro n
    have := hB ((2 ^ n : ℕ) • x)
    rw [two_pow_nsmul_eq hq] at this
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  have hlim : Tendsto (fun n : ℕ => B * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).const_mul B
  exact ge_of_tendsto' hlim hle

/-- **Degree zero, homogeneous form.**  If `q, q_M` satisfy `q(2x) = 4q(x)` and
`|q| ≤ ε q_M + B_ε` for every `ε > 0`, then `q = 0`. -/
theorem eq_zero_of_two_nsmul_of_degree_zero {q qM : M → ℝ} (hq : ∀ x, q (2 • x) = 4 * q x)
    (hqM : ∀ x, qM (2 • x) = 4 * qM x)
    (hcor : ∀ ε > 0, ∃ B, ∀ x, |q x| ≤ ε * qM x + B) (x : M) : q x = 0 := by
  have hbound : ∀ ε > 0, |q x| ≤ ε * qM x := by
    intro ε hε
    obtain ⟨B, hB⟩ := hcor ε hε
    have h1 := nonpos_of_two_nsmul_of_bounded_above (q := fun y => q y - ε * qM y)
      (fun y => by simp only [hq, hqM]; ring) (B := B)
      (fun y => by have := (abs_le.mp (hB y)).2; linarith) x
    have h2 := nonpos_of_two_nsmul_of_bounded_above (q := fun y => -q y - ε * qM y)
      (fun y => by simp only [hq, hqM]; ring) (B := B)
      (fun y => by have := (abs_le.mp (hB y)).1; linarith) x
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  by_contra hne
  have hpos : 0 < |q x| := abs_pos.mpr hne
  have hM : 0 < qM x := by
    have := hbound 1 one_pos
    nlinarith
  have := hbound (|q x| / (2 * qM x)) (by positivity)
  rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hM.ne'] at this
  linarith

/-- **Degree zero has vanishing Tate height.**  Let `h_x, h_M` satisfy Tate's duplication bounds.
If `|h_x| ≤ ε h_M + B_ε` for every `ε > 0`, then `tateLimit h_x = 0`. -/
theorem tateLimit_eq_zero_of_degree_zero {hx hM : M → ℝ} {C C' : ℝ}
    (hCx : ∀ x, |hx (2 • x) - 4 * hx x| ≤ C) (hCM : ∀ x, |hM (2 • x) - 4 * hM x| ≤ C')
    (hcor : ∀ ε > 0, ∃ B, ∀ x, |hx x| ≤ ε * hM x + B) (x : M) : tateLimit hx x = 0 := by
  refine eq_zero_of_two_nsmul_of_degree_zero (tateLimit_two_nsmul hCx) (tateLimit_two_nsmul hCM)
    (fun ε hε => ?_) x
  obtain ⟨B, hB⟩ := hcor ε hε
  refine ⟨B + C / 3 + ε * (C' / 3), fun y => ?_⟩
  have h1 := abs_tateLimit_sub_le hCx y
  have h2 := abs_tateLimit_sub_le hCM y
  have h3 := hB y
  have h2' := (abs_le.mp h2).1
  calc |tateLimit hx y| ≤ |hx y| + |tateLimit hx y - hx y| := by
        have := abs_add_le (hx y) (tateLimit hx y - hx y)
        rwa [add_sub_cancel] at this
    _ ≤ ε * hM y + B + C / 3 := by linarith
    _ ≤ ε * tateLimit hM y + (B + C / 3 + ε * (C' / 3)) := by nlinarith

/-- The Tate limit is linear: `tateLimit (h₁ - c h₂) = tateLimit h₁ - c tateLimit h₂`. -/
theorem tateLimit_sub_smul {h₁ h₂ : M → ℝ} {C₁ C₂ : ℝ}
    (hC₁ : ∀ x, |h₁ (2 • x) - 4 * h₁ x| ≤ C₁) (hC₂ : ∀ x, |h₂ (2 • x) - 4 * h₂ x| ≤ C₂)
    (c : ℝ) :
    tateLimit (fun y => h₁ y - c * h₂ y) = fun y => tateLimit h₁ y - c * tateLimit h₂ y := by
  have hC : ∀ x, |(h₁ (2 • x) - c * h₂ (2 • x)) - 4 * (h₁ x - c * h₂ x)| ≤ C₁ + |c| * C₂ := by
    intro x
    calc |(h₁ (2 • x) - c * h₂ (2 • x)) - 4 * (h₁ x - c * h₂ x)|
        = |(h₁ (2 • x) - 4 * h₁ x) - c * (h₂ (2 • x) - 4 * h₂ x)| := by ring_nf
      _ ≤ |h₁ (2 • x) - 4 * h₁ x| + |c * (h₂ (2 • x) - 4 * h₂ x)| := abs_sub _ _
      _ ≤ C₁ + |c| * C₂ := by
          rw [abs_mul]
          exact add_le_add (hC₁ x) (mul_le_mul_of_nonneg_left (hC₂ x) (abs_nonneg c))
  refine eq_of_two_nsmul_of_bounded (h := fun y => h₁ y - c * h₂ y)
    (tateLimit_two_nsmul hC) (fun y => by
      simp only [tateLimit_two_nsmul hC₁, tateLimit_two_nsmul hC₂]; ring)
    (abs_tateLimit_sub_le hC) (B₂ := C₁ / 3 + |c| * (C₂ / 3)) (fun y => ?_)
  have e1 := abs_tateLimit_sub_le hC₁ y
  have e2 := abs_tateLimit_sub_le hC₂ y
  calc |tateLimit h₁ y - c * tateLimit h₂ y - (h₁ y - c * h₂ y)|
      = |(tateLimit h₁ y - h₁ y) - c * (tateLimit h₂ y - h₂ y)| := by ring_nf
    _ ≤ |tateLimit h₁ y - h₁ y| + |c * (tateLimit h₂ y - h₂ y)| := abs_sub _ _
    _ ≤ C₁ / 3 + |c| * (C₂ / 3) := by
        rw [abs_mul]
        exact add_le_add e1 (mul_le_mul_of_nonneg_left e2 (abs_nonneg c))

/-- **Heights with a degree-zero difference have proportional Tate limits.**  If
`|h₁ - c h₂| ≤ ε h₂ + B_ε` for every `ε > 0`, then `tateLimit h₁ = c · tateLimit h₂`. -/
theorem tateLimit_eq_smul_of_degree_zero {h₁ h₂ : M → ℝ} {C₁ C₂ c : ℝ}
    (hC₁ : ∀ x, |h₁ (2 • x) - 4 * h₁ x| ≤ C₁) (hC₂ : ∀ x, |h₂ (2 • x) - 4 * h₂ x| ≤ C₂)
    (hcor : ∀ ε > 0, ∃ B, ∀ x, |h₁ x - c * h₂ x| ≤ ε * h₂ x + B) (x : M) :
    tateLimit h₁ x = c * tateLimit h₂ x := by
  have hC : ∀ x, |(h₁ (2 • x) - c * h₂ (2 • x)) - 4 * (h₁ x - c * h₂ x)| ≤ C₁ + |c| * C₂ := by
    intro x
    calc |(h₁ (2 • x) - c * h₂ (2 • x)) - 4 * (h₁ x - c * h₂ x)|
        = |(h₁ (2 • x) - 4 * h₁ x) - c * (h₂ (2 • x) - 4 * h₂ x)| := by ring_nf
      _ ≤ |h₁ (2 • x) - 4 * h₁ x| + |c * (h₂ (2 • x) - 4 * h₂ x)| := abs_sub _ _
      _ ≤ C₁ + |c| * C₂ := by
          rw [abs_mul]
          exact add_le_add (hC₁ x) (mul_le_mul_of_nonneg_left (hC₂ x) (abs_nonneg c))
  have h0 := tateLimit_eq_zero_of_degree_zero (hx := fun y => h₁ y - c * h₂ y) hC hC₂ hcor x
  rw [tateLimit_sub_smul hC₁ hC₂ c] at h0
  linarith

end GaloisForLFunctions.KodairaParshinAbc

import Mathlib

/-!
# The exponential profile of a bounded coefficient sequence

For a coefficient sequence with `‖f n‖ ≤ 1` the exponential profile
`F x = ∑ f n * e^{-n x}` is continuous on `(0,∞)`, decays like `e^{-x}` at infinity, and on the
half-plane of absolute convergence its Mellin transform is the Gamma-completed Dirichlet series,
`mellin F s = Γ s * L f s` (`mellin_coeffLaplaceProfile_eq_gamma_mul_LSeries`).

Written radially, `F x = ∑ f n * (e^{-x}) ^ n`, so the profile is exactly the Abel series evaluated
at the radius `e^{-x}` (`coeffLaplaceProfile_eq_tsum_pow`).
-/

open Complex Filter Set MeasureTheory
open scoped LSeries.notation Topology

namespace GaloisForLFunctions.HTGeometry

/-- The exponential (Laplace) profile `∑ f n e^{-n x}` of a coefficient sequence. -/
noncomputable def coeffLaplaceProfile (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, f n * Complex.exp (-((n : ℝ) * x : ℝ))

variable {f : ℕ → ℂ}

/-- The pure exponential majorant used throughout. -/
theorem summable_exp_neg_nat_mul {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => Real.exp (-((n : ℝ) * x)) := by
  refine (Real.summable_pow_mul_exp_neg_nat_mul 0 hx).congr fun n => ?_
  rw [pow_zero, one_mul]
  congr 1
  ring

theorem summable_coeffLaplaceTerm (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => f n * Complex.exp (-((n : ℝ) * x : ℝ)) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_exp_neg_nat_mul hx)
  rw [norm_mul, Complex.norm_exp]
  have hexp : 0 ≤ Real.exp (-((n : ℝ) * x)) := (Real.exp_pos _).le
  simpa using mul_le_mul_of_nonneg_right (hf n) hexp

theorem coeffLaplaceTerm_hasSum (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => f n * Complex.exp (-((n : ℝ) * x : ℝ))) (coeffLaplaceProfile f x) :=
  (summable_coeffLaplaceTerm hf hx).hasSum

theorem coeffLaplaceProfile_weight_summable (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖f n‖ / (n : ℝ) ^ s.re := by
  have h := (LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) hs).norm
  refine h.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    rw [if_pos rfl, Nat.cast_zero, Real.zero_rpow (by linarith : s.re ≠ 0), div_zero]
  · simp [hn]

/-- **Mellin–Dirichlet identity.**  On the half-plane of absolute convergence the Mellin transform
of the exponential profile is `Γ(s)` times the Dirichlet series of the coefficients. -/
theorem mellin_coeffLaplaceProfile_eq_gamma_mul_LSeries
    (hf : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0) {s : ℂ} (hs : 1 < s.re) :
    mellin (coeffLaplaceProfile f) s = Complex.Gamma s * LSeries f s := by
  have hp : ∀ n : ℕ, f n = 0 ∨ 0 < (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · left
      rw [hn, hf0]
    · right
      exact_mod_cast Nat.pos_of_ne_zero hn
  have hs0 : 0 < s.re := by linarith
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun n : ℕ => f n * Real.exp (-(n : ℝ) * t)) (coeffLaplaceProfile f t) := by
    intro t ht
    convert coeffLaplaceTerm_hasSum hf ht using 2 with n
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  have hmellin : HasSum (fun n : ℕ => Complex.Gamma s * f n / (n : ℂ) ^ s)
      (mellin (coeffLaplaceProfile f) s) :=
    hasSum_mellin hp hs0 hF (coeffLaplaceProfile_weight_summable hf hs)
  rw [← hmellin.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def₀ hf0 s n, div_eq_mul_inv, Complex.cpow_neg]
  ring

theorem continuousOn_coeffLaplaceProfile (hf : ∀ n, ‖f n‖ ≤ 1) :
    ContinuousOn (coeffLaplaceProfile f) (Ioi 0) := by
  intro x hx
  set a : ℝ := x / 2 with ha_def
  have hxpos : 0 < x := hx
  have ha : 0 < a := by rw [ha_def]; linarith
  have hax : a < x := by rw [ha_def]; linarith
  have hmajor : Summable fun n : ℕ => Real.exp (-((n : ℝ) * a)) := summable_exp_neg_nat_mul ha
  have hcontinuous : ContinuousOn
      (fun y : ℝ => ∑' n : ℕ, f n * Complex.exp (-((n : ℝ) * y : ℝ))) (Ici a) := by
    refine continuousOn_tsum (fun n => ?_) hmajor (fun n y hy => ?_)
    · fun_prop
    · rw [norm_mul, Complex.norm_exp]
      have hexp : Real.exp (-((n : ℝ) * y)) ≤ Real.exp (-((n : ℝ) * a)) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hmul : (n : ℝ) * a ≤ (n : ℝ) * y := mul_le_mul_of_nonneg_left hy hn
        linarith
      calc ‖f n‖ * Real.exp (-((n : ℝ) * y))
          ≤ 1 * Real.exp (-((n : ℝ) * y)) :=
            mul_le_mul_of_nonneg_right (hf n) (Real.exp_pos _).le
        _ ≤ Real.exp (-((n : ℝ) * a)) := by simpa using hexp
  exact (hcontinuous x hax.le).continuousAt (Ici_mem_nhds hax) |>.continuousWithinAt

theorem coeffLaplaceProfile_locallyIntegrableOn (hf : ∀ n, ‖f n‖ ≤ 1) :
    LocallyIntegrableOn (coeffLaplaceProfile f) (Ioi 0) :=
  (continuousOn_coeffLaplaceProfile hf).locallyIntegrableOn measurableSet_Ioi

theorem norm_coeffLaplaceProfile_le_exp_neg (hf : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖coeffLaplaceProfile f x‖ ≤ Real.exp (-x) * ∑' n : ℕ, Real.exp (-(n : ℝ)) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsum := summable_coeffLaplaceTerm hf hxpos
  have hshift : coeffLaplaceProfile f x =
      ∑' n : ℕ, f (n + 1) * Complex.exp (-(((n + 1 : ℕ) : ℝ) * x : ℝ)) := by
    have hsplit := hsum.sum_add_tsum_nat_add 1
    rw [coeffLaplaceProfile]
    simpa [hf0] using hsplit.symm
  have hshiftSum : Summable
      fun n : ℕ => f (n + 1) * Complex.exp (-(((n + 1 : ℕ) : ℝ) * x : ℝ)) :=
    hsum.comp_injective Nat.succ_injective
  have hgeom : Summable fun n : ℕ => Real.exp (-x) * Real.exp (-(n : ℝ)) :=
    Real.summable_exp_neg_nat.mul_left _
  rw [hshift]
  calc ‖∑' n : ℕ, f (n + 1) * Complex.exp (-(((n + 1 : ℕ) : ℝ) * x : ℝ))‖
      ≤ ∑' n : ℕ, ‖f (n + 1) * Complex.exp (-(((n + 1 : ℕ) : ℝ) * x : ℝ))‖ :=
        norm_tsum_le_tsum_norm hshiftSum.norm
    _ ≤ ∑' n : ℕ, Real.exp (-x) * Real.exp (-(n : ℝ)) := by
        refine hshiftSum.norm.tsum_le_tsum (fun n => ?_) hgeom
        rw [norm_mul, Complex.norm_exp]
        have hexp : Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) ≤ Real.exp (-x) * Real.exp (-(n : ℝ)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          push_cast
          nlinarith
        exact (mul_le_mul_of_nonneg_right (hf (n + 1)) (Real.exp_pos _).le).trans
          (by simpa using hexp)
    _ = Real.exp (-x) * ∑' n : ℕ, Real.exp (-(n : ℝ)) := by rw [tsum_mul_left]

theorem coeffLaplaceProfile_isBigO_exp_neg (hf : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0) :
    coeffLaplaceProfile f =O[atTop] fun x : ℝ => Real.exp (-1 * x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨∑' n : ℕ, Real.exp (-(n : ℝ)), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := norm_coeffLaplaceProfile_le_exp_neg hf hf0 hx
  rw [neg_one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa [mul_comm] using h

/-- The exponential profile is the Abel series at radius `e^{-x}`. -/
theorem coeffLaplaceProfile_eq_tsum_pow (f : ℕ → ℂ) (x : ℝ) :
    coeffLaplaceProfile f x = ∑' n : ℕ, f n * ((Real.exp (-x) : ℝ) : ℂ) ^ n := by
  rw [coeffLaplaceProfile]
  refine tsum_congr fun n => ?_
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem summable_norm_coeff_mul_pow (hf : ∀ n, ‖f n‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ‖f n * (r : ℂ) ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one hr0 hr1)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hpow : (0 : ℝ) ≤ r ^ n := pow_nonneg hr0 n
  simpa using mul_le_mul_of_nonneg_right (hf n) hpow

end GaloisForLFunctions.HTGeometry

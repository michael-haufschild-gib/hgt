import Mathlib

/-!
# Theta series of a Dirichlet series

For coefficients `a₁, a₂, …` with `Σ ‖a_n‖ n^{-σ} < ∞` for every `σ > 1`, the theta series
`θ_a(x) = Σ_{n≥1} a_n e^{-π n² x}` is continuous on `(0, ∞)` and satisfies
`‖θ_a(x)‖ ≤ (π x)^{-b} Σ ‖a_n‖ n^{-2b}` for `0 ≤ b ≤ 1` (`norm_coeffTheta_le`).  The bound comes
from `e^{-y} ≤ y^{-b}`.  Hence `θ_a` is Mellin-convergent on `1/2 < Re w < 1`
(`mellinConvergent_coeffTheta`).  Its Mellin transform at `s/2` is `Γ_ℝ(s) Σ a_n n^{-s}`
for `Re s > 1` (`mellin_coeffTheta`).
-/

open Complex MeasureTheory Filter Topology Set Asymptotics

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `θ_a(x) = Σ_{n≥1} a_n e^{-π n² x}`. -/
def coeffTheta (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, a (n + 1) * ((Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ)

/-- The Dirichlet series `Σ_{n≥1} a_n n^{-s}`. -/
def coeffDirichlet (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, a (n + 1) / (((n : ℝ) + 1 : ℝ) : ℂ) ^ s

/-- `e^{-y} ≤ y^{-b}` for `y > 0` and `0 ≤ b ≤ 1`. -/
theorem exp_neg_le_rpow_neg_of_le_one {y b : ℝ} (hy : 0 < y) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.exp (-y) ≤ y ^ (-b) := by
  have hyb : y ^ b ≤ 1 + y := by
    rcases le_total y 1 with h | h
    · have := Real.rpow_le_one hy.le h hb0
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h hb1
      rw [Real.rpow_one] at this
      linarith
  have hexp : y ^ b ≤ Real.exp y := hyb.trans (by linarith [Real.add_one_le_exp y])
  rw [Real.exp_neg, Real.rpow_neg hy.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hy b) hexp

/-- The termwise bound `‖a_n e^{-π n² x}‖ ≤ (π x)^{-b} ‖a_n‖ n^{-2b}`. -/
theorem norm_thetaTerm_le (a : ℕ → ℂ) {x b : ℝ} (hx : 0 < x) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (n : ℕ) :
    ‖a (n + 1) * ((Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ)‖ ≤
      (Real.pi * x) ^ (-b) * (‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * b)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hy : 0 < Real.pi * ((n : ℝ) + 1) ^ 2 * x := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 := exp_neg_le_rpow_neg_of_le_one hy hb0 hb1
  rw [show -Real.pi * ((n : ℝ) + 1) ^ 2 * x = -(Real.pi * ((n : ℝ) + 1) ^ 2 * x) by ring]
  have h2 : (Real.pi * ((n : ℝ) + 1) ^ 2 * x) ^ (-b) =
      (Real.pi * x) ^ (-b) * (((n : ℝ) + 1) ^ (2 * b))⁻¹ := by
    rw [show Real.pi * ((n : ℝ) + 1) ^ 2 * x = (Real.pi * x) * ((n : ℝ) + 1) ^ 2 by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hn.le, show ((2 : ℕ) : ℝ) * -b = -(2 * b) by push_cast; ring,
      Real.rpow_neg hn.le]
  calc ‖a (n + 1)‖ * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * x))
      ≤ ‖a (n + 1)‖ * (Real.pi * ((n : ℝ) + 1) ^ 2 * x) ^ (-b) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (Real.pi * x) ^ (-b) * (‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * b)) := by
        rw [h2, div_eq_mul_inv]
        ring

theorem summable_norm_thetaTerm (a : ℕ → ℂ) {x b : ℝ} (hx : 0 < x) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * b)) :
    Summable fun n : ℕ =>
      ‖a (n + 1) * ((Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ)‖ :=
  (ha.mul_left ((Real.pi * x) ^ (-b))).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_thetaTerm_le a hx hb0 hb1)

/-- `‖θ_a(x)‖ ≤ (π x)^{-b} Σ ‖a_n‖ n^{-2b}` for `0 ≤ b ≤ 1`. -/
theorem norm_coeffTheta_le (a : ℕ → ℂ) {x b : ℝ} (hx : 0 < x) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * b)) :
    ‖coeffTheta a x‖ ≤
      (Real.pi * x) ^ (-b) * ∑' n : ℕ, ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * b) := by
  unfold coeffTheta
  refine (norm_tsum_le_tsum_norm (summable_norm_thetaTerm a hx hb0 hb1 ha)).trans ?_
  rw [← tsum_mul_left]
  exact (summable_norm_thetaTerm a hx hb0 hb1 ha).tsum_le_tsum (norm_thetaTerm_le a hx hb0 hb1)
    (ha.mul_left _)

theorem continuousOn_coeffTheta (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ)) :
    ContinuousOn (coeffTheta a) (Ioi 0) := by
  have hloc : ∀ δ : ℝ, 0 < δ → ContinuousOn (coeffTheta a) (Ioi δ) := by
    intro δ hδ
    refine continuousOn_tsum (fun n => by fun_prop)
      (ha.mul_left ((Real.pi * δ) ^ (-(1 : ℝ)))) fun n x hx => ?_
    have hxδ : δ < x := hx
    have h1 := norm_thetaTerm_le a (hδ.trans hxδ) zero_le_one le_rfl n
    rw [mul_one] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [Real.rpow_neg_one, Real.rpow_neg_one]
    exact inv_anti₀ (by positivity) (by nlinarith [Real.pi_pos])
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  exact ((hloc (x / 2) (by positivity)).continuousAt
    (Ioi_mem_nhds (by linarith))).continuousWithinAt

/-- The theta series is Mellin-convergent on `1/2 < Re w < 1`. -/
theorem mellinConvergent_coeffTheta (a : ℕ → ℂ)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {w : ℂ} (hw1 : 1 / 2 < w.re) (hw2 : w.re < 1) :
    MellinConvergent (coeffTheta a) w := by
  set b : ℝ := (w.re + 1 / 2) / 2 with hb
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  have hb1 : b ≤ 1 := by rw [hb]; linarith
  have hsb : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * b) :=
    ha _ (by rw [hb]; linarith)
  have hs1 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * (1 : ℝ)) :=
    ha _ (by norm_num)
  refine mellinConvergent_of_isBigO_rpow (a := 1) (b := b)
    ((continuousOn_coeffTheta a (by simpa using hs1)).locallyIntegrableOn measurableSet_Ioi)
    ?_ hw2 ?_ (by rw [hb]; linarith)
  · refine IsBigO.of_bound ((Real.pi) ^ (-(1 : ℝ)) *
      ∑' n : ℕ, ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * (1 : ℝ))) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have h := norm_coeffTheta_le a hx zero_le_one le_rfl hs1
    rw [Real.mul_rpow Real.pi_pos.le hx.le] at h
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]
    calc ‖coeffTheta a x‖ ≤ Real.pi ^ (-(1 : ℝ)) * x ^ (-(1 : ℝ)) *
          ∑' n : ℕ, ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * (1 : ℝ)) := h
      _ = _ := by ring
  · refine IsBigO.of_bound ((Real.pi) ^ (-b) *
      ∑' n : ℕ, ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * b)) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have h := norm_coeffTheta_le a hx0 hb0 hb1 hsb
    rw [Real.mul_rpow Real.pi_pos.le hx0.le] at h
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    calc ‖coeffTheta a x‖ ≤ Real.pi ^ (-b) * x ^ (-b) *
          ∑' n : ℕ, ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 * b) := h
      _ = _ := by ring

/-- **Mellin transform of a theta series.**  For `Re s > 1`,
`∫₀^∞ x^{s/2-1} θ_a(x) dx = Γ_ℝ(s) Σ_{n≥1} a_n n^{-s}`. -/
theorem mellin_coeffTheta (a : ℕ → ℂ)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (coeffTheta a) (s / 2) = Complex.Gammaℝ s * coeffDirichlet a s := by
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun n : ℕ => if ((n : ℝ) + 1) = 0 then 0 else
      a (n + 1) * ((Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) : ℝ) : ℂ)) (coeffTheta a t) := by
    intro t ht
    have hsum := (summable_norm_thetaTerm a ht zero_le_one le_rfl
      (by simpa using ha 2 (by norm_num))).of_norm
    have hne : ∀ n : ℕ, ((n : ℝ) + 1) ≠ 0 := fun n => by positivity
    simp only [hne, if_false]
    exact hsum.hasSum
  have hsum : Summable fun n : ℕ => ‖a (n + 1)‖ / |(n : ℝ) + 1| ^ s.re := by
    have hne : ∀ n : ℕ, |(n : ℝ) + 1| = (n : ℝ) + 1 := fun n => abs_of_pos (by positivity)
    simp only [hne]
    exact ha _ hs
  have h := hasSum_mellin_pi_mul_sq (a := fun n : ℕ => a (n + 1)) (r := fun n : ℕ => (n : ℝ) + 1)
    (by linarith) hF hsum
  rw [← h.tsum_eq, coeffDirichlet, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), mul_div_assoc]

end GaloisForLFunctions.HTGeometry

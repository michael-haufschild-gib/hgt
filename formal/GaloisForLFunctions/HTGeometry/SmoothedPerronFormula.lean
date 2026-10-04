import GaloisForLFunctions.PNTPlus.MediumPNT

/-!
# The smoothed Perron formula for bounded coefficients

Let `ν ≥ 0` be a `C¹` bump supported in `[1/2, 2]` with `∫_0^∞ ν(x) dx/x = 1`, and let
`Smooth1 ν ε` be the corresponding smoothed indicator of `(0, 1]` (PNTPlus).  For a sequence
`c` with `|c(n)| ≤ 1`, `X > 0`, `0 < ε < 1` and `1 < σ ≤ 2`,

`(1/2πi) ∫_{(σ)} L(c, s) 𝓜[Smooth1 ν ε](s) X^s ds = Σ_n c(n) Smooth1 ν ε (n/X)`
(`verticalIntegral'_eq_tsum_smooth1`).

This is the PNTPlus identity for `−ζ'/ζ` (`Chebyshev.SmoothedChebyshevDirichlet`) with the von
Mangoldt function replaced by an arbitrary bounded sequence: expand the Dirichlet series,
exchange sum and integral (absolute convergence), and apply Mellin inversion to each term.

**Mellin bounds.**  On `σ₁ ≤ Re s ≤ 2`: `|𝓜[Smooth1 ν ε](s)| ≤ C/|s|` (`norm_mellin_smooth1_le`)
and `≤ C/(ε|s|²)` (PNTPlus `MellinOfSmooth1b`).
-/

open Set Function Filter Complex Real MeasureTheory

local notation (name := smoothedPerronMellin) "𝓜" => mellin

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SmoothedPerron

variable {ν : ℝ → ℝ}

theorem LSeries_eq_tsum_div (c : ℕ → ℂ) (hc0 : c 0 = 0) (s : ℂ) :
    LSeries c s = ∑' n, c n / (n : ℂ) ^ s := by
  unfold LSeries
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term, hc0]
  · rw [LSeries.term_of_ne_zero hn.ne']

set_option backward.isDefEq.respectTransparency false in
theorem integral_tsum_swap (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2) (mass_one : ∫ (x : ℝ) in Ioi 0, ν x / x = 1)
    (c : ℕ → ℂ) (hc0 : c 0 = 0) (hc : ∀ n, ‖c n‖ ≤ 1) {X : ℝ} (X_pos : 0 < X) {ε : ℝ}
    (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ), ∑' (n : ℕ), c n / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 ν ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
      ∑' (n : ℕ), ∫ (t : ℝ), c n / (n : ℂ) ^ (σ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by
  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + ↑a * I) := by
    refine continuous_iff_continuousAt.mpr fun a => ?_
    have hd := Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩ νpos mass_one
      (s := (σ : ℂ) + (a : ℂ) * I) (by simp; linarith)
    exact ContinuousAt.comp (g := 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)))
      (f := fun a : ℝ => (σ : ℂ) + (a : ℂ) * I) hd.continuousAt (by fun_prop)
  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re,
      mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast
  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simp only [i_eq_zero, hc0, zero_div, zero_mul]
      exact aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp [i_eq_zero, x_neq_zero])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        (Real.summable_one_div_nat_rpow.mpr σ_gt)
      have h1 : ‖c n‖ ≤ 1 := hc n
      gcongr
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν
        mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

set_option backward.isDefEq.respectTransparency false in
/-- **The smoothed Perron formula.** -/
theorem verticalIntegral'_eq_tsum_smooth1 (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2) (mass_one : ∫ (x : ℝ) in Ioi 0, ν x / x = 1)
    (c : ℕ → ℂ) (hc0 : c 0 = 0) (hc : ∀ n, ‖c n‖ ≤ 1) {X : ℝ} (X_pos : 0 < X) {ε : ℝ}
    (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    VerticalIntegral' (fun s => LSeries c s * 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s) σ =
      ∑' n, c n * Smooth1 ν ε (n / X) := by
  dsimp [VerticalIntegral', VerticalIntegral]
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, c n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), c n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, c n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, c n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, c n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, c n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [LSeries_eq_tsum_div c hc0, ← tsum_mul_right, ← tsum_mul_right]
  · congr
    exact integral_tsum_swap diffν νpos suppν mass_one c hc0 hc X_pos εpos ε_lt_one σ_gt σ_le
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
    by_cases n_ne_zero : n = 0
    · simp [n_ne_zero, hc0]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    · have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + I * t) ?_ ?_
      · push_cast at this ⊢
        rw [← this, div_mul_cancel₀]
        · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
      · apply div_nonneg (by linarith : 0 ≤ X); simp
      · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
        not_false_eq_true]
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
  · congr
    ext n
    by_cases n_zero : n = 0
    · simp [n_zero, hc0]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    have := mellinInv_mellin_eq σ (f := fun x ↦ (Smooth1 ν ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [mellinInv, VerticalIntegral] at this
      convert! this using 4
      · norm_cast
      · rw [mul_comm]
        norm_cast
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffν suppν ⟨εpos, ε_lt_one⟩ νpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν mass_one εpos
        ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffν νpos suppν εpos (by positivity)

end GaloisForLFunctions.HTGeometry.SmoothedPerron

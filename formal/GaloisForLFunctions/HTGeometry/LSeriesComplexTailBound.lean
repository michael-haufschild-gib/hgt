import GaloisForLFunctions.HTGeometry.LSeriesPolynomialWeightUniqueness

/-!
# Uniform complex half-plane tail bound for ordinary Dirichlet series

After the first surviving coefficient at `n`, multiplication by `n^s` leaves a tail bounded by
`C (n/(n+1))^Re(s)`.  Unlike the real-ray version, this estimate is uniform in the imaginary
direction and therefore applies on positive-length arcs of expanding circles.
-/

namespace GaloisForLFunctions

open Filter Set Topology LSeries

noncomputable section

/-- The arc `[0, π/3]` of a radius-`R` circle lies in `Re s ≥ R/2`. -/
theorem half_mul_le_circleMap_re {R theta : ℝ} (hR : 0 ≤ R)
    (htheta : theta ∈ Set.Icc (0 : ℝ) (Real.pi / 3)) :
    R / 2 ≤ (circleMap 0 R theta).re := by
  have hcos : (1 : ℝ) / 2 ≤ Real.cos theta := by
    have hpiThird : Real.pi / 3 ≤ Real.pi := by nlinarith [Real.pi_pos]
    have h := Real.cos_le_cos_of_nonneg_of_le_pi htheta.1 hpiThird htheta.2
    rw [Real.cos_pi_div_three] at h
    exact h
  rw [circleMap_zero, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero, Real.exp_zero, one_mul]
  nlinarith

/-- **Complex half-plane exponential domination of a pinned Dirichlet tail.** If coefficients
strictly below `n ≥ 1` vanish, the normalized tail decays geometrically in `Re s`, uniformly in
`Im s`. -/
theorem exists_norm_cpow_mul_LSeries_sub_le {g : ℕ → ℂ} {n : ℕ} (hn : 1 ≤ n) {x₁ : ℝ}
    (hsum : LSeriesSummable g (x₁ : ℂ))
    (hvan : ∀ m, 1 ≤ m → m < n → g m = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, x₁ ≤ s.re →
      ‖(n : ℂ) ^ s * LSeries g s - g n‖ ≤
        C * ((n : ℝ) / (n + 1)) ^ s.re := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set theta : ℝ := (n : ℝ) / (n + 1) with htheta
  have hthetaPos : 0 < theta := by positivity
  set majorant : ℕ → ℝ := fun m =>
    if m ≤ n then 0 else ‖g m‖ * ((n : ℝ) ^ x₁ / (m : ℝ) ^ x₁) with hmajorantDef
  have hmajorantNonneg : ∀ m, 0 ≤ majorant m := by
    intro m
    simp only [hmajorantDef]
    split_ifs
    · exact le_rfl
    · positivity
  have hmajorantEq : ∀ m, n < m →
      majorant m = (n : ℝ) ^ x₁ * ‖LSeries.term g (x₁ : ℂ) m‖ := by
    intro m hm
    rw [hmajorantDef]
    simp only [if_neg (by omega : ¬m ≤ n)]
    rw [LSeries.term_def, if_neg (by omega : m ≠ 0), norm_div,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < m)]
    simp only [Complex.ofReal_re]
    ring
  have hmajorantSummable : Summable majorant := by
    apply Summable.of_nonneg_of_le hmajorantNonneg _
      (hsum.norm.mul_left ((n : ℝ) ^ x₁))
    intro m
    by_cases hm : m ≤ n
    · rw [hmajorantDef]
      simp only [if_pos hm]
      positivity
    · rw [hmajorantEq m (by omega)]
  set C₀ : ℝ := ∑' m, majorant m
  have hC₀ : 0 ≤ C₀ := tsum_nonneg hmajorantNonneg
  refine ⟨C₀ * theta ^ (-x₁), by positivity, ?_⟩
  intro s hs
  have hsummable : LSeriesSummable g s := hsum.of_re_le_re (by simpa using hs)
  have hscaled : Summable fun m => (n : ℂ) ^ s * LSeries.term g s m :=
    hsummable.mul_left _
  have hncpow : (n : ℂ) ^ s ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
    positivity
  have htermN : (n : ℂ) ^ s * LSeries.term g s n = g n := by
    rw [LSeries.term_def, if_neg (by omega : n ≠ 0)]
    field_simp
  have hLSeries : (n : ℂ) ^ s * LSeries g s =
      ∑' m, (n : ℂ) ^ s * LSeries.term g s m := by
    rw [LSeries, tsum_mul_left]
  have hpoint : ∀ m : ℕ,
      ‖if m = n then 0 else (n : ℂ) ^ s * LSeries.term g s m‖ ≤
        majorant m * theta ^ (s.re - x₁) := by
    intro m
    by_cases hmn : m = n
    · simp only [if_pos hmn, norm_zero]
      positivity
    rw [if_neg hmn]
    rcases Nat.lt_or_ge m (n + 1) with hml | hmg
    · have htermZero : LSeries.term g s m = 0 := by
        rcases Nat.eq_zero_or_pos m with rfl | hm1
        · exact LSeries.term_zero g s
        · rw [LSeries.term_def, if_neg (by omega : m ≠ 0),
            hvan m hm1 (by omega), zero_div]
      rw [htermZero, mul_zero, norm_zero]
      positivity
    · have hm0 : 0 < m := by omega
      have hnm : (n : ℝ) < m := by exact_mod_cast (by omega : n < m)
      rw [norm_mul, LSeries.term_def, if_neg (by omega : m ≠ 0), norm_div,
        Complex.norm_natCast_cpow_of_pos hm0,
        Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
      have hratio : (n : ℝ) ^ s.re * (‖g m‖ / (m : ℝ) ^ s.re) =
          (‖g m‖ * ((n : ℝ) ^ x₁ / (m : ℝ) ^ x₁)) *
            ((n : ℝ) / (m : ℝ)) ^ (s.re - x₁) := by
        rw [Real.div_rpow hn0.le (by positivity : (0 : ℝ) ≤ (m : ℝ))]
        rw [Real.rpow_sub hn0,
          Real.rpow_sub (by positivity : (0 : ℝ) < (m : ℝ))]
        field_simp
      have hmajorantM : ‖g m‖ * ((n : ℝ) ^ x₁ / (m : ℝ) ^ x₁) =
          majorant m := by
        rw [hmajorantDef]
        simp only [if_neg (by omega : ¬m ≤ n)]
      rw [hratio, hmajorantM]
      apply mul_le_mul_of_nonneg_left _ (hmajorantNonneg m)
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      rw [htheta, div_le_div_iff₀ (by positivity) (by positivity)]
      have hm1 : (n : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : n + 1 ≤ m)
      nlinarith
  have hdomSummable : Summable fun m =>
      majorant m * theta ^ (s.re - x₁) := hmajorantSummable.mul_right _
  have hnormSummable : Summable fun m =>
      ‖if m = n then 0 else (n : ℂ) ^ s * LSeries.term g s m‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hpoint hdomSummable
  have hsplit := hscaled.tsum_eq_add_tsum_ite n
  rw [hLSeries, hsplit, htermN, add_sub_cancel_left]
  calc
    ‖∑' m, if m = n then 0 else (n : ℂ) ^ s * LSeries.term g s m‖
        ≤ ∑' m, ‖if m = n then 0 else (n : ℂ) ^ s * LSeries.term g s m‖ :=
      norm_tsum_le_tsum_norm hnormSummable
    _ ≤ ∑' m, majorant m * theta ^ (s.re - x₁) :=
      Summable.tsum_le_tsum hpoint hnormSummable hdomSummable
    _ = C₀ * theta ^ (s.re - x₁) := by rw [tsum_mul_right]
    _ = C₀ * theta ^ (-x₁) * theta ^ s.re := by
      rw [show s.re - x₁ = -x₁ + s.re by ring,
        Real.rpow_add hthetaPos, ← mul_assoc]

end

end GaloisForLFunctions

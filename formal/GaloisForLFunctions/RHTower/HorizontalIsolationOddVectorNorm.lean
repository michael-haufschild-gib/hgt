import GaloisForLFunctions.RHTower.HorizontalIsolationCrossPairDecay

/-!
# The odd vector of a barely off-line pair is small

For an off-line zero `p = ½ + ε_p + iγ_p`, the sampled imaginary vector is
`h_p(k) = Im φ̂(γ_p − iε_p − τ_k)/√c`.  On the full sampling grid its square sum is a window
integral (`hasSum_im_sq_grid`):

  `Σ_j (Im φ̂(w_j − iε))² = L ∫_{−L/2}^{L/2} φ(u)² sinh²(εu) du`,   `w_j = γ − (T + j·2π/L)`.

This is sampling Parseval for the window `−iφ sinh(ε·)`, whose transform is `Im φ̂(· − iε)`.  The
block keeps finitely many of these nonnegative terms, so
`‖h_p‖² ≤ L ∫ φ² sinh²(ε_p u) du / c` (`norm_sq_blockImVec_le`).  Since `|sinh x| ≤ |x| cosh x`,

  `‖h_p‖² ≤ L ε_p² ∫ u² φ² cosh²(ε_p u) du / c ≤ L ε_p² cosh²(ε_p L/2) ∫ u² φ² du / c`

(`norm_sq_blockImVec_le_sq_mul`, `norm_sq_blockImVec_le_sq_mul_cosh`).  Relative to
`‖g_p‖² ≈ L ∫φ²/c`, this is `O((ε_p L)²)`.
-/

open Complex MeasureTheory
open scoped RealInnerProductSpace

namespace RHTower

noncomputable section

/-- `|sinh x| ≤ |x| cosh x`. -/
private theorem abs_sinh_le_abs_mul_cosh (x : ℝ) : |Real.sinh x| ≤ |x| * Real.cosh x := by
  have key : ∀ y : ℝ, 0 ≤ y → Real.sinh y ≤ y * Real.cosh y := by
    intro y hy
    rcases eq_or_lt_of_le hy with h0 | hpos
    · rw [← h0]; simp
    obtain ⟨ξ, hξ, hd⟩ := exists_deriv_eq_slope Real.sinh hpos
      Real.continuous_sinh.continuousOn (Real.differentiable_sinh.differentiableOn)
    rw [Real.deriv_sinh, Real.sinh_zero, sub_zero, sub_zero] at hd
    have hc : Real.cosh ξ ≤ Real.cosh y := by
      rw [Real.cosh_le_cosh, abs_of_pos hξ.1, abs_of_pos hpos]; exact hξ.2.le
    have : Real.sinh y = y * Real.cosh ξ := by
      field_simp at hd; linarith
    rw [this]
    exact mul_le_mul_of_nonneg_left hc hy
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx)]
    exact key x hx
  · have h := key (-x) (by linarith)
    rw [Real.sinh_neg, Real.cosh_neg] at h
    rw [abs_of_neg hx, abs_of_neg (Real.sinh_neg_iff.mpr hx)]
    linarith

/-- `sinh² x ≤ x² cosh² x`. -/
theorem sinh_sq_le_sq_mul_cosh_sq (x : ℝ) : Real.sinh x ^ 2 ≤ x ^ 2 * Real.cosh x ^ 2 := by
  have h := abs_sinh_le_abs_mul_cosh x
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow, sq_abs] at h2
  exact h2

/-- **(a) Full-grid square sum of the imaginary parts.**
`Σ_j (Im φ̂(w_j − iε))² = L ∫ φ² sinh²(εu)` with `w_j = γ − (T + j·2π/L)`. -/
theorem hasSum_im_sq_grid (Q : Zeta23.Params) (T : ℝ) (hL : 0 < Q.L T)
    (hc : Continuous (Q.phi T)) (hsupp : ∀ u, Q.L T / 2 ≤ |u| → Q.phi T u = 0)
    (hconj : Zeta23.ZeroSide.PhiHatConj T Q) (γ ε : ℝ) :
    HasSum (fun j : ℤ =>
        (Q.phiHat T ((((γ - (T + j * (2 * Real.pi / Q.L T))) : ℝ) : ℂ) - ε * I)).im ^ 2)
      (Q.L T * ∫ u in (-(Q.L T / 2))..(Q.L T / 2), Q.phi T u ^ 2 * Real.sinh (ε * u) ^ 2) := by
  set L := Q.L T with hLdef
  set φ := Q.phi T with hφ
  set b : ℝ → ℂ := fun u => -I * ((φ u * Real.sinh (ε * u) : ℝ) : ℂ) with hb
  have hbc : Continuous b := by simp only [hb]; fun_prop
  have hbs : ∀ u, L / 2 ≤ |u| → b u = 0 := fun u hu => by
    simp only [hb]; rw [show φ u = 0 from hsupp u hu, zero_mul, Complex.ofReal_zero, mul_zero]
  have h := hasSum_norm_sq_paperFT_grid hL hbc hbs γ T
  have hnorm : ∀ u, ‖b u‖ ^ 2 = φ u ^ 2 * Real.sinh (ε * u) ^ 2 := fun u => by
    simp only [hb]
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, mul_pow]
  have hint : (∫ u in (-(L / 2))..(L / 2), ‖b u‖ ^ 2) =
      ∫ u in (-(L / 2))..(L / 2), φ u ^ 2 * Real.sinh (ε * u) ^ 2 :=
    intervalIntegral.integral_congr fun u _ => hnorm u
  rw [hint] at h
  refine h.congr_fun fun j => ?_
  rw [paperFT_sinh_eq_im Q T hc hsupp hconj, Complex.norm_real, Real.norm_eq_abs, sq_abs]

open Zeta23 Zeta23.ZeroSide

variable {Z : ZeroConfig} {T : ℝ} {P : Params}

/-- `‖h_p‖² = Σ_{k<d} (Im φ̂(w_k − iε_p))²/c` on the grid `w_k = γ_p − (T + k·2π/L)`. -/
theorem norm_sq_blockImVec_eq_grid (hconj : PhiHatConj T P) {c : ℝ} (hc : 0 < c) (p : ZI Z T) :
    ‖blockImVec (blockData Z T P hconj) c p‖ ^ 2 =
      (∑ k : Fin (P.d T),
        (P.phiHat T (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) * (2 * Real.pi / P.L T))) : ℝ) : ℂ)
            - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I)).im ^ 2) / c := by
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.norm_eq_abs, sq_abs, blockImVec_apply, blockData_v_eq, div_pow, hsq]
  congr 3
  simp only [Params.tau, Params.hgrid]
  push_cast
  ring_nf

/-- **(b) Block bound.**  `‖h_p‖² ≤ L ∫ φ² sinh²(ε_p u) du / c`. -/
theorem norm_sq_blockImVec_le (hconj : PhiHatConj T P) {c : ℝ} (hc : 0 < c) (hL : 0 < P.L T)
    (hφc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0) (p : ZI Z T) :
    ‖blockImVec (blockData Z T P hconj) c p‖ ^ 2 ≤
      P.L T * (∫ u in (-(P.L T / 2))..(P.L T / 2),
        P.phi T u ^ 2 * Real.sinh (((p : ℂ).re - 1 / 2) * u) ^ 2) / c := by
  rw [norm_sq_blockImVec_eq_grid hconj hc]
  refine div_le_div_of_nonneg_right ?_ hc.le
  have h := hasSum_im_sq_grid P T hL hφc hsupp hconj (p : ℂ).im ((p : ℂ).re - 1 / 2)
  set f : ℤ → ℝ := fun j => (P.phiHat T (((((p : ℂ).im - (T + j * (2 * Real.pi / P.L T))) : ℝ)
    : ℂ) - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I)).im ^ 2 with hf
  have hinj : Set.InjOn (fun k : Fin (P.d T) => ((k : ℕ) : ℤ))
      ((Finset.univ : Finset (Fin (P.d T))) : Set (Fin (P.d T))) := by
    intro a _ b _ hab
    simp only at hab
    exact Fin.ext (by exact_mod_cast hab)
  have hsum : ∑ k : Fin (P.d T), f ((k : ℕ) : ℤ) =
      ∑ j ∈ Finset.univ.image (fun k : Fin (P.d T) => ((k : ℕ) : ℤ)), f j :=
    (Finset.sum_image hinj).symm
  have hle := sum_le_hasSum (Finset.univ.image (fun k : Fin (P.d T) => ((k : ℕ) : ℤ)))
    (fun j _ => sq_nonneg _) h
  calc ∑ k : Fin (P.d T), (P.phiHat T (((((p : ℂ).im - (T + ((k : ℕ) : ℤ) *
          (2 * Real.pi / P.L T))) : ℝ) : ℂ) - (((p : ℂ).re - 1 / 2 : ℝ) : ℂ) * I)).im ^ 2
        = ∑ k : Fin (P.d T), f ((k : ℕ) : ℤ) := rfl
    _ ≤ _ := hsum ▸ hle

/-- **(c) Smallness.**  `‖h_p‖² ≤ L ε_p² ∫ u² φ² cosh²(ε_p u) du / c`. -/
theorem norm_sq_blockImVec_le_sq_mul (hconj : PhiHatConj T P) {c : ℝ} (hc : 0 < c)
    (hL : 0 < P.L T) (hφc : Continuous (P.phi T))
    (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0) (p : ZI Z T) :
    ‖blockImVec (blockData Z T P hconj) c p‖ ^ 2 ≤
      P.L T * (((p : ℂ).re - 1 / 2) ^ 2 * ∫ u in (-(P.L T / 2))..(P.L T / 2),
        u ^ 2 * P.phi T u ^ 2 * Real.cosh (((p : ℂ).re - 1 / 2) * u) ^ 2) / c := by
  refine (norm_sq_blockImVec_le hconj hc hL hφc hsupp p).trans ?_
  set ε := (p : ℂ).re - 1 / 2
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hL.le) hc.le
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ fun u _ => ?_
  · exact (by fun_prop : Continuous fun u => P.phi T u ^ 2 * Real.sinh (ε * u) ^ 2)
      |>.intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun u =>
      ε ^ 2 * (u ^ 2 * P.phi T u ^ 2 * Real.cosh (ε * u) ^ 2)) |>.intervalIntegrable _ _
  · have h := sinh_sq_le_sq_mul_cosh_sq (ε * u)
    have h2 := mul_le_mul_of_nonneg_left h (sq_nonneg (P.phi T u))
    calc P.phi T u ^ 2 * Real.sinh (ε * u) ^ 2 ≤ P.phi T u ^ 2 * ((ε * u) ^ 2 *
          Real.cosh (ε * u) ^ 2) := h2
      _ = ε ^ 2 * (u ^ 2 * P.phi T u ^ 2 * Real.cosh (ε * u) ^ 2) := by ring

/-- **(c′) Smallness without the hyperbolic weight.**
`‖h_p‖² ≤ L ε_p² cosh²(ε_p L/2) ∫ u² φ² du / c`. -/
theorem norm_sq_blockImVec_le_sq_mul_cosh (hconj : PhiHatConj T P) {c : ℝ} (hc : 0 < c)
    (hL : 0 < P.L T) (hφc : Continuous (P.phi T))
    (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0) (p : ZI Z T) :
    ‖blockImVec (blockData Z T P hconj) c p‖ ^ 2 ≤
      P.L T * (((p : ℂ).re - 1 / 2) ^ 2 * Real.cosh (((p : ℂ).re - 1 / 2) * (P.L T / 2)) ^ 2 *
        ∫ u in (-(P.L T / 2))..(P.L T / 2), u ^ 2 * P.phi T u ^ 2) / c := by
  refine (norm_sq_blockImVec_le_sq_mul hconj hc hL hφc hsupp p).trans ?_
  set ε := (p : ℂ).re - 1 / 2
  set L := P.L T
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hL.le) hc.le
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ε)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ fun u hu => ?_
  · exact (by fun_prop : Continuous fun u => u ^ 2 * P.phi T u ^ 2 * Real.cosh (ε * u) ^ 2)
      |>.intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun u =>
      Real.cosh (ε * (L / 2)) ^ 2 * (u ^ 2 * P.phi T u ^ 2)) |>.intervalIntegrable _ _
  · have hu' : |u| ≤ L / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
    have hcosh : Real.cosh (ε * u) ≤ Real.cosh (ε * (L / 2)) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < L / 2)]
      exact mul_le_mul_of_nonneg_left hu' (abs_nonneg ε)
    have h2 : Real.cosh (ε * u) ^ 2 ≤ Real.cosh (ε * (L / 2)) ^ 2 :=
      pow_le_pow_left₀ (Real.cosh_pos _).le hcosh 2
    have h3 : 0 ≤ u ^ 2 * P.phi T u ^ 2 := by positivity
    calc u ^ 2 * P.phi T u ^ 2 * Real.cosh (ε * u) ^ 2
        ≤ u ^ 2 * P.phi T u ^ 2 * Real.cosh (ε * (L / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = Real.cosh (ε * (L / 2)) ^ 2 * (u ^ 2 * P.phi T u ^ 2) := by ring

end

end RHTower

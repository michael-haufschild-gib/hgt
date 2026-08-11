import GaloisForLFunctions.RHTower.DeningerBoundedMultiplier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The inverse two-sided weight is a bounded multiplier

The logarithmic derivative `v = K\sinh(Kt)/\cosh(Kt)` of the two-sided weight satisfies the closed
equation `v' = K^2 - v^2`, so every derivative of `v` is a polynomial in `v`; since `|v| \le |K|`,
all of them are bounded.  The weight itself satisfies `u' = -vu`, so the Leibniz rule bounds every
derivative of `u` by strong induction.

* `deningerSechLog` : `v = K\sinh(Kt)/\cosh(Kt)`, with `v' = K^2 - v^2`.
* `deningerSechWeight` : `u = 1/(2\cosh(Kt))`, with `u' = -vu`.
* `deningerSechMultiplier` : **`u` as a bounded multiplier of the source.**
-/

namespace RHTower

open scoped ContDiff

noncomputable section

/-- The logarithmic derivative of the two-sided weight. -/
def deningerSechLog (K : ℝ) : ℝ → ℝ := fun t => K * Real.sinh (K * t) / Real.cosh (K * t)

/-- The inverse two-sided weight `1/(e^{Kt}+e^{-Kt})`. -/
def deningerSechWeight (K : ℝ) : ℝ → ℝ := fun t => 1 / (2 * Real.cosh (K * t))

theorem deningerCosh_ne_zero (K t : ℝ) : Real.cosh (K * t) ≠ 0 :=
  ne_of_gt (Real.cosh_pos _)

/-- **The logarithmic derivative satisfies the closed equation `v' = K² - v²`.** -/
theorem deningerSechLog_hasDerivAt (K t : ℝ) :
    HasDerivAt (deningerSechLog K) (K ^ 2 - (deningerSechLog K t) ^ 2) t := by
  have hc : HasDerivAt (fun s : ℝ => Real.cosh (K * s)) (Real.sinh (K * t) * K) t :=
    (Real.hasDerivAt_cosh (K * t)).comp t ((hasDerivAt_id t).const_mul K |>.congr_deriv (by ring))
  have hs : HasDerivAt (fun s : ℝ => K * Real.sinh (K * s)) (K * (Real.cosh (K * t) * K)) t :=
    ((Real.hasDerivAt_sinh (K * t)).comp t
      ((hasDerivAt_id t).const_mul K |>.congr_deriv (by ring))).const_mul K
  have hdiv := hs.div hc (deningerCosh_ne_zero K t)
  refine hdiv.congr_deriv ?_
  have hpy := Real.cosh_sq_sub_sinh_sq (K * t)
  have hne := deningerCosh_ne_zero K t
  rw [deningerSechLog]
  field_simp

theorem deningerSechLog_contDiff (K : ℝ) : ContDiff ℝ ∞ (deningerSechLog K) := by
  refine ContDiff.div ?_ ?_ (fun t => deningerCosh_ne_zero K t)
  · exact contDiff_const.mul (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id))
  · exact Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)

/-- **The logarithmic derivative is bounded by `|K|`.** -/
theorem deningerSechLog_abs_le (K t : ℝ) : |deningerSechLog K t| ≤ |K| := by
  have hpos := Real.cosh_pos (K * t)
  have hpy := Real.cosh_sq_sub_sinh_sq (K * t)
  have hsin : |Real.sinh (K * t)| ≤ Real.cosh (K * t) := by
    have hsq : Real.sinh (K * t) ^ 2 ≤ Real.cosh (K * t) ^ 2 := by nlinarith [hpy]
    nlinarith [sq_abs (Real.sinh (K * t)), abs_nonneg (Real.sinh (K * t)), hpos, hsq]
  rw [deningerSechLog, abs_div, abs_mul, abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith [abs_nonneg K, hsin, hpos]

/-- Every derivative of the logarithmic derivative is a polynomial in it. -/
theorem deningerSechLog_iteratedDeriv_poly (K : ℝ) (j : ℕ) :
    ∃ P : Polynomial ℝ, iteratedDeriv j (deningerSechLog K)
      = fun t => P.eval (deningerSechLog K t) := by
  induction j with
  | zero => exact ⟨Polynomial.X, by funext t; simp [iteratedDeriv_zero]⟩
  | succ j ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P.derivative * (Polynomial.C (K ^ 2) - Polynomial.X ^ 2), ?_⟩
    rw [iteratedDeriv_succ, hP]
    funext t
    have hd : HasDerivAt (fun s : ℝ => P.eval (deningerSechLog K s))
        (P.derivative.eval (deningerSechLog K t) * (K ^ 2 - (deningerSechLog K t) ^ 2)) t :=
      (P.hasDerivAt (deningerSechLog K t)).comp t (deningerSechLog_hasDerivAt K t)
    rw [hd.deriv]
    simp

/-- **Every derivative of the logarithmic derivative is bounded.** -/
theorem deningerSechLog_iteratedDeriv_bounded (K : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |iteratedDeriv j (deningerSechLog K) t| ≤ C := by
  obtain ⟨P, hP⟩ := deningerSechLog_iteratedDeriv_poly K j
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -|K|) (b := |K|)).exists_bound_of_continuousOn
    (Polynomial.continuous P).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  rw [hP]
  have hmem : deningerSechLog K t ∈ Set.Icc (-|K|) |K| := by
    have := deningerSechLog_abs_le K t
    exact ⟨by linarith [neg_abs_le (deningerSechLog K t)], by linarith [le_abs_self (deningerSechLog K t)]⟩
  have hb := hC _ hmem
  rw [Real.norm_eq_abs] at hb
  exact le_trans hb (le_max_left _ _)

/-- **The weight satisfies `u' = -vu`.** -/
theorem deningerSechWeight_hasDerivAt (K t : ℝ) :
    HasDerivAt (deningerSechWeight K)
      (-(deningerSechLog K t) * deningerSechWeight K t) t := by
  have hc : HasDerivAt (fun s : ℝ => 2 * Real.cosh (K * s)) (2 * (Real.sinh (K * t) * K)) t :=
    ((Real.hasDerivAt_cosh (K * t)).comp t
      ((hasDerivAt_id t).const_mul K |>.congr_deriv (by ring))).const_mul 2
  have hne : (2 : ℝ) * Real.cosh (K * t) ≠ 0 := by
    have := Real.cosh_pos (K * t); positivity
  have hd := (hasDerivAt_const t (1 : ℝ)).div hc hne
  refine hd.congr_deriv ?_
  rw [deningerSechLog, deningerSechWeight]
  field_simp
  ring

theorem deningerSechWeight_contDiff (K : ℝ) : ContDiff ℝ ∞ (deningerSechWeight K) := by
  refine ContDiff.div contDiff_const ?_ ?_
  · exact contDiff_const.mul (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id))
  · intro t
    have := Real.cosh_pos (K * t); positivity

theorem deningerSechWeight_abs_le (K t : ℝ) : |deningerSechWeight K t| ≤ 1 := by
  have hpos := Real.cosh_pos (K * t)
  have hone : (1 : ℝ) ≤ Real.cosh (K * t) := Real.one_le_cosh _
  rw [deningerSechWeight, abs_div, abs_one, abs_of_pos (by positivity), div_le_one (by positivity)]
  linarith

/-- Derivative bounds for the logarithmic derivative in `iteratedFDeriv` form. -/
theorem deningerSechLog_iteratedFDeriv_bounded (K : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ j (deningerSechLog K) t‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := deningerSechLog_iteratedDeriv_bounded K j
  refine ⟨C, hC0, fun t => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact hC t

/-- **Every derivative of the weight is bounded**, by strong induction on `u' = -vu`. -/
theorem deningerSechWeight_iteratedFDeriv_bounded (K : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ j (deningerSechWeight K) t‖ ≤ C := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 =>
      refine ⟨1, zero_le_one, fun t => ?_⟩
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact deningerSechWeight_abs_le K t
    | (n + 1) =>
      have hu : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, i ≤ n →
          ‖iteratedFDeriv ℝ i (deningerSechWeight K) t‖ ≤ C := by
        intro i
        by_cases hi : i ≤ n
        · obtain ⟨C, hC0, hC⟩ := ih i (Nat.lt_succ_of_le hi)
          exact ⟨C, hC0, fun t _ => hC t⟩
        · exact ⟨0, le_refl 0, fun _ hcon => absurd hcon hi⟩
      choose Cu hCu0 hCu using hu
      choose Cv hCv0 hCv using deningerSechLog_iteratedFDeriv_bounded K
      have hnegv : ContDiff ℝ ∞ (fun s : ℝ => -(deningerSechLog K s)) :=
        (deningerSechLog_contDiff K).neg
      refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cv i * Cu (n - i),
        Finset.sum_nonneg fun i _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCv0 i)) (hCu0 (n - i)), fun t => ?_⟩
      have hderiv : deriv (deningerSechWeight K)
          = fun s => -(deningerSechLog K s) * deningerSechWeight K s :=
        funext fun s => (deningerSechWeight_hasDerivAt K s).deriv
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ', hderiv,
        ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      refine le_trans (norm_iteratedFDeriv_mul_le hnegv (deningerSechWeight_contDiff K) t
        (by exact_mod_cast le_top)) ?_
      refine Finset.sum_le_sum fun i hi => ?_
      have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hfun : (fun s : ℝ => -(deningerSechLog K s)) = -(deningerSechLog K) := rfl
      have hvi : ‖iteratedFDeriv ℝ i (fun s : ℝ => -(deningerSechLog K s)) t‖ ≤ Cv i := by
        rw [hfun, iteratedFDeriv_neg_apply, norm_neg]
        exact hCv i t
      have hui : ‖iteratedFDeriv ℝ (n - i) (deningerSechWeight K) t‖ ≤ Cu (n - i) :=
        hCu (n - i) t (Nat.sub_le _ _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hvi (Nat.cast_nonneg _)) hui
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCv0 i))

/-- **The inverse two-sided weight as a bounded multiplier of the source.** -/
def deningerSechMultiplier (K : ℝ) : DeningerBddMultiplier where
  toFun := fun t => ((deningerSechWeight K t : ℝ) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp (deningerSechWeight_contDiff K)
  bounded := by
    intro j
    obtain ⟨C, hC0, hC⟩ := deningerSechWeight_iteratedFDeriv_bounded K j
    refine ⟨C, fun t => ?_⟩
    have hcomp : (fun t : ℝ => ((deningerSechWeight K t : ℝ) : ℂ))
        = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ deningerSechWeight K := rfl
    have hnorm := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (f := deningerSechWeight K) (x := t)
      ((deningerSechWeight_contDiff K).contDiffAt) (i := j) (by exact_mod_cast le_top)
    rw [hcomp, hnorm]
    exact hC t

@[simp]
theorem deningerSechMultiplier_apply (K : ℝ) (t : ℝ) :
    (deningerSechMultiplier K : ℝ → ℂ) t = ((deningerSechWeight K t : ℝ) : ℂ) := rfl

end

end RHTower

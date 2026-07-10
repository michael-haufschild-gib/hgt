/-
# Archimedean winding forces transverse zeros of the finite carrier

On the critical line the completed finite carrier is the sum of one direct completed Dirichlet
summand and its conjugate.  At a zero, the direct summand is purely imaginary.  Differentiating
there shows that the zero's slope is its modulus times the net phase velocity: the archimedean
winding rate plus the logarithmic derivative of the finite Dirichlet polynomial.

The Dirichlet contribution is bounded by the explicit finite frequency sum
`∑_{n≤N} n⁻¹ᐟ² log n`.  Consequently, wherever the Dirichlet part has a positive floor and the
archimedean winding dominates this sum, every critical-line carrier zero is simple.  Simplicity is
therefore derived from the existing floor and winding data rather than supplied independently.
-/
import GaloisForLFunctions.RHTower.DpolyBallFloor
import GaloisForLFunctions.RHTower.WindingRigidity
import GaloisForLFunctions.RHTower.LargeValuesDpoly
import GaloisForLFunctions.RHTower.ResonanceClosedForm

open Complex Real Metric

noncomputable section

namespace RHTower

/-- The absolute logarithmic-derivative budget of the length-`N` Dirichlet polynomial on the
critical line. -/
def dirichletLineDerivativeBudget (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n

theorem dirichletLineDerivativeBudget_nonneg (N : ℕ) :
    0 ≤ dirichletLineDerivativeBudget N := by
  unfold dirichletLineDerivativeBudget
  positivity

/-- The complex derivative of the finite Dirichlet polynomial on the critical line is bounded
by the sum of its logarithmic frequencies. -/
theorem norm_deriv_dirichletPoly_line_le (N : ℕ) (τ : ℝ) :
    ‖deriv (dirichletPoly N) (linePt τ)‖ ≤ dirichletLineDerivativeBudget N := by
  have hline : HasDerivAt (fun u : ℝ => dirichletPoly N (linePt u))
      (deriv (dirichletPoly N) (linePt τ) * I) τ := by
    exact ((dirichletPoly_differentiable N (linePt τ)).hasDerivAt.comp τ
      (hasDerivAt_linePt τ))
  have heq : (fun u : ℝ => dirichletPoly N (linePt u)) =
      fun u : ℝ => dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) u := by
    funext u
    exact dirichletPoly_line_eq N u
  rw [heq] at hline
  have hd := dpoly_hasDerivAt (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)))
    (Finset.Icc 1 N) τ
  have hcoeff := hline.unique hd
  have hnorm : ‖deriv (dirichletPoly N) (linePt τ)‖ =
      ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n)
        (Finset.Icc 1 N) τ‖ := by
    have := congrArg norm hcoeff
    simpa [norm_mul] using this
  rw [hnorm]
  refine le_trans (norm_dpoly_le _ _ τ) ?_
  unfold dirichletLineDerivativeBudget
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [abs_of_nonneg]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg hn1)

/-- The line Dirichlet polynomial is globally Lipschitz with the explicit finite derivative
budget. -/
theorem norm_dirichletPoly_line_sub_le_budget (N : ℕ) (u v : ℝ) :
    ‖dirichletPoly N (linePt u) - dirichletPoly N (linePt v)‖ ≤
      dirichletLineDerivativeBudget N * |u - v| := by
  let f : ℝ → ℂ := fun τ => dirichletPoly N (linePt τ)
  have hf : ∀ τ ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ f τ := by
    intro τ _
    exact ((dirichletPoly_differentiable N (linePt τ)).hasDerivAt.comp τ
      (hasDerivAt_linePt τ)).differentiableAt
  have hbound : ∀ τ ∈ (Set.univ : Set ℝ),
      ‖deriv f τ‖ ≤ dirichletLineDerivativeBudget N := by
    intro τ _
    have hline : HasDerivAt f (deriv (dirichletPoly N) (linePt τ) * I) τ :=
      (dirichletPoly_differentiable N (linePt τ)).hasDerivAt.comp τ
        (hasDerivAt_linePt τ)
    rw [hline.deriv, norm_mul, Complex.norm_I, mul_one]
    exact norm_deriv_dirichletPoly_line_le N τ
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (x := v) (y := u) hf hbound convex_univ (Set.mem_univ v) (Set.mem_univ u)
  simpa [f, Real.norm_eq_abs, abs_sub_comm] using h

/-- A positive Dirichlet floor converts the finite derivative budget into a lower bound for
the real part of the logarithmic derivative. -/
theorem re_dirichletPoly_logDeriv_line_ge (N : ℕ) (τ d : ℝ)
    (hd0 : 0 < d) (hDfloor : d ≤ ‖dirichletPoly N (linePt τ)‖) :
    -(dirichletLineDerivativeBudget N / d) ≤
      (deriv (dirichletPoly N) (linePt τ) / dirichletPoly N (linePt τ)).re := by
  let D : ℂ := dirichletPoly N (linePt τ)
  let q : ℂ := deriv (dirichletPoly N) (linePt τ) / D
  let B : ℝ := dirichletLineDerivativeBudget N
  have hB0 : 0 ≤ B := dirichletLineDerivativeBudget_nonneg N
  have hDn0 : 0 < ‖D‖ := lt_of_lt_of_le hd0 hDfloor
  have hderiv : ‖deriv (dirichletPoly N) (linePt τ)‖ ≤ B :=
    norm_deriv_dirichletPoly_line_le N τ
  have hqnorm : ‖q‖ ≤ B / ‖D‖ := by
    dsimp [q]
    rw [norm_div]
    exact div_le_div_of_nonneg_right hderiv hDn0.le
  have hfrac : B / ‖D‖ ≤ B / d :=
    div_le_div_of_nonneg_left hB0 hd0 hDfloor
  have habs : -‖q‖ ≤ q.re := neg_le_of_abs_le (Complex.abs_re_le_norm q)
  dsimp [D, q, B] at hqnorm hfrac habs ⊢
  linarith

/-- On the critical line, complex differentiation of the finite Dirichlet polynomial is the
negative logarithmically weighted trigonometric polynomial. -/
theorem deriv_dirichletPoly_line_eq_neg_dpoly_log (N : ℕ) (τ : ℝ) :
    deriv (dirichletPoly N) (linePt τ) =
      -dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n)
        (Finset.Icc 1 N) τ := by
  have hline : HasDerivAt (fun u : ℝ => dirichletPoly N (linePt u))
      (deriv (dirichletPoly N) (linePt τ) * I) τ :=
    ((dirichletPoly_differentiable N (linePt τ)).hasDerivAt.comp τ
      (hasDerivAt_linePt τ))
  have heq : (fun u : ℝ => dirichletPoly N (linePt u)) =
      fun u : ℝ => dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) u := by
    funext u
    exact dirichletPoly_line_eq N u
  rw [heq] at hline
  have hd := dpoly_hasDerivAt (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)))
    (Finset.Icc 1 N) τ
  have hcoeff := hline.unique hd
  apply mul_right_cancel₀ (Complex.I_ne_zero)
  rw [hcoeff]
  ring

/-- The direct completed summand on the critical line. -/
def completedDirectLine (N : ℕ) (τ : ℝ) : ℂ :=
  archFactor (linePt τ) * dirichletPoly N (linePt τ)

/-- Its line derivative. -/
def completedDirectLineSlope (N : ℕ) (τ : ℝ) : ℂ :=
  archFactorDeriv (linePt τ) * I * dirichletPoly N (linePt τ) +
    archFactor (linePt τ) * (deriv (dirichletPoly N) (linePt τ) * I)

theorem completedGN_line_eq_direct_add_conj (N : ℕ) (τ : ℝ) :
    completedGN N (linePt τ) =
      completedDirectLine N τ + (starRingEnd ℂ) (completedDirectLine N τ) := by
  rw [completedGN, gN_line_conjForm, mul_add]
  unfold completedDirectLine
  rw [← mul_assoc, archFactor_mul_zetaChi
    (Gammaℝ_ne_zero_of_re_pos (linePt_re_pos τ)), ← conj_linePt, archFactor_conj,
    map_mul]

theorem hasDerivAt_completedDirectLine (N : ℕ) (τ : ℝ) :
    HasDerivAt (completedDirectLine N) (completedDirectLineSlope N τ) τ := by
  have hD : HasDerivAt (fun u : ℝ => dirichletPoly N (linePt u))
      (deriv (dirichletPoly N) (linePt τ) * I) τ :=
    ((dirichletPoly_differentiable N (linePt τ)).hasDerivAt.comp τ
      (hasDerivAt_linePt τ))
  simpa [completedDirectLine, completedDirectLineSlope, mul_assoc] using
    (hasDerivAt_archFactor_line τ).mul hD

theorem deriv_completedGN_line_mul_I (N : ℕ) (τ : ℝ) :
    deriv (completedGN N) (linePt τ) * I =
      completedDirectLineSlope N τ +
        (starRingEnd ℂ) (completedDirectLineSlope N τ) := by
  have hleft : HasDerivAt (fun u : ℝ => completedGN N (linePt u))
      (deriv (completedGN N) (linePt τ) * I) τ := by
    have hdiff :=
      (completedGN_analyticAt (N := N) (linePt_re_pos τ) (linePt_re_lt_one τ)).differentiableAt
    exact hdiff.hasDerivAt.comp τ (hasDerivAt_linePt τ)
  have hp := hasDerivAt_completedDirectLine N τ
  have hpc : HasDerivAt (fun u : ℝ => (starRingEnd ℂ) (completedDirectLine N u))
      ((starRingEnd ℂ) (completedDirectLineSlope N τ)) τ := by
    simpa using ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      τ hp)
  have hright : HasDerivAt (fun u : ℝ =>
      completedDirectLine N u + (starRingEnd ℂ) (completedDirectLine N u))
      (completedDirectLineSlope N τ + (starRingEnd ℂ) (completedDirectLineSlope N τ)) τ :=
    hp.add hpc
  have heq : (fun u : ℝ => completedGN N (linePt u)) = fun u : ℝ =>
      completedDirectLine N u + (starRingEnd ℂ) (completedDirectLine N u) := by
    funext u
    exact completedGN_line_eq_direct_add_conj N u
  rw [heq] at hleft
  exact hleft.unique hright

theorem completedDirectLineSlope_eq_factor (N : ℕ) (τ : ℝ)
    (hD : dirichletPoly N (linePt τ) ≠ 0) :
    completedDirectLineSlope N τ = completedDirectLine N τ *
      ((archWinding τ + deriv (dirichletPoly N) (linePt τ) /
        dirichletPoly N (linePt τ)) * I) := by
  unfold completedDirectLineSlope completedDirectLine
  rw [archFactorDeriv_eq_mul_archWinding]
  field_simp

/-- At a critical-line zero, the completed carrier derivative is the direct summand's modulus
times the net archimedean-plus-Dirichlet phase velocity. -/
theorem norm_deriv_completedGN_line_zero (N : ℕ) (τ : ℝ)
    (hzero : completedGN N (linePt τ) = 0)
    (hD : dirichletPoly N (linePt τ) ≠ 0)
    (hphase : 0 ≤ windingRate τ +
      (deriv (dirichletPoly N) (linePt τ) / dirichletPoly N (linePt τ)).re) :
    ‖deriv (completedGN N) (linePt τ)‖ =
      2 * ‖archFactor (linePt τ)‖ * ‖dirichletPoly N (linePt τ)‖ *
        (windingRate τ +
          (deriv (dirichletPoly N) (linePt τ) / dirichletPoly N (linePt τ)).re) := by
  let P : ℂ := completedDirectLine N τ
  let Z : ℂ := archWinding τ +
    deriv (dirichletPoly N) (linePt τ) / dirichletPoly N (linePt τ)
  have hPre : P.re = 0 := by
    have hline := completedGN_line_eq_direct_add_conj N τ
    rw [hzero] at hline
    have hre := congrArg Complex.re hline
    simp only [Complex.zero_re, Complex.add_re, Complex.conj_re] at hre
    dsimp [P]
    linarith
  have hZre : Z.re = windingRate τ +
      (deriv (dirichletPoly N) (linePt τ) / dirichletPoly N (linePt τ)).re := by
    simp [Z, windingRate]
  have hZ0 : 0 ≤ Z.re := by rwa [hZre]
  have hslope : completedDirectLineSlope N τ = P * (Z * I) := by
    dsimp [P, Z]
    exact completedDirectLineSlope_eq_factor N τ hD
  have hQre : (completedDirectLineSlope N τ).re = -P.im * Z.re := by
    rw [hslope]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, hPre, zero_mul]
    ring
  have hPnorm : ‖P‖ = |P.im| := by
    rw [Complex.norm_def, Complex.normSq_apply, hPre, zero_mul, zero_add, ← pow_two,
      Real.sqrt_sq_eq_abs]
  have hlineDeriv := deriv_completedGN_line_mul_I N τ
  have hsum : completedDirectLineSlope N τ +
      (starRingEnd ℂ) (completedDirectLineSlope N τ) =
      ((2 * (completedDirectLineSlope N τ).re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  calc
    ‖deriv (completedGN N) (linePt τ)‖ =
        ‖deriv (completedGN N) (linePt τ) * I‖ := by rw [norm_mul, Complex.norm_I, mul_one]
    _ = ‖completedDirectLineSlope N τ +
        (starRingEnd ℂ) (completedDirectLineSlope N τ)‖ := by rw [hlineDeriv]
    _ = |2 * (completedDirectLineSlope N τ).re| := by
      rw [hsum, Complex.norm_real, Real.norm_eq_abs]
    _ = 2 * |P.im| * Z.re := by
      rw [hQre]
      simp [abs_mul, abs_of_nonneg hZ0]
      ring
    _ = 2 * ‖P‖ * Z.re := by rw [hPnorm]
    _ = 2 * ‖archFactor (linePt τ)‖ * ‖dirichletPoly N (linePt τ)‖ * Z.re := by
      rw [show ‖P‖ = ‖archFactor (linePt τ)‖ * ‖dirichletPoly N (linePt τ)‖ by
        simp [P, completedDirectLine]]
      ring
    _ = _ := by rw [hZre]

/-- A Dirichlet-part floor makes every sufficiently high critical-line zero of the completed
finite carrier transverse.  The archimedean winding must dominate only the explicit finite
logarithmic-frequency budget. -/
theorem deriv_completedGN_line_zero_lower_bound (N : ℕ) (τ d : ℝ)
    (hd0 : 0 < d)
    (hDfloor : d ≤ ‖dirichletPoly N (linePt τ)‖)
    (hdom : dirichletLineDerivativeBudget N < d * windingRate τ)
    (hzero : completedGN N (linePt τ) = 0) :
    2 * ‖archFactor (linePt τ)‖ *
        (d * windingRate τ - dirichletLineDerivativeBudget N) ≤
      ‖deriv (completedGN N) (linePt τ)‖ := by
  let D : ℂ := dirichletPoly N (linePt τ)
  let q : ℂ := deriv (dirichletPoly N) (linePt τ) / D
  let B : ℝ := dirichletLineDerivativeBudget N
  have hB0 : 0 ≤ B := dirichletLineDerivativeBudget_nonneg N
  have hDn0 : 0 < ‖D‖ := lt_of_lt_of_le hd0 hDfloor
  have hDne : D ≠ 0 := norm_pos_iff.mp hDn0
  have hderiv : ‖deriv (dirichletPoly N) (linePt τ)‖ ≤ B :=
    norm_deriv_dirichletPoly_line_le N τ
  have hqnorm : ‖q‖ ≤ B / ‖D‖ := by
    dsimp [q]
    rw [norm_div]
    exact div_le_div_of_nonneg_right hderiv hDn0.le
  have hqre : -(B / ‖D‖) ≤ q.re := by
    have hre := Complex.abs_re_le_norm q
    have habs : -‖q‖ ≤ q.re := neg_le_of_abs_le hre
    linarith
  have hwind0 : 0 < windingRate τ := by nlinarith
  have hmulq : -B ≤ ‖D‖ * q.re := by
    have hm := mul_le_mul_of_nonneg_left hqre hDn0.le
    rw [mul_neg, mul_div_cancel₀ B hDn0.ne'] at hm
    exact hm
  have hmain : d * windingRate τ - B ≤
      ‖D‖ * (windingRate τ + q.re) := by
    have hDw : d * windingRate τ ≤ ‖D‖ * windingRate τ :=
      mul_le_mul_of_nonneg_right hDfloor hwind0.le
    nlinarith
  have hphase : 0 ≤ windingRate τ + q.re := by
    have hpos : 0 < d * windingRate τ - B := by simpa [B] using hdom
    have hprodpos : 0 < ‖D‖ * (windingRate τ + q.re) := lt_of_lt_of_le hpos hmain
    nlinarith
  have hexact := norm_deriv_completedGN_line_zero N τ hzero hDne hphase
  dsimp [D, q] at hmain hphase ⊢
  rw [hexact]
  have harch0 : 0 ≤ 2 * ‖archFactor (linePt τ)‖ := by positivity
  convert mul_le_mul_of_nonneg_left hmain harch0 using 1
  all_goals ring

/-- Above the explicit phase-dominance threshold, every critical-line carrier zero inside the
Dirichlet floor is simple. -/
theorem deriv_completedGN_line_zero_ne_zero (N : ℕ) (τ d : ℝ)
    (hd0 : 0 < d)
    (hDfloor : d ≤ ‖dirichletPoly N (linePt τ)‖)
    (hdom : dirichletLineDerivativeBudget N < d * windingRate τ)
    (hzero : completedGN N (linePt τ) = 0) :
    deriv (completedGN N) (linePt τ) ≠ 0 := by
  have hlower := deriv_completedGN_line_zero_lower_bound N τ d hd0 hDfloor hdom hzero
  have harch : 0 < ‖archFactor (linePt τ)‖ := norm_pos_iff.mpr (archFactor_linePt_ne_zero τ)
  have hgap : 0 < d * windingRate τ - dirichletLineDerivativeBudget N := by linarith
  have : 0 < ‖deriv (completedGN N) (linePt τ)‖ := lt_of_lt_of_le (by positivity) hlower
  exact norm_pos_iff.mp this

end RHTower

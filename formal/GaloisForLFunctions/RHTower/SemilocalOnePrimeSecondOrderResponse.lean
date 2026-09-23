import GaloisForLFunctions.RHTower.SemilocalTruncationDefectBound

/-!
# The one-prime second-order response

The Euler factor `1/(1 − 2ε cos(δs) + ε²)` (`ε = p^{-1/2}`, `δ = log p`) is
`1 + 2ε cos(δs) + ε²(1 + 2cos(2δs)) + O(ε³)` (`abs_eulerFactor_sub_quadratic_le`).  For the
degree-two truncation the Gram matrix is `1 + εT(δ) + ε²(1 + T(2δ))` and

`(log D_n)''(0) = 2(n+1) + 2 J_{2δ}(n) − tr(T(δ)²)`  (`deriv_deriv_log_eulerQuadraticDeterminant`),

`(a_n²)''(0) = r_n² (2 ΔΔJ_{2δ} − ΔΔ tr(T(δ)²) + (ΔΔJ_δ)²)`  (`deriv_deriv_eulerQuadraticSquaredRadius`),

so `[ε²] a_n² = r_n² (ΔΔJ_{2δ} − ½ ΔΔ tr(T(δ)²) + ½ (ΔΔJ_δ)²)`: the harmonic jet at `2δ`, minus half the
second difference of the variance term, plus half the square of the first-order jet.  With the boost
bound every piece is `O((cosh δ)^{-1})` or `O((cosh 2δ)^{-1/2})`, i.e. `O(1/p)`: the second-order term
of the one-prime deviation is `O(q²)` against the first-order `O(q)`
(`abs_onePrimeSecondOrder_le`).
-/

open Matrix Real MeasureTheory Filter Topology Finset
open scoped BigOperators

namespace RHTower
namespace CosineModeResponse

open GaloisForLFunctions.HilbertMetric FirstEulerCriticalJet MeixnerPollaczek

/-! ## The Euler factor and its quadratic truncation -/

/-- `|1/(1 − 2ε cos x + ε²) − (1 + 2ε cos x + ε²(1 + 2 cos 2x))| ≤ 60 ε³` for `0 ≤ ε ≤ 1/6`. -/
theorem abs_eulerFactor_sub_quadratic_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 6) (x : ℝ) :
    |1 / (1 - 2 * ε * Real.cos x + ε ^ (2 : ℕ)) -
      (1 + 2 * ε * Real.cos x + ε ^ (2 : ℕ) * (1 + 2 * Real.cos (2 * x)))| ≤ 60 * ε ^ (3 : ℕ) := by
  set c := Real.cos x with hc
  have hc1 : |c| ≤ 1 := Real.abs_cos_le_one x
  have hc2 : Real.cos (2 * x) = 2 * c ^ (2 : ℕ) - 1 := Real.cos_two_mul x
  set y := 2 * ε * c - ε ^ (2 : ℕ) with hy
  have hyabs : |y| ≤ 3 * ε := by
    rw [hy]
    have h1 : |2 * ε * c| ≤ 2 * ε := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ε)]
      nlinarith
    have h2 : |ε ^ (2 : ℕ)| ≤ ε := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    calc |2 * ε * c - ε ^ (2 : ℕ)| ≤ |2 * ε * c| + |ε ^ (2 : ℕ)| := abs_sub_le_abs_add_abs _ _
      _ ≤ 2 * ε + ε := add_le_add h1 h2
      _ = 3 * ε := by ring
  have hy1 : 1 / 2 ≤ 1 - y := by
    have := (abs_le.mp hyabs).2
    linarith
  have hy0 : 1 - y ≠ 0 := by linarith
  have hden : 1 - 2 * ε * c + ε ^ (2 : ℕ) = 1 - y := by rw [hy]; ring
  have hE : 1 / (1 - 2 * ε * c + ε ^ (2 : ℕ)) - (1 + y + y ^ (2 : ℕ)) = y ^ (3 : ℕ) / (1 - y) := by
    rw [hden]
    field_simp
    ring
  have hT : (1 + y + y ^ (2 : ℕ)) - (1 + 2 * ε * c + ε ^ (2 : ℕ) * (1 + 2 * Real.cos (2 * x))) =
      -4 * ε ^ (3 : ℕ) * c + ε ^ (4 : ℕ) := by
    rw [hc2, hy]
    ring
  have hsplit : 1 / (1 - 2 * ε * c + ε ^ (2 : ℕ)) -
      (1 + 2 * ε * c + ε ^ (2 : ℕ) * (1 + 2 * Real.cos (2 * x))) =
      y ^ (3 : ℕ) / (1 - y) + (-4 * ε ^ (3 : ℕ) * c + ε ^ (4 : ℕ)) := by
    rw [← hE, ← hT]
    ring
  rw [hsplit]
  have hA : |y ^ (3 : ℕ) / (1 - y)| ≤ 54 * ε ^ (3 : ℕ) := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - y), abs_pow]
    have h3 : |y| ^ (3 : ℕ) ≤ (3 * ε) ^ (3 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hyabs 3
    calc |y| ^ (3 : ℕ) / (1 - y) ≤ (3 * ε) ^ (3 : ℕ) / (1 / 2) :=
          div_le_div₀ (by positivity) h3 (by norm_num) hy1
      _ = 54 * ε ^ (3 : ℕ) := by ring
  have hB : |-4 * ε ^ (3 : ℕ) * c + ε ^ (4 : ℕ)| ≤ 6 * ε ^ (3 : ℕ) := by
    have h1 : |-4 * ε ^ (3 : ℕ) * c| ≤ 4 * ε ^ (3 : ℕ) := by
      rw [abs_mul, abs_mul, show |(-4 : ℝ)| = 4 by norm_num, abs_of_nonneg (pow_nonneg hε0 3)]
      nlinarith [pow_nonneg hε0 3, abs_nonneg c]
    have h2 : |ε ^ (4 : ℕ)| ≤ ε ^ (3 : ℕ) := by
      rw [abs_of_nonneg (by positivity)]
      have : ε ^ (4 : ℕ) = ε ^ (3 : ℕ) * ε := by ring
      rw [this]
      nlinarith [pow_nonneg hε0 3]
    calc |-4 * ε ^ (3 : ℕ) * c + ε ^ (4 : ℕ)| ≤ |-4 * ε ^ (3 : ℕ) * c| + |ε ^ (4 : ℕ)| := abs_add_le _ _
      _ ≤ 4 * ε ^ (3 : ℕ) + ε ^ (3 : ℕ) := add_le_add h1 h2
      _ ≤ 6 * ε ^ (3 : ℕ) := by nlinarith [pow_nonneg hε0 3]
  calc |y ^ (3 : ℕ) / (1 - y) + (-4 * ε ^ (3 : ℕ) * c + ε ^ (4 : ℕ))|
      ≤ |y ^ (3 : ℕ) / (1 - y)| + |-4 * ε ^ (3 : ℕ) * c + ε ^ (4 : ℕ)| := abs_add_le _ _
    _ ≤ 54 * ε ^ (3 : ℕ) + 6 * ε ^ (3 : ℕ) := add_le_add hA hB
    _ = 60 * ε ^ (3 : ℕ) := by ring

/-! ## The quadratic Gram matrix -/

/-- Gram matrix for the weight `(1 + 2ε cos(δs) + ε²(1 + 2cos(2δs))) μ`. -/
noncomputable def eulerQuadraticGram (δ ε : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => ∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s *
    (1 + 2 * ε * Real.cos (δ * s) + ε ^ (2 : ℕ) * (1 + 2 * Real.cos (2 * δ * s)))
    ∂semilocalArchimedeanGammaMeasure

/-- `1 + ε T(δ) + ε² (1 + T(2δ))`. -/
noncomputable def eulerQuadraticMatrix (δ : ℝ) (n : ℕ) (ε : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  1 + ε • cosineModeTangent δ n + (ε ^ (2 : ℕ)) • (1 + cosineModeTangent (2 * δ) n)

theorem eulerQuadraticGram_eq (δ ε : ℝ) (n : ℕ) :
    eulerQuadraticGram δ ε n = eulerQuadraticMatrix δ n ε := by
  ext i j
  unfold eulerQuadraticGram
  set P : ℝ → ℝ := fun s => (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s with hP
  have h0 : Integrable P semilocalArchimedeanGammaMeasure :=
    integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
      (semilocalArchimedeanJacobiPolynomial i) (semilocalArchimedeanJacobiPolynomial j)
  have h1 : Integrable (fun s => P s * Real.cos (δ * s)) semilocalArchimedeanGammaMeasure :=
    integrable_eval_mul_eval_mul_cos i j δ
  have h2 : Integrable (fun s => P s * Real.cos (2 * δ * s)) semilocalArchimedeanGammaMeasure :=
    integrable_eval_mul_eval_mul_cos i j (2 * δ)
  have hsplit : (fun s : ℝ => (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s *
      (1 + 2 * ε * Real.cos (δ * s) + ε ^ (2 : ℕ) * (1 + 2 * Real.cos (2 * δ * s)))) =
      fun s => P s + (2 * ε) * (P s * Real.cos (δ * s)) + ε ^ (2 : ℕ) * P s +
        (2 * ε ^ (2 : ℕ)) * (P s * Real.cos (2 * δ * s)) := by
    funext s
    simp only [hP]
    ring
  have hA : Integrable (fun s => P s + (2 * ε) * (P s * Real.cos (δ * s)))
      semilocalArchimedeanGammaMeasure := h0.add (h1.const_mul _)
  have hB : Integrable (fun s => P s + (2 * ε) * (P s * Real.cos (δ * s)) + ε ^ (2 : ℕ) * P s)
      semilocalArchimedeanGammaMeasure := hA.add (h0.const_mul _)
  rw [hsplit, integral_add hB (h2.const_mul _), integral_add hA (h0.const_mul _),
    integral_add h0 (h1.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]
  have hgram : ∫ s : ℝ, P s ∂semilocalArchimedeanGammaMeasure = if (i : ℕ) = j then 1 else 0 :=
    semilocalArchimedeanJacobiGram_eq_ite i j
  rw [hgram]
  simp only [eulerQuadraticMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    cosineModeTangent, hP]
  by_cases hij : i = j
  · subst hij; simp; ring
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp [hij, hij']; ring

/-- The quadratic determinant path. -/
noncomputable def eulerQuadraticDeterminant (δ : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  (eulerQuadraticGram δ ε n).det

theorem eulerQuadraticDeterminant_eq (δ : ℝ) (n : ℕ) (ε : ℝ) :
    eulerQuadraticDeterminant δ n ε = (eulerQuadraticMatrix δ n ε).det := by
  unfold eulerQuadraticDeterminant
  rw [eulerQuadraticGram_eq]

/-- `(log D_n)''(0) = 2(n+1) + 2J_{2δ}(n) − tr(T(δ)²)`. -/
noncomputable def eulerQuadraticLogJet (δ : ℝ) (n : ℕ) : ℝ :=
  2 * ((n : ℝ) + 1 + cosineModeDeterminantJet (2 * δ) n) - truncationDefect δ δ n

section calculus

variable (δ : ℝ) (n : ℕ)

theorem eulerQuadraticMatrix_zero : eulerQuadraticMatrix δ n 0 = 1 := by
  unfold eulerQuadraticMatrix
  simp

theorem hasDerivAt_eulerQuadraticMatrix_entry (t : ℝ) (i j : Fin (n + 1)) :
    HasDerivAt (fun ε => eulerQuadraticMatrix δ n ε i j)
      ((cosineModeTangent δ n + (2 * t) • (1 + cosineModeTangent (2 * δ) n)) i j) t := by
  have hfun : (fun ε => eulerQuadraticMatrix δ n ε i j) =
      fun ε => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j + ε * cosineModeTangent δ n i j +
        ε ^ (2 : ℕ) * ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j + cosineModeTangent (2 * δ) n i j) := by
    funext ε
    simp only [eulerQuadraticMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hfun]
  have h := (((hasDerivAt_id t).mul_const (cosineModeTangent δ n i j)).const_add
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j)).add
    (((hasDerivAt_id t).pow 2).mul_const
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j + cosineModeTangent (2 * δ) n i j))
  refine h.congr_deriv ?_
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem hasDerivAt_eulerQuadraticDeterminant (t : ℝ) :
    HasDerivAt (fun ε => eulerQuadraticDeterminant δ n ε)
      (detFirstJet (eulerQuadraticMatrix δ n t)
        (cosineModeTangent δ n + (2 * t) • (1 + cosineModeTangent (2 * δ) n))) t := by
  have hfun : (fun ε => eulerQuadraticDeterminant δ n ε) =
      fun ε => (eulerQuadraticMatrix δ n ε).det := by
    funext ε
    exact eulerQuadraticDeterminant_eq δ n ε
  rw [hfun]
  exact hasDerivAt_matrixDet (fun ε => eulerQuadraticMatrix δ n ε) _ t
    (fun i j => hasDerivAt_eulerQuadraticMatrix_entry δ n t i j)

/-- The inner slope `g_n(t) = tr(A(t)⁻¹ (T + 2t(1 + T(2δ))))`. -/
noncomputable def eulerQuadraticSlope (t : ℝ) : ℝ :=
  Matrix.trace ((eulerQuadraticMatrix δ n t)⁻¹ *
    (cosineModeTangent δ n + (2 * t) • (1 + cosineModeTangent (2 * δ) n)))

theorem deriv_log_eulerQuadraticDeterminant (t : ℝ) (hdet : (eulerQuadraticMatrix δ n t).det ≠ 0) :
    deriv (fun ε => Real.log (eulerQuadraticDeterminant δ n ε)) t = eulerQuadraticSlope δ n t := by
  have h := hasDerivAt_eulerQuadraticDeterminant δ n t
  have h0 : eulerQuadraticDeterminant δ n t ≠ 0 := by rw [eulerQuadraticDeterminant_eq]; exact hdet
  have hlog := h.log h0
  rw [hlog.deriv, eulerQuadraticDeterminant_eq, detFirstJet_eq_det_mul_trace_inv_mul _ _ hdet]
  unfold eulerQuadraticSlope
  field_simp

theorem eulerQuadraticSlope_zero : eulerQuadraticSlope δ n 0 = cosineModeDeterminantJet δ n := by
  unfold eulerQuadraticSlope
  rw [eulerQuadraticMatrix_zero]
  simp [trace_cosineModeTangent, cosineModeDeterminantJet]

theorem hasDerivAt_eulerQuadraticSlope :
    HasDerivAt (eulerQuadraticSlope δ n) (eulerQuadraticLogJet δ n) 0 := by
  have hfun : eulerQuadraticSlope δ n = fun t => ∑ i, ∑ k, (eulerQuadraticMatrix δ n t)⁻¹ i k *
      (cosineModeTangent δ n + (2 * t) • (1 + cosineModeTangent (2 * δ) n)) k i := by
    funext t
    unfold eulerQuadraticSlope
    simp [Matrix.trace, Matrix.mul_apply]
  rw [hfun]
  set T := cosineModeTangent δ n with hT
  set B := (1 + cosineModeTangent (2 * δ) n : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) with hB
  have hinv : ∀ i j, HasDerivAt (fun t : ℝ => (eulerQuadraticMatrix δ n t)⁻¹ i j) (-(T i j)) 0 := by
    intro i j
    have h := hasDerivAt_matrix_inv (fun t => eulerQuadraticMatrix δ n t) T 0
      (fun i j => by
        have := hasDerivAt_eulerQuadraticMatrix_entry δ n 0 i j
        simpa using this) (by rw [eulerQuadraticMatrix_zero]; simp) i j
    rw [eulerQuadraticMatrix_zero] at h
    simpa using h
  have hN : ∀ k i, HasDerivAt (fun t : ℝ => (T + (2 * t) • B) k i) (2 * B k i) 0 := by
    intro k i
    have hfun : (fun t : ℝ => (T + (2 * t) • B) k i) = fun t => T k i + (2 * t) * B k i := by
      funext t
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hfun]
    have := ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (B k i)
    refine (this.const_add (T k i)).congr_deriv ?_
    simp
  have hterm : ∀ i k : Fin (n + 1), HasDerivAt
      (fun t : ℝ => (eulerQuadraticMatrix δ n t)⁻¹ i k * (T + (2 * t) • B) k i)
      (-(T i k) * T k i + (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i k * (2 * B k i)) 0 := by
    intro i k
    refine ((hinv i k).fun_mul (hN k i)).congr_deriv ?_
    rw [eulerQuadraticMatrix_zero]
    simp
  have hrow : ∀ i : Fin (n + 1), HasDerivAt
      (fun t : ℝ => ∑ k, (eulerQuadraticMatrix δ n t)⁻¹ i k * (T + (2 * t) • B) k i)
      (∑ k, (-(T i k) * T k i + (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i k * (2 * B k i))) 0 :=
    fun i => HasDerivAt.fun_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin (n + 1))))
      (fun k _ => hterm i k)
  have h := HasDerivAt.fun_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin (n + 1)))) (fun i _ => hrow i)
  refine h.congr_deriv ?_
  unfold eulerQuadraticLogJet truncationDefect
  rw [hB]
  have hval : (∑ i, ∑ k, (-(T i k) * T k i +
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i k * (2 * (1 + cosineModeTangent (2 * δ) n) k i))) =
      -Matrix.trace (T * T) + 2 * Matrix.trace (1 + cosineModeTangent (2 * δ) n) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, neg_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply, Matrix.add_apply]
  rw [hval, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, trace_cosineModeTangent]
  unfold cosineModeDeterminantJet
  push_cast
  ring

/-- **The second derivative of the quadratic-weight log determinant.** -/
theorem deriv_deriv_log_eulerQuadraticDeterminant :
    deriv (deriv (fun ε => Real.log (eulerQuadraticDeterminant δ n ε))) 0 = eulerQuadraticLogJet δ n := by
  have hcont : Continuous (fun t : ℝ => (eulerQuadraticMatrix δ n t).det) := by
    apply Continuous.matrix_det
    unfold eulerQuadraticMatrix
    exact (continuous_const.add (continuous_id.smul continuous_const)).add
      ((continuous_id.pow 2).smul continuous_const)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (eulerQuadraticMatrix δ n t).det ≠ 0 :=
    hcont.continuousAt.eventually_ne (by rw [eulerQuadraticMatrix_zero]; simp)
  have heq : deriv (fun ε => Real.log (eulerQuadraticDeterminant δ n ε)) =ᶠ[𝓝 0]
      eulerQuadraticSlope δ n := by
    filter_upwards [hev] with t h
    exact deriv_log_eulerQuadraticDeterminant δ n t h
  exact ((hasDerivAt_eulerQuadraticSlope δ n).congr_of_eventuallyEq heq).deriv

end calculus

/-! ## The squared radius -/

theorem hasDerivAt_eulerQuadraticDeterminant' (δ : ℝ) (m : ℕ) (t : ℝ)
    (hdet : (eulerQuadraticMatrix δ m t).det ≠ 0) :
    HasDerivAt (fun ε => eulerQuadraticDeterminant δ m ε)
      (eulerQuadraticDeterminant δ m t * eulerQuadraticSlope δ m t) t := by
  refine (hasDerivAt_eulerQuadraticDeterminant δ m t).congr_deriv ?_
  rw [detFirstJet_eq_det_mul_trace_inv_mul _ _ hdet, eulerQuadraticDeterminant_eq]
  rfl

/-- `Δ_{n−1}` with `Δ_{−1} = 1`. -/
noncomputable def eulerQuadraticPrevDeterminant (δ : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | m + 1, ε => eulerQuadraticDeterminant δ m ε

/-- `g_{n−1}` with `g_{−1} = 0`. -/
noncomputable def eulerQuadraticPrevSlope (δ : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | m + 1, t => eulerQuadraticSlope δ m t

theorem hasDerivAt_eulerQuadraticPrevDeterminant (δ : ℝ) (n : ℕ) (t : ℝ)
    (hall : ∀ m ≤ n + 1, (eulerQuadraticMatrix δ m t).det ≠ 0) :
    HasDerivAt (fun ε => eulerQuadraticPrevDeterminant δ n ε)
      (eulerQuadraticPrevDeterminant δ n t * eulerQuadraticPrevSlope δ n t) t := by
  cases n with
  | zero =>
      change HasDerivAt (fun _ : ℝ => (1 : ℝ)) ((1 : ℝ) * 0) t
      rw [mul_zero]
      exact hasDerivAt_const _ _
  | succ m => exact hasDerivAt_eulerQuadraticDeterminant' δ m t (hall m (by omega))

theorem hasDerivAt_eulerQuadraticPrevSlope (δ : ℝ) (n : ℕ) :
    HasDerivAt (eulerQuadraticPrevSlope δ n) (prevJet (eulerQuadraticLogJet δ) n) 0 := by
  cases n with
  | zero =>
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0
      exact hasDerivAt_const _ _
  | succ m =>
      change HasDerivAt (eulerQuadraticSlope δ m) (eulerQuadraticLogJet δ m) 0
      exact hasDerivAt_eulerQuadraticSlope δ m

theorem eulerQuadraticPrevSlope_zero (δ : ℝ) (n : ℕ) :
    eulerQuadraticPrevSlope δ n 0 = prevJet (cosineModeDeterminantJet δ) n := by
  cases n with
  | zero => rfl
  | succ m => exact eulerQuadraticSlope_zero δ m

theorem eulerQuadraticPrevDeterminant_zero (δ : ℝ) (n : ℕ) :
    eulerQuadraticPrevDeterminant δ n 0 = 1 := by
  cases n with
  | zero => rfl
  | succ m =>
      change eulerQuadraticDeterminant δ m 0 = 1
      rw [eulerQuadraticDeterminant_eq, eulerQuadraticMatrix_zero]
      simp

theorem eulerQuadraticDeterminant_zero (δ : ℝ) (m : ℕ) : eulerQuadraticDeterminant δ m 0 = 1 := by
  rw [eulerQuadraticDeterminant_eq, eulerQuadraticMatrix_zero]
  simp

/-- The quadratic-weight squared Jacobi radius `r_n² Δ_{n−1} Δ_{n+1} / Δ_n²`. -/
noncomputable def eulerQuadraticSquaredRadius (δ : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  archimedeanSquaredRadius n *
    (eulerQuadraticPrevDeterminant δ n ε * eulerQuadraticDeterminant δ (n + 1) ε /
      eulerQuadraticDeterminant δ n ε ^ (2 : ℕ))

/-- `g_{n−1} + g_{n+1} − 2 g_n`. -/
noncomputable def eulerQuadraticRadiusSlope (δ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  eulerQuadraticPrevSlope δ n t + eulerQuadraticSlope δ (n + 1) t - 2 * eulerQuadraticSlope δ n t

theorem eulerQuadraticRadiusSlope_zero (δ : ℝ) (n : ℕ) :
    eulerQuadraticRadiusSlope δ n 0 = prevJet (cosineModeDeterminantJet δ) n +
      cosineModeDeterminantJet δ (n + 1) - 2 * cosineModeDeterminantJet δ n := by
  unfold eulerQuadraticRadiusSlope
  rw [eulerQuadraticPrevSlope_zero, eulerQuadraticSlope_zero, eulerQuadraticSlope_zero]

theorem hasDerivAt_eulerQuadraticRadiusSlope (δ : ℝ) (n : ℕ) :
    HasDerivAt (eulerQuadraticRadiusSlope δ n)
      (prevJet (eulerQuadraticLogJet δ) n + eulerQuadraticLogJet δ (n + 1) -
        2 * eulerQuadraticLogJet δ n) 0 := by
  unfold eulerQuadraticRadiusSlope
  exact ((hasDerivAt_eulerQuadraticPrevSlope δ n).add (hasDerivAt_eulerQuadraticSlope δ (n + 1))).sub
    ((hasDerivAt_eulerQuadraticSlope δ n).const_mul 2)

theorem hasDerivAt_eulerQuadraticSquaredRadius (δ : ℝ) (n : ℕ) (t : ℝ)
    (hall : ∀ m ≤ n + 1, (eulerQuadraticMatrix δ m t).det ≠ 0) :
    HasDerivAt (fun ε => eulerQuadraticSquaredRadius δ n ε)
      (eulerQuadraticSquaredRadius δ n t * eulerQuadraticRadiusSlope δ n t) t := by
  have hP := hasDerivAt_eulerQuadraticPrevDeterminant δ n t hall
  have hN := hasDerivAt_eulerQuadraticDeterminant' δ (n + 1) t (hall (n + 1) le_rfl)
  have hD := hasDerivAt_eulerQuadraticDeterminant' δ n t (hall n (by omega))
  have hD0 : eulerQuadraticDeterminant δ n t ≠ 0 := by
    rw [eulerQuadraticDeterminant_eq]
    exact hall n (by omega)
  have hquot := ((hP.mul hN).div (hD.pow 2) (pow_ne_zero 2 hD0)).const_mul
    (archimedeanSquaredRadius n)
  have hquot' : HasDerivAt (fun ε => eulerQuadraticSquaredRadius δ n ε) _ t := hquot
  refine hquot'.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply]
  unfold eulerQuadraticSquaredRadius eulerQuadraticRadiusSlope
  field_simp
  ring

theorem eulerQuadraticSquaredRadius_zero (δ : ℝ) (n : ℕ) :
    eulerQuadraticSquaredRadius δ n 0 = archimedeanSquaredRadius n := by
  unfold eulerQuadraticSquaredRadius
  rw [eulerQuadraticPrevDeterminant_zero, eulerQuadraticDeterminant_zero, eulerQuadraticDeterminant_zero]
  simp

/-- `(a_n²)''(0) = r_n² ((ΔΔ L)(n) + (ΔΔ J_δ)(n)²)`, `L = (log D)''(0)`. -/
noncomputable def onePrimeSecondOrderJet (δ : ℝ) (n : ℕ) : ℝ :=
  archimedeanSquaredRadius n *
    ((prevJet (eulerQuadraticLogJet δ) n + eulerQuadraticLogJet δ (n + 1) - 2 * eulerQuadraticLogJet δ n) +
      (prevJet (cosineModeDeterminantJet δ) n + cosineModeDeterminantJet δ (n + 1) -
        2 * cosineModeDeterminantJet δ n) ^ (2 : ℕ))

/-- **The second derivative of the quadratic-weight squared radius.** -/
theorem deriv_deriv_eulerQuadraticSquaredRadius (δ : ℝ) (n : ℕ) :
    deriv (deriv (fun ε => eulerQuadraticSquaredRadius δ n ε)) 0 = onePrimeSecondOrderJet δ n := by
  have hcont : ∀ m : ℕ, Continuous (fun t : ℝ => (eulerQuadraticMatrix δ m t).det) := by
    intro m
    apply Continuous.matrix_det
    unfold eulerQuadraticMatrix
    exact (continuous_const.add (continuous_id.smul continuous_const)).add
      ((continuous_id.pow 2).smul continuous_const)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ m ∈ Finset.range (n + 2), (eulerQuadraticMatrix δ m t).det ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro m _
    exact (hcont m).continuousAt.eventually_ne (by rw [eulerQuadraticMatrix_zero]; simp)
  have heq : deriv (fun ε => eulerQuadraticSquaredRadius δ n ε) =ᶠ[𝓝 0]
      fun t => eulerQuadraticSquaredRadius δ n t * eulerQuadraticRadiusSlope δ n t := by
    filter_upwards [hev] with t h
    exact (hasDerivAt_eulerQuadraticSquaredRadius δ n t
      (fun m hm => h m (Finset.mem_range.mpr (by omega)))).deriv
  have hall0 : ∀ m ≤ n + 1, (eulerQuadraticMatrix δ m 0).det ≠ 0 := fun m _ => by
    rw [eulerQuadraticMatrix_zero]; simp
  have hA := hasDerivAt_eulerQuadraticSquaredRadius δ n 0 hall0
  have hG := hasDerivAt_eulerQuadraticRadiusSlope δ n
  have hprod := hA.fun_mul hG
  rw [(hprod.congr_of_eventuallyEq heq).deriv, eulerQuadraticSquaredRadius_zero,
    eulerQuadraticRadiusSlope_zero]
  unfold onePrimeSecondOrderJet
  ring

/-! ## Bounds -/

theorem abs_squaredRadiusJetOf_cosineMode_le {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    |squaredRadiusJetOf (cosineModeDeterminantJet δ) n| ≤
      archimedeanSquaredRadius n * (2 * (entryBound δ (n + 1) (n + 1) + entryBound δ n n)) := by
  rw [squaredRadiusJetOf_cosineMode, abs_mul, abs_of_pos (archimedeanSquaredRadius_pos n), abs_mul,
    abs_two]
  have h1 := abs_cosineDiagonalMoment_le hδ (n + 1)
  have h2 := abs_cosineDiagonalMoment_le hδ n
  have h3 := abs_sub_le_abs_add_abs (cosineDiagonalMoment δ (n + 1)) (cosineDiagonalMoment δ n)
  apply mul_le_mul_of_nonneg_left _ (archimedeanSquaredRadius_pos n).le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  linarith

/-- **The one-prime second-order response is the harmonic jet at `2δ` up to `O((cosh δ)^{-1})`:**
`|[ε²] a²_{m+1} − [ε] a²_{m+1}|_{2δ}| ≤ r² (4 Σ E(i,m+2)² + 4 Σ E(i,m+1)² + 2 (E(m+2) + E(m+1))²)`. -/
theorem abs_onePrimeSecondOrder_le {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    |onePrimeSecondOrderJet δ (m + 1) / 2 -
        squaredRadiusJetOf (cosineModeDeterminantJet (2 * δ)) (m + 1)| ≤
      archimedeanSquaredRadius (m + 1) *
        (4 * ∑ i : Fin (m + 3), entryBound δ i (m + 2) * entryBound δ i (m + 2) +
          4 * ∑ i : Fin (m + 2), entryBound δ i (m + 1) * entryBound δ i (m + 1) +
          2 * (entryBound δ (m + 2) (m + 2) + entryBound δ (m + 1) (m + 1)) ^ (2 : ℕ)) := by
  have hr := archimedeanSquaredRadius_pos (m + 1)
  set r2 := archimedeanSquaredRadius (m + 1) with hr2
  -- exact decomposition
  have hdec : onePrimeSecondOrderJet δ (m + 1) / 2 -
      squaredRadiusJetOf (cosineModeDeterminantJet (2 * δ)) (m + 1) =
      r2 * (-(1 / 2) * ((truncationDefect δ δ (m + 2) - truncationDefect δ δ (m + 1)) -
        (truncationDefect δ δ (m + 1) - truncationDefect δ δ m)) +
        (1 / 2) * (cosineModeDeterminantJet δ m + cosineModeDeterminantJet δ (m + 2) -
          2 * cosineModeDeterminantJet δ (m + 1)) ^ (2 : ℕ)) := by
    unfold onePrimeSecondOrderJet squaredRadiusJetOf eulerQuadraticLogJet
    simp only [prevJet]
    push_cast
    ring
  rw [hdec, abs_mul, abs_of_pos hr]
  apply mul_le_mul_of_nonneg_left _ hr.le
  have i1 : |truncationDefect δ δ (m + 2) - truncationDefect δ δ (m + 1)| ≤
      8 * ∑ i : Fin (m + 3), entryBound δ i (m + 2) * entryBound δ i (m + 2) :=
    abs_truncationDefect_succ_sub_le hδ hδ (m + 1)
  have i0 := abs_truncationDefect_succ_sub_le hδ hδ m
  have hD := abs_sub_le_abs_add_abs (truncationDefect δ δ (m + 2) - truncationDefect δ δ (m + 1))
    (truncationDefect δ δ (m + 1) - truncationDefect δ δ m)
  have hJ : |cosineModeDeterminantJet δ m + cosineModeDeterminantJet δ (m + 2) -
      2 * cosineModeDeterminantJet δ (m + 1)| ≤
      2 * (entryBound δ (m + 2) (m + 2) + entryBound δ (m + 1) (m + 1)) := by
    have e1 := cosineModeDeterminantJet_succ_sub δ (m + 1)
    have e0 := cosineModeDeterminantJet_succ_sub δ m
    have hm : (m + 1 + 1) = m + 2 := rfl
    rw [hm] at e1
    have hid : cosineModeDeterminantJet δ m + cosineModeDeterminantJet δ (m + 2) -
        2 * cosineModeDeterminantJet δ (m + 1) =
        2 * (cosineDiagonalMoment δ (m + 2) - cosineDiagonalMoment δ (m + 1)) := by linarith
    rw [hid, abs_mul, abs_two]
    have b1 := abs_cosineDiagonalMoment_le hδ (m + 2)
    have b2 := abs_cosineDiagonalMoment_le hδ (m + 1)
    have b3 := abs_sub_le_abs_add_abs (cosineDiagonalMoment δ (m + 2)) (cosineDiagonalMoment δ (m + 1))
    nlinarith
  have hJ2 : (cosineModeDeterminantJet δ m + cosineModeDeterminantJet δ (m + 2) -
      2 * cosineModeDeterminantJet δ (m + 1)) ^ (2 : ℕ) ≤
      (2 * (entryBound δ (m + 2) (m + 2) + entryBound δ (m + 1) (m + 1))) ^ (2 : ℕ) := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hJ 2
  have hsplit := abs_add_le (-(1 / 2 : ℝ) * ((truncationDefect δ δ (m + 2) - truncationDefect δ δ (m + 1)) -
        (truncationDefect δ δ (m + 1) - truncationDefect δ δ m)))
    ((1 / 2 : ℝ) * (cosineModeDeterminantJet δ m + cosineModeDeterminantJet δ (m + 2) -
          2 * cosineModeDeterminantJet δ (m + 1)) ^ (2 : ℕ))
  rw [abs_mul, abs_mul, show |(-(1 / 2) : ℝ)| = 1 / 2 by norm_num, show |(1 / 2 : ℝ)| = 1 / 2 by norm_num,
    abs_of_nonneg (sq_nonneg (cosineModeDeterminantJet δ m + cosineModeDeterminantJet δ (m + 2) -
      2 * cosineModeDeterminantJet δ (m + 1)))] at hsplit
  calc _ ≤ _ := hsplit
    _ ≤ 1 / 2 * (8 * ∑ i : Fin (m + 3), entryBound δ i (m + 2) * entryBound δ i (m + 2) +
          8 * ∑ i : Fin (m + 2), entryBound δ i (m + 1) * entryBound δ i (m + 1)) +
        1 / 2 * (2 * (entryBound δ (m + 2) (m + 2) + entryBound δ (m + 1) (m + 1))) ^ (2 : ℕ) := by
        gcongr
        linarith
    _ = _ := by ring

end CosineModeResponse
end RHTower

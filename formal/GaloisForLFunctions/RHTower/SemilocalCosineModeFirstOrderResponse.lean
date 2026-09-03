import GaloisForLFunctions.RHTower.SemilocalProlateFirstEulerCriticalJet
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiOrthonormal

/-!
# First-order response of the semilocal Jacobi data to a cosine mode

Multiply the archimedean Gamma measure `μ` by `1 + 2ε cos(δ s)`.  In the orthonormal archimedean
Jacobi basis the Gram matrix of the perturbed measure is `1 + ε T_n(δ)` with the cosine tangent
`T_n(δ)_{ij} = 2 ∫ p_i p_j cos(δ s) dμ`, so the normalized Hankel determinant of the perturbed
measure has first-order jet `tr T_n(δ) = 2 Σ_{j ≤ n} m_j(δ)`, where `m_j(δ) = ∫ p_j² cos(δ s) dμ`
is the diagonal cosine moment.  Carrying this determinant family through the Hankel quotient
`a_n² = r_n² Δ_{n−1}Δ_{n+1}/Δ_n²` gives the **first-order response of the Jacobi radii**

`a_n(ε)² = r_n² (1 + 2ε (m_{n+1}(δ) − m_n(δ))) + O(ε²)`,   `a_n(ε) = r_n (1 + ε (m_{n+1}(δ) − m_n(δ))) + O(ε²)`,

and the corresponding jet of the Route J four-radius critical residual.  The two-prime beat mode
of Connes–Consani–Moscovici's semilocal measure is the instance `δ = log(p₂/p₁)`,
`ε = (p₁p₂)^{−1/2}`; the one-prime harmonics are the instances `δ = d log p`,
`ε = q^{d/2}/(1 − q)`.  The transfer theorems are stated for an arbitrary jet sequence, so they
also recover the corpus's first Euler jet as the special case of the published rank-two tangent.
-/

open Matrix Real MeasureTheory
open scoped BigOperators

namespace RHTower

namespace CosineModeResponse

open GaloisForLFunctions.HilbertMetric
open FirstEulerCriticalJet

/-! ## General transfer with an arbitrary jet sequence -/

/-- Jet of the formal predecessor: `0` at degree zero, `J (n)` at degree `n + 1`. -/
def prevJet (J : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => J n

theorem hasDerivAt_previousDeterminantPathOf_jet
    (Δ : ℕ → ℝ → ℝ) (J : ℕ → ℝ)
    (hΔ : ∀ n, HasDerivAt (Δ n) (J n) 0) (n : ℕ) :
    HasDerivAt (previousDeterminantPathOf Δ n) (prevJet J n) 0 := by
  cases n with
  | zero =>
      change HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0
      exact hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))
  | succ n =>
      change HasDerivAt (Δ n) (J n) 0
      exact hΔ n

/-- Squared-radius jet attached to a jet sequence: `r_n² (J_{n−1} + J_{n+1} − 2 J_n)`. -/
noncomputable def squaredRadiusJetOf (J : ℕ → ℝ) (n : ℕ) : ℝ :=
  archimedeanSquaredRadius n * (prevJet J n + J (n + 1) - 2 * J n)

/-- **General determinant-to-radius transfer.** -/
theorem hasDerivAt_squaredJacobiRadiusPathOf_jet
    (Δ : ℕ → ℝ → ℝ) (J : ℕ → ℝ)
    (hzero : ∀ n, Δ n 0 = 1)
    (hΔ : ∀ n, HasDerivAt (Δ n) (J n) 0) (n : ℕ) :
    HasDerivAt (squaredJacobiRadiusPathOf Δ n) (squaredRadiusJetOf J n) 0 := by
  have hprev := hasDerivAt_previousDeterminantPathOf_jet Δ J hΔ n
  have hnext := hΔ (n + 1)
  have hcurrent := hΔ n
  have hquot := (hprev.mul hnext).div (hcurrent.pow 2) (by simp [hzero])
  have hscaled := hquot.const_mul (archimedeanSquaredRadius n)
  change HasDerivAt
    (fun q : ℝ => archimedeanSquaredRadius n *
      ((previousDeterminantPathOf Δ n * Δ (n + 1) / Δ n ^ 2) q))
    (squaredRadiusJetOf J n) 0
  refine hscaled.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply, previousDeterminantPathOf_zero Δ hzero, hzero,
    one_pow, mul_one, one_mul, Nat.cast_ofNat, div_one]
  unfold squaredRadiusJetOf
  ring

/-- Radius jet attached to a jet sequence. -/
noncomputable def radiusJetOf (J : ℕ → ℝ) (n : ℕ) : ℝ :=
  squaredRadiusJetOf J n / (2 * semilocalArchimedeanJacobiCoefficient n)

theorem hasDerivAt_jacobiRadiusPathOf_jet
    (Δ : ℕ → ℝ → ℝ) (J : ℕ → ℝ)
    (hzero : ∀ n, Δ n 0 = 1)
    (hΔ : ∀ n, HasDerivAt (Δ n) (J n) 0) (n : ℕ) :
    HasDerivAt (jacobiRadiusPathOf Δ n) (radiusJetOf J n) 0 := by
  have hpos : 0 < squaredJacobiRadiusPathOf Δ n 0 := by
    rw [squaredJacobiRadiusPathOf_zero Δ hzero]
    exact archimedeanSquaredRadius_pos n
  have hsqrt := (hasDerivAt_squaredJacobiRadiusPathOf_jet Δ J hzero hΔ n).sqrt hpos.ne'
  change HasDerivAt (fun q : ℝ => Real.sqrt (squaredJacobiRadiusPathOf Δ n q))
    (radiusJetOf J n) 0
  refine hsqrt.congr_deriv ?_
  unfold radiusJetOf
  rw [show Real.sqrt (squaredJacobiRadiusPathOf Δ n 0) =
      semilocalArchimedeanJacobiCoefficient n by
    simpa [jacobiRadiusPathOf] using jacobiRadiusPathOf_zero Δ hzero n]

/-- Residual jet attached to a jet sequence. -/
noncomputable def residualJetOf (J : ℕ → ℝ) (n : ℕ) : ℝ :=
  let r := semilocalArchimedeanJacobiCoefficient
  let u := radiusJetOf J
  u (2 * n) * r (2 * n + 1) + r (2 * n) * u (2 * n + 1) -
      2 * r (2 * n + 1) * u (2 * n + 1) - 2 * r (2 * n + 2) * u (2 * n + 2) +
      u (2 * n + 2) * r (2 * n + 3) + r (2 * n + 2) * u (2 * n + 3)

theorem hasDerivAt_criticalResidualPathOf_jet
    (Δ : ℕ → ℝ → ℝ) (J : ℕ → ℝ)
    (hzero : ∀ n, Δ n 0 = 1)
    (hΔ : ∀ n, HasDerivAt (Δ n) (J n) 0) (n : ℕ) :
    HasDerivAt (criticalResidualPathOf Δ n) (residualJetOf J n) 0 := by
  have h₀ := hasDerivAt_jacobiRadiusPathOf_jet Δ J hzero hΔ (2 * n)
  have h₁ := hasDerivAt_jacobiRadiusPathOf_jet Δ J hzero hΔ (2 * n + 1)
  have h₂ := hasDerivAt_jacobiRadiusPathOf_jet Δ J hzero hΔ (2 * n + 2)
  have h₃ := hasDerivAt_jacobiRadiusPathOf_jet Δ J hzero hΔ (2 * n + 3)
  have h := (((h₀.mul h₁).sub (h₁.pow 2)).sub (h₂.pow 2)).add (h₂.mul h₃)
  change HasDerivAt
    (jacobiRadiusPathOf Δ (2 * n) * jacobiRadiusPathOf Δ (2 * n + 1) -
      jacobiRadiusPathOf Δ (2 * n + 1) ^ 2 -
      jacobiRadiusPathOf Δ (2 * n + 2) ^ 2 +
      jacobiRadiusPathOf Δ (2 * n + 2) * jacobiRadiusPathOf Δ (2 * n + 3))
    (residualJetOf J n) 0
  refine h.congr_deriv ?_
  simp only [jacobiRadiusPathOf_zero Δ hzero, Nat.cast_ofNat]
  unfold residualJetOf
  ring

/-! ## The cosine mode -/

/-- The diagonal cosine moment `m_j(δ) = ∫ p_j² cos(δ s) dμ`. -/
noncomputable def cosineDiagonalMoment (δ : ℝ) (j : ℕ) : ℝ :=
  ∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial j).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s * Real.cos (δ * s)
    ∂semilocalArchimedeanGammaMeasure

/-- The cosine tangent `T_n(δ)_{ij} = 2 ∫ p_i p_j cos(δ s) dμ`. -/
noncomputable def cosineModeTangent (δ : ℝ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => 2 * ∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s * Real.cos (δ * s)
    ∂semilocalArchimedeanGammaMeasure

theorem trace_cosineModeTangent (δ : ℝ) (n : ℕ) :
    (cosineModeTangent δ n).trace =
      2 * ∑ j ∈ Finset.range (n + 1), cosineDiagonalMoment δ j := by
  unfold Matrix.trace cosineModeTangent cosineDiagonalMoment
  simp only [Matrix.diag_apply]
  rw [Finset.mul_sum]
  exact (Fin.sum_univ_eq_sum_range (fun j => 2 * ∫ s : ℝ,
    (semilocalArchimedeanJacobiPolynomial j).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s * Real.cos (δ * s)
      ∂semilocalArchimedeanGammaMeasure) (n + 1))

theorem integrable_eval_mul_eval_mul_cos (i j : ℕ) (δ : ℝ) :
    Integrable (fun s : ℝ => (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s * Real.cos (δ * s))
      semilocalArchimedeanGammaMeasure := by
  have h := integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (semilocalArchimedeanJacobiPolynomial i) (semilocalArchimedeanJacobiPolynomial j)
  have hc : Continuous fun s : ℝ => Real.cos (δ * s) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  refine (h.mul_bdd (c := 1) hc.aestronglyMeasurable ?_)
  exact Filter.Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _

/-- Gram matrix of the archimedean orthonormal polynomials for the measure
`(1 + 2ε cos(δ s)) μ`. -/
noncomputable def cosineModeGram (δ ε : ℝ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => ∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s * (1 + 2 * ε * Real.cos (δ * s))
    ∂semilocalArchimedeanGammaMeasure

/-- **The perturbed Gram matrix is `1 + ε T_n(δ)`.** -/
theorem cosineModeGram_eq (δ ε : ℝ) (n : ℕ) :
    cosineModeGram δ ε n = 1 + ε • cosineModeTangent δ n := by
  ext i j
  unfold cosineModeGram cosineModeTangent
  have h1 := integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (semilocalArchimedeanJacobiPolynomial i) (semilocalArchimedeanJacobiPolynomial j)
  have h2 := integrable_eval_mul_eval_mul_cos i j δ
  have hsplit : (fun s : ℝ => (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s * (1 + 2 * ε * Real.cos (δ * s))) =
      fun s => (semilocalArchimedeanJacobiPolynomial i).eval s *
        (semilocalArchimedeanJacobiPolynomial j).eval s +
        (2 * ε) * ((semilocalArchimedeanJacobiPolynomial i).eval s *
          (semilocalArchimedeanJacobiPolynomial j).eval s * Real.cos (δ * s)) := by
    funext s; ring
  rw [hsplit, integral_add h1 (h2.const_mul _), integral_const_mul]
  have hgram : ∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s ∂semilocalArchimedeanGammaMeasure =
      if (i : ℕ) = j then 1 else 0 := semilocalArchimedeanJacobiGram_eq_ite i j
  rw [hgram, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp; ring
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp [hij, hij']; ring

/-- Normalized determinant path of the cosine mode. -/
noncomputable def cosineModeDeterminantPath (δ : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  (cosineModeGram δ ε n).det

/-- First-order jet of the cosine-mode determinant: the trace of the cosine tangent. -/
noncomputable def cosineModeDeterminantJet (δ : ℝ) (n : ℕ) : ℝ :=
  2 * ∑ j ∈ Finset.range (n + 1), cosineDiagonalMoment δ j

theorem cosineModeDeterminantPath_zero (δ : ℝ) (n : ℕ) :
    cosineModeDeterminantPath δ n 0 = 1 := by
  unfold cosineModeDeterminantPath
  rw [cosineModeGram_eq]
  simp

/-- **Determinant jet of the cosine mode is the trace of the cosine tangent.** -/
theorem hasDerivAt_cosineModeDeterminantPath (δ : ℝ) (n : ℕ) :
    HasDerivAt (cosineModeDeterminantPath δ n) (cosineModeDeterminantJet δ n) 0 := by
  have hpath : cosineModeDeterminantPath δ n =
      fun ε => (1 + ε • cosineModeTangent δ n).det := by
    funext ε
    unfold cosineModeDeterminantPath
    rw [cosineModeGram_eq]
  rw [hpath]
  have hentry : ∀ i j, HasDerivAt (fun ε : ℝ => (1 + ε • cosineModeTangent δ n) i j)
      (cosineModeTangent δ n i j) 0 := by
    intro i j
    have : (fun ε : ℝ => (1 + ε • cosineModeTangent δ n) i j) =
        fun ε => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j + ε * cosineModeTangent δ n i j := by
      funext ε
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (cosineModeTangent δ n i j)).const_add
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j)
  have hdet := hasDerivAt_matrixDet (fun ε : ℝ => 1 + ε • cosineModeTangent δ n)
    (cosineModeTangent δ n) 0 hentry
  refine hdet.congr_deriv ?_
  simp only [zero_smul, add_zero]
  rw [detFirstJet_eq_det_mul_trace_inv_mul (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (cosineModeTangent δ n) (by simp)]
  simp [trace_cosineModeTangent, cosineModeDeterminantJet]

/-! ## The first-order response -/

theorem cosineModeDeterminantJet_succ_sub (δ : ℝ) (n : ℕ) :
    cosineModeDeterminantJet δ (n + 1) - cosineModeDeterminantJet δ n =
      2 * cosineDiagonalMoment δ (n + 1) := by
  unfold cosineModeDeterminantJet
  rw [Finset.sum_range_succ]
  ring

theorem cosineModeDeterminantJet_sub_prev (δ : ℝ) (n : ℕ) :
    cosineModeDeterminantJet δ n - prevJet (cosineModeDeterminantJet δ) n =
      2 * cosineDiagonalMoment δ n := by
  cases n with
  | zero =>
      simp [prevJet, cosineModeDeterminantJet]
  | succ n =>
      change cosineModeDeterminantJet δ (n + 1) - cosineModeDeterminantJet δ n = _
      exact cosineModeDeterminantJet_succ_sub δ n

/-- **First-order response of the squared Jacobi radius to the cosine mode:**
`[ε] a_n(ε)² = 2 r_n² (m_{n+1}(δ) − m_n(δ))`. -/
theorem squaredRadiusJetOf_cosineMode (δ : ℝ) (n : ℕ) :
    squaredRadiusJetOf (cosineModeDeterminantJet δ) n =
      archimedeanSquaredRadius n * (2 * (cosineDiagonalMoment δ (n + 1) -
        cosineDiagonalMoment δ n)) := by
  unfold squaredRadiusJetOf
  have h1 := cosineModeDeterminantJet_succ_sub δ n
  have h2 := cosineModeDeterminantJet_sub_prev δ n
  have : prevJet (cosineModeDeterminantJet δ) n + cosineModeDeterminantJet δ (n + 1) -
      2 * cosineModeDeterminantJet δ n =
      (cosineModeDeterminantJet δ (n + 1) - cosineModeDeterminantJet δ n) -
      (cosineModeDeterminantJet δ n - prevJet (cosineModeDeterminantJet δ) n) := by ring
  rw [this, h1, h2]
  ring

/-- **First-order response of the Jacobi radius:** `[ε] a_n(ε) = r_n (m_{n+1}(δ) − m_n(δ))`. -/
theorem radiusJetOf_cosineMode (δ : ℝ) (n : ℕ) :
    radiusJetOf (cosineModeDeterminantJet δ) n =
      semilocalArchimedeanJacobiCoefficient n *
        (cosineDiagonalMoment δ (n + 1) - cosineDiagonalMoment δ n) := by
  unfold radiusJetOf
  rw [squaredRadiusJetOf_cosineMode, archimedeanSquaredRadius_eq_coefficient_sq]
  have hr := (semilocalArchimedeanJacobiCoefficient_pos n).ne'
  field_simp

/-- **The cosine-mode Jacobi radii have the first-order response `r_n (m_{n+1} − m_n)`.** -/
theorem hasDerivAt_cosineModeJacobiRadius (δ : ℝ) (n : ℕ) :
    HasDerivAt (jacobiRadiusPathOf (cosineModeDeterminantPath δ) n)
      (semilocalArchimedeanJacobiCoefficient n *
        (cosineDiagonalMoment δ (n + 1) - cosineDiagonalMoment δ n)) 0 := by
  have h := hasDerivAt_jacobiRadiusPathOf_jet (cosineModeDeterminantPath δ)
    (cosineModeDeterminantJet δ) (cosineModeDeterminantPath_zero δ)
    (hasDerivAt_cosineModeDeterminantPath δ) n
  rwa [radiusJetOf_cosineMode] at h

/-- **The cosine-mode Route J residual has first-order jet `residualJetOf`.** -/
theorem hasDerivAt_cosineModeCriticalResidual (δ : ℝ) (n : ℕ) :
    HasDerivAt (criticalResidualPathOf (cosineModeDeterminantPath δ) n)
      (residualJetOf (cosineModeDeterminantJet δ) n) 0 :=
  hasDerivAt_criticalResidualPathOf_jet (cosineModeDeterminantPath δ)
    (cosineModeDeterminantJet δ) (cosineModeDeterminantPath_zero δ)
    (hasDerivAt_cosineModeDeterminantPath δ) n

/-! ## The beat mode of two primes -/

/-- Beat frequency of the Euler factors of two primes. -/
noncomputable def beatFrequency (p₁ p₂ : ℕ) : ℝ := Real.log ((p₂ : ℝ) / p₁)

/-- Beat amplitude of the Euler factors of two primes. -/
noncomputable def beatAmplitude (p₁ p₂ : ℕ) : ℝ := ((p₁ : ℝ) * p₂) ^ (-(1 : ℝ) / 2)

/-- **First-order beat-mode response of the Jacobi radii.** -/
theorem hasDerivAt_beatModeJacobiRadius (p₁ p₂ n : ℕ) :
    HasDerivAt (jacobiRadiusPathOf (cosineModeDeterminantPath (beatFrequency p₁ p₂)) n)
      (semilocalArchimedeanJacobiCoefficient n *
        (cosineDiagonalMoment (beatFrequency p₁ p₂) (n + 1) -
          cosineDiagonalMoment (beatFrequency p₁ p₂) n)) 0 :=
  hasDerivAt_cosineModeJacobiRadius _ n

end CosineModeResponse

end RHTower

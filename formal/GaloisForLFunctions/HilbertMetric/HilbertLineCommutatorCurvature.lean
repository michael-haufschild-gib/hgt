import GaloisForLFunctions.HilbertMetric.GaussianMetricRankOneFracture

/-!
# Gaussian Hilbert-line commutator curvature

A finite configuration whose affine span is one-dimensional has Gaussian Gram
`K(t)_{ij} = exp (-t ‖x_i - x_j‖²)`, which in the scalar coordinate of the line is
`exp (-t (ξ_i - ξ_j)²)`.  Its coherent family `ε(√(2t) ξ_i e)` has Gram
`exp (2t ξ_i ξ_j)`, and the annihilation operator in the direction of the line acts on that family
diagonally with eigenvalues `√(2t) ξ_i`.  The compression of the annihilation operator to the span
of the coherent family is therefore, in any orthonormal coordinates, the positive-square-root
similarity of the eigenvalue diagonal by the coherent Gram.

The main theorem is the exact curvature law

```text
-t² · (log det K)''(t) = ½ ‖[A_t, A_tᵀ]‖²_HS .
```

* `HilbertMetric.selfCommutator_energy_sqrtSimilarity_eq_of_gram` — the compressed-eigenoperator
  energy depends only on the Gram of the spanning family, not on the chosen square root.  This is
  the exact sense in which `A_t` is well defined;
* `HilbertMetric.hilbertLineGaussian_logDet_curvature_eq_selfCommutator` — the law itself;
* `HilbertMetric.hilbertLineGaussian_logDet_secondDerivative_lt_zero` — strict negativity for
  distinct points and at least two of them;
* `HilbertMetric.hilbertLineAnnihilationEnergy_translation_invariant` and
  `..._reflection_invariant` — independence of the origin and of the chosen unit vector on the
  line.
-/

open scoped BigOperators Matrix MatrixOrder

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-! ### Orthogonal invariance of the self-commutator energy -/

theorem matrixSelfCommutator_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q A : Matrix ι ι ℝ) (hQ : Qᵀ * Q = 1) :
    matrixSelfCommutator (Q * A * Qᵀ) = Q * matrixSelfCommutator A * Qᵀ := by
  unfold matrixSelfCommutator
  have htrans : (Q * A * Qᵀ)ᵀ = Q * Aᵀ * Qᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    noncomm_ring
  rw [htrans]
  calc
    Q * A * Qᵀ * (Q * Aᵀ * Qᵀ) - Q * Aᵀ * Qᵀ * (Q * A * Qᵀ)
        = Q * A * (Qᵀ * Q) * Aᵀ * Qᵀ - Q * Aᵀ * (Qᵀ * Q) * A * Qᵀ := by noncomm_ring
    _ = Q * (A * Aᵀ - Aᵀ * A) * Qᵀ := by rw [hQ]; noncomm_ring

theorem matrixHilbertSchmidtEnergy_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q B : Matrix ι ι ℝ) (hQ : Qᵀ * Q = 1) :
    matrixHilbertSchmidtEnergy (Q * B * Qᵀ) = matrixHilbertSchmidtEnergy B := by
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul,
    matrixHilbertSchmidtEnergy_eq_trace_transpose_mul]
  have htrans : (Q * B * Qᵀ)ᵀ = Q * Bᵀ * Qᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    noncomm_ring
  rw [htrans]
  calc
    Matrix.trace (Q * Bᵀ * Qᵀ * (Q * B * Qᵀ))
        = Matrix.trace (Q * (Bᵀ * B) * Qᵀ) := by
          congr 1
          calc
            Q * Bᵀ * Qᵀ * (Q * B * Qᵀ) = Q * Bᵀ * (Qᵀ * Q) * B * Qᵀ := by noncomm_ring
            _ = Q * (Bᵀ * B) * Qᵀ := by rw [hQ]; noncomm_ring
    _ = Matrix.trace (Qᵀ * (Q * (Bᵀ * B))) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Bᵀ * B) := by
          rw [show Qᵀ * (Q * (Bᵀ * B)) = (Qᵀ * Q) * (Bᵀ * B) by noncomm_ring, hQ, one_mul]

theorem matrixHilbertSchmidtEnergy_selfCommutator_conj
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q A : Matrix ι ι ℝ) (hQ : Qᵀ * Q = 1) :
    matrixHilbertSchmidtEnergy (matrixSelfCommutator (Q * A * Qᵀ))
      = matrixHilbertSchmidtEnergy (matrixSelfCommutator A) := by
  rw [matrixSelfCommutator_conj Q A hQ, matrixHilbertSchmidtEnergy_conj _ _ hQ]

/-! ### The compressed-eigenoperator energy depends only on the Gram -/

/-- **Gram invariance of the compressed-eigenoperator energy.**  If `R` is any matrix whose Gram
`Rᵀ R` is the positive-definite matrix `M`, then conjugating `D` by `R` gives the same
self-commutator energy as the canonical positive-square-root similarity.  Concretely: the
compression of an operator that is diagonal on a spanning family depends only on the Gram of that
family. -/
theorem selfCommutator_energy_sqrtSimilarity_eq_of_gram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M D R : Matrix ι ι ℝ) (hM : M.PosDef) (hR : Rᵀ * R = M) :
    matrixHilbertSchmidtEnergy (matrixSelfCommutator (R * D * R⁻¹))
      = matrixHilbertSchmidtEnergy (matrixSelfCommutator (matrixSqrtSimilarity M D)) := by
  have hPunit : IsUnit (CFC.sqrt M) :=
    (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  letI : Invertible (CFC.sqrt M) := hPunit.nonempty_invertible.some
  set P : Matrix ι ι ℝ := CFC.sqrt M with hPdef
  have hPtrans : Pᵀ = P := matrixSqrt_transpose M
  have hP2 : P * P = M := matrixSqrt_mul_self M hM
  have hPinvP : P⁻¹ * P = 1 := Matrix.inv_mul_of_invertible _
  have hPPinv : P * P⁻¹ = 1 := Matrix.mul_inv_of_invertible _
  have hPinvTrans : (P⁻¹)ᵀ = P⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hPtrans]
  set Q : Matrix ι ι ℝ := R * P⁻¹ with hQdef
  have hQortho : Qᵀ * Q = 1 := by
    rw [hQdef, Matrix.transpose_mul, hPinvTrans]
    calc
      P⁻¹ * Rᵀ * (R * P⁻¹) = P⁻¹ * (Rᵀ * R) * P⁻¹ := by noncomm_ring
      _ = P⁻¹ * (P * P) * P⁻¹ := by rw [hR, hP2]
      _ = (P⁻¹ * P) * (P * P⁻¹) := by noncomm_ring
      _ = 1 := by rw [hPinvP, hPPinv, one_mul]
  have hRunit : IsUnit R := by
    have hQunit : IsUnit Q := IsUnit.of_mul_eq_one_right Qᵀ hQortho
    have : R = Q * P := by rw [hQdef]; rw [Matrix.mul_assoc, hPinvP, Matrix.mul_one]
    rw [this]
    exact hQunit.mul hPunit
  letI : Invertible R := hRunit.nonempty_invertible.some
  have hRQP : R = Q * P := by rw [hQdef, Matrix.mul_assoc, hPinvP, Matrix.mul_one]
  have hQinv : Q⁻¹ = Qᵀ := by
    have hQunit : IsUnit Q := IsUnit.of_mul_eq_one_right Qᵀ hQortho
    letI : Invertible Q := hQunit.nonempty_invertible.some
    exact Matrix.inv_eq_left_inv hQortho
  have hRinvEq : R⁻¹ = P⁻¹ * Qᵀ := by
    have hQunit : IsUnit Q := IsUnit.of_mul_eq_one_right Qᵀ hQortho
    letI : Invertible Q := hQunit.nonempty_invertible.some
    rw [hRQP, Matrix.mul_inv_rev, hQinv]
  have hconj : R * D * R⁻¹ = Q * matrixSqrtSimilarity M D * Qᵀ := by
    rw [hRinvEq, hRQP, matrixSqrtSimilarity, ← hPdef]
    noncomm_ring
  rw [hconj, matrixHilbertSchmidtEnergy_selfCommutator_conj _ _ hQortho]

/-- Rescaling the spanning family by a positive diagonal gauge does not change the compressed
eigenoperator energy, provided the eigenvalue matrix is diagonal. -/
theorem selfCommutator_energy_sqrtSimilarity_gauge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef) (δ d : ι → ℝ) (hδ : ∀ i, δ i ≠ 0)
    (hgauge : (Matrix.diagonal δ * M * Matrix.diagonal δ).PosDef) :
    matrixHilbertSchmidtEnergy (matrixSelfCommutator
        (matrixSqrtSimilarity (Matrix.diagonal δ * M * Matrix.diagonal δ)
          (Matrix.diagonal d)))
      = matrixHilbertSchmidtEnergy (matrixSelfCommutator
          (matrixSqrtSimilarity M (Matrix.diagonal d))) := by
  have hPunit : IsUnit (CFC.sqrt M) :=
    (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  letI : Invertible (CFC.sqrt M) := hPunit.nonempty_invertible.some
  set P : Matrix ι ι ℝ := CFC.sqrt M with hPdef
  have hPtrans : Pᵀ = P := matrixSqrt_transpose M
  have hP2 : P * P = M := matrixSqrt_mul_self M hM
  have hΔunit : IsUnit (Matrix.diagonal δ) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hδ i)
  letI : Invertible (Matrix.diagonal δ) := hΔunit.nonempty_invertible.some
  set R : Matrix ι ι ℝ := P * Matrix.diagonal δ with hRdef
  have hRgram : Rᵀ * R = Matrix.diagonal δ * M * Matrix.diagonal δ := by
    rw [hRdef, Matrix.transpose_mul, Matrix.diagonal_transpose, hPtrans]
    calc
      Matrix.diagonal δ * P * (P * Matrix.diagonal δ)
          = Matrix.diagonal δ * (P * P) * Matrix.diagonal δ := by noncomm_ring
      _ = Matrix.diagonal δ * M * Matrix.diagonal δ := by rw [hP2]
  have hkey := selfCommutator_energy_sqrtSimilarity_eq_of_gram
    (Matrix.diagonal δ * M * Matrix.diagonal δ) (Matrix.diagonal d) R hgauge hRgram
  rw [← hkey]
  congr 1
  congr 1
  have hRinv : R⁻¹ = (Matrix.diagonal δ)⁻¹ * P⁻¹ := by
    rw [hRdef, Matrix.mul_inv_rev]
  rw [hRdef, hRinv, matrixSqrtSimilarity, ← hPdef]
  have hcomm : Matrix.diagonal δ * Matrix.diagonal d
      = Matrix.diagonal d * Matrix.diagonal δ := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp [mul_comm]
  calc
    P * Matrix.diagonal δ * Matrix.diagonal d * ((Matrix.diagonal δ)⁻¹ * P⁻¹)
        = P * (Matrix.diagonal δ * Matrix.diagonal d) * (Matrix.diagonal δ)⁻¹ * P⁻¹ := by
          noncomm_ring
    _ = P * Matrix.diagonal d * (Matrix.diagonal δ * (Matrix.diagonal δ)⁻¹) * P⁻¹ := by
          rw [hcomm]; noncomm_ring
    _ = P * Matrix.diagonal d * P⁻¹ := by
          rw [Matrix.mul_inv_of_invertible]; noncomm_ring

/-! ### The Hilbert line configuration -/

/-- Gaussian Gram of a finite configuration on an affine Hilbert line, in the scalar coordinate. -/
def hilbertLineGaussianGram {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (-t * (ξ i - ξ j) ^ 2)

/-- Gram of the coherent family `ε(√(2t) ξ_i e)`: `⟪ε u, ε v⟫ = exp ⟪u, v⟫`. -/
def hilbertLineCoherentGram {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (2 * t * (ξ i * ξ j))

/-- The gauge relating the Gaussian Gram to the coherent Gram. -/
def hilbertLineGaugeVector {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) (i : Fin n) : ℝ :=
  Real.exp (-t * ξ i ^ 2)

/-- Matrix of the compression of the annihilation operator in the direction of the line to the
span of the coherent family, in orthonormal coordinates. -/
def hilbertLineAnnihilationCompression {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  matrixSqrtSimilarity (hilbertLineCoherentGram ξ t)
    (Matrix.diagonal fun i => Real.sqrt (2 * t) * ξ i)

theorem hilbertLineGaussianGram_eq_finiteGaussianDistanceGram {n : ℕ}
    (ξ : Fin n → ℝ) (t : ℝ) :
    hilbertLineGaussianGram ξ t = finiteGaussianDistanceGram (fun i (_ : Fin 1) => ξ i) t := by
  ext i j
  simp [hilbertLineGaussianGram, finiteGaussianDistanceGram]

theorem hilbertLineGaussianGram_posDef {n : ℕ} {ξ : Fin n → ℝ} (hξ : Function.Injective ξ)
    {t : ℝ} (ht : 0 < t) : (hilbertLineGaussianGram ξ t).PosDef := by
  rw [hilbertLineGaussianGram_eq_finiteGaussianDistanceGram]
  refine finiteGaussianDistanceGram_posDef_of_injective_of_pos _ ?_ ht
  intro i j hij
  exact hξ (congrFun hij 0)

/-- Splitting the Gaussian bandwidth is Schur multiplication by the one-dimensional Gaussian
semigroup. -/
theorem hilbertLineGaussianGram_split {n : ℕ} (ξ : Fin n → ℝ) (t₀ s : ℝ) :
    hilbertLineGaussianGram ξ (t₀ + s)
      = rankOneSchurGaussianPath (hilbertLineGaussianGram ξ t₀) ξ s := by
  ext i j
  simp only [hilbertLineGaussianGram, rankOneSchurGaussianPath]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The exponential path of the split background is the coherent Gram in the gauge. -/
theorem rankOneSchurExponentialPath_hilbertLine {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) :
    rankOneSchurExponentialPath (hilbertLineGaussianGram ξ (t / 2)) ξ t
      = Matrix.diagonal (hilbertLineGaugeVector ξ (t / 2)) *
          hilbertLineCoherentGram ξ t *
          Matrix.diagonal (hilbertLineGaugeVector ξ (t / 2)) := by
  ext i j
  simp only [rankOneSchurExponentialPath, hilbertLineGaussianGram, hilbertLineCoherentGram,
    hilbertLineGaugeVector, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem hilbertLineCoherentGram_eq_gaussianCoherentGram {n : ℕ} (ξ : Fin n → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    hilbertLineCoherentGram ξ t
      = gaussianCoherentGram (fun i (_ : Fin 1) => Real.sqrt (2 * t) * ξ i) := by
  have hsq : Real.sqrt (2 * t) ^ 2 = 2 * t := Real.sq_sqrt (by linarith)
  ext i j
  simp only [hilbertLineCoherentGram, gaussianCoherentGram, coordinateDot,
    Finset.univ_unique, Finset.sum_singleton]
  congr 1
  rw [show Real.sqrt (2 * t) * ξ i * (Real.sqrt (2 * t) * ξ j)
      = Real.sqrt (2 * t) ^ 2 * (ξ i * ξ j) by ring, hsq]

theorem hilbertLineCoherentGram_posDef {n : ℕ} {ξ : Fin n → ℝ} (hξ : Function.Injective ξ)
    {t : ℝ} (ht : 0 < t) : (hilbertLineCoherentGram ξ t).PosDef := by
  rw [hilbertLineCoherentGram_eq_gaussianCoherentGram ξ ht.le]
  refine (gaussianCoherentGram_posDef_iff_injective _).2 ?_
  intro i j hij
  have hs : Real.sqrt (2 * t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  exact hξ (mul_left_cancel₀ hs (congrFun hij 0))

/-! ### The exact curvature law -/

theorem hilbertLineGaussian_logDet_secondDerivative_eq {n : ℕ} {ξ : Fin n → ℝ}
    (hξ : Function.Injective ξ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (fun s => Real.log (hilbertLineGaussianGram ξ s).det)) t
      = -2 * matrixHilbertSchmidtEnergy (matrixSelfCommutator
          (matrixSqrtSimilarity (hilbertLineCoherentGram ξ t) (Matrix.diagonal ξ))) := by
  set C : Matrix (Fin n) (Fin n) ℝ := hilbertLineGaussianGram ξ (t / 2) with hCdef
  have hC : C.PosDef := hilbertLineGaussianGram_posDef hξ (by linarith)
  set g : ℝ → ℝ := fun u => Real.log (rankOneSchurGaussianPath C ξ u).det with hgdef
  have hgram : ∀ s : ℝ, hilbertLineGaussianGram ξ s = rankOneSchurGaussianPath C ξ (s - t / 2) := by
    intro s
    have h := hilbertLineGaussianGram_split ξ (t / 2) (s - t / 2)
    rw [show t / 2 + (s - t / 2) = s by ring] at h
    exact h
  have hfun : (fun s => Real.log (hilbertLineGaussianGram ξ s).det) = fun s => g (s - t / 2) := by
    funext s
    rw [hgdef, hgram s]
  rw [hfun]
  have h1 : deriv (fun s : ℝ => g (s - t / 2)) = fun s => deriv g (s - t / 2) :=
    funext fun s => deriv_comp_sub_const g (t / 2) s
  rw [h1, deriv_comp_sub_const (deriv g) (t / 2) t,
    show t - t / 2 = t / 2 by ring]
  have hcorpus := rankOneSchurGaussian_logDet_secondDerivative_eq C ξ hC (t / 2) (by linarith)
  rw [hgdef, hcorpus, show 2 * (t / 2) = t by ring]
  congr 1
  have hgaugePosDef : (rankOneSchurExponentialPath C ξ t).PosDef :=
    rankOneSchurExponentialPath_posDef C ξ hC t ht.le
  have hsplit := rankOneSchurExponentialPath_hilbertLine ξ t
  rw [← hCdef] at hsplit
  rw [hsplit] at hgaugePosDef ⊢
  rw [rankOneLabelDiagonal]
  exact selfCommutator_energy_sqrtSimilarity_gauge (hilbertLineCoherentGram ξ t)
    (hilbertLineCoherentGram_posDef hξ ht) (hilbertLineGaugeVector ξ (t / 2)) ξ
    (fun i => (Real.exp_pos _).ne') hgaugePosDef

/-! ### Scaling algebra of the compressed annihilator -/

theorem matrixSelfCommutator_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (A : Matrix ι ι ℝ) :
    matrixSelfCommutator (c • A) = (c * c) • matrixSelfCommutator A := by
  unfold matrixSelfCommutator
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, ← smul_sub]

theorem matrixHilbertSchmidtEnergy_smul {ι : Type*} [Fintype ι]
    (c : ℝ) (A : Matrix ι ι ℝ) :
    matrixHilbertSchmidtEnergy (c • A) = c ^ 2 * matrixHilbertSchmidtEnergy A := by
  unfold matrixHilbertSchmidtEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.smul_apply, mul_pow]

theorem matrixSqrtSimilarity_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ℝ) (D : Matrix ι ι ℝ) :
    matrixSqrtSimilarity M (c • D) = c • matrixSqrtSimilarity M D := by
  unfold matrixSqrtSimilarity
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem hilbertLineAnnihilationCompression_eq_smul {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) :
    hilbertLineAnnihilationCompression ξ t
      = Real.sqrt (2 * t) • matrixSqrtSimilarity (hilbertLineCoherentGram ξ t)
          (Matrix.diagonal ξ) := by
  rw [hilbertLineAnnihilationCompression,
    show (Matrix.diagonal fun i => Real.sqrt (2 * t) * ξ i)
      = Real.sqrt (2 * t) • Matrix.diagonal ξ by
        rw [← Matrix.diagonal_smul]; rfl,
    matrixSqrtSimilarity_smul]

/-- **Gaussian Hilbert-line commutator curvature law.**  On a finite configuration whose affine
span is a line, the Gaussian log-determinant curvature is exactly the non-normality energy of the
compressed annihilation operator of the coherent family. -/
theorem hilbertLineGaussian_logDet_curvature_eq_selfCommutator {n : ℕ} {ξ : Fin n → ℝ}
    (hξ : Function.Injective ξ) {t : ℝ} (ht : 0 < t) :
    -t ^ 2 * deriv (deriv (fun s => Real.log (hilbertLineGaussianGram ξ s).det)) t
      = (1 / 2) * matrixHilbertSchmidtEnergy
          (matrixSelfCommutator (hilbertLineAnnihilationCompression ξ t)) := by
  have hsq : Real.sqrt (2 * t) ^ 2 = 2 * t := Real.sq_sqrt (by linarith)
  rw [hilbertLineGaussian_logDet_secondDerivative_eq hξ ht,
    hilbertLineAnnihilationCompression_eq_smul, matrixSelfCommutator_smul,
    matrixHilbertSchmidtEnergy_smul]
  have hpow : (Real.sqrt (2 * t) * Real.sqrt (2 * t)) ^ 2 = 4 * t ^ 2 := by
    rw [show Real.sqrt (2 * t) * Real.sqrt (2 * t) = Real.sqrt (2 * t) ^ 2 by ring, hsq]
    ring
  rw [hpow]
  ring

/-! ### Strictness -/

theorem hilbertLineGaussian_logDet_secondDerivative_lt_zero {n : ℕ} {ξ : Fin n → ℝ}
    (hξ : Function.Injective ξ) (hn : 1 < n) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (fun s => Real.log (hilbertLineGaussianGram ξ s).det)) t < 0 := by
  set C : Matrix (Fin n) (Fin n) ℝ := hilbertLineGaussianGram ξ (t / 2) with hCdef
  have hC : C.PosDef := hilbertLineGaussianGram_posDef hξ (by linarith)
  set g : ℝ → ℝ := fun u => Real.log (rankOneSchurGaussianPath C ξ u).det with hgdef
  have hgram : ∀ s : ℝ, hilbertLineGaussianGram ξ s = rankOneSchurGaussianPath C ξ (s - t / 2) := by
    intro s
    have h := hilbertLineGaussianGram_split ξ (t / 2) (s - t / 2)
    rw [show t / 2 + (s - t / 2) = s by ring] at h
    exact h
  have hfun : (fun s => Real.log (hilbertLineGaussianGram ξ s).det) = fun s => g (s - t / 2) := by
    funext s
    rw [hgdef, hgram s]
  rw [hfun]
  have h1 : deriv (fun s : ℝ => g (s - t / 2)) = fun s => deriv g (s - t / 2) :=
    funext fun s => deriv_comp_sub_const g (t / 2) s
  rw [h1, deriv_comp_sub_const (deriv g) (t / 2) t, show t - t / 2 = t / 2 by ring, hgdef]
  refine rankOneSchurGaussian_logDet_secondDerivative_lt_zero C ξ hC (t / 2) (by linarith)
    (fun i j => ?_) ?_
  · rw [hCdef, hilbertLineGaussianGram]
    exact (Real.exp_pos _).ne'
  · refine ⟨⟨0, by omega⟩, ⟨1, hn⟩, ?_⟩
    intro hval
    have : (⟨0, by omega⟩ : Fin n) = ⟨1, hn⟩ := hξ hval
    simpa using congrArg Fin.val this

/-- The compressed annihilator of a line configuration with at least two distinct points is
never normal. -/
theorem hilbertLineAnnihilationEnergy_pos {n : ℕ} {ξ : Fin n → ℝ}
    (hξ : Function.Injective ξ) (hn : 1 < n) {t : ℝ} (ht : 0 < t) :
    0 < matrixHilbertSchmidtEnergy
      (matrixSelfCommutator (hilbertLineAnnihilationCompression ξ t)) := by
  have hlaw := hilbertLineGaussian_logDet_curvature_eq_selfCommutator hξ ht
  have hneg := hilbertLineGaussian_logDet_secondDerivative_lt_zero hξ hn ht
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hkey : 0 < -t ^ 2 * deriv (deriv (fun s =>
      Real.log (hilbertLineGaussianGram ξ s).det)) t := by
    nlinarith [mul_pos ht2 (neg_pos.mpr hneg)]
  rw [hlaw] at hkey
  linarith

/-! ### Origin and direction independence -/

theorem hilbertLineGaussianGram_translate {n : ℕ} (ξ : Fin n → ℝ) (c t : ℝ) :
    hilbertLineGaussianGram (fun i => ξ i + c) t = hilbertLineGaussianGram ξ t := by
  ext i j
  simp only [hilbertLineGaussianGram]
  congr 2
  ring

theorem hilbertLineGaussianGram_neg {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) :
    hilbertLineGaussianGram (fun i => -ξ i) t = hilbertLineGaussianGram ξ t := by
  ext i j
  simp only [hilbertLineGaussianGram]
  congr 2
  ring

theorem hilbertLineCoherentGram_neg {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) :
    hilbertLineCoherentGram (fun i => -ξ i) t = hilbertLineCoherentGram ξ t := by
  ext i j
  simp only [hilbertLineCoherentGram]
  congr 1
  ring

/-- Reversing the unit vector of the line replaces the compressed annihilator by its negative,
so the curvature law is independent of that choice. -/
theorem hilbertLineAnnihilationCompression_neg {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) :
    hilbertLineAnnihilationCompression (fun i => -ξ i) t
      = -hilbertLineAnnihilationCompression ξ t := by
  rw [hilbertLineAnnihilationCompression, hilbertLineAnnihilationCompression,
    hilbertLineCoherentGram_neg]
  have hdiag : (Matrix.diagonal fun i => Real.sqrt (2 * t) * -ξ i)
      = -(Matrix.diagonal fun i => Real.sqrt (2 * t) * ξ i) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.diagonal_apply_ne _ h]
  rw [hdiag]
  unfold matrixSqrtSimilarity
  rw [Matrix.mul_neg, Matrix.neg_mul]

theorem matrixSelfCommutator_neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : matrixSelfCommutator (-A) = matrixSelfCommutator A := by
  unfold matrixSelfCommutator
  rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_neg]
  simp

theorem hilbertLineAnnihilationEnergy_reflection_invariant {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) :
    matrixHilbertSchmidtEnergy
        (matrixSelfCommutator (hilbertLineAnnihilationCompression (fun i => -ξ i) t))
      = matrixHilbertSchmidtEnergy
        (matrixSelfCommutator (hilbertLineAnnihilationCompression ξ t)) := by
  rw [hilbertLineAnnihilationCompression_neg, matrixSelfCommutator_neg]

theorem matrixSelfCommutator_add_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lam : ℝ) :
    matrixSelfCommutator (A + lam • (1 : Matrix ι ι ℝ)) = matrixSelfCommutator A := by
  simp only [matrixSelfCommutator, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, smul_add]
  abel

theorem matrixSqrtSimilarity_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M D E : Matrix ι ι ℝ) :
    matrixSqrtSimilarity M (D + E)
      = matrixSqrtSimilarity M D + matrixSqrtSimilarity M E := by
  unfold matrixSqrtSimilarity
  rw [Matrix.mul_add, Matrix.add_mul]

theorem matrixSqrtSimilarity_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef) (lam : ℝ) :
    matrixSqrtSimilarity M (lam • (1 : Matrix ι ι ℝ)) = lam • (1 : Matrix ι ι ℝ) := by
  have hPunit : IsUnit (CFC.sqrt M) :=
    (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  letI : Invertible (CFC.sqrt M) := hPunit.nonempty_invertible.some
  unfold matrixSqrtSimilarity
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_inv_of_invertible]

theorem hilbertLineCoherentGram_translate {n : ℕ} (ξ : Fin n → ℝ) (c t : ℝ) :
    hilbertLineCoherentGram (fun i => ξ i + c) t
      = Matrix.diagonal (fun i => Real.exp (t * c ^ 2 + 2 * t * c * ξ i)) *
          hilbertLineCoherentGram ξ t *
          Matrix.diagonal (fun i => Real.exp (t * c ^ 2 + 2 * t * c * ξ i)) := by
  ext i j
  simp only [hilbertLineCoherentGram, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Translating the configuration along its line adds a scalar to the compressed annihilator, so
the curvature law is independent of the chosen origin. -/
theorem hilbertLineAnnihilationEnergy_translation_invariant {n : ℕ} {ξ : Fin n → ℝ}
    (hξ : Function.Injective ξ) (c : ℝ) {t : ℝ} (ht : 0 < t) :
    matrixHilbertSchmidtEnergy
        (matrixSelfCommutator (hilbertLineAnnihilationCompression (fun i => ξ i + c) t))
      = matrixHilbertSchmidtEnergy
        (matrixSelfCommutator (hilbertLineAnnihilationCompression ξ t)) := by
  have hshift : Function.Injective fun i => ξ i + c := by
    intro i j hij
    exact hξ (by simpa using hij)
  have hG : (hilbertLineCoherentGram ξ t).PosDef := hilbertLineCoherentGram_posDef hξ ht
  have hGc : (hilbertLineCoherentGram (fun i => ξ i + c) t).PosDef :=
    hilbertLineCoherentGram_posDef hshift ht
  have hgauge := hGc
  rw [hilbertLineCoherentGram_translate ξ c t] at hgauge
  have hkey := selfCommutator_energy_sqrtSimilarity_gauge (hilbertLineCoherentGram ξ t) hG
    (fun i => Real.exp (t * c ^ 2 + 2 * t * c * ξ i))
    (fun i => Real.sqrt (2 * t) * (ξ i + c))
    (fun i => (Real.exp_pos _).ne') hgauge
  rw [hilbertLineAnnihilationCompression, hilbertLineCoherentGram_translate ξ c t, hkey]
  have hsplit : (Matrix.diagonal fun i => Real.sqrt (2 * t) * (ξ i + c))
      = (Matrix.diagonal fun i => Real.sqrt (2 * t) * ξ i)
        + (Real.sqrt (2 * t) * c) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.one_apply_eq]; ring
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  rw [hsplit, matrixSqrtSimilarity_add, matrixSqrtSimilarity_smul_one _ hG,
    matrixSelfCommutator_add_smul_one, hilbertLineAnnihilationCompression]

/-! ### The packaged law -/

/-- **Gaussian Hilbert-line commutator curvature law.**  For a finite configuration of at least
two distinct points on an affine line, the Gaussian log-determinant curvature is exactly minus
half the non-normality energy of the compressed annihilation operator, divided by `t²`; the
curvature is strictly negative and the compressed annihilator is never normal. -/
theorem hilbertLineCommutatorCurvatureLaw {n : ℕ} {ξ : Fin n → ℝ}
    (hξ : Function.Injective ξ) (hn : 1 < n) {t : ℝ} (ht : 0 < t) :
    -t ^ 2 * deriv (deriv (fun s => Real.log (hilbertLineGaussianGram ξ s).det)) t
        = (1 / 2) * matrixHilbertSchmidtEnergy
            (matrixSelfCommutator (hilbertLineAnnihilationCompression ξ t)) ∧
      deriv (deriv (fun s => Real.log (hilbertLineGaussianGram ξ s).det)) t < 0 ∧
      0 < matrixHilbertSchmidtEnergy
        (matrixSelfCommutator (hilbertLineAnnihilationCompression ξ t)) :=
  ⟨hilbertLineGaussian_logDet_curvature_eq_selfCommutator hξ ht,
    hilbertLineGaussian_logDet_secondDerivative_lt_zero hξ hn ht,
    hilbertLineAnnihilationEnergy_pos hξ hn ht⟩

end

end GaloisForLFunctions.HilbertMetric

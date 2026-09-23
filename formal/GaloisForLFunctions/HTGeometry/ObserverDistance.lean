import GaloisForLFunctions.HTGeometry.HermitianLog
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne

/-!
# The radial distance on the space of observer metrics

The tangent norm of the observer-metric geometry at the reference point is the Hilbert–Schmidt norm
of a Hermitian direction, which the spectral decomposition computes as the Euclidean norm of the
eigenvalues.  It is a genuine norm: the Hilbert–Schmidt theory of this corpus supplies its triangle
inequality and its definiteness.

Transported by the exponential, it measures how far an observer metric is from the reference one:
`dist P = ‖log P‖`.  Along a ray this distance grows at the constant rate `‖T‖`, so the rays of the
card are radial geodesics parametrized proportionally to arclength, and only the reference metric is
at distance zero.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {P T : E →ₗ[ℂ] E}

/-! ## The tangent norm of a direction -/

/-- **Every operator of a finite-dimensional space is Hilbert–Schmidt.** -/
theorem isHilbertSchmidt_toCLM (T : E →ₗ[ℂ] E) :
    ContinuousLinearMap.IsHilbertSchmidt (LinearMap.toContinuousLinearMap T) :=
  ContinuousLinearMap.isHilbertSchmidt_of_summable
    ((stdOrthonormalBasis ℂ E).toHilbertBasis) Summable.of_finite

/-- **The Hilbert–Schmidt norm is absolutely homogeneous.** -/
theorem hsNorm_smul_of_isHilbertSchmidt {S : E →L[ℂ] E}
    (hS : ContinuousLinearMap.IsHilbertSchmidt S) (c : ℂ) :
    ContinuousLinearMap.hsNorm (c • S) = ‖c‖ * ContinuousLinearMap.hsNorm S := by
  rw [ContinuousLinearMap.hsNorm, ContinuousLinearMap.hsNorm, hsNormSq_smul hS c,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

/-- **The tangent norm of an operator diagonal in an orthonormal basis** is the Euclidean norm of
its diagonal. -/
theorem hsNorm_toCLM_diagonal (b : OrthonormalBasis (Fin n) ℂ E) {f : E →ₗ[ℂ] E} {d : Fin n → ℂ}
    (hd : ∀ i, f (b i) = d i • b i) :
    ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap f)
      = Real.sqrt (∑ i, ‖d i‖ ^ (2 : ℕ)) := by
  classical
  rw [ContinuousLinearMap.hsNorm,
    ContinuousLinearMap.hsNormSq_eq (isHilbertSchmidt_toCLM f) b.toHilbertBasis, tsum_fintype]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hb : (b.toHilbertBasis : Fin n → E) i = b i := by
    rw [OrthonormalBasis.coe_toHilbertBasis]
  have happ : (LinearMap.toContinuousLinearMap f) ((b.toHilbertBasis : Fin n → E) i) = f (b i) := by
    rw [hb]
    rfl
  rw [happ, hd i, norm_smul, b.orthonormal.1 i, mul_one]

/-- **The tangent norm of a Hermitian direction is the Euclidean norm of its eigenvalues.** -/
theorem hsNorm_toCLM_eq_sqrt (hT : T.IsSymmetric) (hn : finrank ℂ E = n) :
    ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T)
      = Real.sqrt (∑ i, hT.eigenvalues hn i ^ (2 : ℕ)) := by
  rw [hsNorm_toCLM_diagonal (hT.eigenvectorBasis hn) (hT.apply_eigenvectorBasis hn)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.norm_ofReal, sq_abs]

theorem hsNorm_toCLM_nonneg (T : E →ₗ[ℂ] E) :
    0 ≤ ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T) :=
  ContinuousLinearMap.hsNorm_nonneg _

/-- **The tangent norm obeys the triangle inequality**, so the Hermitian directions at the reference
metric form a normed space. -/
theorem hsNorm_toCLM_add_le (S T : E →ₗ[ℂ] E) :
    ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap (S + T))
      ≤ ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap S)
        + ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T) := by
  have hmap : LinearMap.toContinuousLinearMap (S + T)
      = LinearMap.toContinuousLinearMap S + LinearMap.toContinuousLinearMap T := by
    ext v
    rfl
  rw [hmap]
  exact ContinuousLinearMap.hsNorm_add_le (isHilbertSchmidt_toCLM S) (isHilbertSchmidt_toCLM T)

/-- **The tangent norm vanishes only at the zero direction.** -/
theorem hsNorm_toCLM_eq_zero_iff (T : E →ₗ[ℂ] E) :
    ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T) = 0 ↔ T = 0 := by
  rw [ContinuousLinearMap.hsNorm_eq_zero_iff (isHilbertSchmidt_toCLM T)]
  constructor
  · intro h
    ext v
    have := congrArg (fun f : E →L[ℂ] E => f v) h
    simpa using this
  · rintro rfl
    ext v
    simp

/-! ## The radial distance -/

/-- **The logarithm of a point of a ray is the scaled direction.** -/
theorem logOp_metricRay_smul (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {t : ℝ} (ht : 0 < t) :
    logOp (isSymmetric_metricRay hT hn t) hn = (t : ℂ) • T := by
  refine eq_of_eigenSum_eq (isSymmetric_logOp _ hn) (isSymmetric_smul_real hT t) hn fun c => ?_
  rw [eigenSum_logOp (isSymmetric_metricRay hT hn t) hn
      (fun v hv => inner_metricRay_pos hT hn hv t) c,
    eigenSum_metricRay hT hn ht (Real.exp_pos c), Real.log_exp]
  have hsm := eigenSum_smul (T := T) ht (c / t)
  rw [mul_div_cancel₀ c (ne_of_gt ht)] at hsm
  rw [hsm]

/-- The distance of an observer metric from the reference metric. -/
noncomputable def distId (hP : P.IsSymmetric) (hn : finrank ℂ E = n) : ℝ :=
  ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap (logOp hP hn))

/-- **A ray moves away from the reference metric at constant rate.**  At parameter `t` the point of
the ray is at distance `t · ‖T‖` from the reference metric, so the rays of the card are radial
geodesics parametrized proportionally to arclength. -/
theorem distId_metricRay (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {t : ℝ} (ht : 0 < t) :
    distId (isSymmetric_metricRay hT hn t) hn
      = t * ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T) := by
  have hmap : LinearMap.toContinuousLinearMap ((t : ℂ) • T)
      = (t : ℂ) • LinearMap.toContinuousLinearMap T := by
    ext v
    rfl
  rw [distId, logOp_metricRay_smul hT hn ht, hmap,
    hsNorm_smul_of_isHilbertSchmidt (isHilbertSchmidt_toCLM T), Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht]

/-- **Only the reference metric is at distance zero.** -/
theorem distId_eq_zero_iff (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) :
    distId hP hn = 0 ↔ P = LinearMap.id := by
  rw [distId, hsNorm_toCLM_eq_zero_iff]
  constructor
  · intro hzero
    have hexp := metricRay_logOp hP hn hpos
    rw [hzero] at hexp
    have hid : ((metricRay (0 : E →ₗ[ℂ] E) 1 : E →ₗ[ℂ] E)) = LinearMap.id := by
      have hz : ((1 : ℝ) : ℂ) • (0 : E →ₗ[ℂ] E).toContinuousLinearMap = 0 := by
        simp
      show ((NormedSpace.exp (((1 : ℝ) : ℂ) • (0 : E →ₗ[ℂ] E).toContinuousLinearMap) :
        E →L[ℂ] E) : E →ₗ[ℂ] E) = LinearMap.id
      rw [hz, NormedSpace.exp_zero]
      rfl
    rw [← hexp, hid]
  · intro h
    subst h
    have hval : ∀ i, hP.eigenvalues hn i = 1 := by
      intro i
      have hne : (hP.eigenvectorBasis hn) i ≠ 0 := (hP.eigenvectorBasis hn).orthonormal.ne_zero i
      have hb := hP.apply_eigenvectorBasis hn i
      rw [LinearMap.id_apply] at hb
      have h1 : ((1 : ℝ) : ℂ) • (hP.eigenvectorBasis hn) i
          = ((hP.eigenvalues hn i : ℝ) : ℂ) • (hP.eigenvectorBasis hn) i := by
        rw [show (((1 : ℝ) : ℂ) • (hP.eigenvectorBasis hn) i)
          = (hP.eigenvectorBasis hn) i from by simp]
        exact hb
      have h2 := smul_left_injective ℂ hne h1
      simpa using h2.symm
    refine Basis.ext (hP.eigenvectorBasis hn).toBasis fun i => ?_
    rw [OrthonormalBasis.coe_toBasis, logOp_apply_basis hP hn i, hval i, Real.log_one]
    simp

end GaloisForLFunctions.HTGeometry

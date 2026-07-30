import GaloisForLFunctions.HTGeometry.DoubledParityClock
import GaloisForLFunctions.RHTower.MobiusIncidenceKMSCofinalResponse
import GaloisForLFunctions.RHTower.MobiusCriticalClockMoments
import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift

open Complex Filter
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RHTower

abbrev finiteMobiusHilbert (N : ℕ) :=
  EuclideanSpace ℂ (squarefreeMobiusCriticalFiniteIndex N)

private def finiteDiagonalLinearMap {N : ℕ}
    (a : squarefreeMobiusCriticalFiniteIndex N → ℂ) :
    finiteMobiusHilbert N →ₗ[ℂ] finiteMobiusHilbert N where
  toFun x := WithLp.toLp 2 (fun i => a i * x i)
  map_add' x y := by
    apply (WithLp.equiv 2 _).injective
    funext i
    simp
    ring
  map_smul' c x := by
    apply (WithLp.equiv 2 _).injective
    funext i
    simp
    ring

def finiteMobiusDiagonal {N : ℕ}
    (a : squarefreeMobiusCriticalFiniteIndex N → ℂ) :
    finiteMobiusHilbert N →L[ℂ] finiteMobiusHilbert N :=
  LinearMap.toContinuousLinearMap (finiteDiagonalLinearMap a)

@[simp] theorem finiteMobiusDiagonal_apply {N : ℕ}
    (a : squarefreeMobiusCriticalFiniteIndex N → ℂ)
    (x : finiteMobiusHilbert N) (i : squarefreeMobiusCriticalFiniteIndex N) :
    finiteMobiusDiagonal a x i = a i * x i := rfl

end RHTower

namespace RHTower

private abbrev finiteMobiusProbability (sigma : ℝ) (N : ℕ)
    (i : squarefreeMobiusCriticalFiniteIndex N) : ℝ :=
  finiteIncidenceProbability sigma
    (squarefreeMobiusCriticalFiniteIndexValue (N := N)) i

def finiteMobiusSourceWeight (sigma : ℝ) (N : ℕ)
    (i : squarefreeMobiusCriticalFiniteIndex N) : ℂ :=
  ((ArithmeticFunction.moebius (squarefreeMobiusCriticalFiniteIndexValue i) : ℤ) : ℂ) *
    Real.sqrt (finiteMobiusProbability sigma N i)

private theorem norm_finiteMobiusSourceWeight_sq (sigma : ℝ) (N : ℕ)
    (i : squarefreeMobiusCriticalFiniteIndex N) :
    ‖finiteMobiusSourceWeight sigma N i‖ ^ 2 =
      finiteMobiusProbability sigma N i := by
  rw [finiteMobiusSourceWeight, norm_mul, mul_pow]
  rw [show ArithmeticFunction.moebius (squarefreeMobiusCriticalFiniteIndexValue i) =
      (-1 : ℤ) ^ ArithmeticFunction.cardFactors
        (squarefreeMobiusCriticalFiniteIndexValue i) by
    simpa [squarefreeMobiusCriticalFiniteIndexValue] using
      ArithmeticFunction.moebius_apply_of_squarefree i.2]
  have hnorm : ‖((((-1 : ℤ) ^
      ArithmeticFunction.cardFactors (squarefreeMobiusCriticalFiniteIndexValue i) : ℤ) : ℂ))‖ = 1 := by
    rw [Complex.norm_intCast]
    simp
  rw [hnorm, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
  exact (finiteIncidenceProbability_pos
    (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N)) i).le

def finiteMobiusSource (sigma : ℝ) (N : ℕ) : finiteMobiusHilbert N :=
  WithLp.toLp 2 (finiteMobiusSourceWeight sigma N)

@[simp] theorem finiteMobiusSource_apply (sigma : ℝ) (N : ℕ)
    (i : squarefreeMobiusCriticalFiniteIndex N) :
    finiteMobiusSource sigma N i = finiteMobiusSourceWeight sigma N i := rfl

theorem norm_finiteMobiusSource_sq (sigma : ℝ) (N : ℕ) :
    ‖finiteMobiusSource sigma N‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [finiteMobiusSource_apply,
    norm_finiteMobiusSourceWeight_sq]
  exact sum_finiteIncidenceProbability
    (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N))

theorem norm_finiteMobiusSource (sigma : ℝ) (N : ℕ) :
    ‖finiteMobiusSource sigma N‖ = 1 := by
  nlinarith [norm_finiteMobiusSource_sq sigma N,
    norm_nonneg (finiteMobiusSource sigma N)]

end RHTower

namespace RHTower

private theorem finiteMobiusDiagonal_isSelfAdjoint {N : ℕ}
    (a : squarefreeMobiusCriticalFiniteIndex N → ℂ)
    (ha : ∀ i, (starRingEnd ℂ) (a i) = a i) :
    IsSelfAdjoint (finiteMobiusDiagonal a) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  change y i * (starRingEnd ℂ) (a i * x i) =
    (a i * y i) * (starRingEnd ℂ) (x i)
  rw [map_mul, ha]
  ring

private theorem finiteMobiusDiagonal_sq {N : ℕ}
    (a : squarefreeMobiusCriticalFiniteIndex N → ℂ)
    (ha : ∀ i, a i ^ 2 = 1) :
    finiteMobiusDiagonal a ^ 2 = 1 := by
  ext x i
  change a i * (a i * x i) = x i
  rw [← mul_assoc, ← pow_two, ha, one_mul]

private theorem finiteMobiusDiagonal_mul_comm {N : ℕ}
    (a b : squarefreeMobiusCriticalFiniteIndex N → ℂ) :
    finiteMobiusDiagonal a * finiteMobiusDiagonal b =
      finiteMobiusDiagonal b * finiteMobiusDiagonal a := by
  ext x i
  change a i * (b i * x i) = b i * (a i * x i)
  ring

def finiteMobiusParity (N : ℕ) :
    finiteMobiusHilbert N →L[ℂ] finiteMobiusHilbert N :=
  finiteMobiusDiagonal (fun i =>
    ((ArithmeticFunction.moebius (squarefreeMobiusCriticalFiniteIndexValue i) : ℤ) : ℂ))

private theorem finiteMobiusParity_coefficient_sq (N : ℕ)
    (i : squarefreeMobiusCriticalFiniteIndex N) :
    (((ArithmeticFunction.moebius
      (squarefreeMobiusCriticalFiniteIndexValue i) : ℤ) : ℂ)) ^ 2 = 1 := by
  rw [show ArithmeticFunction.moebius (squarefreeMobiusCriticalFiniteIndexValue i) =
      (-1 : ℤ) ^ ArithmeticFunction.cardFactors
        (squarefreeMobiusCriticalFiniteIndexValue i) by
    simpa [squarefreeMobiusCriticalFiniteIndexValue] using
      ArithmeticFunction.moebius_apply_of_squarefree i.2]
  push_cast
  rw [← pow_mul]
  norm_num

private theorem finiteMobiusParity_coefficient_norm (N : ℕ)
    (i : squarefreeMobiusCriticalFiniteIndex N) :
    ‖(((ArithmeticFunction.moebius
      (squarefreeMobiusCriticalFiniteIndexValue i) : ℤ) : ℂ))‖ = 1 := by
  rw [show ArithmeticFunction.moebius (squarefreeMobiusCriticalFiniteIndexValue i) =
      (-1 : ℤ) ^ ArithmeticFunction.cardFactors
        (squarefreeMobiusCriticalFiniteIndexValue i) by
    simpa [squarefreeMobiusCriticalFiniteIndexValue] using
      ArithmeticFunction.moebius_apply_of_squarefree i.2]
  rw [Complex.norm_intCast]
  simp

theorem finiteMobiusParity_sq (N : ℕ) : finiteMobiusParity N ^ 2 = 1 := by
  exact finiteMobiusDiagonal_sq _ (finiteMobiusParity_coefficient_sq N)

theorem finiteMobiusParity_isSelfAdjoint (N : ℕ) :
    IsSelfAdjoint (finiteMobiusParity N) := by
  apply finiteMobiusDiagonal_isSelfAdjoint
  intro i
  simp only [map_intCast]

theorem finiteMobiusParity_norm (N : ℕ) (x : finiteMobiusHilbert N) :
    ‖finiteMobiusParity N x‖ = ‖x‖ := by
  have hsquare : ‖finiteMobiusParity N x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    change ‖(((ArithmeticFunction.moebius
      (squarefreeMobiusCriticalFiniteIndexValue i) : ℤ) : ℂ)) * x i‖ ^ 2 =
        ‖x i‖ ^ 2
    rw [norm_mul, mul_pow, finiteMobiusParity_coefficient_norm, one_pow, one_mul]
  nlinarith [norm_nonneg (finiteMobiusParity N x), norm_nonneg x]

def finiteMobiusLogMean (sigma : ℝ) (N : ℕ) : ℝ :=
  ∑ i : squarefreeMobiusCriticalFiniteIndex N,
    finiteMobiusProbability sigma N i *
      Real.log (squarefreeMobiusCriticalFiniteIndexValue i)

def finiteMobiusLogVariance (sigma : ℝ) (N : ℕ) : ℝ :=
  ∑ i : squarefreeMobiusCriticalFiniteIndex N,
    finiteMobiusProbability sigma N i *
      (Real.log (squarefreeMobiusCriticalFiniteIndexValue i) -
        finiteMobiusLogMean sigma N) ^ 2

def finiteMobiusCriticalCenteredLogObservable (sigma : ℝ) (N : ℕ) :
    finiteMobiusHilbert N →L[ℂ] finiteMobiusHilbert N :=
  finiteMobiusDiagonal (fun i =>
    ((sigma - 1) *
      (Real.log (squarefreeMobiusCriticalFiniteIndexValue i) -
        finiteMobiusLogMean sigma N) : ℝ))

theorem finiteMobiusCriticalCenteredLogObservable_isSelfAdjoint
    (sigma : ℝ) (N : ℕ) :
    IsSelfAdjoint (finiteMobiusCriticalCenteredLogObservable sigma N) := by
  apply finiteMobiusDiagonal_isSelfAdjoint
  intro i
  exact Complex.conj_ofReal _

theorem finiteMobiusParity_comm_centeredLog (sigma : ℝ) (N : ℕ) :
    finiteMobiusParity N * finiteMobiusCriticalCenteredLogObservable sigma N =
      finiteMobiusCriticalCenteredLogObservable sigma N * finiteMobiusParity N := by
  exact finiteMobiusDiagonal_mul_comm _ _

theorem norm_finiteMobiusCriticalCenteredLogObservable_source_sq
    (sigma : ℝ) (N : ℕ) :
    ‖finiteMobiusCriticalCenteredLogObservable sigma N
      (finiteMobiusSource sigma N)‖ ^ 2 =
      (sigma - 1) ^ 2 * finiteMobiusLogVariance sigma N := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold finiteMobiusCriticalCenteredLogObservable finiteMobiusLogVariance
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change ‖(((sigma - 1) *
      (Real.log (squarefreeMobiusCriticalFiniteIndexValue i) -
        finiteMobiusLogMean sigma N) : ℝ) : ℂ) *
          finiteMobiusSourceWeight sigma N i‖ ^ 2 =
    (sigma - 1) ^ 2 *
      (finiteMobiusProbability sigma N i *
        (Real.log (squarefreeMobiusCriticalFiniteIndexValue i) -
          finiteMobiusLogMean sigma N) ^ 2)
  rw [norm_mul, mul_pow,
    norm_finiteMobiusSourceWeight_sq]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

end RHTower

namespace RHTower

abbrev finiteMobiusDoubledHilbert (N : ℕ) :=
  WithLp 2 (finiteMobiusHilbert N × finiteMobiusHilbert N)

def finiteMobiusDoubledClock (N : ℕ) :
    finiteMobiusDoubledHilbert N →L[ℂ] finiteMobiusDoubledHilbert N :=
  HTGeometry.doubledParityClock (finiteMobiusParity N)

def finiteMobiusDoubledObservable (sigma : ℝ) (N : ℕ) :
    finiteMobiusDoubledHilbert N →L[ℂ] finiteMobiusDoubledHilbert N :=
  HTGeometry.doubledOddObservable
    (finiteMobiusCriticalCenteredLogObservable sigma N)

def finiteMobiusDoubledSource (sigma : ℝ) (N : ℕ) :
    finiteMobiusDoubledHilbert N :=
  HTGeometry.doubledParitySource (finiteMobiusParity N)
    (finiteMobiusSource sigma N)

theorem finiteMobiusDoubledClock_sq (N : ℕ) :
    finiteMobiusDoubledClock N ^ 2 = 1 :=
  HTGeometry.doubledParityClock_sq _ (finiteMobiusParity_sq N)

theorem finiteMobiusDoubledClock_isSelfAdjoint (N : ℕ) :
    IsSelfAdjoint (finiteMobiusDoubledClock N) :=
  HTGeometry.doubledParityClock_isSelfAdjoint _
    (finiteMobiusParity_isSelfAdjoint N)

theorem finiteMobiusDoubledClock_adjoint_mul (N : ℕ) :
    (finiteMobiusDoubledClock N).adjoint * finiteMobiusDoubledClock N = 1 :=
  HTGeometry.doubledParityClock_adjoint_mul _
    (finiteMobiusParity_isSelfAdjoint N) (finiteMobiusParity_sq N)

theorem finiteMobiusDoubledObservable_isSelfAdjoint (sigma : ℝ) (N : ℕ) :
    IsSelfAdjoint (finiteMobiusDoubledObservable sigma N) :=
  HTGeometry.doubledOddObservable_isSelfAdjoint _
    (finiteMobiusCriticalCenteredLogObservable_isSelfAdjoint sigma N)

theorem norm_finiteMobiusDoubledSource (sigma : ℝ) (N : ℕ) :
    ‖finiteMobiusDoubledSource sigma N‖ = 1 :=
  HTGeometry.norm_doubledParitySource _ _
    (finiteMobiusParity_norm N (finiteMobiusSource sigma N))
    (norm_finiteMobiusSource sigma N)

theorem finiteMobiusDoubledClock_fixed_source (sigma : ℝ) (N : ℕ) :
    finiteMobiusDoubledClock N (finiteMobiusDoubledSource sigma N) =
      finiteMobiusDoubledSource sigma N :=
  HTGeometry.doubledParityClock_fixed_source _
    (finiteMobiusParity_sq N) (finiteMobiusSource sigma N)

theorem finiteMobiusDoubledClock_odd_observable_source (sigma : ℝ) (N : ℕ) :
    finiteMobiusDoubledClock N
        (finiteMobiusDoubledObservable sigma N
          (finiteMobiusDoubledSource sigma N)) =
      -finiteMobiusDoubledObservable sigma N
        (finiteMobiusDoubledSource sigma N) :=
  HTGeometry.doubledParityClock_odd_source _ _
    (finiteMobiusParity_sq N)
    (finiteMobiusParity_comm_centeredLog sigma N)
    (finiteMobiusSource sigma N)

theorem finiteMobiusDoubledClock_commutator_source (sigma : ℝ) (N : ℕ) :
    ((finiteMobiusDoubledObservable sigma N * finiteMobiusDoubledClock N -
      finiteMobiusDoubledClock N * finiteMobiusDoubledObservable sigma N) :
        finiteMobiusDoubledHilbert N →L[ℂ] finiteMobiusDoubledHilbert N)
        (finiteMobiusDoubledSource sigma N) =
      (2 : ℂ) • finiteMobiusDoubledObservable sigma N
        (finiteMobiusDoubledSource sigma N) :=
  HTGeometry.doubledParityClock_commutator_source _ _
    (finiteMobiusParity_sq N)
    (finiteMobiusParity_comm_centeredLog sigma N)
    (finiteMobiusSource sigma N)

theorem norm_finiteMobiusDoubledObservable_source_sq (sigma : ℝ) (N : ℕ) :
    ‖finiteMobiusDoubledObservable sigma N
      (finiteMobiusDoubledSource sigma N)‖ ^ 2 =
      (sigma - 1) ^ 2 * finiteMobiusLogVariance sigma N := by
  rw [finiteMobiusDoubledObservable, finiteMobiusDoubledSource,
    HTGeometry.norm_doubledOddObservable_source_sq _ _
      (finiteMobiusParity_norm N)
      (finiteMobiusParity_comm_centeredLog sigma N)]
  exact norm_finiteMobiusCriticalCenteredLogObservable_source_sq sigma N

/-- The complete doubled-clock star-Kadison energy is exactly the scaled finite Möbius logarithmic
variance.  This is the static arbitrary-operator observability value underlying the doubled QFI. -/
theorem re_inner_finiteMobiusDoubledObservableTwirlStarKadisonDefect_eq_variance
    (sigma : ℝ) (N : ℕ) :
    RCLike.re
        (inner ℂ (finiteMobiusDoubledSource sigma N)
          (HTGeometry.finiteCyclicObservableTwirlStarKadisonDefect
            (finiteMobiusDoubledClock N) (finiteMobiusDoubledObservable sigma N) 2
            (finiteMobiusDoubledSource sigma N))) =
      (sigma - 1) ^ 2 * finiteMobiusLogVariance sigma N := by
  rw [HTGeometry.re_inner_finiteInvolutiveObservableTwirlStarKadisonDefect_eq_quarter_commutatorNormSq_of_fixed
    (finiteMobiusDoubledClock N) (finiteMobiusDoubledObservable sigma N)
    (finiteMobiusDoubledClock_adjoint_mul N) (finiteMobiusDoubledClock_sq N)
    (finiteMobiusDoubledClock_fixed_source sigma N),
    finiteMobiusDoubledClock_commutator_source, norm_smul]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo, mul_pow, norm_finiteMobiusDoubledObservable_source_sq]
  ring

def finiteMobiusDoubledErasedQFI (sigma : ℝ) (N : ℕ) : ℝ :=
  HTGeometry.pureStateQuantumFisherValue (‖finiteMobiusDoubledSource sigma N‖ ^ 2)
    (‖inner ℂ (finiteMobiusDoubledSource sigma N)
      ((1 - HTGeometry.finiteCyclicGaugeAverage (finiteMobiusDoubledClock N) 2)
        (finiteMobiusDoubledObservable sigma N
          (finiteMobiusDoubledSource sigma N)))‖)
    (‖(1 - HTGeometry.finiteCyclicGaugeAverage (finiteMobiusDoubledClock N) 2)
      (finiteMobiusDoubledObservable sigma N
        (finiteMobiusDoubledSource sigma N))‖ ^ 2)

theorem finiteMobiusDoubledErasedQFI_eq_variance (sigma : ℝ) (N : ℕ) :
    finiteMobiusDoubledErasedQFI sigma N =
      4 * (sigma - 1) ^ 2 * finiteMobiusLogVariance sigma N := by
  unfold finiteMobiusDoubledErasedQFI
  rw [HTGeometry.finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_starObservabilityEnergy
    (finiteMobiusDoubledClock N) (finiteMobiusDoubledObservable sigma N) 2 two_ne_zero
    (finiteMobiusDoubledClock_adjoint_mul N) (finiteMobiusDoubledClock_sq N)
    (norm_finiteMobiusDoubledSource sigma N)
    (finiteMobiusDoubledClock_fixed_source sigma N),
    re_inner_finiteMobiusDoubledObservableTwirlStarKadisonDefect_eq_variance]
  ring

theorem norm_finiteMobiusDoubledClock_commutator_source_sq
    (sigma : ℝ) (N : ℕ) :
    ‖((finiteMobiusDoubledObservable sigma N * finiteMobiusDoubledClock N -
      finiteMobiusDoubledClock N * finiteMobiusDoubledObservable sigma N) :
        finiteMobiusDoubledHilbert N →L[ℂ] finiteMobiusDoubledHilbert N)
        (finiteMobiusDoubledSource sigma N)‖ ^ 2 =
      4 * (sigma - 1) ^ 2 * finiteMobiusLogVariance sigma N := by
  rw [finiteMobiusDoubledClock_commutator_source, norm_smul]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo, mul_pow, norm_finiteMobiusDoubledObservable_source_sq]
  ring

end RHTower

namespace RHTower

private theorem sum_finiteIndex_eq_sum_range_of_zero_not_squarefree
    {N : ℕ} (f : ℕ → ℝ)
    (hzero : ∀ n, ¬ Squarefree n → f n = 0) :
    (∑ i : squarefreeMobiusCriticalFiniteIndex N,
      f (squarefreeMobiusCriticalFiniteIndexValue i)) =
      ∑ n ∈ Finset.range (N + 2), f n := by
  unfold squarefreeMobiusCriticalFiniteIndexValue
    squarefreeMobiusCriticalFiniteIndex
  calc
    (∑ i : {i : Fin (N + 2) // Squarefree (i : ℕ)}, f (i.1 : ℕ)) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin (N + 2) => Squarefree (i : ℕ)),
          f (i : ℕ) := by
      exact (Finset.sum_subtype
        (p := fun i : Fin (N + 2) => Squarefree (i : ℕ))
        (M := ℝ)
        (Finset.univ.filter (fun i : Fin (N + 2) => Squarefree (i : ℕ)))
        (by
          intro i
          constructor
          · exact fun hi => (Finset.mem_filter.mp hi).2
          · exact fun hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
        (fun i : Fin (N + 2) => f (i : ℕ))).symm
    _ = ∑ i : Fin (N + 2), f (i : ℕ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with hsq
      · rfl
      · exact (hzero (i : ℕ) hsq).symm
    _ = ∑ n ∈ Finset.range (N + 2), f n := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n hn
      simp [Finset.mem_range.mp hn]

private theorem finiteMobiusProbability_eq_probability_div_partial
    {sigma : ℝ} (hsigma : 1 < sigma) (N : ℕ)
    (i : squarefreeMobiusCriticalFiniteIndex N) :
    finiteMobiusProbability sigma N i =
      squarefreeMobiusProbability sigma
          (squarefreeMobiusCriticalFiniteIndexValue i) /
        (∑ n ∈ Finset.range (N + 2), squarefreeMobiusProbability sigma n) := by
  change finiteIncidenceProbability sigma
      (squarefreeMobiusCriticalFiniteIndexValue (N := N)) i = _
  rw [finiteIncidenceProbability_squarefreeMobiusCriticalFiniteIndex,
    sum_range_squarefreeMobiusProbability_eq_partition_div_total]
  unfold squarefreeMobiusProbability
  have htotal : squarefreeMobiusTotal sigma ≠ 0 :=
    ne_of_gt (squarefreeMobiusTotal_pos hsigma)
  have hpartition : finiteIncidencePartition sigma
      (squarefreeMobiusCriticalFiniteIndexValue (N := N)) ≠ 0 :=
    ne_of_gt (finiteIncidencePartition_pos
      (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N)))
  field_simp [htotal, hpartition]

def finiteMobiusLogRawMoment (k : ℕ) (sigma : ℝ) (N : ℕ) : ℝ :=
  ∑ i : squarefreeMobiusCriticalFiniteIndex N,
    finiteMobiusProbability sigma N i *
      Real.log (squarefreeMobiusCriticalFiniteIndexValue i) ^ k

private theorem finiteMobiusLogRawMoment_eq_partial_ratio
    {sigma : ℝ} (hsigma : 1 < sigma) (k N : ℕ) :
    finiteMobiusLogRawMoment k sigma N =
      (∑ n ∈ Finset.range (N + 2),
        squarefreeMobiusProbability sigma n * Real.log n ^ k) /
      (∑ n ∈ Finset.range (N + 2), squarefreeMobiusProbability sigma n) := by
  unfold finiteMobiusLogRawMoment
  simp_rw [finiteMobiusProbability_eq_probability_div_partial hsigma]
  rw [show (fun x : squarefreeMobiusCriticalFiniteIndex N =>
      (squarefreeMobiusProbability sigma
          (squarefreeMobiusCriticalFiniteIndexValue x) /
        ∑ n ∈ Finset.range (N + 2), squarefreeMobiusProbability sigma n) *
          Real.log (squarefreeMobiusCriticalFiniteIndexValue x) ^ k) =
      fun x => (squarefreeMobiusProbability sigma
          (squarefreeMobiusCriticalFiniteIndexValue x) *
            Real.log (squarefreeMobiusCriticalFiniteIndexValue x) ^ k) /
        (∑ n ∈ Finset.range (N + 2), squarefreeMobiusProbability sigma n) by
    funext x
    ring]
  rw [← Finset.sum_div]
  congr 1
  exact sum_finiteIndex_eq_sum_range_of_zero_not_squarefree
    (N := N) (fun n => squarefreeMobiusProbability sigma n * Real.log n ^ k)
    (fun n hn => by
      simp [squarefreeMobiusProbability, squarefreeMobiusMass, hn])

private theorem tendsto_partial_squarefreeMobiusProbability
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range (N + 2), squarefreeMobiusProbability sigma n)
      atTop (nhds 1) := by
  have h := (summable_squarefreeMobiusProbability hsigma).hasSum.tendsto_sum_nat
  rw [tsum_squarefreeMobiusProbability hsigma] at h
  exact h.comp (Filter.tendsto_add_atTop_nat 2)

private theorem tendsto_partial_squarefreeMobiusLogMoment
    {sigma : ℝ} (hsigma : 1 < sigma) (k : ℕ) :
    Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range (N + 2),
        squarefreeMobiusProbability sigma n * Real.log n ^ k)
      atTop (nhds (squarefreeMobiusLogMoment k sigma)) := by
  exact (summable_squarefreeMobiusLogMoment k hsigma).hasSum.tendsto_sum_nat.comp
    (Filter.tendsto_add_atTop_nat 2)

theorem tendsto_finiteMobiusLogRawMoment
    {sigma : ℝ} (hsigma : 1 < sigma) (k : ℕ) :
    Tendsto (fun N : ℕ => finiteMobiusLogRawMoment k sigma N)
      atTop (nhds (squarefreeMobiusLogMoment k sigma)) := by
  have hratio := (tendsto_partial_squarefreeMobiusLogMoment hsigma k).div
    (tendsto_partial_squarefreeMobiusProbability hsigma) (by norm_num)
  have heq : (∀ N : ℕ,
      (∑ n ∈ Finset.range (N + 2),
          squarefreeMobiusProbability sigma n * Real.log n ^ k) /
        (∑ n ∈ Finset.range (N + 2), squarefreeMobiusProbability sigma n) =
          finiteMobiusLogRawMoment k sigma N) := by
    intro N
    exact (finiteMobiusLogRawMoment_eq_partial_ratio hsigma k N).symm
  simpa using hratio.congr' (Filter.Eventually.of_forall heq)

theorem finiteMobiusLogMean_eq_rawMoment_one (sigma : ℝ) (N : ℕ) :
    finiteMobiusLogMean sigma N = finiteMobiusLogRawMoment 1 sigma N := by
  unfold finiteMobiusLogMean finiteMobiusLogRawMoment
  simp only [pow_one]

theorem finiteMobiusLogVariance_eq_rawMoments (sigma : ℝ) (N : ℕ) :
    finiteMobiusLogVariance sigma N =
      finiteMobiusLogRawMoment 2 sigma N -
        finiteMobiusLogRawMoment 1 sigma N ^ 2 := by
  unfold finiteMobiusLogVariance
  rw [finiteMobiusLogMean_eq_rawMoment_one]
  unfold finiteMobiusLogRawMoment
  rw [show (fun i : squarefreeMobiusCriticalFiniteIndex N =>
      finiteMobiusProbability sigma N i *
        (Real.log (squarefreeMobiusCriticalFiniteIndexValue i) -
          ∑ j : squarefreeMobiusCriticalFiniteIndex N,
            finiteMobiusProbability sigma N j *
              Real.log (squarefreeMobiusCriticalFiniteIndexValue j) ^ 1) ^ 2) =
      fun i => finiteMobiusProbability sigma N i *
          Real.log (squarefreeMobiusCriticalFiniteIndexValue i) ^ 2 +
        (-2 * (∑ j : squarefreeMobiusCriticalFiniteIndex N,
          finiteMobiusProbability sigma N j *
            Real.log (squarefreeMobiusCriticalFiniteIndexValue j) ^ 1)) *
          (finiteMobiusProbability sigma N i *
            Real.log (squarefreeMobiusCriticalFiniteIndexValue i)) +
        (∑ j : squarefreeMobiusCriticalFiniteIndex N,
          finiteMobiusProbability sigma N j *
            Real.log (squarefreeMobiusCriticalFiniteIndexValue j) ^ 1) ^ 2 *
          finiteMobiusProbability sigma N i by
    funext i
    simp only [pow_one]
    ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_finiteIncidenceProbability
    (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N))]
  simp only [pow_one]
  ring

theorem tendsto_finiteMobiusLogVariance
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Tendsto (fun N : ℕ => finiteMobiusLogVariance sigma N)
      atTop (nhds (squarefreeMobiusLogMoment 2 sigma -
        squarefreeMobiusLogMoment 1 sigma ^ 2)) := by
  apply ((tendsto_finiteMobiusLogRawMoment hsigma 2).sub
    ((tendsto_finiteMobiusLogRawMoment hsigma 1).pow 2)).congr'
  filter_upwards with N
  exact (finiteMobiusLogVariance_eq_rawMoments sigma N).symm

theorem tendsto_finiteMobiusDoubledErasedQFI
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Tendsto (fun N : ℕ => finiteMobiusDoubledErasedQFI sigma N)
      atTop (nhds (squarefreeMobiusCriticalProjectiveFisherEnergy sigma)) := by
  have hconst : Tendsto (fun _ : ℕ => 4 * (sigma - 1) ^ 2)
      atTop (nhds (4 * (sigma - 1) ^ 2)) := tendsto_const_nhds
  have h := hconst.mul (tendsto_finiteMobiusLogVariance hsigma)
  have h' : Tendsto (fun N : ℕ =>
      4 * (sigma - 1) ^ 2 * finiteMobiusLogVariance sigma N)
      atTop (nhds (squarefreeMobiusCriticalProjectiveFisherEnergy sigma)) := by
    have henergy : squarefreeMobiusCriticalProjectiveFisherEnergy sigma =
        4 * (sigma - 1) ^ 2 *
          (squarefreeMobiusLogMoment 2 sigma -
            squarefreeMobiusLogMoment 1 sigma ^ 2) := by
      unfold squarefreeMobiusCriticalProjectiveFisherEnergy
        squarefreeMobiusCriticalClockVariance
      ring
    rw [henergy]
    exact h
  apply h'.congr'
  filter_upwards with N
  exact (finiteMobiusDoubledErasedQFI_eq_variance sigma N).symm

end RHTower
namespace RHTower

private theorem hasDerivAt_finiteIncidenceMass
    {sigma : ℝ} {n : ℕ} (hn : 0 < n) :
    HasDerivAt (fun t : ℝ => (n : ℝ) ^ (-t))
      (-((n : ℝ) ^ (-sigma) * Real.log n)) sigma := by
  have hbase : HasDerivAt (fun _ : ℝ => (n : ℝ)) 0 sigma := hasDerivAt_const _ _
  have hexp : HasDerivAt (fun t : ℝ => -t) (-1) sigma :=
    (hasDerivAt_id sigma).neg
  have h := hbase.rpow hexp (by exact_mod_cast hn)
  convert h using 1
  ring

private theorem hasDerivAt_finiteIncidencePartition
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma : ℝ} {d : α → ℕ} (hd : ∀ i, 0 < d i) :
    HasDerivAt (fun t : ℝ => finiteIncidencePartition t d)
      (-∑ i, (d i : ℝ) ^ (-sigma) * Real.log (d i)) sigma := by
  unfold finiteIncidencePartition
  have hsum0 := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => hasDerivAt_finiteIncidenceMass (sigma := sigma) (hd i))
  have hsum : HasDerivAt (fun t : ℝ => ∑ i, (d i : ℝ) ^ (-t))
      (∑ i, -((d i : ℝ) ^ (-sigma) * Real.log (d i))) sigma := by
    convert hsum0 using 1
    all_goals try rfl
    funext t
    simp
  convert hsum using 1
  rw [Finset.sum_neg_distrib]

end RHTower

namespace RHTower

private def finiteIncidenceLogMean
    {α : Type*} [Fintype α] (sigma : ℝ) (d : α → ℕ) : ℝ :=
  ∑ i, finiteIncidenceProbability sigma d i * Real.log (d i)

private theorem hasDerivAt_finiteIncidenceProbability
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma : ℝ} {d : α → ℕ} (hd : ∀ i, 0 < d i) (i : α) :
    HasDerivAt (fun t : ℝ => finiteIncidenceProbability t d i)
      (finiteIncidenceProbability sigma d i *
        (finiteIncidenceLogMean sigma d - Real.log (d i))) sigma := by
  have hmass := hasDerivAt_finiteIncidenceMass (sigma := sigma) (hd i)
  have hpartition := hasDerivAt_finiteIncidencePartition (sigma := sigma) hd
  have hpartitionNe : finiteIncidencePartition sigma d ≠ 0 :=
    ne_of_gt (finiteIncidencePartition_pos hd)
  have hquot := hmass.div hpartition hpartitionNe
  unfold finiteIncidenceProbability
  convert hquot using 1
  all_goals try rfl
  unfold finiteIncidenceLogMean finiteIncidenceProbability
  rw [show (fun j : α => (d j : ℝ) ^ (-sigma) /
      finiteIncidencePartition sigma d * Real.log (d j)) =
      fun j => ((d j : ℝ) ^ (-sigma) * Real.log (d j)) /
        finiteIncidencePartition sigma d by
    funext j
    ring]
  rw [← Finset.sum_div Finset.univ]
  field_simp [hpartitionNe]
  ring

private theorem hasDerivAt_sqrt_finiteIncidenceProbability
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma : ℝ} {d : α → ℕ} (hd : ∀ i, 0 < d i) (i : α) :
    HasDerivAt (fun t : ℝ => Real.sqrt (finiteIncidenceProbability t d i))
      ((1 / 2) * (finiteIncidenceLogMean sigma d - Real.log (d i)) *
        Real.sqrt (finiteIncidenceProbability sigma d i)) sigma := by
  have hp := hasDerivAt_finiteIncidenceProbability (sigma := sigma) hd i
  have hpne : finiteIncidenceProbability sigma d i ≠ 0 :=
    ne_of_gt (finiteIncidenceProbability_pos hd i)
  have hsqrt := hp.sqrt hpne
  convert hsqrt using 1
  have hsqrtPos : Real.sqrt (finiteIncidenceProbability sigma d i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (finiteIncidenceProbability_pos hd i))
  field_simp [hsqrtPos]
  rw [Real.sq_sqrt (finiteIncidenceProbability_pos hd i).le]

end RHTower

namespace RHTower

private theorem hasDerivAt_finiteMobiusSourceWeight
    {sigma : ℝ} (N : ℕ) (i : squarefreeMobiusCriticalFiniteIndex N) :
    HasDerivAt (fun t : ℝ => finiteMobiusSourceWeight t N i)
      ((((1 / 2 : ℝ) *
        (finiteMobiusLogMean sigma N -
          Real.log (squarefreeMobiusCriticalFiniteIndexValue i)) : ℝ) : ℂ) *
        finiteMobiusSourceWeight sigma N i) sigma := by
  let d := squarefreeMobiusCriticalFiniteIndexValue (N := N)
  have hsqrt := hasDerivAt_sqrt_finiteIncidenceProbability
    (sigma := sigma) (d := d)
    (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N)) i
  have hcomplex := hsqrt.ofReal_comp
  have hmul := hcomplex.const_mul
    (((ArithmeticFunction.moebius
      (squarefreeMobiusCriticalFiniteIndexValue i) : ℤ) : ℂ))
  convert hmul using 1
  all_goals try rfl
  unfold finiteMobiusSourceWeight finiteMobiusLogMean
    finiteIncidenceLogMean
  dsimp [d]
  push_cast
  ring

def finiteMobiusFisherTangentWeight (sigma : ℝ) (N : ℕ)
    (i : squarefreeMobiusCriticalFiniteIndex N) : ℂ :=
  ((-2 * (sigma - 1) *
    (Real.log (squarefreeMobiusCriticalFiniteIndexValue i) -
      finiteMobiusLogMean sigma N) : ℝ) : ℂ) *
    finiteMobiusSourceWeight sigma N i

theorem finiteMobiusFisherTangentWeight_eq_four_mul_deriv_source
    {sigma : ℝ} (N : ℕ) (i : squarefreeMobiusCriticalFiniteIndex N) :
    finiteMobiusFisherTangentWeight sigma N i =
      ((4 * (sigma - 1) : ℝ) : ℂ) *
        deriv (fun t : ℝ => finiteMobiusSourceWeight t N i) sigma := by
  rw [(hasDerivAt_finiteMobiusSourceWeight N i).deriv]
  unfold finiteMobiusFisherTangentWeight
  push_cast
  ring

end RHTower

namespace RHTower

/-! ### The finite Fisher tangent as a Hilbert vector -/

/-- The finite completed critical Fisher tangent as a Hilbert vector. -/
def finiteMobiusFisherTangent (sigma : ℝ) (N : ℕ) : finiteMobiusHilbert N :=
  WithLp.toLp 2 (finiteMobiusFisherTangentWeight sigma N)

@[simp] theorem finiteMobiusFisherTangent_apply (sigma : ℝ) (N : ℕ)
    (i : squarefreeMobiusCriticalFiniteIndex N) :
    finiteMobiusFisherTangent sigma N i = finiteMobiusFisherTangentWeight sigma N i := rfl

/-- The finite Fisher tangent is exactly `-2` times the centered logarithmic clock observable
applied to the normalized source state. -/
theorem finiteMobiusFisherTangent_eq_smul (sigma : ℝ) (N : ℕ) :
    finiteMobiusFisherTangent sigma N
      = (-2 : ℂ) • finiteMobiusCriticalCenteredLogObservable sigma N
          (finiteMobiusSource sigma N) := by
  apply (WithLp.equiv 2 _).injective
  funext i
  change finiteMobiusFisherTangentWeight sigma N i
    = (-2 : ℂ) * (finiteMobiusCriticalCenteredLogObservable sigma N
        (finiteMobiusSource sigma N) i)
  rw [finiteMobiusFisherTangentWeight, finiteMobiusCriticalCenteredLogObservable,
    finiteMobiusDiagonal_apply, finiteMobiusSource_apply]
  push_cast
  ring

/-- **The finite Fisher tangent has the scaled finite logarithmic variance as its energy.** -/
theorem norm_finiteMobiusFisherTangent_sq (sigma : ℝ) (N : ℕ) :
    ‖finiteMobiusFisherTangent sigma N‖ ^ 2
      = 4 * (sigma - 1) ^ 2 * finiteMobiusLogVariance sigma N := by
  have hnorm : ‖(-2 : ℂ)‖ = 2 := by norm_num
  rw [finiteMobiusFisherTangent_eq_smul, norm_smul, mul_pow, hnorm,
    norm_finiteMobiusCriticalCenteredLogObservable_source_sq]
  ring

/-- **The finite-clock Fisher identity.**  The erased doubled-clock quantum Fisher value of the
Möbius parity source is exactly the squared norm of its finite Fisher tangent. -/
theorem finiteMobiusDoubledErasedQFI_eq_norm_finiteMobiusFisherTangent_sq (sigma : ℝ) (N : ℕ) :
    finiteMobiusDoubledErasedQFI sigma N = ‖finiteMobiusFisherTangent sigma N‖ ^ 2 := by
  rw [finiteMobiusDoubledErasedQFI_eq_variance, norm_finiteMobiusFisherTangent_sq]

/-- The doubled clock commutator energy is the same finite Fisher tangent energy. -/
theorem norm_finiteMobiusDoubledClock_commutator_source_sq_eq_norm_fisherTangent_sq
    (sigma : ℝ) (N : ℕ) :
    ‖((finiteMobiusDoubledObservable sigma N * finiteMobiusDoubledClock N -
        finiteMobiusDoubledClock N * finiteMobiusDoubledObservable sigma N) :
        finiteMobiusDoubledHilbert N →L[ℂ] finiteMobiusDoubledHilbert N)
        (finiteMobiusDoubledSource sigma N)‖ ^ 2
      = ‖finiteMobiusFisherTangent sigma N‖ ^ 2 := by
  rw [norm_finiteMobiusDoubledClock_commutator_source_sq, norm_finiteMobiusFisherTangent_sq]

/-- **Cofinal limit of the finite-clock Fisher identity.**  Finite squarefree cutoffs exhaust the
Hilbert tangent energy of the infinite source. -/
theorem tendsto_norm_finiteMobiusFisherTangent_sq {sigma : ℝ} (hsigma : 1 < sigma) :
    Tendsto (fun N : ℕ => ‖finiteMobiusFisherTangent sigma N‖ ^ 2) atTop
      (nhds (‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2)) := by
  rw [norm_infiniteMobiusCriticalFisherTangentLp_sq hsigma]
  refine (tendsto_finiteMobiusDoubledErasedQFI hsigma).congr fun N => ?_
  rw [finiteMobiusDoubledErasedQFI_eq_norm_finiteMobiusFisherTangent_sq]

end RHTower

/-
# The coupled all-prime Sonin column and Gram operators

The block-diagonal all-prime operator separates prime powers and therefore deletes all mixed
prime words.  The canonical coupled assembly instead stacks every weighted residual over the
same Sonin source space.  Its Gram operator is positive and retains cross-prime overlaps.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRectangular
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.QuantumChannelEnergyAugmentation
import GaloisForLFunctions.HTGeometry.TwoProjectionQuantumWalk
import GaloisForLFunctions.RHTower.SoninAllPrimeResidualKernel
import GaloisForLFunctions.RHTower.SoninPrimePowerRegularization

noncomputable section

open scoped BigOperators

namespace RHTower

local instance soninCoupledPrimeDecidableEq : DecidableEq SoninAllPrimeIndex :=
  Classical.decEq _

/-- Rectangular matrix of the canonical column operator.  Rows are indexed by a prime power and
an output Sonin coordinate; columns use the single common Sonin input coordinate. -/
def soninAllPrimeColumnKernel (a : ℝ) :
    SoninAllPrimeIndex × SoninHilbertIndex → ℂ := fun z =>
  inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 z.1.2)
    (centralSoninWeightedPrimePowerResidual a z.1.1
      (ContinuousLinearMap.hsBasis ℂ SoninL2 z.2))

private def soninAllPrimeColumnEquiv :
    (Nat.Primes × ℕ) × (SoninHilbertIndex × SoninHilbertIndex) ≃
      SoninAllPrimeIndex × SoninHilbertIndex where
  toFun pji := ((pji.1, pji.2.2), pji.2.1)
  invFun z := (z.1.1, (z.2, z.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The existing all-prime Hilbert--Schmidt energy sum proves convergence of the coupled column
without any additional hypothesis. -/
theorem soninAllPrimeColumnKernel_isHSRect (a : ℝ) (ha : 0 < a) :
    HilbertSchmidt.IsHSRect (soninAllPrimeColumnKernel a) := by
  apply (soninAllPrimeColumnEquiv.summable_iff).mp
  refine (summable_all_prime_residual_matrix_entries a ha).congr (fun pji => ?_)
  rfl

/-- Coordinate version of the all-prime column operator. -/
def soninAllPrimeColumnCoordinateOperator (a : ℝ) (ha : 0 < a) :
    lp (fun _ : SoninHilbertIndex => ℂ) 2 →L[ℂ] SoninAllPrimeL2 :=
  HilbertSchmidt.toOperatorRect (soninAllPrimeColumnKernel_isHSRect a ha)

/-- The canonical column operator on the actual common Sonin space. -/
def soninAllPrimeColumnOperator (a : ℝ) (ha : 0 < a) :
    SoninL2 →L[ℂ] SoninAllPrimeL2 :=
  soninAllPrimeColumnCoordinateOperator a ha ∘L
    (ContinuousLinearMap.hsBasis ℂ SoninL2).repr.toContinuousLinearEquiv.toContinuousLinearMap

/-- The coupled column is genuinely Hilbert--Schmidt. -/
theorem soninAllPrimeColumnOperator_isHilbertSchmidt (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt (soninAllPrimeColumnOperator a ha) := by
  exact (HilbertSchmidt.isHilbertSchmidt_toOperatorRect
    (soninAllPrimeColumnKernel_isHSRect a ha)).comp_right
      (ContinuousLinearMap.hsBasis ℂ SoninL2).repr.toContinuousLinearEquiv.toContinuousLinearMap

/-- Evaluation of the column at a prime-power/output-basis row. -/
theorem soninAllPrimeColumnOperator_apply (a : ℝ) (ha : 0 < a) (x : SoninL2)
    (pk : Nat.Primes × ℕ) (i : SoninHilbertIndex) :
    soninAllPrimeColumnOperator a ha x (pk, i) =
      inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 i)
        (centralSoninWeightedPrimePowerResidual a pk x) := by
  let b := ContinuousLinearMap.hsBasis ℂ SoninL2
  let A := centralSoninWeightedPrimePowerResidual a pk
  rw [soninAllPrimeColumnOperator, ContinuousLinearMap.comp_apply,
    soninAllPrimeColumnCoordinateOperator, HilbertSchmidt.toOperatorRect_apply]
  change (∑' j, inner ℂ (b i) (A (b j)) * b.repr x j) = inner ℂ (b i) (A x)
  simp_rw [b.repr_apply_apply]
  calc
    (∑' j, inner ℂ (b i) (A (b j)) * inner ℂ (b j) x) =
        ∑' j, inner ℂ (ContinuousLinearMap.adjoint A (b i)) (b j) *
          inner ℂ (b j) x := by
      apply tsum_congr
      intro j
      rw [ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ (ContinuousLinearMap.adjoint A (b i)) x :=
      b.tsum_inner_mul_inner _ _
    _ = inner ℂ (b i) (A x) := ContinuousLinearMap.adjoint_inner_left A x (b i)

/-! ### Aperture-independent quantum-instrument radius -/

/-- The square-summed logarithmic Euler weight.  It is finite before any aperture is chosen. -/
def soninAllPrimeColumnWeightSqMass : ℝ :=
  ∑' pk : Nat.Primes × ℕ, ‖soninLogPrimePowerCoefficient pk‖ ^ 2

theorem soninAllPrimeColumnWeightSqMass_nonneg :
    0 ≤ soninAllPrimeColumnWeightSqMass := by
  exact tsum_nonneg fun _ => sq_nonneg _

/-- The fixed Euler weight mass is strictly positive: one nonzero prime-power coefficient already
forces strict positivity of the square-summed instrument mass. -/
theorem soninAllPrimeColumnWeightSqMass_pos :
    0 < soninAllPrimeColumnWeightSqMass := by
  let pk : Nat.Primes × ℕ := (⟨2, Nat.prime_two⟩, 0)
  apply summable_norm_soninLogPrimePowerCoefficient_sq.tsum_pos
  · exact fun _ => sq_nonneg _
  · exact sq_pos_of_pos
      (norm_pos_iff.mpr (soninLogPrimePowerCoefficient_ne_zero pk))

/-- The common-source effect radius obtained by combining the local residual ceiling `4` with
orthogonal prime-power outcome stacking. -/
def soninAllPrimeColumnEffectRadius : ℝ :=
  16 * soninAllPrimeColumnWeightSqMass

theorem soninAllPrimeColumnEffectRadius_nonneg :
    0 ≤ soninAllPrimeColumnEffectRadius := by
  exact mul_nonneg (by norm_num) soninAllPrimeColumnWeightSqMass_nonneg

/-- The source-effect radius is a genuine positive radius, so it can be used directly in the
scaled Hausdorff-to-RH implication without comparison to a separately calibrated endpoint. -/
theorem soninAllPrimeColumnEffectRadius_pos :
    0 < soninAllPrimeColumnEffectRadius := by
  exact mul_pos (by norm_num) soninAllPrimeColumnWeightSqMass_pos

/-- Every unweighted prime-power outcome channel has the same operator-norm ceiling, independent
of aperture and prime-power scale. -/
theorem norm_centralSoninPrimePowerResidual_le_four
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    ‖centralSoninPrimePowerResidual a pk‖ ≤ 4 := by
  simpa only [centralSoninPrimePowerResidual] using
    norm_centralSoninDilationCornerResidual_le_four a
      (soninPrimePowerScale pk) (one_lt_soninPrimePowerScale pk)

/-- Weighting a local outcome channel multiplies its common ceiling by the Euler coefficient. -/
theorem norm_centralSoninWeightedPrimePowerResidual_le_four_mul
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    ‖centralSoninWeightedPrimePowerResidual a pk‖ ≤
      4 * ‖soninLogPrimePowerCoefficient pk‖ := by
  calc
    ‖centralSoninWeightedPrimePowerResidual a pk‖ =
        ‖soninLogPrimePowerCoefficient pk‖ *
          ‖centralSoninPrimePowerResidual a pk‖ := by
      rw [centralSoninWeightedPrimePowerResidual, norm_smul]
    _ ≤ ‖soninLogPrimePowerCoefficient pk‖ * 4 :=
      mul_le_mul_of_nonneg_left
        (norm_centralSoninPrimePowerResidual_le_four a pk)
        (norm_nonneg _)
    _ = 4 * ‖soninLogPrimePowerCoefficient pk‖ := by ring

private theorem summable_four_mul_norm_soninLogPrimePowerCoefficient_sq :
    Summable (fun pk : Nat.Primes × ℕ =>
      (4 * ‖soninLogPrimePowerCoefficient pk‖) ^ 2) := by
  exact (summable_norm_soninLogPrimePowerCoefficient_sq.mul_left 16).congr
    (fun _ => by ring)

/-- Parseval over the output basis turns the norm of the stacked channel into the sum of the
energies of its prime-power outcome channels. -/
theorem norm_sq_soninAllPrimeColumnOperator_apply_eq_tsum
    (a : ℝ) (ha : 0 < a) (x : SoninL2) :
    ‖soninAllPrimeColumnOperator a ha x‖ ^ 2 =
      ∑' pk : Nat.Primes × ℕ,
        ‖centralSoninWeightedPrimePowerResidual a pk x‖ ^ 2 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  have hout := HilbertSchmidt.summable_coe_sq
    (soninAllPrimeColumnOperator a ha x)
  rw [hout.tsum_prod]
  apply tsum_congr
  intro pk
  simp_rw [soninAllPrimeColumnOperator_apply]
  exact tsum_sq_norm_inner_hilbertBasis
    (ContinuousLinearMap.hsBasis ℂ SoninL2)
    (centralSoninWeightedPrimePowerResidual a pk x)

/-- **Uniform stacked-channel energy bound.**  The full coupled all-prime column has an
aperture-independent Bessel budget. -/
theorem norm_sq_soninAllPrimeColumnOperator_apply_le_effectRadius
    (a : ℝ) (ha : 0 < a) (x : SoninL2) :
    ‖soninAllPrimeColumnOperator a ha x‖ ^ 2 ≤
      soninAllPrimeColumnEffectRadius * ‖x‖ ^ 2 := by
  rw [norm_sq_soninAllPrimeColumnOperator_apply_eq_tsum]
  have henergy := HTGeometry.orthogonalInstrumentEnergy_le
    (A := fun pk : Nat.Primes × ℕ =>
      centralSoninWeightedPrimePowerResidual a pk)
    (b := fun pk => 4 * ‖soninLogPrimePowerCoefficient pk‖)
    (fun _ => mul_nonneg (by norm_num) (norm_nonneg _))
    (norm_centralSoninWeightedPrimePowerResidual_le_four_mul a)
    summable_four_mul_norm_soninLogPrimePowerCoefficient_sq x
  have hbudget :
      (∑' pk : Nat.Primes × ℕ,
          (4 * ‖soninLogPrimePowerCoefficient pk‖) ^ 2) =
        soninAllPrimeColumnEffectRadius := by
    rw [soninAllPrimeColumnEffectRadius, soninAllPrimeColumnWeightSqMass,
      ← tsum_mul_left]
    apply tsum_congr
    intro pk
    ring
  rwa [hbudget] at henergy

/-- Operator-norm form of the uniform stacked-channel energy bound. -/
theorem norm_soninAllPrimeColumnOperator_le_sqrt_effectRadius
    (a : ℝ) (ha : 0 < a) :
    ‖soninAllPrimeColumnOperator a ha‖ ≤
      Real.sqrt soninAllPrimeColumnEffectRadius := by
  apply (soninAllPrimeColumnOperator a ha).opNorm_le_bound
    (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  calc
    ‖soninAllPrimeColumnOperator a ha x‖ ^ 2 ≤
        soninAllPrimeColumnEffectRadius * ‖x‖ ^ 2 :=
      norm_sq_soninAllPrimeColumnOperator_apply_le_effectRadius a ha x
    _ = (Real.sqrt soninAllPrimeColumnEffectRadius * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt soninAllPrimeColumnEffectRadius_nonneg]

/-- The Hilbert-coordinate presentation has the same aperture-independent norm ceiling as the
actual Sonin-space column. -/
theorem norm_soninAllPrimeColumnCoordinateOperator_le_sqrt_effectRadius
    (a : ℝ) (ha : 0 < a) :
    ‖soninAllPrimeColumnCoordinateOperator a ha‖ ≤
      Real.sqrt soninAllPrimeColumnEffectRadius := by
  let U := (ContinuousLinearMap.hsBasis ℂ SoninL2).repr
  apply (soninAllPrimeColumnCoordinateOperator a ha).opNorm_le_bound
    (Real.sqrt_nonneg _)
  intro f
  let x : SoninL2 := U.symm f
  have happly : soninAllPrimeColumnOperator a ha x =
      soninAllPrimeColumnCoordinateOperator a ha f := by
    simp [soninAllPrimeColumnOperator, U, x]
  have hxnorm : ‖x‖ = ‖f‖ := by
    simpa only [x] using U.symm.norm_map f
  calc
    ‖soninAllPrimeColumnCoordinateOperator a ha f‖ =
        ‖soninAllPrimeColumnOperator a ha x‖ := by rw [happly]
    _ ≤ ‖soninAllPrimeColumnOperator a ha‖ * ‖x‖ :=
      (soninAllPrimeColumnOperator a ha).le_opNorm x
    _ ≤ Real.sqrt soninAllPrimeColumnEffectRadius * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (norm_soninAllPrimeColumnOperator_le_sqrt_effectRadius a ha)
        (norm_nonneg x)
    _ = Real.sqrt soninAllPrimeColumnEffectRadius * ‖f‖ := by rw [hxnorm]

/-- Squared coordinate-column norm bound, in the form consumed by replica-moment estimates. -/
theorem norm_soninAllPrimeColumnCoordinateOperator_sq_le_effectRadius
    (a : ℝ) (ha : 0 < a) :
    ‖soninAllPrimeColumnCoordinateOperator a ha‖ ^ 2 ≤
      soninAllPrimeColumnEffectRadius := by
  calc
    ‖soninAllPrimeColumnCoordinateOperator a ha‖ ^ 2 ≤
        (Real.sqrt soninAllPrimeColumnEffectRadius) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (Real.sqrt_nonneg _)).2
          (norm_soninAllPrimeColumnCoordinateOperator_le_sqrt_effectRadius a ha)
    _ = soninAllPrimeColumnEffectRadius :=
      Real.sq_sqrt soninAllPrimeColumnEffectRadius_nonneg

/-- A nonzero prime-power residual gives a nonzero row channel in the stacked all-prime
instrument.  Orthogonal outcome stacking therefore cannot cancel local Sonin information. -/
theorem soninAllPrimeColumnKernel_ne_zero_of_weightedPrimePowerResidual_ne_zero
    (a : ℝ) (pk : Nat.Primes × ℕ)
    (hpk : centralSoninWeightedPrimePowerResidual a pk ≠ 0) :
    soninAllPrimeColumnKernel a ≠ 0 := by
  intro hkernel
  apply hpk
  let b := ContinuousLinearMap.hsBasis ℂ SoninL2
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) ?_
  rintro x ⟨j, rfl⟩
  apply b.repr.injective
  ext i
  rw [b.repr_apply_apply]
  have hentry := congrFun hkernel ((pk, i), j)
  simpa [soninAllPrimeColumnKernel, b] using hentry

/-- A single nonzero residual channel is sufficient for nondegeneracy of the coordinate column
used by every coupled Gram and source-normalization theorem downstream. -/
theorem soninAllPrimeColumnCoordinateOperator_ne_zero_of_weightedPrimePowerResidual_ne_zero
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ)
    (hpk : centralSoninWeightedPrimePowerResidual a pk ≠ 0) :
    soninAllPrimeColumnCoordinateOperator a ha ≠ 0 := by
  exact (HilbertSchmidt.toOperatorRect_ne_zero_iff
    (soninAllPrimeColumnKernel_isHSRect a ha)).2
      (soninAllPrimeColumnKernel_ne_zero_of_weightedPrimePowerResidual_ne_zero a pk hpk)

/-- The nonzero logarithmic Euler coefficient introduces no new nondegeneracy premise. -/
theorem soninAllPrimeColumnCoordinateOperator_ne_zero_of_primePowerResidual_ne_zero
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ)
    (hpk : centralSoninPrimePowerResidual a pk ≠ 0) :
    soninAllPrimeColumnCoordinateOperator a ha ≠ 0 := by
  apply soninAllPrimeColumnCoordinateOperator_ne_zero_of_weightedPrimePowerResidual_ne_zero
    a ha pk
  simpa [centralSoninWeightedPrimePowerResidual,
    soninLogPrimePowerCoefficient_ne_zero] using hpk

/-- **Local-channel criterion for coupled-source nondegeneracy.**  The global all-prime source
column is nonzero exactly when at least one unweighted prime-power residual is nonzero.  This
replaces an opaque infinite-column hypothesis by one concrete channel witness. -/
theorem soninAllPrimeColumnCoordinateOperator_ne_zero_iff_exists_primePowerResidual_ne_zero
    (a : ℝ) (ha : 0 < a) :
    soninAllPrimeColumnCoordinateOperator a ha ≠ 0 ↔
      ∃ pk : Nat.Primes × ℕ, centralSoninPrimePowerResidual a pk ≠ 0 := by
  constructor
  · intro hcolumn
    by_contra hnone
    push Not at hnone
    apply hcolumn
    exact (HilbertSchmidt.toOperatorRect_eq_zero_iff
      (soninAllPrimeColumnKernel_isHSRect a ha)).2 (by
        funext z
        simp [soninAllPrimeColumnKernel, centralSoninWeightedPrimePowerResidual,
          hnone z.1.1])
  · rintro ⟨pk, hpk⟩
    exact soninAllPrimeColumnCoordinateOperator_ne_zero_of_primePowerResidual_ne_zero
      a ha pk hpk

/-- The coupled all-prime source column is nonzero at every positive aperture.  Any retained
prime-power coordinate supplies a witness; the prime-square channel at `2²` is canonical. -/
theorem soninAllPrimeColumnCoordinateOperator_ne_zero
    (a : ℝ) (ha : 0 < a) :
    soninAllPrimeColumnCoordinateOperator a ha ≠ 0 := by
  let pk : Nat.Primes × ℕ := (⟨2, Nat.prime_two⟩, 0)
  exact soninAllPrimeColumnCoordinateOperator_ne_zero_of_primePowerResidual_ne_zero
    a ha pk (centralSoninPrimePowerResidual_ne_zero a ha pk)

/-- The global coupled source is nonzero exactly when its correction response detects one
Chebyshev mode of one prime dilation signal.  This replaces the two-parameter scale family by one
polynomial orbit per prime without changing the nondegeneracy obligation. -/
theorem soninAllPrimeColumnCoordinateOperator_ne_zero_iff_exists_cosineResponse_ne_zero
    (a : ℝ) (ha : 0 < a) :
    soninAllPrimeColumnCoordinateOperator a ha ≠ 0 ↔
      ∃ pk : Nat.Primes × ℕ,
        centralSoninCornerCorrectionResponse a
          (HTGeometry.unitaryCosineRecurrence
            (soninPrimeDilationSignal pk.1) (pk.2 + 2)) ≠ 0 := by
  simpa only [centralSoninPrimePowerResidual_eq_cosineResponse] using
    soninAllPrimeColumnCoordinateOperator_ne_zero_iff_exists_primePowerResidual_ne_zero a ha

/-- The coupled positive energy on the single Sonin space. -/
def soninAllPrimeMixedEnergyOperator (a : ℝ) (ha : 0 < a) :
    SoninL2 →L[ℂ] SoninL2 :=
  ContinuousLinearMap.adjoint (soninAllPrimeColumnOperator a ha) ∘L
    soninAllPrimeColumnOperator a ha

/-- Explicit trace-class factorization through the all-prime column Hilbert space. -/
theorem soninAllPrimeMixedEnergyOperator_traceClassFactorization (a : ℝ) (ha : 0 < a) :
    ∃ S : SoninAllPrimeL2 →L[ℂ] SoninL2, ∃ U : SoninL2 →L[ℂ] SoninAllPrimeL2,
      ContinuousLinearMap.IsHilbertSchmidt S ∧
      ContinuousLinearMap.IsHilbertSchmidt U ∧
      soninAllPrimeMixedEnergyOperator a ha = S ∘L U := by
  refine ⟨ContinuousLinearMap.adjoint (soninAllPrimeColumnOperator a ha),
    soninAllPrimeColumnOperator a ha, ?_, ?_, rfl⟩
  · exact (soninAllPrimeColumnOperator_isHilbertSchmidt a ha).adjoint
  · exact soninAllPrimeColumnOperator_isHilbertSchmidt a ha

/-- The coupled energy is self-adjoint. -/
theorem soninAllPrimeMixedEnergyOperator_isSelfAdjoint (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.adjoint (soninAllPrimeMixedEnergyOperator a ha) =
      soninAllPrimeMixedEnergyOperator a ha := by
  rw [soninAllPrimeMixedEnergyOperator, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- The coupled energy has a nonnegative quadratic form. -/
theorem soninAllPrimeMixedEnergyOperator_nonnegative (a : ℝ) (ha : 0 < a) (x : SoninL2) :
    0 ≤ (inner ℂ x (soninAllPrimeMixedEnergyOperator a ha x)).re := by
  change 0 ≤ Complex.re
    (inner ℂ x
      (ContinuousLinearMap.adjoint (soninAllPrimeColumnOperator a ha)
        (soninAllPrimeColumnOperator a ha x)))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (E := SoninAllPrimeL2)

/-- A mixed prime-power overlap.  Its Hilbert--Schmidt energy is the cross term retained by the
coupled Gram and erased by the block-diagonal assembly. -/
def soninPrimePowerCrossOverlap (a : ℝ) (α β : Nat.Primes × ℕ) :
    SoninL2 →L[ℂ] SoninL2 :=
  centralSoninWeightedPrimePowerResidual a α ∘L
    ContinuousLinearMap.adjoint (centralSoninWeightedPrimePowerResidual a β)

/-- The same cross overlap before inserting the nonzero logarithmic Euler coefficients. -/
def soninPrimePowerResidualCrossOverlap (a : ℝ) (α β : Nat.Primes × ℕ) :
    SoninL2 →L[ℂ] SoninL2 :=
  centralSoninPrimePowerResidual a α ∘L
    ContinuousLinearMap.adjoint (centralSoninPrimePowerResidual a β)

/-- Weighting multiplies the residual cross overlap by the expected product of coefficients. -/
theorem soninPrimePowerCrossOverlap_eq_smul (a : ℝ) (α β : Nat.Primes × ℕ) :
    soninPrimePowerCrossOverlap a α β =
      (soninLogPrimePowerCoefficient α * star (soninLogPrimePowerCoefficient β)) •
        soninPrimePowerResidualCrossOverlap a α β := by
  have hadj : ContinuousLinearMap.adjoint
      (centralSoninWeightedPrimePowerResidual a β) =
      star (soninLogPrimePowerCoefficient β) •
        ContinuousLinearMap.adjoint (centralSoninPrimePowerResidual a β) := by
    change star (soninLogPrimePowerCoefficient β • centralSoninPrimePowerResidual a β) = _
    rw [star_smul]
    rfl
  rw [soninPrimePowerCrossOverlap, centralSoninWeightedPrimePowerResidual, hadj]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    soninPrimePowerResidualCrossOverlap, map_smul, smul_smul]
  rw [mul_comm]

/-- The Euler weights introduce no artificial vanishing: weighted and unweighted cross
overlaps are nonzero simultaneously. -/
theorem soninPrimePowerCrossOverlap_ne_zero_iff (a : ℝ) (α β : Nat.Primes × ℕ) :
    soninPrimePowerCrossOverlap a α β ≠ 0 ↔
      soninPrimePowerResidualCrossOverlap a α β ≠ 0 := by
  rw [soninPrimePowerCrossOverlap_eq_smul]
  simp [soninLogPrimePowerCoefficient_ne_zero]

theorem soninPrimePowerCrossOverlap_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (α β : Nat.Primes × ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt (soninPrimePowerCrossOverlap a α β) := by
  exact (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha β).adjoint.comp_left
    (centralSoninWeightedPrimePowerResidual a α)

theorem soninPrimePowerCrossOverlap_hsNormSq_nonneg
    (a : ℝ) (α β : Nat.Primes × ℕ) :
    0 ≤ ContinuousLinearMap.hsNormSq (soninPrimePowerCrossOverlap a α β) :=
  ContinuousLinearMap.hsNormSq_nonneg _

/-- The output-side energy `C_a C_a†`.  Its prime-power block `(α,β)` is exactly the cross
overlap `A_α A_β†`. -/
def soninAllPrimeOutputEnergyOperator (a : ℝ) (ha : 0 < a) :
    SoninAllPrimeL2 →L[ℂ] SoninAllPrimeL2 :=
  soninAllPrimeColumnOperator a ha ∘L
    ContinuousLinearMap.adjoint (soninAllPrimeColumnOperator a ha)

theorem soninAllPrimeOutputEnergyOperator_isHilbertSchmidt (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt (soninAllPrimeOutputEnergyOperator a ha) :=
  (soninAllPrimeColumnOperator_isHilbertSchmidt a ha).adjoint.comp_left
    (soninAllPrimeColumnOperator a ha)

/-- Pulling a coordinate vector back through the column adjoint selects the corresponding
prime-power residual adjoint. -/
theorem adjoint_soninAllPrimeColumnOperator_single (a : ℝ) (ha : 0 < a)
    (pk : Nat.Primes × ℕ) (j : SoninHilbertIndex) :
    ContinuousLinearMap.adjoint (soninAllPrimeColumnOperator a ha)
        (lp.single 2 (pk, j) (1 : ℂ)) =
      ContinuousLinearMap.adjoint (centralSoninWeightedPrimePowerResidual a pk)
        (ContinuousLinearMap.hsBasis ℂ SoninL2 j) := by
  classical
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right, lp.inner_single_right,
    soninAllPrimeColumnOperator_apply]
  simp [RCLike.inner_apply]

/-- The `(α,β)` block of `C_a C_a†` is the actual cross-prime overlap `A_α A_β†`. -/
theorem matrix_soninAllPrimeOutputEnergyOperator (a : ℝ) (ha : 0 < a)
    (α β : Nat.Primes × ℕ) (i j : SoninHilbertIndex) :
    HilbertSchmidt.matrixOf (soninAllPrimeOutputEnergyOperator a ha)
        ((α, i), (β, j)) =
      inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 i)
        (soninPrimePowerCrossOverlap a α β
          (ContinuousLinearMap.hsBasis ℂ SoninL2 j)) := by
  classical
  change soninAllPrimeOutputEnergyOperator a ha
      (lp.single 2 (β, j) (1 : ℂ)) (α, i) = _
  rw [soninAllPrimeOutputEnergyOperator, ContinuousLinearMap.comp_apply,
    soninAllPrimeColumnOperator_apply, adjoint_soninAllPrimeColumnOperator_single,
    soninPrimePowerCrossOverlap, ContinuousLinearMap.comp_apply]

private def soninAllPrimeSecondMomentEquiv :
    ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)) ×
        (SoninHilbertIndex × SoninHilbertIndex) ≃
      SoninAllPrimeIndex × SoninAllPrimeIndex where
  toFun z := ((z.1.1, z.2.2), (z.1.2, z.2.1))
  invFun z := ((z.1.1, z.2.1), (z.2.2, z.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complete family of cross-prime overlap energies is summable.  This is stronger than
termwise Hilbert--Schmidt membership and gives an actual finite mixed second moment. -/
theorem summable_soninPrimePowerCrossOverlap_hsNormSq (a : ℝ) (ha : 0 < a) :
    Summable (fun ab : (Nat.Primes × ℕ) × (Nat.Primes × ℕ) =>
      ContinuousLinearMap.hsNormSq (soninPrimePowerCrossOverlap a ab.1 ab.2)) := by
  let S := soninAllPrimeOutputEnergyOperator a ha
  let M := HilbertSchmidt.matrixOf S
  have hS : ContinuousLinearMap.IsHilbertSchmidt S :=
    soninAllPrimeOutputEnergyOperator_isHilbertSchmidt a ha
  have hM : HilbertSchmidt.IsHS M := HilbertSchmidt.isHS_matrixOf hS
  have hflat : Summable (fun z : ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)) ×
      (SoninHilbertIndex × SoninHilbertIndex) =>
      ‖inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 z.2.2)
        (soninPrimePowerCrossOverlap a z.1.1 z.1.2
          (ContinuousLinearMap.hsBasis ℂ SoninL2 z.2.1))‖ ^ 2) := by
    have hm : Summable (fun z : SoninAllPrimeIndex × SoninAllPrimeIndex => ‖M z‖ ^ 2) := hM
    have he := (soninAllPrimeSecondMomentEquiv.summable_iff).mpr hm
    refine he.congr (fun z => ?_)
    change ‖M (soninAllPrimeSecondMomentEquiv z)‖ ^ 2 = _
    rw [show M (soninAllPrimeSecondMomentEquiv z) =
        inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 z.2.2)
          (soninPrimePowerCrossOverlap a z.1.1 z.1.2
            (ContinuousLinearMap.hsBasis ℂ SoninL2 z.2.1)) by
      exact matrix_soninAllPrimeOutputEnergyOperator a ha
        z.1.1 z.1.2 z.2.2 z.2.1]
  have hprod := hflat
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)] at hprod
  refine hprod.2.congr (fun ab => ?_)
  rw [ContinuousLinearMap.hsNormSq_eq
    (soninPrimePowerCrossOverlap_isHilbertSchmidt a ha ab.1 ab.2)
    (ContinuousLinearMap.hsBasis ℂ SoninL2)]
  rw [(hprod.1 ab).tsum_prod]
  apply tsum_congr
  intro j
  exact tsum_sq_norm_inner_hilbertBasis (ContinuousLinearMap.hsBasis ℂ SoninL2)
    (soninPrimePowerCrossOverlap a ab.1 ab.2
      (ContinuousLinearMap.hsBasis ℂ SoninL2 j))

/-- The Hilbert--Schmidt energy of `C_a C_a†` is the sum of all cross-prime overlap energies. -/
theorem hsNormSq_soninAllPrimeOutputEnergyOperator (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (soninAllPrimeOutputEnergyOperator a ha) =
      ∑' ab : (Nat.Primes × ℕ) × (Nat.Primes × ℕ),
        ContinuousLinearMap.hsNormSq (soninPrimePowerCrossOverlap a ab.1 ab.2) := by
  let S := soninAllPrimeOutputEnergyOperator a ha
  let M := HilbertSchmidt.matrixOf S
  have hS : ContinuousLinearMap.IsHilbertSchmidt S :=
    soninAllPrimeOutputEnergyOperator_isHilbertSchmidt a ha
  have hM : HilbertSchmidt.IsHS M := HilbertSchmidt.isHS_matrixOf hS
  have hround : HilbertSchmidt.toOperator hM = S := HilbertSchmidt.toOperator_matrixOf hS
  have hnorm : ContinuousLinearMap.hsNormSq S = HilbertSchmidt.hsNormSq M := by
    rw [← hround, HilbertSchmidt.hsNormSq_toOperator]
  rw [show soninAllPrimeOutputEnergyOperator a ha = S from rfl, hnorm]
  change (∑' z : SoninAllPrimeIndex × SoninAllPrimeIndex, ‖M z‖ ^ 2) = _
  rw [← soninAllPrimeSecondMomentEquiv.tsum_eq
    (fun z : SoninAllPrimeIndex × SoninAllPrimeIndex => ‖M z‖ ^ 2)]
  have hflat : Summable (fun z : ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)) ×
      (SoninHilbertIndex × SoninHilbertIndex) =>
      ‖M (soninAllPrimeSecondMomentEquiv z)‖ ^ 2) :=
    (soninAllPrimeSecondMomentEquiv.summable_iff).mpr hM
  rw [hflat.tsum_prod]
  apply tsum_congr
  intro ab
  rw [ContinuousLinearMap.hsNormSq_eq
    (soninPrimePowerCrossOverlap_isHilbertSchmidt a ha ab.1 ab.2)
    (ContinuousLinearMap.hsBasis ℂ SoninL2)]
  have hab : Summable (fun ji : SoninHilbertIndex × SoninHilbertIndex =>
      ‖M (soninAllPrimeSecondMomentEquiv (ab, ji))‖ ^ 2) := by
    exact hflat.comp_injective (fun ji ji' h => (Prod.ext_iff.mp h).2)
  rw [hab.tsum_prod]
  apply tsum_congr
  intro j
  rw [← tsum_sq_norm_inner_hilbertBasis (ContinuousLinearMap.hsBasis ℂ SoninL2)
    (soninPrimePowerCrossOverlap a ab.1 ab.2
      (ContinuousLinearMap.hsBasis ℂ SoninL2 j))]
  apply tsum_congr
  intro i
  rw [show M (soninAllPrimeSecondMomentEquiv (ab, (j, i))) =
      inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 i)
        (soninPrimePowerCrossOverlap a ab.1 ab.2
          (ContinuousLinearMap.hsBasis ℂ SoninL2 j)) by
    dsimp [M, S]
    exact matrix_soninAllPrimeOutputEnergyOperator a ha ab.1 ab.2 i j]

theorem soninAllPrimeMixedEnergyOperator_isHilbertSchmidt (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt (soninAllPrimeMixedEnergyOperator a ha) :=
  (soninAllPrimeColumnOperator_isHilbertSchmidt a ha).comp_left
    (ContinuousLinearMap.adjoint (soninAllPrimeColumnOperator a ha))

/-- Cyclicity transfers the second trace moment from `C_a†C_a` on the Sonin space to
`C_aC_a†` on the all-prime output space. -/
theorem opTrace_sq_soninAllPrimeMixedEnergyOperator_cyclic (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.opTrace
        (soninAllPrimeMixedEnergyOperator a ha ∘L soninAllPrimeMixedEnergyOperator a ha) =
      ContinuousLinearMap.opTrace
        (soninAllPrimeOutputEnergyOperator a ha ∘L
          soninAllPrimeOutputEnergyOperator a ha) := by
  let C := soninAllPrimeColumnOperator a ha
  let S := soninAllPrimeOutputEnergyOperator a ha
  let B : SoninL2 →L[ℂ] SoninAllPrimeL2 := S ∘L C
  have hC : ContinuousLinearMap.IsHilbertSchmidt C :=
    soninAllPrimeColumnOperator_isHilbertSchmidt a ha
  have hS : ContinuousLinearMap.IsHilbertSchmidt S :=
    soninAllPrimeOutputEnergyOperator_isHilbertSchmidt a ha
  have hB : ContinuousLinearMap.IsHilbertSchmidt B := hC.comp_left S
  have hcyc := ContinuousLinearMap.opTrace_comp_comm hC.adjoint hB
  calc
    ContinuousLinearMap.opTrace
        (soninAllPrimeMixedEnergyOperator a ha ∘L soninAllPrimeMixedEnergyOperator a ha) =
        ContinuousLinearMap.opTrace (ContinuousLinearMap.adjoint C ∘L B) := by
      congr 1
    _ = ContinuousLinearMap.opTrace (B ∘L ContinuousLinearMap.adjoint C) := hcyc
    _ = ContinuousLinearMap.opTrace
        (soninAllPrimeOutputEnergyOperator a ha ∘L
          soninAllPrimeOutputEnergyOperator a ha) := by
      congr 1

/-- **Exact infinite mixed second moment.**  The second trace moment of the coupled Sonin Gram
is the convergent sum of every prime-power cross-overlap energy.  The diagonal direct-sum model
retains only the subfamily `α=β` and therefore misses the off-diagonal arithmetic interaction. -/
theorem re_opTrace_sq_soninAllPrimeMixedEnergyOperator (a : ℝ) (ha : 0 < a) :
    (ContinuousLinearMap.opTrace
      (soninAllPrimeMixedEnergyOperator a ha ∘L
        soninAllPrimeMixedEnergyOperator a ha)).re =
      ∑' ab : (Nat.Primes × ℕ) × (Nat.Primes × ℕ),
        ContinuousLinearMap.hsNormSq (soninPrimePowerCrossOverlap a ab.1 ab.2) := by
  rw [opTrace_sq_soninAllPrimeMixedEnergyOperator_cyclic a ha]
  let S := soninAllPrimeOutputEnergyOperator a ha
  have hS : ContinuousLinearMap.IsHilbertSchmidt S :=
    soninAllPrimeOutputEnergyOperator_isHilbertSchmidt a ha
  have hSad : ContinuousLinearMap.adjoint S = S := by
    dsimp [S, soninAllPrimeOutputEnergyOperator]
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  rw [show soninAllPrimeOutputEnergyOperator a ha = S from rfl,
    ContinuousLinearMap.opTrace_comp_eq_hsInner S S, hSad]
  calc
    (ContinuousLinearMap.hsInner S S).re = ContinuousLinearMap.hsNormSq S := by
      simpa using ContinuousLinearMap.hsInner_self_re hS
    _ = ∑' ab : (Nat.Primes × ℕ) × (Nat.Primes × ℕ),
        ContinuousLinearMap.hsNormSq (soninPrimePowerCrossOverlap a ab.1 ab.2) :=
      hsNormSq_soninAllPrimeOutputEnergyOperator a ha

/-- Diagonal pairs of prime powers. -/
def soninPrimePowerDiagonalSet :
    Set ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)) :=
  {ab | ab.1 = ab.2}

private def soninPrimePowerDiagonalEquiv :
    (Nat.Primes × ℕ) ≃ soninPrimePowerDiagonalSet where
  toFun α := ⟨(α, α), rfl⟩
  invFun z := z.1.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨α, β⟩, h⟩
    change α = β at h
    subst β
    rfl

/-- The diagonal contribution retained by the old block-diagonal assembly. -/
def soninAllPrimeDiagonalSecondMoment (a : ℝ) : ℝ :=
  ∑' α : Nat.Primes × ℕ,
    ContinuousLinearMap.hsNormSq (soninPrimePowerCrossOverlap a α α)

/-- The first coupled Sonin invariant: the total off-diagonal cross-prime-power energy. -/
def soninAllPrimeMixedSecondInvariant (a : ℝ) : ℝ :=
  ∑' z : ↥(soninPrimePowerDiagonalSetᶜ),
    ContinuousLinearMap.hsNormSq
      (soninPrimePowerCrossOverlap a z.1.1 z.1.2)

theorem soninAllPrimeMixedSecondInvariant_nonneg (a : ℝ) :
    0 ≤ soninAllPrimeMixedSecondInvariant a := by
  exact tsum_nonneg fun _ => ContinuousLinearMap.hsNormSq_nonneg _

/-- The coupled second trace moment is the diagonal moment plus the off-diagonal invariant
`I₂`.  This is the precise infinite version of the formal block expansion. -/
theorem re_opTrace_sq_soninAllPrimeMixedEnergyOperator_eq_diagonal_add_I2
    (a : ℝ) (ha : 0 < a) :
    (ContinuousLinearMap.opTrace
      (soninAllPrimeMixedEnergyOperator a ha ∘L
        soninAllPrimeMixedEnergyOperator a ha)).re =
      soninAllPrimeDiagonalSecondMoment a + soninAllPrimeMixedSecondInvariant a := by
  let g : ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)) → ℝ := fun ab =>
    ContinuousLinearMap.hsNormSq (soninPrimePowerCrossOverlap a ab.1 ab.2)
  have hg : Summable g := summable_soninPrimePowerCrossOverlap_hsNormSq a ha
  have hdiag : (∑' α : Nat.Primes × ℕ, g (α, α)) =
      ∑' z : soninPrimePowerDiagonalSet, g z := by
    exact soninPrimePowerDiagonalEquiv.tsum_eq
      (fun z : soninPrimePowerDiagonalSet => g z)
  rw [re_opTrace_sq_soninAllPrimeMixedEnergyOperator a ha,
    soninAllPrimeDiagonalSecondMoment, soninAllPrimeMixedSecondInvariant]
  change (∑' ab, g ab) = (∑' α : Nat.Primes × ℕ, g (α, α)) +
    ∑' z : ↥(soninPrimePowerDiagonalSetᶜ), g z
  rw [hdiag, hg.tsum_subtype_add_tsum_subtype_compl soninPrimePowerDiagonalSet]

/-- To prove strict positivity of `I₂`, it is enough to exhibit one nonzero off-diagonal
cross-prime-power overlap. -/
theorem soninAllPrimeMixedSecondInvariant_pos_of_crossOverlap_ne_zero
    (a : ℝ) (ha : 0 < a) (z : ↥(soninPrimePowerDiagonalSetᶜ))
    (hz : soninPrimePowerCrossOverlap a z.1.1 z.1.2 ≠ 0) :
    0 < soninAllPrimeMixedSecondInvariant a := by
  let g : ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)) → ℝ := fun ab =>
    ContinuousLinearMap.hsNormSq (soninPrimePowerCrossOverlap a ab.1 ab.2)
  have hg : Summable g := summable_soninPrimePowerCrossOverlap_hsNormSq a ha
  have hgsub : Summable (fun w : ↥(soninPrimePowerDiagonalSetᶜ) => g w) :=
    hg.subtype (fun ab => ab ∈ soninPrimePowerDiagonalSetᶜ)
  have hHS := soninPrimePowerCrossOverlap_isHilbertSchmidt a ha z.1.1 z.1.2
  have hne : g z ≠ 0 := by
    intro hzero
    exact hz ((ContinuousLinearMap.hsNormSq_eq_zero_iff hHS).mp hzero)
  have hpos : 0 < g z :=
    lt_of_le_of_ne (ContinuousLinearMap.hsNormSq_nonneg _) (Ne.symm hne)
  exact hgsub.tsum_pos
    (fun w => ContinuousLinearMap.hsNormSq_nonneg _) z hpos

theorem soninAllPrimeMixedSecondInvariant_pos_of_residualCrossOverlap_ne_zero
    (a : ℝ) (ha : 0 < a) (z : ↥(soninPrimePowerDiagonalSetᶜ))
    (hz : soninPrimePowerResidualCrossOverlap a z.1.1 z.1.2 ≠ 0) :
    0 < soninAllPrimeMixedSecondInvariant a :=
  soninAllPrimeMixedSecondInvariant_pos_of_crossOverlap_ne_zero a ha z
    ((soninPrimePowerCrossOverlap_ne_zero_iff a z.1.1 z.1.2).mpr hz)

end RHTower

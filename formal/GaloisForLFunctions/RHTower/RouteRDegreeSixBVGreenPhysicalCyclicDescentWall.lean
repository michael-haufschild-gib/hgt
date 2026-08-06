import GaloisForLFunctions.RHTower.RouteRDeningerBVGreenPositiveUnitComparison

/-!
# Degree-six BV--Green physical cyclic-descent wall

The literal ordinary-integer BV--Green boundary at degree six is the
Hochschild boundary of `S₆* ⊗ Q S₆`.  This file separates existence of a
normalized cyclic source reader from agreement with Route R's fixed physical
reader.

The source side is nonvacuous.  If `dₖ(T) = (T eₖ)ₖ`, then

`τ₆ = (5 / 6) d₁ + d₆`

has `τ₆(Q)=1` and takes the same value `1/6` on the two products defining the
boundary.  It therefore kills the degree-six boundary unconditionally.

Every reader cyclic on that exact pair also kills the boundary.  Consequently
a normalized cyclic reader whose boundary value agrees with the already fixed
physical marginal exists at `rho` exactly when that physical marginal is zero.
By the positive-unit comparison, this is exactly `Re rho = 1/2`; globally it
is RH.

Thus Hochschild infrastructure, cyclic-reader existence, and normalization are
closed.  The source-to-fixed-physical comparison is the entire remaining
RH-bearing operation; this module does not assert it unconditionally.
-/

open Complex
open scoped TensorProduct
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Literal degree-six chain and boundary -/

/-- Left product `S₆* Q S₆` in the degree-six BV--Green boundary. -/
def deningerDegreeSixBVGreenLeftProduct : DeningerOrdinaryIntegerEnd :=
  deningerOrdinaryIntegerWoldBackward 6 *
    (deningerOrdinaryIntegerReciprocalGreen *
      deningerOrdinaryIntegerWoldShift 6)

/-- Right product `Q S₆ S₆*` in the degree-six BV--Green boundary. -/
def deningerDegreeSixBVGreenRightProduct : DeningerOrdinaryIntegerEnd :=
  (deningerOrdinaryIntegerReciprocalGreen *
      deningerOrdinaryIntegerWoldShift 6) *
    deningerOrdinaryIntegerWoldBackward 6

/-- Literal degree-one Hochschild chain whose boundary is the degree-six
BV--Green commutator. -/
def deningerDegreeSixBVGreenHochschildChain :
    DeningerOrdinaryIntegerEnd ⊗[ℂ] DeningerOrdinaryIntegerEnd :=
  deningerOrdinaryIntegerWoldBackward 6 ⊗ₜ[ℂ]
    (deningerOrdinaryIntegerReciprocalGreen *
      deningerOrdinaryIntegerWoldShift 6)

theorem deningerDegreeSixBVGreenBoundary_eq_sub :
    deningerOrdinaryIntegerBVGreenStokesBoundary 6 =
      deningerDegreeSixBVGreenLeftProduct -
        deningerDegreeSixBVGreenRightProduct :=
  rfl

/-- The explicit degree-six operator is literally a Hochschild boundary. -/
theorem deningerDegreeSixBVGreenBoundary_eq_hochschildBoundary :
    deningerOrdinaryIntegerBVGreenStokesBoundary 6 =
      hochschildBoundaryOne deningerDegreeSixBVGreenHochschildChain := by
  exact deningerOrdinaryIntegerBVGreenStokesBoundary_eq_hochschildBoundary 6

/-! ## A source-native normalized cyclic reader -/

/-- Algebraic positive-integer basis vector `eₖ`. -/
def deningerOrdinaryIntegerBasisVector (k : PNat) :
    DeningerOrdinaryIntegerSequence :=
  fun j => if j = k then 1 else 0

/-- Diagonal coefficient `dₖ(T)=(T eₖ)ₖ` as a linear reader on the endomorphism
algebra. -/
def deningerOrdinaryIntegerDiagonalCoefficient (k : PNat) :
    DeningerOrdinaryIntegerEnd →ₗ[ℂ] ℂ where
  toFun T := T (deningerOrdinaryIntegerBasisVector k) k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem deningerOrdinaryIntegerBasisVector_self (k : PNat) :
    deningerOrdinaryIntegerBasisVector k k = 1 := by
  simp [deningerOrdinaryIntegerBasisVector]

@[simp]
theorem deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen
    (k : PNat) :
    deningerOrdinaryIntegerDiagonalCoefficient k
        deningerOrdinaryIntegerReciprocalGreen =
      (((k : ℕ) : ℂ))⁻¹ := by
  simp [deningerOrdinaryIntegerDiagonalCoefficient]

/-- Explicit source-only reader `τ₆=(5/6)d₁+d₆`. -/
def deningerDegreeSixBVGreenCyclicReader :
    DeningerOrdinaryIntegerEnd →ₗ[ℂ] ℂ :=
  ((5 / 6 : ℂ) • deningerOrdinaryIntegerDiagonalCoefficient 1) +
    deningerOrdinaryIntegerDiagonalCoefficient 6

/-- The explicit cyclic reader is nonzero and normalized on the reciprocal
Green density. -/
theorem deningerDegreeSixBVGreenCyclicReader_reciprocalGreen :
    deningerDegreeSixBVGreenCyclicReader
        deningerOrdinaryIntegerReciprocalGreen = 1 := by
  rw [deningerDegreeSixBVGreenCyclicReader, LinearMap.add_apply,
    LinearMap.smul_apply]
  rw [deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen,
    deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen]
  norm_num

theorem deningerDegreeSixBVGreenCyclicReader_leftProduct :
    deningerDegreeSixBVGreenCyclicReader
        deningerDegreeSixBVGreenLeftProduct = 1 / 6 := by
  rw [deningerDegreeSixBVGreenLeftProduct,
    deningerOrdinaryIntegerWoldBackward_reciprocalGreen_WoldShift]
  simp only [map_smul,
    deningerDegreeSixBVGreenCyclicReader_reciprocalGreen]
  norm_num

theorem deningerDegreeSixBVGreenCyclicReader_projectionGreen :
    deningerDegreeSixBVGreenCyclicReader
        (deningerOrdinaryIntegerDivisibilityProjection 6 *
          deningerOrdinaryIntegerReciprocalGreen) = 1 / 6 := by
  have h61 : ¬ (6 : PNat) ∣ (1 : PNat) := by
    rintro ⟨k, hk⟩
    have hkNat := congrArg (fun x : PNat => (x : ℕ)) hk
    norm_num at hkNat
    have hkpos : 0 < (k : ℕ) := k.2
    omega
  rw [deningerDegreeSixBVGreenCyclicReader, LinearMap.add_apply,
    LinearMap.smul_apply]
  simp [deningerOrdinaryIntegerDiagonalCoefficient,
    deningerOrdinaryIntegerBasisVector, h61]

theorem deningerDegreeSixBVGreenCyclicReader_rightProduct :
    deningerDegreeSixBVGreenCyclicReader
        deningerDegreeSixBVGreenRightProduct = 1 / 6 := by
  rw [deningerDegreeSixBVGreenRightProduct, mul_assoc,
    deningerOrdinaryIntegerWoldShift_comp_WoldBackward]
  rw [←
    deningerOrdinaryIntegerDivisibilityProjection_commutes_reciprocalGreen]
  exact deningerDegreeSixBVGreenCyclicReader_projectionGreen

/-- The source reader is cyclic on the exact product pair defining `B₆`. -/
theorem deningerDegreeSixBVGreenCyclicReader_pair_cyclic :
    deningerDegreeSixBVGreenCyclicReader
        deningerDegreeSixBVGreenLeftProduct =
      deningerDegreeSixBVGreenCyclicReader
        deningerDegreeSixBVGreenRightProduct := by
  rw [deningerDegreeSixBVGreenCyclicReader_leftProduct,
    deningerDegreeSixBVGreenCyclicReader_rightProduct]

/-- Hence the explicit normalized source reader kills the degree-six
Hochschild boundary unconditionally. -/
theorem deningerDegreeSixBVGreenCyclicReader_boundary :
    deningerDegreeSixBVGreenCyclicReader
        (deningerOrdinaryIntegerBVGreenStokesBoundary 6) = 0 := by
  rw [deningerDegreeSixBVGreenBoundary_eq_sub]
  simp only [map_sub,
    deningerDegreeSixBVGreenCyclicReader_pair_cyclic, sub_self]

/-! ## Exact physical-descent wall -/

/-- A genuine normalized source reader, cyclic on the literal degree-six
product pair, whose boundary value agrees with Route R's already fixed
same-fibre physical marginal. -/
def RouteRDegreeSixBVGreenPhysicalCyclicDescent
    (rho : XiDivisorSupport) : Prop :=
  ∃ tau : DeningerOrdinaryIntegerEnd →ₗ[ℂ] ℂ,
    tau deningerOrdinaryIntegerReciprocalGreen = 1 ∧
      tau deningerDegreeSixBVGreenLeftProduct =
        tau deningerDegreeSixBVGreenRightProduct ∧
      tau (deningerOrdinaryIntegerBVGreenStokesBoundary 6) =
        routeRDeningerBVGreenReflectedBoundary rho

/-- Any reader cyclic on the defining product pair kills the literal
degree-six boundary. -/
theorem deningerDegreeSixBVGreenBoundary_eq_zero_of_pair_cyclic
    (tau : DeningerOrdinaryIntegerEnd →ₗ[ℂ] ℂ)
    (hcyclic :
      tau deningerDegreeSixBVGreenLeftProduct =
        tau deningerDegreeSixBVGreenRightProduct) :
    tau (deningerOrdinaryIntegerBVGreenStokesBoundary 6) = 0 := by
  rw [deningerDegreeSixBVGreenBoundary_eq_sub]
  simp only [map_sub, hcyclic, sub_self]

/-- Nonvacuous classification: physical cyclic descent is exactly zero of
the fixed physical marginal.  The reverse implication uses the explicit
normalized source reader above. -/
theorem routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_boundary_zero
    (rho : XiDivisorSupport) :
    RouteRDegreeSixBVGreenPhysicalCyclicDescent rho ↔
      routeRDeningerBVGreenReflectedBoundary rho = 0 := by
  constructor
  · rintro ⟨tau, _hnormalized, hcyclic, hphysical⟩
    have hcomplex :
        (routeRDeningerBVGreenReflectedBoundary rho : ℂ) = 0 := by
      rw [← hphysical]
      exact deningerDegreeSixBVGreenBoundary_eq_zero_of_pair_cyclic tau hcyclic
    exact_mod_cast hcomplex
  · intro hzero
    refine ⟨deningerDegreeSixBVGreenCyclicReader,
      deningerDegreeSixBVGreenCyclicReader_reciprocalGreen,
      deningerDegreeSixBVGreenCyclicReader_pair_cyclic, ?_⟩
    rw [deningerDegreeSixBVGreenCyclicReader_boundary]
    simp [hzero]

/-- Pointwise physical cyclic descent cuts out exactly the critical line. -/
theorem routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_re_eq_half
    (rho : XiDivisorSupport) :
    RouteRDegreeSixBVGreenPhysicalCyclicDescent rho ↔
      (rho : ℂ).re = 1 / 2 :=
  (routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_boundary_zero rho).trans
    (routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_re_eq_half rho)

/-- The same wall in Route R's explicit Hodge-mate coefficient chart. -/
theorem
    routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    RouteRDegreeSixBVGreenPhysicalCyclicDescent rho ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 :=
  (routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_boundary_zero rho).trans
    (routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_hodgeMateCoefficient_eq_zero
      p rho)

/-- Global physical cyclic descent of the explicit degree-six boundary is
equivalent to RH.  This is a classifier, not an unconditional producer. -/
theorem forall_routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport,
      RouteRDegreeSixBVGreenPhysicalCyclicDescent rho) ↔
      RiemannHypothesis := by
  rw [←
    forall_routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_riemannHypothesis]
  exact forall_congr'
    routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_boundary_zero

end

end RHTower

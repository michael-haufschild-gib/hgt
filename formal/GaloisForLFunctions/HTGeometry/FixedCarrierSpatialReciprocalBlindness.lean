import GaloisForLFunctions.HTGeometry.ColorEventLocalResponseIndependence

/-!
# Fixed-carrier spatial change is reciprocal-spectrally invisible

For a rectangular complex transfer `D`, a two-sided skew spatial variation `A * D + D * B`
changes the reciprocal squares only by commutators. Every cyclic trace reporter is therefore
blind to this variation.

At an isometric carrier, the stronger full-Gram variation sequence is exact: every variation
whose complete domain Gram derivative vanishes is a left skew-frame variation, and every
Hermitian record variation has an explicit lift.

The scalar complex ternary carrier also has a faithful real family of phase derivations invisible
to its positive square. These are unconditional finite algebraic statements. They do not identify
spatial variation with physical gauge, normal variation with gravity, or the Gram record with
spacetime.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

/-- Two-sided spatial variation of a rectangular transfer. -/
def rectangularSpatialVariation
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (D : Matrix m n ℂ) :
    Matrix m n ℂ :=
  A * D + D * B

/-- First algebraic variation of the domain reciprocal square. -/
def reciprocalDomainFirstVariation
    {m n : Type*} [Fintype m] [Fintype n]
    (D E : Matrix m n ℂ) : Matrix n n ℂ :=
  Eᴴ * D + Dᴴ * E

/-- First algebraic variation of the codomain reciprocal square. -/
def reciprocalCodomainFirstVariation
    {m n : Type*} [Fintype m] [Fintype n]
    (D E : Matrix m n ℂ) : Matrix m m ℂ :=
  E * Dᴴ + D * Eᴴ

/-- A skew two-sided spatial variation changes the domain reciprocal square by a commutator. -/
theorem reciprocalDomainFirstVariation_spatial
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (D : Matrix m n ℂ)
    (hA : Aᴴ = -A) (hB : Bᴴ = -B) :
    reciprocalDomainFirstVariation D (rectangularSpatialVariation A B D) =
      (Dᴴ * D) * B - B * (Dᴴ * D) := by
  simp only [reciprocalDomainFirstVariation, rectangularSpatialVariation,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul]
  rw [hA, hB]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    Matrix.mul_neg, Matrix.neg_mul]
  abel

/-- A skew two-sided spatial variation changes the codomain reciprocal square by a commutator. -/
theorem reciprocalCodomainFirstVariation_spatial
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (D : Matrix m n ℂ)
    (hA : Aᴴ = -A) (hB : Bᴴ = -B) :
    reciprocalCodomainFirstVariation D (rectangularSpatialVariation A B D) =
      A * (D * Dᴴ) - (D * Dᴴ) * A := by
  simp only [reciprocalCodomainFirstVariation, rectangularSpatialVariation,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul]
  rw [hA, hB]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    Matrix.mul_neg, Matrix.neg_mul]
  abel

/-- Finite matrix trace annihilates every commutator. -/
theorem trace_matrixCommutator_eq_zero
    {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) :
    Matrix.trace (A * B - B * A) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm]
  exact sub_self _

/-- Every power reporter of the domain reciprocal square is blind to a spatial commutator. -/
theorem trace_domainSpatialCommutator_pow_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q B : Matrix n n ℂ) (k : ℕ) :
    Matrix.trace (Q ^ k * B - B * Q ^ k) = 0 :=
  trace_matrixCommutator_eq_zero (Q ^ k) B

/-- Every power reporter of the codomain reciprocal square is blind to a spatial commutator. -/
theorem trace_codomainSpatialCommutator_pow_eq_zero
    {m : Type*} [Fintype m] [DecidableEq m]
    (A G : Matrix m m ℂ) (k : ℕ) :
    Matrix.trace (A * G ^ k - G ^ k * A) = 0 :=
  trace_matrixCommutator_eq_zero A (G ^ k)

/-- Scalar complex ternary product. -/
def complexScalarTernaryProduct (x y z : ℂ) : ℂ :=
  x * star y * z

/-- Phase derivative on the scalar complex ternary carrier. -/
def phaseTernaryDerivation (rate : ℝ) (z : ℂ) : ℂ :=
  Complex.I * (rate : ℂ) * z

/-- Every real phase rate obeys the scalar ternary Leibniz identity. -/
theorem phaseTernaryDerivation_leibniz
    (rate : ℝ) (x y z : ℂ) :
    phaseTernaryDerivation rate (complexScalarTernaryProduct x y z) =
      complexScalarTernaryProduct (phaseTernaryDerivation rate x) y z +
      complexScalarTernaryProduct x (phaseTernaryDerivation rate y) z +
      complexScalarTernaryProduct x y (phaseTernaryDerivation rate z) := by
  simp [phaseTernaryDerivation, complexScalarTernaryProduct]
  ring

/-- The scalar positive reciprocal square is blind to every phase derivative. -/
theorem phaseTernaryDerivation_reciprocalSquare_eq_zero
    (rate : ℝ) (z : ℂ) :
    star (phaseTernaryDerivation rate z) * z +
        star z * phaseTernaryDerivation rate z = 0 := by
  simp [phaseTernaryDerivation]
  ring

/-- Distinct real phase rates give distinct ternary derivations. -/
theorem phaseTernaryDerivation_injective :
    Function.Injective phaseTernaryDerivation := by
  intro rate₁ rate₂ h
  have him := congrArg Complex.im (congrFun h 1)
  simpa [phaseTernaryDerivation, Complex.mul_im] using him

/-- Explicit left skew generator of a Gram-invisible variation at an isometric carrier. -/
def isometricGramKernelGenerator
    {m n : Type*} [Fintype m] [Fintype n]
    (D E : Matrix m n ℂ) : Matrix m m ℂ :=
  E * Dᴴ - D * Eᴴ - D * (Dᴴ * E) * Dᴴ

/-- The explicit Gram-kernel generator is skew-adjoint. -/
theorem isometricGramKernelGenerator_conjTranspose
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D E : Matrix m n ℂ)
    (hE : reciprocalDomainFirstVariation D E = 0) :
    (isometricGramKernelGenerator D E)ᴴ =
      -isometricGramKernelGenerator D E := by
  have hED : Eᴴ * D = -(Dᴴ * E) := by
    exact eq_neg_of_add_eq_zero_left hE
  simp only [isometricGramKernelGenerator, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [hED]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

/-- At an isometric carrier the explicit skew generator produces the original variation. -/
theorem isometricGramKernelGenerator_mul_eq
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D E : Matrix m n ℂ)
    (hD : Dᴴ * D = 1)
    (hE : reciprocalDomainFirstVariation D E = 0) :
    isometricGramKernelGenerator D E * D = E := by
  have hED : Eᴴ * D = -(Dᴴ * E) := by
    exact eq_neg_of_add_eq_zero_left hE
  simp only [isometricGramKernelGenerator]
  rw [Matrix.sub_mul, Matrix.sub_mul]
  simp only [Matrix.mul_assoc, hD, Matrix.mul_one]
  rw [hED]
  simp only [Matrix.mul_neg]
  noncomm_ring

/-- Complete Gram invisibility at an isometric carrier is exactly left skew-frame motion. -/
theorem exists_skew_left_of_isometric_gramVariation_eq_zero
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D E : Matrix m n ℂ)
    (hD : Dᴴ * D = 1)
    (hE : reciprocalDomainFirstVariation D E = 0) :
    ∃ A : Matrix m m ℂ, Aᴴ = -A ∧ A * D = E := by
  exact ⟨isometricGramKernelGenerator D E,
    isometricGramKernelGenerator_conjTranspose D E hE,
    isometricGramKernelGenerator_mul_eq D E hD hE⟩

/-- Every left skew-frame motion is invisible to the complete domain Gram derivative. -/
theorem reciprocalDomainFirstVariation_skewLeft_eq_zero
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (D : Matrix m n ℂ)
    (hA : Aᴴ = -A) :
    reciprocalDomainFirstVariation D (A * D) = 0 := by
  simpa [rectangularSpatialVariation] using
    reciprocalDomainFirstVariation_spatial A (0 : Matrix n n ℂ) D hA (by simp)

/-- Exact kernel statement for the isometric Gram-variation sequence. -/
theorem isometric_gramVariation_eq_zero_iff_exists_skewLeft
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D E : Matrix m n ℂ)
    (hD : Dᴴ * D = 1) :
    reciprocalDomainFirstVariation D E = 0 ↔
      ∃ A : Matrix m m ℂ, Aᴴ = -A ∧ A * D = E := by
  constructor
  · intro hE
    exact exists_skew_left_of_isometric_gramVariation_eq_zero D E hD hE
  · rintro ⟨A, hA, rfl⟩
    exact reciprocalDomainFirstVariation_skewLeft_eq_zero A D hA

/-- Component of a variation orthogonal to the source columns of an isometric carrier. -/
def isometricTransverseVariation
    {m n : Type*} [Fintype m] [Fintype n]
    (D E : Matrix m n ℂ) : Matrix m n ℂ :=
  E - D * (Dᴴ * E)

/-- Parallel projection plus transverse remainder reconstructs every variation. -/
theorem isometricParallel_add_transverseVariation
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D E : Matrix m n ℂ) :
    D * (Dᴴ * E) + isometricTransverseVariation D E = E := by
  simp only [isometricTransverseVariation]
  abel

/-- The transverse remainder has zero source comparison at an isometric carrier. -/
theorem conjTranspose_mul_isometricTransverseVariation_eq_zero
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D E : Matrix m n ℂ) (hD : Dᴴ * D = 1) :
    Dᴴ * isometricTransverseVariation D E = 0 := by
  simp only [isometricTransverseVariation]
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, hD, Matrix.one_mul]
  exact sub_self _

/-- Every variation splits into Hermitian record, skew frame, and transverse parts. -/
theorem isometricVariation_threeWay_decomposition
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D E : Matrix m n ℂ) :
    D * localHermitianResponse (Dᴴ * E) +
        D * localSkewHermitianResponse (Dᴴ * E) +
        isometricTransverseVariation D E = E := by
  rw [← Matrix.mul_add, localHermitianResponse_add_localSkewHermitianResponse]
  exact isometricParallel_add_transverseVariation D E

/-- A first-order invisible transverse possibility reappears as a positive quadratic record.

If `D` is isometric and `Dᴴ * N = 0`, then the cross terms vanish exactly:
`(D + N)ᴴ * (D + N) = 1 + Nᴴ * N`.
-/
theorem gram_add_transverse_eq_one_add_square
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D N : Matrix m n ℂ) (hD : Dᴴ * D = 1) (hN : Dᴴ * N = 0) :
    (D + N)ᴴ * (D + N) = 1 + Nᴴ * N := by
  have hND : Nᴴ * D = 0 := by
    have h := congrArg Matrix.conjTranspose hN
    simpa using h
  rw [Matrix.conjTranspose_add]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hD, hN, hND]
  abel

/-- Scaled form of the positive quadratic return law. -/
theorem gram_add_smul_transverse_eq_one_add_square
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D N : Matrix m n ℂ) (t : ℂ) (hD : Dᴴ * D = 1) (hN : Dᴴ * N = 0) :
    (D + t • N)ᴴ * (D + t • N) =
      1 + (star t * t) • (Nᴴ * N) := by
  have htN : Dᴴ * (t • N) = 0 := by
    simpa using congrArg (t • ·) hN
  rw [gram_add_transverse_eq_one_add_square D (t • N) hD htN]
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm t (star t)]

/-- The canonical transverse remainder is first-order invisible and contributes its square exactly. -/
theorem gram_add_isometricTransverseVariation
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D E : Matrix m n ℂ) (hD : Dᴴ * D = 1) :
    (D + isometricTransverseVariation D E)ᴴ *
        (D + isometricTransverseVariation D E) =
      1 + (isometricTransverseVariation D E)ᴴ *
        isometricTransverseVariation D E := by
  exact gram_add_transverse_eq_one_add_square D (isometricTransverseVariation D E) hD
    (conjTranspose_mul_isometricTransverseVariation_eq_zero D E hD)

/-- Explicit lift of a Hermitian first variation through an isometric Gram record. -/
def isometricHermitianGramLift
    {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℂ) (H : Matrix n n ℂ) : Matrix m n ℂ :=
  (2 : ℂ)⁻¹ • (D * H)

/-- The isometric Gram derivative is surjective onto all Hermitian record variations. -/
theorem reciprocalDomainFirstVariation_isometricHermitianGramLift
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) (H : Matrix n n ℂ)
    (hD : Dᴴ * D = 1) (hH : Hᴴ = H) :
    reciprocalDomainFirstVariation D (isometricHermitianGramLift D H) = H := by
  simp only [reciprocalDomainFirstVariation, isometricHermitianGramLift,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hH,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hD, mul_one]
  rw [← Matrix.mul_assoc Dᴴ D H, hD, one_mul]
  have hhalf : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, hhalf]
  ring

/-- Existential surjectivity form of the isometric Hermitian Gram lift. -/
theorem exists_gramVariation_eq_hermitian_of_isometric
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) (H : Matrix n n ℂ)
    (hD : Dᴴ * D = 1) (hH : Hᴴ = H) :
    ∃ E : Matrix m n ℂ, reciprocalDomainFirstVariation D E = H :=
  ⟨isometricHermitianGramLift D H,
    reciprocalDomainFirstVariation_isometricHermitianGramLift D H hD hH⟩

/-- The three canonical faces of one rectangular variation: Hermitian record, skew comparison,
and transverse remainder.  No physical interpretation is assumed. -/
def variationThreeFaceReport
    {m n : Type*} [Fintype m] [Fintype n]
    (D E : Matrix m n ℂ) :
    Matrix n n ℂ × Matrix n n ℂ × Matrix m n ℂ :=
  (localHermitianResponse (Dᴴ * E),
    localSkewHermitianResponse (Dᴴ * E),
    isometricTransverseVariation D E)

/-- **Joint-conservativity shadow.**  Although its three coordinates are projections, their
combined report determines the complete variation. -/
theorem variationThreeFaceReport_injective
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D : Matrix m n ℂ) :
    Function.Injective (variationThreeFaceReport D) := by
  intro E F h
  have hH :
      localHermitianResponse (Dᴴ * E) =
        localHermitianResponse (Dᴴ * F) :=
    congrArg Prod.fst h
  have hS :
      localSkewHermitianResponse (Dᴴ * E) =
        localSkewHermitianResponse (Dᴴ * F) :=
    congrArg (fun x => x.2.1) h
  have hN :
      isometricTransverseVariation D E =
        isometricTransverseVariation D F :=
    congrArg (fun x => x.2.2) h
  calc
    E = D * localHermitianResponse (Dᴴ * E) +
          D * localSkewHermitianResponse (Dᴴ * E) +
          isometricTransverseVariation D E :=
      (isometricVariation_threeWay_decomposition D E).symm
    _ = D * localHermitianResponse (Dᴴ * F) +
          D * localSkewHermitianResponse (Dᴴ * F) +
          isometricTransverseVariation D F := by
      rw [hH, hS, hN]
    _ = F := isometricVariation_threeWay_decomposition D F

/-- The complete first Gram reporter is exactly twice the Hermitian face.  It therefore sees only
one coordinate of the jointly conservative three-face report. -/
theorem reciprocalDomainFirstVariation_eq_two_smul_localHermitianResponse
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (D E : Matrix m n ℂ) :
    reciprocalDomainFirstVariation D E =
      (2 : ℂ) • localHermitianResponse (Dᴴ * E) := by
  ext i j
  simp [reciprocalDomainFirstVariation, localHermitianResponse]
  ring

end GaloisForLFunctions.HTGeometry

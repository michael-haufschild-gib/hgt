import GaloisForLFunctions.RHTower.CCMFirstClockBoundedExteriorPolarizationNoGo
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric

/-!
# Jordan positive-part ceiling for the first-clock exterior current

The calibrated Julia--Gamma exterior matrix is Hermitian of rank at most two after multiplication
by `i`. Its sole positive eigenvalue is the square root of a weighted height variance. This file
proves that variance is translation invariant and diameter bounded, then specializes its maximal
unit-coordinate Jordan envelope to the first-clock prime block.

Even the full target-selected positive spectral projector has only `O(X / log X)` capacity on
that block, strictly below the certified bad-mass square `≥ X / 576`. Thus nonlinear positive-part
functional calculus cannot repair the actual exterior seam.
-/

open Finset
open scoped BigOperators ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace RHTower

/-- Square of the unique positive eigenvalue of the Hermitian rank-two exterior matrix. -/
def sourceExteriorSpectralVariance
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) : ℝ :=
  (∑ i ∈ packet, amplitude i ^ 2) *
      (∑ i ∈ packet, (amplitude i * height i) ^ 2) -
    (∑ i ∈ packet, amplitude i * (amplitude i * height i)) ^ 2

theorem sourceExteriorSpectralVariance_nonneg
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) :
    0 ≤ sourceExteriorSpectralVariance packet amplitude height := by
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq packet amplitude
      (fun i => amplitude i * height i)
  unfold sourceExteriorSpectralVariance
  linarith

/-! ## Literal Hermitian matrix and its CFC positive part -/

/-- Fintype form of the exterior spectral variance, used for the matrix indexed by a packet
subtype. -/
def sourceExteriorFintypeSpectralVariance
    {ι : Type*} [Fintype ι] (amplitude height : ι → ℝ) : ℝ :=
  (∑ i, amplitude i ^ 2) * (∑ i, (amplitude i * height i) ^ 2) -
    (∑ i, amplitude i * (amplitude i * height i)) ^ 2

theorem sourceExteriorFintypeSpectralVariance_nonneg
    {ι : Type*} [Fintype ι] (amplitude height : ι → ℝ) :
    0 ≤ sourceExteriorFintypeSpectralVariance amplitude height := by
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ amplitude
      (fun i => amplitude i * height i)
  unfold sourceExteriorFintypeSpectralVariance
  nlinarith

/-- Algebraic rank-two exterior matrix before multiplication by `i`. -/
def sourceExteriorAlternatingOuterMatrix
    {ι : Type*} (u v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec v u - Matrix.vecMulVec u v

/-- Cubic law for every alternating difference of two rank-one outer products. -/
theorem sourceExteriorAlternatingOuterMatrix_cubic
    {ι : Type*} [Fintype ι] (u v : ι → ℂ)
    (huv : u ⬝ᵥ v = v ⬝ᵥ u) :
    sourceExteriorAlternatingOuterMatrix u v *
        sourceExteriorAlternatingOuterMatrix u v *
        sourceExteriorAlternatingOuterMatrix u v =
      -((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2) •
        sourceExteriorAlternatingOuterMatrix u v := by
  unfold sourceExteriorAlternatingOuterMatrix
  simp only [sub_mul, mul_sub, Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
    Pi.smul_apply, smul_dotProduct, smul_eq_mul]
  rw [huv]
  ring

/-- Literal Hermitian exterior matrix
`Kᵢⱼ = i aᵢ aⱼ (hᵢ - hⱼ)` on a finite source packet. -/
def sourceExteriorHermitianMatrix
    {ι : Type*} (amplitude height : ι → ℝ) : Matrix ι ι ℂ :=
  fun i j =>
    Complex.I *
      ((amplitude i * amplitude j * (height i - height j) : ℝ) : ℂ)

theorem sourceExteriorHermitianMatrix_isHermitian
    {ι : Type*} (amplitude height : ι → ℝ) :
    (sourceExteriorHermitianMatrix amplitude height).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [sourceExteriorHermitianMatrix]
  ring

/-- Outer-product factorization, exposing the matrix range inside the two-dimensional span of
the amplitude and height-weighted amplitude vectors. -/
theorem sourceExteriorHermitianMatrix_eq_smul_outer
    {ι : Type*} (amplitude height : ι → ℝ) :
    sourceExteriorHermitianMatrix amplitude height =
      Complex.I • sourceExteriorAlternatingOuterMatrix
        (fun i => (amplitude i : ℂ))
        (fun i => ((amplitude i * height i : ℝ) : ℂ)) := by
  ext i j
  simp [sourceExteriorHermitianMatrix, sourceExteriorAlternatingOuterMatrix,
    Matrix.smul_apply, Matrix.vecMulVec_apply]
  ring

/-- Exact minimal polynomial of the literal Hermitian exterior matrix.  It is the operator-level
statement behind the spectrum `{0, ±√Δ}`. -/
theorem sourceExteriorHermitianMatrix_cubic
    {ι : Type*} [Fintype ι] (amplitude height : ι → ℝ) :
    sourceExteriorHermitianMatrix amplitude height *
        sourceExteriorHermitianMatrix amplitude height *
        sourceExteriorHermitianMatrix amplitude height =
      (sourceExteriorFintypeSpectralVariance amplitude height : ℂ) •
        sourceExteriorHermitianMatrix amplitude height := by
  let u : ι → ℂ := fun i => (amplitude i : ℂ)
  let v : ι → ℂ := fun i => ((amplitude i * height i : ℝ) : ℂ)
  have huv : u ⬝ᵥ v = v ⬝ᵥ u := by
    unfold dotProduct u v
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have houter :=
    sourceExteriorAlternatingOuterMatrix_cubic u v huv
  have hmatrix :
      sourceExteriorHermitianMatrix amplitude height =
        Complex.I • sourceExteriorAlternatingOuterMatrix u v := by
    simpa [u, v] using
      sourceExteriorHermitianMatrix_eq_smul_outer amplitude height
  rw [hmatrix]
  calc
    (Complex.I • sourceExteriorAlternatingOuterMatrix u v) *
          (Complex.I • sourceExteriorAlternatingOuterMatrix u v) *
          (Complex.I • sourceExteriorAlternatingOuterMatrix u v) =
        (Complex.I ^ 3) •
          (sourceExteriorAlternatingOuterMatrix u v *
            sourceExteriorAlternatingOuterMatrix u v *
            sourceExteriorAlternatingOuterMatrix u v) := by
      simp only [smul_mul_smul]
      ring
    _ = (sourceExteriorFintypeSpectralVariance amplitude height : ℂ) •
          (Complex.I • sourceExteriorAlternatingOuterMatrix u v) := by
      rw [houter]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      unfold sourceExteriorFintypeSpectralVariance dotProduct u v
      push_cast
      have hI3 : Complex.I ^ 3 = -Complex.I := by
        rw [show Complex.I ^ 3 = Complex.I ^ 2 * Complex.I by ring,
          Complex.I_sq]
        ring
      rw [hI3]
      ring

/-- The operator norm of the literal exterior matrix is at most the square root of its spectral
variance.  The proof uses only the exact cubic law and the C-star identity. -/
theorem norm_sourceExteriorHermitianMatrix_le_sqrt_variance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (amplitude height : ι → ℝ) :
    ‖sourceExteriorHermitianMatrix amplitude height‖ ≤
      Real.sqrt (sourceExteriorFintypeSpectralVariance amplitude height) := by
  let K := sourceExteriorHermitianMatrix amplitude height
  have hK : IsSelfAdjoint K :=
    (sourceExteriorHermitianMatrix_isHermitian amplitude height).isSelfAdjoint
  have hcubic :
      K * K * K =
        (sourceExteriorFintypeSpectralVariance amplitude height : ℂ) • K := by
    simpa [K] using
      sourceExteriorHermitianMatrix_cubic amplitude height
  have hfour :
      K ^ 4 =
        (sourceExteriorFintypeSpectralVariance amplitude height : ℂ) •
          (K * K) := by
    calc
      K ^ 4 = (K * K * K) * K := by noncomm_ring
      _ = ((sourceExteriorFintypeSpectralVariance amplitude height : ℂ) • K) *
          K := by rw [hcubic]
      _ = (sourceExteriorFintypeSpectralVariance amplitude height : ℂ) •
          (K * K) := by rw [smul_mul_assoc]
  have hnorm := congrArg norm hfour
  have hvariance :
      0 ≤ sourceExteriorFintypeSpectralVariance amplitude height :=
    sourceExteriorFintypeSpectralVariance_nonneg amplitude height
  have hpow : ‖K ^ 4‖ = ‖K‖ ^ 4 := by
    simpa using hK.norm_pow_two_pow 2
  rw [hpow, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hvariance, hK.norm_mul_self] at hnorm
  have hsq :
      ‖K‖ ^ 2 ≤ sourceExteriorFintypeSpectralVariance amplitude height := by
    nlinarith [sq_nonneg ‖K‖]
  have hsqrt := Real.sqrt_le_sqrt hsq
  simpa [Real.sqrt_sq (norm_nonneg K)] using hsqrt

/-- Genuine continuous-functional-calculus positive part of the literal exterior matrix. -/
def sourceExteriorJordanPositivePart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (amplitude height : ι → ℝ) : Matrix ι ι ℂ :=
  (sourceExteriorHermitianMatrix amplitude height)⁺

/-- Quadratic energy of the genuine CFC positive part. -/
def sourceExteriorJordanPositivePartEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (amplitude height : ι → ℝ) (z : EuclideanSpace ℂ ι) : ℂ :=
  inner ℂ z
    ((EuclideanSpace.equiv ι ℂ).symm
      (sourceExteriorJordanPositivePart amplitude height *ᵥ z.ofLp))

theorem sourceExteriorJordanPositivePartEnergy_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (amplitude height : ι → ℝ) (z : EuclideanSpace ℂ ι) :
    0 ≤ sourceExteriorJordanPositivePartEnergy amplitude height z := by
  have hnonneg :=
    CFC.posPart_nonneg (sourceExteriorHermitianMatrix amplitude height)
  change
    ((sourceExteriorHermitianMatrix amplitude height)⁺ - 0).PosSemidef
      at hnonneg
  have hpsd :
      (sourceExteriorJordanPositivePart amplitude height).PosSemidef := by
    simpa [sourceExteriorJordanPositivePart] using hnonneg
  have hquad := hpsd.dotProduct_mulVec_nonneg z.ofLp
  unfold sourceExteriorJordanPositivePartEnergy
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct_comm] using hquad

theorem norm_sourceExteriorJordanPositivePartEnergy_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (amplitude height : ι → ℝ) (z : EuclideanSpace ℂ ι) :
    ‖sourceExteriorJordanPositivePartEnergy amplitude height z‖ ≤
      Real.sqrt (sourceExteriorFintypeSpectralVariance amplitude height) *
        ‖z‖ ^ 2 := by
  have hmul :=
    Matrix.l2_opNorm_mulVec
      (sourceExteriorJordanPositivePart amplitude height) z
  have hpositiveNorm :
      ‖sourceExteriorJordanPositivePart amplitude height‖ ≤
        Real.sqrt (sourceExteriorFintypeSpectralVariance amplitude height) :=
    (CStarAlgebra.norm_posPart_le
      (sourceExteriorHermitianMatrix amplitude height)).trans
        (norm_sourceExteriorHermitianMatrix_le_sqrt_variance amplitude height)
  unfold sourceExteriorJordanPositivePartEnergy
  calc
    ‖inner ℂ z ((EuclideanSpace.equiv ι ℂ).symm
        (sourceExteriorJordanPositivePart amplitude height *ᵥ z.ofLp))‖ ≤
        ‖z‖ * ‖(EuclideanSpace.equiv ι ℂ).symm
          (sourceExteriorJordanPositivePart amplitude height *ᵥ z.ofLp)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖z‖ *
        (‖sourceExteriorJordanPositivePart amplitude height‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left hmul (norm_nonneg z)
    _ ≤ ‖z‖ *
        (Real.sqrt (sourceExteriorFintypeSpectralVariance amplitude height) *
          ‖z‖) := by
      gcongr
    _ = Real.sqrt (sourceExteriorFintypeSpectralVariance amplitude height) *
        ‖z‖ ^ 2 := by ring

theorem norm_sourceExteriorJordanPositivePartEnergy_le_card_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (amplitude height : ι → ℝ) (z : EuclideanSpace ℂ ι)
    {B : ℝ} (hB : 0 ≤ B) (hz : ∀ i, ‖z i‖ ≤ B) :
    ‖sourceExteriorJordanPositivePartEnergy amplitude height z‖ ≤
      (Fintype.card ι : ℝ) *
        Real.sqrt (sourceExteriorFintypeSpectralVariance amplitude height) *
        B ^ 2 := by
  have hzsq : ‖z‖ ^ 2 ≤ (Fintype.card ι : ℝ) * B ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      (∑ i, ‖z i‖ ^ 2) ≤ ∑ _i : ι, B ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hz i)
      _ = (Fintype.card ι : ℝ) * B ^ 2 := by simp
  calc
    ‖sourceExteriorJordanPositivePartEnergy amplitude height z‖ ≤
        Real.sqrt (sourceExteriorFintypeSpectralVariance amplitude height) *
          ‖z‖ ^ 2 :=
      norm_sourceExteriorJordanPositivePartEnergy_le amplitude height z
    _ ≤ Real.sqrt (sourceExteriorFintypeSpectralVariance amplitude height) *
        ((Fintype.card ι : ℝ) * B ^ 2) :=
      mul_le_mul_of_nonneg_left hzsq (Real.sqrt_nonneg _)
    _ = (Fintype.card ι : ℝ) *
        Real.sqrt (sourceExteriorFintypeSpectralVariance amplitude height) *
        B ^ 2 := by ring

theorem sourceExteriorFintypeSpectralVariance_subtype_eq
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) :
    sourceExteriorFintypeSpectralVariance
        (fun i : ↥packet => amplitude i) (fun i : ↥packet => height i) =
      sourceExteriorSpectralVariance packet amplitude height := by
  have hatt : packet.attach = Finset.univ := by
    ext i
    simp
  have hsA := Finset.sum_attach packet (fun i => amplitude i ^ 2)
  have hsC := Finset.sum_attach packet
    (fun i => (amplitude i * height i) ^ 2)
  have hsB := Finset.sum_attach packet
    (fun i => amplitude i * (amplitude i * height i))
  rw [hatt] at hsA hsC hsB
  unfold sourceExteriorFintypeSpectralVariance
    sourceExteriorSpectralVariance
  rw [hsA, hsC, hsB]

theorem sourceExteriorSpectralVariance_sub_const
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) (c : ℝ) :
    sourceExteriorSpectralVariance packet amplitude (fun i => height i - c) =
      sourceExteriorSpectralVariance packet amplitude height := by
  let A := ∑ i ∈ packet, amplitude i ^ 2
  let B := ∑ i ∈ packet, amplitude i * (amplitude i * height i)
  let C := ∑ i ∈ packet, (amplitude i * height i) ^ 2
  have hB :
      (∑ i ∈ packet,
        amplitude i * (amplitude i * (height i - c))) = B - c * A := by
    dsimp only [A, B]
    calc
      (∑ i ∈ packet, amplitude i * (amplitude i * (height i - c))) =
          ∑ i ∈ packet,
            (amplitude i * (amplitude i * height i) -
              c * amplitude i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i ∈ packet, amplitude i * (amplitude i * height i)) -
          ∑ i ∈ packet, c * amplitude i ^ 2 := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i ∈ packet, amplitude i * (amplitude i * height i)) -
          c * ∑ i ∈ packet, amplitude i ^ 2 := by
            rw [Finset.mul_sum]
  have hC :
      (∑ i ∈ packet, (amplitude i * (height i - c)) ^ 2) =
        C - 2 * c * B + c ^ 2 * A := by
    dsimp only [A, B, C]
    calc
      (∑ i ∈ packet, (amplitude i * (height i - c)) ^ 2) =
          ∑ i ∈ packet,
            ((amplitude i * height i) ^ 2 -
              2 * c * (amplitude i * (amplitude i * height i)) +
              c ^ 2 * amplitude i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i ∈ packet, (amplitude i * height i) ^ 2) -
            ∑ i ∈ packet,
              2 * c * (amplitude i * (amplitude i * height i)) +
          ∑ i ∈ packet, c ^ 2 * amplitude i ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ i ∈ packet, (amplitude i * height i) ^ 2) -
            2 * c *
              ∑ i ∈ packet, amplitude i * (amplitude i * height i) +
          c ^ 2 * ∑ i ∈ packet, amplitude i ^ 2 := by
            rw [Finset.mul_sum, Finset.mul_sum]
  unfold sourceExteriorSpectralVariance
  rw [hB, hC]
  dsimp only [A, B, C]
  ring

theorem sourceExteriorSpectralVariance_le_of_diameter
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ)
    {D : ℝ} (hD : 0 ≤ D)
    (hdiameter : ∀ i ∈ packet, ∀ j ∈ packet, |height i - height j| ≤ D) :
    sourceExteriorSpectralVariance packet amplitude height ≤
      D ^ 2 * (∑ i ∈ packet, amplitude i ^ 2) ^ 2 := by
  by_cases hpacket : packet = ∅
  · simp [hpacket, sourceExteriorSpectralVariance]
  · obtain ⟨anchor, hanchor⟩ := Finset.nonempty_iff_ne_empty.mpr hpacket
    let centered : ι → ℝ := fun i => height i - height anchor
    have hcenter :
        sourceExteriorSpectralVariance packet amplitude centered =
          sourceExteriorSpectralVariance packet amplitude height :=
      sourceExteriorSpectralVariance_sub_const packet amplitude height (height anchor)
    have hcenterSq :
        (∑ i ∈ packet, (amplitude i * centered i) ^ 2) ≤
          D ^ 2 * ∑ i ∈ packet, amplitude i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have habsSq : |centered i| ^ 2 ≤ D ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hD).2
          (by simpa [centered] using hdiameter i hi anchor hanchor)
      have hsq : centered i ^ 2 ≤ D ^ 2 := by
        simpa [sq_abs] using habsSq
      calc
        (amplitude i * centered i) ^ 2 =
            amplitude i ^ 2 * centered i ^ 2 := by ring
        _ ≤ amplitude i ^ 2 * D ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = D ^ 2 * amplitude i ^ 2 := by ring
    have hA :
        0 ≤ ∑ i ∈ packet, amplitude i ^ 2 :=
      Finset.sum_nonneg fun i hi => sq_nonneg _
    have hcenterUpper :
        sourceExteriorSpectralVariance packet amplitude centered ≤
          (∑ i ∈ packet, amplitude i ^ 2) *
            (∑ i ∈ packet, (amplitude i * centered i) ^ 2) := by
      unfold sourceExteriorSpectralVariance
      nlinarith [sq_nonneg
        (∑ i ∈ packet, amplitude i * (amplitude i * centered i))]
    rw [← hcenter]
    calc
      sourceExteriorSpectralVariance packet amplitude centered ≤
          (∑ i ∈ packet, amplitude i ^ 2) *
            (∑ i ∈ packet, (amplitude i * centered i) ^ 2) := hcenterUpper
      _ ≤ (∑ i ∈ packet, amplitude i ^ 2) *
            (D ^ 2 * ∑ i ∈ packet, amplitude i ^ 2) :=
          mul_le_mul_of_nonneg_left hcenterSq hA
      _ = D ^ 2 * (∑ i ∈ packet, amplitude i ^ 2) ^ 2 := by ring

/-- Natural maximal bounded-coordinate envelope of the Jordan positive part. -/
def sourceExteriorPositivePartEnvelope
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) : ℝ :=
  (packet.card : ℝ) * Real.sqrt
    (sourceExteriorSpectralVariance packet amplitude height)

/-- Actual CFC positive-part energy on a finite packet, with the packet itself as matrix index. -/
def sourceExteriorPacketJordanPositivePartEnergy
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ)
    (z : EuclideanSpace ℂ ↥packet) : ℂ := by
  classical
  exact sourceExteriorJordanPositivePartEnergy
    (fun i : ↥packet => amplitude i) (fun i : ↥packet => height i) z

theorem sourceExteriorPacketJordanPositivePartEnergy_nonneg
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ)
    (z : EuclideanSpace ℂ ↥packet) :
    0 ≤ sourceExteriorPacketJordanPositivePartEnergy
      packet amplitude height z := by
  classical
  exact sourceExteriorJordanPositivePartEnergy_nonneg
    (fun i : ↥packet => amplitude i) (fun i : ↥packet => height i) z

/-- The previously defined scalar envelope is a genuine upper bound for the literal CFC
positive-part quadratic energy, not merely a named variance surrogate. -/
theorem norm_sourceExteriorPacketJordanPositivePartEnergy_le
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ)
    (z : EuclideanSpace ℂ ↥packet) {B : ℝ}
    (hB : 0 ≤ B) (hz : ∀ i, ‖z i‖ ≤ B) :
    ‖sourceExteriorPacketJordanPositivePartEnergy
        packet amplitude height z‖ ≤
      sourceExteriorPositivePartEnvelope packet amplitude height * B ^ 2 := by
  classical
  have hbound :=
    norm_sourceExteriorJordanPositivePartEnergy_le_card_mul
      (fun i : ↥packet => amplitude i) (fun i : ↥packet => height i)
      z hB hz
  unfold sourceExteriorPacketJordanPositivePartEnergy
    sourceExteriorPositivePartEnvelope
  rw [sourceExteriorFintypeSpectralVariance_subtype_eq] at hbound
  simpa using hbound

theorem sourceExteriorPositivePartEnvelope_le_of_diameter_one
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ)
    (hdiameter : ∀ i ∈ packet, ∀ j ∈ packet, |height i - height j| ≤ 1) :
    sourceExteriorPositivePartEnvelope packet amplitude height ≤
      (packet.card : ℝ) * ∑ i ∈ packet, amplitude i ^ 2 := by
  have hvar :=
    sourceExteriorSpectralVariance_le_of_diameter packet amplitude height
      (D := 1) (by norm_num) hdiameter
  have hsumNonneg :
      0 ≤ ∑ i ∈ packet, amplitude i ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hsqrt :
      Real.sqrt (sourceExteriorSpectralVariance packet amplitude height) ≤
        ∑ i ∈ packet, amplitude i ^ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hsumNonneg
    · simpa using hvar
  unfold sourceExteriorPositivePartEnvelope
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- Actual first-clock block envelope for the spectral positive part. -/
def ccmFirstClockEulerDepthZeroPositivePartEnvelope (m : ℕ) : ℝ :=
  sourceExteriorPositivePartEnvelope
    (suzukiMangoldtFivePrimeBlock (m ^ 4))
    ccmFirstClockEulerDepthZeroExteriorAmplitude
    ccmFirstClockEulerDepthZeroExteriorHeight

/-- Literal CFC Jordan-positive-part energy of the actual Euler depth-zero exterior matrix on the
first-clock prime block. -/
def ccmFirstClockEulerDepthZeroJordanPositivePartEnergy
    (m : ℕ)
    (z : EuclideanSpace ℂ ↥(suzukiMangoldtFivePrimeBlock (m ^ 4))) : ℂ :=
  sourceExteriorPacketJordanPositivePartEnergy
    (suzukiMangoldtFivePrimeBlock (m ^ 4))
    ccmFirstClockEulerDepthZeroExteriorAmplitude
    ccmFirstClockEulerDepthZeroExteriorHeight z

theorem ccmFirstClockEulerDepthZeroJordanPositivePartEnergy_nonneg
    (m : ℕ)
    (z : EuclideanSpace ℂ ↥(suzukiMangoldtFivePrimeBlock (m ^ 4))) :
    0 ≤ ccmFirstClockEulerDepthZeroJordanPositivePartEnergy m z :=
  sourceExteriorPacketJordanPositivePartEnergy_nonneg
    (suzukiMangoldtFivePrimeBlock (m ^ 4))
    ccmFirstClockEulerDepthZeroExteriorAmplitude
    ccmFirstClockEulerDepthZeroExteriorHeight z

theorem ccmFirstClockEulerDepthZeroPositivePartEnvelope_le
    {m : ℕ} (hm : 25 ≤ m) :
    ccmFirstClockEulerDepthZeroPositivePartEnvelope m ≤
      (25 / 2 : ℝ) * Real.log 4 ^ 2 *
        ((m ^ 4 : ℕ) : ℝ) / Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) := by
  have hmOne : 1 ≤ m ^ 4 := one_le_pow₀ (by omega : 1 ≤ m)
  have hbase :=
    sourceExteriorPositivePartEnvelope_le_of_diameter_one
      (suzukiMangoldtFivePrimeBlock (m ^ 4))
      ccmFirstClockEulerDepthZeroExteriorAmplitude
      ccmFirstClockEulerDepthZeroExteriorHeight
      (fun p hp q hq =>
        ccmFirstClockEulerDepthZeroExteriorHeight_diameter_le_one hm hp hq)
  have hlogTwoN : 0 < Real.log (2 * (((m ^ 4 : ℕ) : ℝ))) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 2 * m ^ 4 by omega)
  have hcardMass :=
    card_mul_log_two_mul_le_suzukiMangoldtFivePrimeBlock_logMass hmOne
  have hmassUpper :=
    suzukiMangoldtFivePrimeBlock_logMass_upper (n := m ^ 4)
  have hcard :
      ((suzukiMangoldtFivePrimeBlock (m ^ 4)).card : ℝ) ≤
        5 * ((m ^ 4 : ℕ) : ℝ) * Real.log 4 /
          Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) := by
    apply (le_div_iff₀ hlogTwoN).2
    exact hcardMass.trans hmassUpper
  have hsq :=
    sum_sq_ccmFirstClockEulerDepthZeroExteriorAmplitude_le hmOne
  have hsumNonneg :
      0 ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockEulerDepthZeroExteriorAmplitude p ^ 2 :=
    Finset.sum_nonneg fun p hp => sq_nonneg _
  calc
    ccmFirstClockEulerDepthZeroPositivePartEnvelope m
        ≤ ((suzukiMangoldtFivePrimeBlock (m ^ 4)).card : ℝ) *
          ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
            ccmFirstClockEulerDepthZeroExteriorAmplitude p ^ 2 := hbase
    _ ≤ (5 * ((m ^ 4 : ℕ) : ℝ) * Real.log 4 /
          Real.log (2 * ((m ^ 4 : ℕ) : ℝ))) *
        ((5 / 2 : ℝ) * Real.log 4) :=
      mul_le_mul hcard hsq hsumNonneg (by positivity)
    _ = (25 / 2 : ℝ) * Real.log 4 ^ 2 *
        ((m ^ 4 : ℕ) : ℝ) / Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) := by ring

/-- The full Jordan-positive-part envelope of the actual rank-two exterior matrix is still
strictly smaller than the certified first-clock bad-mass square. -/
theorem ccmFirstClockEulerDepthZeroPositivePartEnvelope_lt_badMass_sq
    {m : ℕ} (hmLarge : Real.exp 7201 < (m : ℝ)) :
    ccmFirstClockEulerDepthZeroPositivePartEnvelope m <
      (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p) ^ 2 := by
  have hmPos : (0 : ℝ) < m := (Real.exp_pos 7201).trans hmLarge
  have hm25 : 25 ≤ m := by
    have hexp := Real.add_one_le_exp (7201 : ℝ)
    exact_mod_cast (show (25 : ℝ) ≤ m by linarith)
  have hmCheb : Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ) := by
    have h20 : Real.exp 20 < Real.exp 7201 :=
      Real.exp_lt_exp.mpr (by norm_num)
    have hmLePow : m ≤ m ^ 4 := by
      have hmNatPos : 0 < m := by exact_mod_cast hmPos
      simpa using
        (Nat.pow_le_pow_right hmNatPos (show 1 ≤ 4 by omega) :
          m ^ 1 ≤ m ^ 4)
    exact (h20.trans hmLarge).le.trans (by exact_mod_cast hmLePow)
  have hlogm : 7201 < Real.log (m : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 7201) hmLarge
    rwa [Real.log_exp] at h
  have hlogDen :
      28800 < Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) := by
    have hmNe : (m : ℝ) ≠ 0 := ne_of_gt hmPos
    rw [show ((m ^ 4 : ℕ) : ℝ) = (m : ℝ) ^ 4 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 4 hmNe),
      Real.log_pow]
    norm_num
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have henvelope :=
    ccmFirstClockEulerDepthZeroPositivePartEnvelope_le hm25
  have hlogFour : Real.log 4 < 2 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hlogFour0 : 0 ≤ Real.log 4 :=
    (Real.log_pos (by norm_num)).le
  have hmPowPos : (0 : ℝ) < ((m ^ 4 : ℕ) : ℝ) := by positivity
  have hdenPos : 0 < Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) := by linarith
  have hcoarse :
      (25 / 2 : ℝ) * Real.log 4 ^ 2 *
          ((m ^ 4 : ℕ) : ℝ) / Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) <
        ((m ^ 4 : ℕ) : ℝ) / 576 := by
    have hlogSq : Real.log 4 ^ 2 < 4 := by nlinarith
    apply (div_lt_iff₀ hdenPos).2
    have hdenScaled : 50 * 576 < Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) := by
      norm_num
      simpa only [Nat.cast_pow] using hlogDen
    nlinarith
  have hbadMass :=
    ccmFirstClockJuliaSixthPower_block_badMass_lower hm25 hmCheb
  have hbadNonneg :
      0 ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p := by
    apply Finset.sum_nonneg
    intro p hp
    have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
    rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime]
    exact (ccmFirstClockJuliaSixthPower_block_badTerm_pos hm25 hp).le
  have hbadSq :
      ((m ^ 4 : ℕ) : ℝ) / 576 ≤
        (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p) ^ 2 := by
    have hmassSq :=
      (sq_le_sq₀ (by positivity : 0 ≤ (m : ℝ) ^ 2 / 24) hbadNonneg).2 hbadMass
    push_cast at hmassSq ⊢
    nlinarith
  exact henvelope.trans_lt (hcoarse.trans_le hbadSq)

/-- Direct operator-level no-go: every unit-coordinate state of the genuine CFC positive part of
the literal first-clock exterior matrix has energy strictly below the certified bad-mass square. -/
theorem norm_ccmFirstClockEulerDepthZeroJordanPositivePartEnergy_lt_badMass_sq
    {m : ℕ} (hmLarge : Real.exp 7201 < (m : ℝ))
    (z : EuclideanSpace ℂ ↥(suzukiMangoldtFivePrimeBlock (m ^ 4)))
    (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖ccmFirstClockEulerDepthZeroJordanPositivePartEnergy m z‖ <
      (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p) ^ 2 := by
  have hoperator :=
    norm_sourceExteriorPacketJordanPositivePartEnergy_le
      (suzukiMangoldtFivePrimeBlock (m ^ 4))
      ccmFirstClockEulerDepthZeroExteriorAmplitude
      ccmFirstClockEulerDepthZeroExteriorHeight z (B := 1)
      (by norm_num) hz
  have henvelope :=
    ccmFirstClockEulerDepthZeroPositivePartEnvelope_lt_badMass_sq hmLarge
  change
    ‖ccmFirstClockEulerDepthZeroJordanPositivePartEnergy m z‖ ≤
      sourceExteriorPositivePartEnvelope
        (suzukiMangoldtFivePrimeBlock (m ^ 4))
        ccmFirstClockEulerDepthZeroExteriorAmplitude
        ccmFirstClockEulerDepthZeroExteriorHeight * 1 ^ 2
    at hoperator
  have hoperator' :
      ‖ccmFirstClockEulerDepthZeroJordanPositivePartEnergy m z‖ ≤
        sourceExteriorPositivePartEnvelope
          (suzukiMangoldtFivePrimeBlock (m ^ 4))
          ccmFirstClockEulerDepthZeroExteriorAmplitude
          ccmFirstClockEulerDepthZeroExteriorHeight := by
    simpa using hoperator
  change
    sourceExteriorPositivePartEnvelope
        (suzukiMangoldtFivePrimeBlock (m ^ 4))
        ccmFirstClockEulerDepthZeroExteriorAmplitude
        ccmFirstClockEulerDepthZeroExteriorHeight <
      (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p) ^ 2
    at henvelope
  exact lt_of_le_of_lt hoperator' (by exact henvelope)

end RHTower

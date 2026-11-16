import GaloisForLFunctions.HTGeometry.Quantum.PositiveConstraintSupport
import GaloisForLFunctions.HTGeometry.TwoOutcomePinchingKadison
import GaloisForLFunctions.HTGeometry.ProductStabilizerPhysicalScore

/-!
# Compression, excursions, and zero disturbance

Compression discards a linear null space, not a multiplicative ideal. Its
square defect is the positive square of the excursion out of the retained
sector. Zero expectation characterizes precisely which states avoid that
excursion. The same support law applies to Lüders disturbance and product
stabilizer sectors already present in the corpus.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix
open scoped ComplexOrder MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Zero complementary energy is exactly support in the fixed space of `P`. -/
theorem complement_constraintEnergy_eq_zero_iff (P : Matrix ι ι ℂ)
    {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    constraintEnergy (1 - P) ρ = 0 ↔ P * ρ = ρ := by
  rw [constraintEnergy_eq_zero_iff _ hρ, sub_mul, one_mul, sub_eq_zero, eq_comm]

/-- The square of a compressed observable misses exactly the positive excursion square. -/
theorem compression_square_defect {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (A : Matrix ι ι ℂ) :
    P * (Aᴴ * A) * P - (P * A * P)ᴴ * (P * A * P) =
      ((1 - P) * A * P)ᴴ * ((1 - P) * A * P) := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hP.eq]
  noncomm_ring [hPP]
  simp only [← Matrix.mul_assoc P P, hPP]
  module

/-- Compression of a positive square vanishes only when the full departing operator vanishes. -/
omit [DecidableEq ι] in
theorem compressed_square_eq_zero_iff {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (A : Matrix ι ι ℂ) :
    P * (Aᴴ * A) * P = 0 ↔ A * P = 0 := by
  have h : P * (Aᴴ * A) * P = (A * P)ᴴ * (A * P) := by
    simp only [Matrix.conjTranspose_mul, hP.eq, Matrix.mul_assoc]
  rw [h, Matrix.conjTranspose_mul_self_eq_zero]

/-- Exact equality in the compressed square law is state-dependent absence of excursions. -/
theorem trace_compression_square_defect_eq_zero_iff
    {P ρ : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (hρ : ρ.PosSemidef) (A : Matrix ι ι ℂ) :
    ((P * (Aᴴ * A) * P - (P * A * P)ᴴ * (P * A * P)) * ρ).trace.re = 0 ↔
      (1 - P) * A * P * ρ = 0 := by
  rw [compression_square_defect hP hPP, ← constraintEnergy_eq_trace,
    constraintEnergy_eq_zero_iff _ hρ]

/-- A state's zero Lüders defect means precisely that measurement erases no observable
component on that state's support. -/
theorem trace_pinching_defect_eq_zero_iff {P A ρ : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hA : A.IsHermitian)
    (hρ : ρ.PosSemidef) :
    (_root_.HTGeometry.twoOutcomePinchingKadisonDefect P A * ρ).trace.re = 0 ↔
      (A - _root_.HTGeometry.twoOutcomePinching P A) * ρ = 0 := by
  rw [_root_.HTGeometry.twoOutcomePinchingKadisonDefect_eq_disturbanceMasterProduct
    hPP (by simpa only [Matrix.star_eq_conjTranspose] using hP.eq)
    (by simpa only [Matrix.star_eq_conjTranspose] using hA.eq)]
  rw [Matrix.star_eq_conjTranspose, ← constraintEnergy_eq_trace,
    constraintEnergy_eq_zero_iff _ hρ]

/-- The complement of every product-stabilizer state exposes exactly its supported states. -/
theorem productStabilizer_zero_leakage_iff {σ : Type*} [Fintype σ] [DecidableEq σ]
    (smpl : σ → Fin 3 × Bool)
    {ρ : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ}
    (hρ : ρ.PosSemidef) :
    constraintEnergy (1 - productStabilizerDensity smpl) ρ = 0 ↔
      productStabilizerDensity smpl * ρ = ρ :=
  complement_constraintEnergy_eq_zero_iff _ hρ

/-- Product-stabilizer compression is multiplicative in a state's expectation exactly when
the corresponding excursion annihilates that state. -/
theorem productStabilizer_compression_defect_eq_zero_iff
    {σ : Type*} [Fintype σ] [DecidableEq σ] (smpl : σ → Fin 3 × Bool)
    (A ρ : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (hρ : ρ.PosSemidef) :
    ((productStabilizerDensity smpl * (Aᴴ * A) * productStabilizerDensity smpl -
      (productStabilizerDensity smpl * A * productStabilizerDensity smpl)ᴴ *
        (productStabilizerDensity smpl * A * productStabilizerDensity smpl)) * ρ).trace.re = 0 ↔
      (1 - productStabilizerDensity smpl) * A * productStabilizerDensity smpl * ρ = 0 :=
  trace_compression_square_defect_eq_zero_iff
    (productStabilizerDensity_isHermitian smpl)
    (productStabilizerDensity_mul_self smpl) hρ A

end GaloisForLFunctions.HTGeometry.Quantum

#print axioms GaloisForLFunctions.HTGeometry.Quantum.complement_constraintEnergy_eq_zero_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.compression_square_defect
#print axioms GaloisForLFunctions.HTGeometry.Quantum.compressed_square_eq_zero_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.trace_compression_square_defect_eq_zero_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.trace_pinching_defect_eq_zero_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.productStabilizer_zero_leakage_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.productStabilizer_compression_defect_eq_zero_iff

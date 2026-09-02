import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ValuatedPluckerGram
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.WedgeNorm
import GaloisForLFunctions.HTGeometry.ComplexGramPlucker
import GaloisForLFunctions.HTGeometry.GalePeriodClosureFracture
import GaloisForLFunctions.HTGeometry.ChirotopeBlindPhysicalHolomorphicPeriodIncidenceUniversalityLaw
import GaloisForLFunctions.HTGeometry.HLSPhysicalAssumptions
import GaloisForLFunctions.HTGeometry.HiggsSpinorNullCone
import GaloisForLFunctions.QECLean.Foundations.Basic
import GaloisForLFunctions.QuantumAlg.Core.Base.State
import GaloisForLFunctions.QuantumAlg.Util.FinPow

/-!
# Nieto 1810 mechanical applications: Pluecker, qubit, twistor, and spinor layers

This file transfers the paper's rank-two Grassmann--Pluecker mechanism into existing period,
QECLean, QuantumAlg, twistor, and Lorentz-spinor representations. Every theorem is unconditional.
The final section also supplies the missing converse to the paper's null outer-product argument:
a complex `2 × 2` matrix is singular exactly when it factors as an outer product.
-/

open Matrix Finset
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

namespace GaloisForLFunctions.Nieto1810

noncomputable section

variable {R ι : Type*} [CommRing R]

/-- Coordinates of the decomposable bivector `u ∧ v`. -/
def decomposableBivector (u v : ι → R) (i j : ι) : R :=
  u i * v j - v i * u j

@[simp] theorem decomposableBivector_self (u v : ι → R) (i : ι) :
    decomposableBivector u v i i = 0 := by
  simp only [decomposableBivector]
  ring

theorem decomposableBivector_swap (u v : ι → R) (i j : ι) :
    decomposableBivector u v j i = -decomposableBivector u v i j := by
  simp [decomposableBivector]
  ring

/-- Three-term Grassmann--Pluecker relation for every decomposable bivector. -/
theorem decomposableBivector_plucker (u v : ι → R) (i j k l : ι) :
    decomposableBivector u v i j * decomposableBivector u v k l
      - decomposableBivector u v i k * decomposableBivector u v j l
      + decomposableBivector u v i l * decomposableBivector u v j k = 0 := by
  simp only [decomposableBivector]
  ring

/-- Action of a `2 × 2` matrix on the two generating rows of a bivector. -/
def twoRowAction (S : Matrix (Fin 2) (Fin 2) R) (u v : ι → R) : Fin 2 → ι → R :=
  fun a x => S a 0 * u x + S a 1 * v x

/-- Pluecker coordinates scale by the determinant under a change of generating rows. -/
theorem decomposableBivector_twoRowAction (S : Matrix (Fin 2) (Fin 2) R)
    (u v : ι → R) (i j : ι) :
    decomposableBivector (twoRowAction S u v 0) (twoRowAction S u v 1) i j =
      S.det * decomposableBivector u v i j := by
  simp only [decomposableBivector, twoRowAction, Matrix.det_fin_two]
  ring

/-! ## Twistor and period applications -/

abbrev Twistor := Fin 4 → ℂ

/-- Two-twistor Pluecker coordinate from equations (32)--(35). -/
def twistorBivector (P₁ P₂ : Twistor) : Fin 4 → Fin 4 → ℂ :=
  decomposableBivector P₁ P₂

theorem twistorBivector_plucker (P₁ P₂ : Twistor) (i j k l : Fin 4) :
    twistorBivector P₁ P₂ i j * twistorBivector P₁ P₂ k l
      - twistorBivector P₁ P₂ i k * twistorBivector P₁ P₂ j l
      + twistorBivector P₁ P₂ i l * twistorBivector P₁ P₂ j k = 0 :=
  decomposableBivector_plucker P₁ P₂ i j k l

theorem twistorBivector_changeFrame (S : Matrix (Fin 2) (Fin 2) ℂ)
    (P₁ P₂ : Twistor) (i j : Fin 4) :
    twistorBivector (twoRowAction S P₁ P₂ 0) (twoRowAction S P₁ P₂ 1) i j =
      S.det * twistorBivector P₁ P₂ i j :=
  decomposableBivector_twoRowAction S P₁ P₂ i j

/-- Real orbital-angular-momentum bivector from equation (34). -/
def orbitalBivector (x p : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  decomposableBivector x p

theorem orbitalBivector_antisymmetric (x p : Fin 4 → ℝ) (i j : Fin 4) :
    orbitalBivector x p j i = -orbitalBivector x p i j :=
  decomposableBivector_swap x p i j

theorem orbitalBivector_plucker (x p : Fin 4 → ℝ) (i j k l : Fin 4) :
    orbitalBivector x p i j * orbitalBivector x p k l
      - orbitalBivector x p i k * orbitalBivector x p j l
      + orbitalBivector x p i l * orbitalBivector x p j k = 0 :=
  decomposableBivector_plucker x p i j k l

theorem orbitalBivector_changeFrame (S : Matrix (Fin 2) (Fin 2) ℝ)
    (x p : Fin 4 → ℝ) (i j : Fin 4) :
    orbitalBivector (twoRowAction S x p 0) (twoRowAction S x p 1) i j =
      S.det * orbitalBivector x p i j :=
  decomposableBivector_twoRowAction S x p i j

/-- Every complex period family has decomposable real-oriented area coordinates. -/
theorem realOrientation_plucker {κ : Type*} (z : κ → ℂ) (i j k l : κ) :
    HTGeometry.realOrientation (z i) (z j) * HTGeometry.realOrientation (z k) (z l)
      - HTGeometry.realOrientation (z i) (z k) * HTGeometry.realOrientation (z j) (z l)
      + HTGeometry.realOrientation (z i) (z l) * HTGeometry.realOrientation (z j) (z k) = 0 := by
  simpa [HTGeometry.realOrientation, decomposableBivector] using
    (decomposableBivector_plucker (R := ℝ)
      (fun a => (z a).re) (fun a => (z a).im) i j k l)

theorem realOrientation_swap (z w : ℂ) :
    HTGeometry.realOrientation w z = -HTGeometry.realOrientation z w := by
  simp only [HTGeometry.realOrientation]
  ring

theorem periodChirotope_self (v : Fin 3 → ℂ) (i : Fin 3) :
    HTGeometry.periodChirotope v i i = 0 := by
  have h : HTGeometry.realOrientation (v i) (v i) = 0 := by
    simp only [HTGeometry.realOrientation]
    ring
  simp [HTGeometry.periodChirotope, h]

theorem periodChirotope_swap (v : Fin 3 → ℂ) (i j : Fin 3) :
    HTGeometry.periodChirotope v j i = -HTGeometry.periodChirotope v i j := by
  rw [HTGeometry.periodChirotope, HTGeometry.periodChirotope, realOrientation_swap,
    Left.sign_neg]

theorem latticePeriodTriple_plucker (i j k l : Fin 3) :
    HTGeometry.realOrientation (HTGeometry.latticePeriodTriple i) (HTGeometry.latticePeriodTriple j)
        * HTGeometry.realOrientation (HTGeometry.latticePeriodTriple k) (HTGeometry.latticePeriodTriple l)
      - HTGeometry.realOrientation (HTGeometry.latticePeriodTriple i) (HTGeometry.latticePeriodTriple k)
        * HTGeometry.realOrientation (HTGeometry.latticePeriodTriple j) (HTGeometry.latticePeriodTriple l)
      + HTGeometry.realOrientation (HTGeometry.latticePeriodTriple i) (HTGeometry.latticePeriodTriple l)
        * HTGeometry.realOrientation (HTGeometry.latticePeriodTriple j) (HTGeometry.latticePeriodTriple k) = 0 :=
  realOrientation_plucker HTGeometry.latticePeriodTriple i j k l

theorem irrationalPeriodTriple_plucker (i j k l : Fin 3) :
    HTGeometry.realOrientation (HTGeometry.irrationalPeriodTriple i) (HTGeometry.irrationalPeriodTriple j)
        * HTGeometry.realOrientation (HTGeometry.irrationalPeriodTriple k) (HTGeometry.irrationalPeriodTriple l)
      - HTGeometry.realOrientation (HTGeometry.irrationalPeriodTriple i) (HTGeometry.irrationalPeriodTriple k)
        * HTGeometry.realOrientation (HTGeometry.irrationalPeriodTriple j) (HTGeometry.irrationalPeriodTriple l)
      + HTGeometry.realOrientation (HTGeometry.irrationalPeriodTriple i) (HTGeometry.irrationalPeriodTriple l)
        * HTGeometry.realOrientation (HTGeometry.irrationalPeriodTriple j) (HTGeometry.irrationalPeriodTriple k) = 0 :=
  realOrientation_plucker HTGeometry.irrationalPeriodTriple i j k l

theorem positiveLatticePeriodTriple_plucker (i j k l : Fin 3) :
    HTGeometry.realOrientation (positiveLatticePeriodTriple i) (positiveLatticePeriodTriple j)
        * HTGeometry.realOrientation (positiveLatticePeriodTriple k) (positiveLatticePeriodTriple l)
      - HTGeometry.realOrientation (positiveLatticePeriodTriple i) (positiveLatticePeriodTriple k)
        * HTGeometry.realOrientation (positiveLatticePeriodTriple j) (positiveLatticePeriodTriple l)
      + HTGeometry.realOrientation (positiveLatticePeriodTriple i) (positiveLatticePeriodTriple l)
        * HTGeometry.realOrientation (positiveLatticePeriodTriple j) (positiveLatticePeriodTriple k) = 0 :=
  realOrientation_plucker positiveLatticePeriodTriple i j k l

theorem irrationalConicPeriodTriple_plucker (i j k l : Fin 3) :
    HTGeometry.realOrientation (conicRankThreeSource irrationalConicParameter i)
          (conicRankThreeSource irrationalConicParameter j)
        * HTGeometry.realOrientation (conicRankThreeSource irrationalConicParameter k)
          (conicRankThreeSource irrationalConicParameter l)
      - HTGeometry.realOrientation (conicRankThreeSource irrationalConicParameter i)
          (conicRankThreeSource irrationalConicParameter k)
        * HTGeometry.realOrientation (conicRankThreeSource irrationalConicParameter j)
          (conicRankThreeSource irrationalConicParameter l)
      + HTGeometry.realOrientation (conicRankThreeSource irrationalConicParameter i)
          (conicRankThreeSource irrationalConicParameter l)
        * HTGeometry.realOrientation (conicRankThreeSource irrationalConicParameter j)
          (conicRankThreeSource irrationalConicParameter k) = 0 :=
  realOrientation_plucker (conicRankThreeSource irrationalConicParameter) i j k l

/-! ## QECLean and QuantumAlg qubit flattenings -/

/-- One-qubit versus `n`-qubit flattening of a QECLean amplitude vector. -/
def qecFlattening {n : ℕ} (ψ : Quantum.NQubitVec (n + 1)) :
    Fin 2 → Quantum.NQubitBasis n → ℂ :=
  fun a tail => ψ (Fin.cons a tail)

/-- Rank-two Pluecker coordinate of a QECLean one-qubit cut. -/
def qecPlucker {n : ℕ} (ψ : Quantum.NQubitVec (n + 1))
    (x y : Quantum.NQubitBasis n) : ℂ :=
  decomposableBivector (qecFlattening ψ 0) (qecFlattening ψ 1) x y

theorem qecPlucker_relation {n : ℕ} (ψ : Quantum.NQubitVec (n + 1))
    (i j k l : Quantum.NQubitBasis n) :
    qecPlucker ψ i j * qecPlucker ψ k l
      - qecPlucker ψ i k * qecPlucker ψ j l
      + qecPlucker ψ i l * qecPlucker ψ j k = 0 :=
  decomposableBivector_plucker _ _ i j k l

theorem qecThreeQubit_plucker_relation (ψ : Quantum.NQubitVec 3)
    (i j k l : Quantum.NQubitBasis 2) :
    qecPlucker ψ i j * qecPlucker ψ k l
      - qecPlucker ψ i k * qecPlucker ψ j l
      + qecPlucker ψ i l * qecPlucker ψ j k = 0 := by
  simpa using qecPlucker_relation (n := 2) ψ i j k l

theorem qecFourQubit_plucker_relation (ψ : Quantum.NQubitVec 4)
    (i j k l : Quantum.NQubitBasis 3) :
    qecPlucker ψ i j * qecPlucker ψ k l
      - qecPlucker ψ i k * qecPlucker ψ j l
      + qecPlucker ψ i l * qecPlucker ψ j k = 0 := by
  simpa using qecPlucker_relation (n := 3) ψ i j k l

/-- Action of a two-dimensional frame matrix on the first QECLean qubit. -/
def qecFirstQubitAction {n : ℕ} (S : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : Quantum.NQubitVec (n + 1)) : Quantum.NQubitVec (n + 1) :=
  fun bits =>
    S (bits 0) 0 * ψ (Fin.cons 0 (Fin.tail bits)) +
      S (bits 0) 1 * ψ (Fin.cons 1 (Fin.tail bits))

theorem qecFlattening_firstQubitAction {n : ℕ} (S : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : Quantum.NQubitVec (n + 1)) :
    qecFlattening (qecFirstQubitAction S ψ) =
      twoRowAction S (qecFlattening ψ 0) (qecFlattening ψ 1) := by
  funext a tail
  simp [qecFlattening, qecFirstQubitAction, twoRowAction]

/-- QECLean Pluecker amplitudes obey the paper's determinant covariance law. -/
theorem qecPlucker_firstQubitAction {n : ℕ} (S : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : Quantum.NQubitVec (n + 1)) (i j : Quantum.NQubitBasis n) :
    qecPlucker (qecFirstQubitAction S ψ) i j = S.det * qecPlucker ψ i j := by
  simp only [qecPlucker, qecFlattening_firstQubitAction]
  exact decomposableBivector_twoRowAction S _ _ i j

/-- Canonically ordered QECLean flattening, used for coordinate-minor sums. -/
def qecOrderedFlattening {n : ℕ} (ψ : Quantum.NQubitVec (n + 1)) :
    Fin 2 → Fin (Fintype.card (Quantum.NQubitBasis n)) → ℂ :=
  fun a k => qecFlattening ψ a ((Fintype.equivFin (Quantum.NQubitBasis n)).symm k)

theorem qecFlattening_gram_plucker {n : ℕ} (ψ : Quantum.NQubitVec (n + 1)) :
    (HTGeometry.hermFeatureGram (qecOrderedFlattening ψ)).det =
      (HTGeometry.hermPluckerNormSq (qecOrderedFlattening ψ) : ℂ) :=
  HTGeometry.det_hermFeatureGram_eq_pluckerNormSq _

theorem qecFlattening_gram_ne_zero_iff {n : ℕ} (ψ : Quantum.NQubitVec (n + 1)) :
    (HTGeometry.hermFeatureGram (qecOrderedFlattening ψ)).det ≠ 0 ↔
      LinearIndependent ℂ (qecOrderedFlattening ψ) :=
  HTGeometry.det_hermFeatureGram_ne_zero_iff _

/-- One-qubit versus `n`-qubit flattening of a QuantumAlg state vector. -/
def quantumAlgFlattening {n : ℕ}
    (ψ : QuantumAlg.StateVector (QuantumAlg.Qubits (1 + n))) :
    Fin 2 → Fin (2 ^ n) → ℂ :=
  fun a tail => ψ (QuantumAlg.prodEquiv (m := 1) (n := n) (a, tail))

/-- Rank-two Pluecker coordinate of a QuantumAlg one-qubit cut. -/
def quantumAlgPlucker {n : ℕ}
    (ψ : QuantumAlg.StateVector (QuantumAlg.Qubits (1 + n)))
    (x y : Fin (2 ^ n)) : ℂ :=
  decomposableBivector (quantumAlgFlattening ψ 0) (quantumAlgFlattening ψ 1) x y

theorem quantumAlgPlucker_relation {n : ℕ}
    (ψ : QuantumAlg.StateVector (QuantumAlg.Qubits (1 + n))) (i j k l : Fin (2 ^ n)) :
    quantumAlgPlucker ψ i j * quantumAlgPlucker ψ k l
      - quantumAlgPlucker ψ i k * quantumAlgPlucker ψ j l
      + quantumAlgPlucker ψ i l * quantumAlgPlucker ψ j k = 0 :=
  decomposableBivector_plucker _ _ i j k l

theorem quantumAlgThreeQubit_plucker_relation
    (ψ : QuantumAlg.StateVector (QuantumAlg.Qubits 3)) (i j k l : Fin 4) :
    quantumAlgPlucker (n := 2) ψ i j * quantumAlgPlucker (n := 2) ψ k l
      - quantumAlgPlucker (n := 2) ψ i k * quantumAlgPlucker (n := 2) ψ j l
      + quantumAlgPlucker (n := 2) ψ i l * quantumAlgPlucker (n := 2) ψ j k = 0 := by
  simpa using quantumAlgPlucker_relation (n := 2) ψ i j k l

theorem quantumAlgFourQubit_plucker_relation
    (ψ : QuantumAlg.StateVector (QuantumAlg.Qubits 4)) (i j k l : Fin 8) :
    quantumAlgPlucker (n := 3) ψ i j * quantumAlgPlucker (n := 3) ψ k l
      - quantumAlgPlucker (n := 3) ψ i k * quantumAlgPlucker (n := 3) ψ j l
      + quantumAlgPlucker (n := 3) ψ i l * quantumAlgPlucker (n := 3) ψ j k = 0 := by
  simpa using quantumAlgPlucker_relation (n := 3) ψ i j k l

/-- Action of a two-dimensional frame matrix on the first QuantumAlg qubit. -/
def quantumAlgFirstQubitAction {n : ℕ} (S : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : QuantumAlg.StateVector (QuantumAlg.Qubits (1 + n))) :
    QuantumAlg.StateVector (QuantumAlg.Qubits (1 + n)) :=
  WithLp.toLp 2 fun bits =>
    let split := QuantumAlg.prodEquiv (m := 1) (n := n) |>.symm bits
    S split.1 0 * ψ (QuantumAlg.prodEquiv (m := 1) (n := n) (0, split.2)) +
      S split.1 1 * ψ (QuantumAlg.prodEquiv (m := 1) (n := n) (1, split.2))

theorem quantumAlgFlattening_firstQubitAction {n : ℕ}
    (S : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : QuantumAlg.StateVector (QuantumAlg.Qubits (1 + n))) :
    quantumAlgFlattening (quantumAlgFirstQubitAction S ψ) =
      twoRowAction S (quantumAlgFlattening ψ 0) (quantumAlgFlattening ψ 1) := by
  funext a tail
  simp [quantumAlgFlattening, quantumAlgFirstQubitAction, twoRowAction]

/-- QuantumAlg Pluecker amplitudes obey the paper's determinant covariance law. -/
theorem quantumAlgPlucker_firstQubitAction {n : ℕ}
    (S : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : QuantumAlg.StateVector (QuantumAlg.Qubits (1 + n))) (i j : Fin (2 ^ n)) :
    quantumAlgPlucker (quantumAlgFirstQubitAction S ψ) i j =
      S.det * quantumAlgPlucker ψ i j := by
  simp only [quantumAlgPlucker, quantumAlgFlattening_firstQubitAction]
  exact decomposableBivector_twoRowAction S _ _ i j

theorem quantumAlgFlattening_gram_plucker {n : ℕ}
    (ψ : QuantumAlg.StateVector (QuantumAlg.Qubits (1 + n))) :
    (HTGeometry.hermFeatureGram (quantumAlgFlattening ψ)).det =
      (HTGeometry.hermPluckerNormSq (quantumAlgFlattening ψ) : ℂ) :=
  HTGeometry.det_hermFeatureGram_eq_pluckerNormSq _

theorem quantumAlgFlattening_gram_ne_zero_iff {n : ℕ}
    (ψ : QuantumAlg.StateVector (QuantumAlg.Qubits (1 + n))) :
    (HTGeometry.hermFeatureGram (quantumAlgFlattening ψ)).det ≠ 0 ↔
      LinearIndependent ℂ (quantumAlgFlattening ψ) :=
  HTGeometry.det_hermFeatureGram_ne_zero_iff _

/-! ## Spinor null-cone package and converse -/

theorem spinorOuterSquare_null_package (H : Fin 2 → ℂ) :
    (HTGeometry.higgsSpinorEventMatrix H).IsHermitian ∧
      (HTGeometry.higgsSpinorEventMatrix H).PosSemidef ∧
      (HTGeometry.higgsSpinorEventMatrix H).det = 0 ∧
      HTGeometry.higgsSpinorEventMatrix H =
        HTGeometry.lorentzHermitianMatrix
          (HTGeometry.higgsSpinorTime H) (HTGeometry.higgsSpinorX H)
          (HTGeometry.higgsSpinorY H) (HTGeometry.higgsSpinorZ H) ∧
      HTGeometry.higgsSpinorTime H ^ 2 - HTGeometry.higgsSpinorX H ^ 2
        - HTGeometry.higgsSpinorY H ^ 2 - HTGeometry.higgsSpinorZ H ^ 2 = 0 :=
  ⟨HTGeometry.higgsSpinorEventMatrix_isHermitian H,
    HTGeometry.higgsSpinorEventMatrix_posSemidef H,
    HTGeometry.higgsSpinorEventMatrix_det H,
    HTGeometry.higgsSpinorEventMatrix_eq_lorentzHermitianMatrix H,
    HTGeometry.higgsSpinor_lorentzQuadratic_eq_zero H⟩

/-- Every singular `2 × 2` matrix over a field is an outer product, and conversely. -/
theorem det_fin_two_eq_zero_iff_outerProduct {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) :
    M.det = 0 ↔ ∃ u v : Fin 2 → K, M = Matrix.vecMulVec u v := by
  constructor
  · intro hdet
    rw [Matrix.det_fin_two] at hdet
    have hcross : M 0 0 * M 1 1 = M 0 1 * M 1 0 := sub_eq_zero.mp hdet
    by_cases h00 : M 0 0 = 0
    · by_cases h10 : M 1 0 = 0
      · refine ⟨![M 0 1, M 1 1], ![0, 1], ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec, h00, h10]
      · have h01 : M 0 1 = 0 := by
          apply (mul_eq_zero.mp ?_).resolve_right h10
          simpa [h00] using hcross.symm
        refine ⟨![0, M 1 0], ![1, M 1 1 / M 1 0], ?_⟩
        ext i j
        fin_cases i <;> fin_cases j
        · simp [Matrix.vecMulVec, h00]
        · simp [Matrix.vecMulVec, h01]
        · simp [Matrix.vecMulVec]
        · simp only [Matrix.vecMulVec, Matrix.of_apply]
          change M 1 1 = M 1 0 * (M 1 1 / M 1 0)
          field_simp
    · refine ⟨![M 0 0, M 1 0], ![1, M 0 1 / M 0 0], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.vecMulVec]
      · simp only [Matrix.vecMulVec, Matrix.of_apply]
        change M 0 1 = M 0 0 * (M 0 1 / M 0 0)
        field_simp
      · simp [Matrix.vecMulVec]
      · simp only [Matrix.vecMulVec, Matrix.of_apply]
        change M 1 1 = M 1 0 * (M 0 1 / M 0 0)
        calc
          M 1 1 = (M 1 0 * M 0 1) / M 0 0 := by
            apply (eq_div_iff h00).2
            simpa [mul_comm] using hcross
          _ = M 1 0 * (M 0 1 / M 0 0) := mul_div_assoc _ _ _
  · rintro ⟨u, v, rfl⟩
    exact Matrix.det_vecMulVec u v

/-- Null Lorentz coordinates are exactly those whose Hermitian matrix factors through spinors. -/
theorem lorentz_null_iff_spinorFactorization (t x y z : ℝ) :
    t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 = 0 ↔
      ∃ u v : Fin 2 → ℂ,
        HTGeometry.lorentzHermitianMatrix t x y z = Matrix.vecMulVec u v := by
  constructor
  · intro hnull
    rw [← det_fin_two_eq_zero_iff_outerProduct]
    rw [HTGeometry.lorentzHermitianMatrix_det]
    exact_mod_cast hnull
  · intro hfactor
    have hdet := (det_fin_two_eq_zero_iff_outerProduct
      (HTGeometry.lorentzHermitianMatrix t x y z)).2 hfactor
    rw [HTGeometry.lorentzHermitianMatrix_det] at hdet
    exact_mod_cast hdet

end

end GaloisForLFunctions.Nieto1810

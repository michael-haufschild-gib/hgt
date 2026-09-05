import GaloisForLFunctions.HTGeometry.FermionWickTheorem
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Algebras.TFIM

/-!
# Jordan--Wigner spin/fermion bridge for finite chains

This module realizes the creation, annihilation, number, and magnetization identities used in
Appendix E of Formicola--Di Bello--de Candia--De Filippis--Perroni,
*Discrete time crystals in disordered anisotropic Heisenberg chains*, arXiv:2609.04037.

The convention matches the paper: spin up is occupied, so `c†c = (1 + Z)/2`.  The concrete
operators instantiate the corpus's abstract `FermionSystem`, allowing its Wick and Pfaffian
theorems to be applied to the Jordan--Wigner chain.
-/

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open QuantumAlg

/-- Pauli matrices anticommute whenever their binary symplectic pairing is one. -/
theorem pauliMat_mul_eq_neg_mul_of_pauliOmega_one
    {n : ℕ} {s t : Fin n → Fin 4} (h : pauliOmega s t = 1) :
    pauliMat s * pauliMat t = -(pauliMat t * pauliMat s) := by
  rw [pauliMat_mul_closed, pauliMat_mul_closed, pauliXor_comm t s,
    pauliPhase_swap s t, h, negOnePow_one]
  module

/-- Concrete Jordan--Wigner Majorana matrix. -/
def jordanWignerMajorana {n : ℕ} (p : Fin n × Fin 2) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  pauliMat (QuantumAlg.TFIM.jwLabel p)

/-- Every Jordan--Wigner Majorana is Hermitian. -/
theorem jordanWignerMajorana_isHermitian {n : ℕ} (p : Fin n × Fin 2) :
    (jordanWignerMajorana p)ᴴ = jordanWignerMajorana p := by
  exact pauliMat_isHermitian _

/-- Every Jordan--Wigner Majorana squares to the identity. -/
theorem jordanWignerMajorana_sq {n : ℕ} (p : Fin n × Fin 2) :
    jordanWignerMajorana p * jordanWignerMajorana p = 1 := by
  exact pauliMat_sq _

/-- Distinct Jordan--Wigner Majoranas anticommute as matrices. -/
theorem jordanWignerMajorana_anticommutes
    {n : ℕ} {p q : Fin n × Fin 2} (hpq : p ≠ q) :
    jordanWignerMajorana p * jordanWignerMajorana q =
      -(jordanWignerMajorana q * jordanWignerMajorana p) := by
  exact pauliMat_mul_eq_neg_mul_of_pauliOmega_one
    (QuantumAlg.TFIM.jwOmega p q hpq)

/-- `Z`-string followed by `X` at site `j`. -/
def jordanWignerMajoranaX {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  jordanWignerMajorana (j, 0)

/-- `Z`-string followed by `Y` at site `j`. -/
def jordanWignerMajoranaY {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  jordanWignerMajorana (j, 1)

@[simp] theorem jordanWignerMajoranaX_isHermitian {n : ℕ} (j : Fin n) :
    (jordanWignerMajoranaX j)ᴴ = jordanWignerMajoranaX j := by
  exact jordanWignerMajorana_isHermitian _

@[simp] theorem jordanWignerMajoranaY_isHermitian {n : ℕ} (j : Fin n) :
    (jordanWignerMajoranaY j)ᴴ = jordanWignerMajoranaY j := by
  exact jordanWignerMajorana_isHermitian _

@[simp] theorem jordanWignerMajoranaX_sq {n : ℕ} (j : Fin n) :
    jordanWignerMajoranaX j * jordanWignerMajoranaX j = 1 := by
  exact jordanWignerMajorana_sq _

@[simp] theorem jordanWignerMajoranaY_sq {n : ℕ} (j : Fin n) :
    jordanWignerMajoranaY j * jordanWignerMajoranaY j = 1 := by
  exact jordanWignerMajorana_sq _

/-- At one site, the ordered Majorana product is `i Z_j`. -/
theorem jordanWignerMajoranaX_mul_majoranaY {n : ℕ} (j : Fin n) :
    jordanWignerMajoranaX j * jordanWignerMajoranaY j =
      Complex.I • pauliMat (QuantumAlg.TFIM.zLabel j) := by
  have hphase : pauliPhase (QuantumAlg.TFIM.jwLabel (j, 0))
      (QuantumAlg.TFIM.jwLabel (j, 1)) = Complex.I := by
    rw [pauliPhase, Finset.prod_eq_single j]
    · simp [QuantumAlg.TFIM.jwLabel, phase1]
    · intro k _ hkj
      by_cases hlt : k < j
      · rw [QuantumAlg.TFIM.jwLabel_of_lt (j, 0) hlt,
          QuantumAlg.TFIM.jwLabel_of_lt (j, 1) hlt]
        simp [phase1]
      · have hgt : j < k := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hkj)
        rw [QuantumAlg.TFIM.jwLabel_of_gt (j, 0) hgt,
          QuantumAlg.TFIM.jwLabel_of_gt (j, 1) hgt]
        simp [phase1]
    · exact fun h => absurd (Finset.mem_univ j) h
  have hxor : pauliXor (QuantumAlg.TFIM.jwLabel (j, 0))
      (QuantumAlg.TFIM.jwLabel (j, 1)) = QuantumAlg.TFIM.zLabel j := by
    simpa only [PauliMajoranaFrame.edgeLabel_mk, QuantumAlg.TFIM.frame_v_index] using
      QuantumAlg.TFIM.edgeLabel_field j
  rw [jordanWignerMajoranaX, jordanWignerMajoranaY,
    jordanWignerMajorana, jordanWignerMajorana,
    pauliMat_mul_closed, hphase, hxor]

/-- Jordan--Wigner parity string strictly to the left of site `j`. -/
def jordanWignerParityPrefixLabel {n : ℕ} (j : Fin n) (k : Fin n) : Fin 4 :=
  if k < j then 3 else 0

/-- Single-site Pauli label. -/
def jordanWignerLocalPauliLabel {n : ℕ} (j : Fin n) (a : Fin 4) (k : Fin n) : Fin 4 :=
  if k = j then a else 0

/-- Parity-prefix matrix. -/
def jordanWignerParityPrefix {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  pauliMat (jordanWignerParityPrefixLabel j)

/-- Multiplying a Jordan--Wigner Majorana by its parity prefix removes the nonlocal string. -/
theorem jordanWignerParityPrefix_mul_majorana
    {n : ℕ} (j : Fin n) (p : Fin 2) :
    jordanWignerParityPrefix j * jordanWignerMajorana (j, p) =
      pauliMat (jordanWignerLocalPauliLabel j (if p = 0 then 1 else 2)) := by
  have hphase : pauliPhase (jordanWignerParityPrefixLabel j)
      (QuantumAlg.TFIM.jwLabel (j, p)) = 1 := by
    rw [pauliPhase]
    apply Finset.prod_eq_one
    intro k _
    by_cases hlt : k < j
    · rw [QuantumAlg.TFIM.jwLabel_of_lt (j, p) hlt]
      simp [jordanWignerParityPrefixLabel, hlt, phase1]
    · by_cases heq : k = j
      · subst k
        rw [QuantumAlg.TFIM.jwLabel_at]
        fin_cases p <;> simp [jordanWignerParityPrefixLabel, phase1]
      · have hgt : j < k := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
        rw [QuantumAlg.TFIM.jwLabel_of_gt (j, p) hgt]
        simp [jordanWignerParityPrefixLabel, hlt, phase1]
  have hxor : pauliXor (jordanWignerParityPrefixLabel j)
      (QuantumAlg.TFIM.jwLabel (j, p)) =
        jordanWignerLocalPauliLabel j (if p = 0 then 1 else 2) := by
    funext k
    change xor4 (jordanWignerParityPrefixLabel j k)
      (QuantumAlg.TFIM.jwLabel (j, p) k) =
        jordanWignerLocalPauliLabel j (if p = 0 then 1 else 2) k
    by_cases hlt : k < j
    · rw [QuantumAlg.TFIM.jwLabel_of_lt (j, p) hlt]
      simp [jordanWignerParityPrefixLabel, jordanWignerLocalPauliLabel,
        hlt, ne_of_lt hlt, xor4]
    · by_cases heq : k = j
      · subst k
        rw [QuantumAlg.TFIM.jwLabel_at]
        fin_cases p <;>
          simp [jordanWignerParityPrefixLabel, jordanWignerLocalPauliLabel, xor4]
      · have hgt : j < k := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
        rw [QuantumAlg.TFIM.jwLabel_of_gt (j, p) hgt]
        simp [jordanWignerParityPrefixLabel, jordanWignerLocalPauliLabel,
          hlt, heq, xor4]
  rw [jordanWignerParityPrefix, jordanWignerMajorana,
    pauliMat_mul_closed, hphase, hxor, one_smul]

/-- The same parity string may be placed on the right. -/
theorem jordanWignerMajorana_mul_parityPrefix
    {n : ℕ} (j : Fin n) (p : Fin 2) :
    jordanWignerMajorana (j, p) * jordanWignerParityPrefix j =
      pauliMat (jordanWignerLocalPauliLabel j (if p = 0 then 1 else 2)) := by
  calc
    jordanWignerMajorana (j, p) * jordanWignerParityPrefix j =
        (jordanWignerParityPrefix j * jordanWignerMajorana (j, p))ᴴ := by
      rw [Matrix.conjTranspose_mul, jordanWignerMajorana_isHermitian,
        jordanWignerParityPrefix, pauliMat_isHermitian]
    _ = pauliMat (jordanWignerLocalPauliLabel j (if p = 0 then 1 else 2)) := by
      rw [jordanWignerParityPrefix_mul_majorana, pauliMat_isHermitian]

/-- Fermion creation operator, with spin-up interpreted as occupied. -/
def jordanWignerCreation {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (2 : ℂ)⁻¹ •
    (jordanWignerMajoranaX j + Complex.I • jordanWignerMajoranaY j)

/-- Fermion annihilation operator, with spin-up interpreted as occupied. -/
def jordanWignerAnnihilation {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (2 : ℂ)⁻¹ •
    (jordanWignerMajoranaX j + (-Complex.I) • jordanWignerMajoranaY j)

/-- Physical local spin-raising operator. -/
def jordanWignerLocalSpinRaising {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (2 : ℂ)⁻¹ •
    (pauliMat (jordanWignerLocalPauliLabel j 1) +
      Complex.I • pauliMat (jordanWignerLocalPauliLabel j 2))

/-- Physical local spin-lowering operator. -/
def jordanWignerLocalSpinLowering {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (2 : ℂ)⁻¹ •
    (pauliMat (jordanWignerLocalPauliLabel j 1) +
      (-Complex.I) • pauliMat (jordanWignerLocalPauliLabel j 2))

/-- Paper's multisite dictionary `S⁺_j = parityPrefix_j c†_j`. -/
theorem jordanWignerParityPrefix_mul_creation {n : ℕ} (j : Fin n) :
    jordanWignerParityPrefix j * jordanWignerCreation j =
      jordanWignerLocalSpinRaising j := by
  unfold jordanWignerCreation jordanWignerLocalSpinRaising
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul]
  rw [show jordanWignerParityPrefix j * jordanWignerMajoranaX j =
      pauliMat (jordanWignerLocalPauliLabel j 1) by
        simpa [jordanWignerMajoranaX] using
          jordanWignerParityPrefix_mul_majorana j (0 : Fin 2)]
  rw [show jordanWignerParityPrefix j * jordanWignerMajoranaY j =
      pauliMat (jordanWignerLocalPauliLabel j 2) by
        simpa [jordanWignerMajoranaY] using
          jordanWignerParityPrefix_mul_majorana j (1 : Fin 2)]

/-- Paper's equivalent right-string dictionary `S⁺_j = c†_j parityPrefix_j`. -/
theorem jordanWignerCreation_mul_parityPrefix {n : ℕ} (j : Fin n) :
    jordanWignerCreation j * jordanWignerParityPrefix j =
      jordanWignerLocalSpinRaising j := by
  unfold jordanWignerCreation jordanWignerLocalSpinRaising
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul]
  rw [show jordanWignerMajoranaX j * jordanWignerParityPrefix j =
      pauliMat (jordanWignerLocalPauliLabel j 1) by
        simpa [jordanWignerMajoranaX] using
          jordanWignerMajorana_mul_parityPrefix j (0 : Fin 2)]
  rw [show jordanWignerMajoranaY j * jordanWignerParityPrefix j =
      pauliMat (jordanWignerLocalPauliLabel j 2) by
        simpa [jordanWignerMajoranaY] using
          jordanWignerMajorana_mul_parityPrefix j (1 : Fin 2)]

/-- Paper's multisite dictionary `S⁻_j = parityPrefix_j c_j`. -/
theorem jordanWignerParityPrefix_mul_annihilation {n : ℕ} (j : Fin n) :
    jordanWignerParityPrefix j * jordanWignerAnnihilation j =
      jordanWignerLocalSpinLowering j := by
  unfold jordanWignerAnnihilation jordanWignerLocalSpinLowering
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul]
  rw [show jordanWignerParityPrefix j * jordanWignerMajoranaX j =
      pauliMat (jordanWignerLocalPauliLabel j 1) by
        simpa [jordanWignerMajoranaX] using
          jordanWignerParityPrefix_mul_majorana j (0 : Fin 2)]
  rw [show jordanWignerParityPrefix j * jordanWignerMajoranaY j =
      pauliMat (jordanWignerLocalPauliLabel j 2) by
        simpa [jordanWignerMajoranaY] using
          jordanWignerParityPrefix_mul_majorana j (1 : Fin 2)]

/-- Paper's equivalent right-string dictionary `S⁻_j = c_j parityPrefix_j`. -/
theorem jordanWignerAnnihilation_mul_parityPrefix {n : ℕ} (j : Fin n) :
    jordanWignerAnnihilation j * jordanWignerParityPrefix j =
      jordanWignerLocalSpinLowering j := by
  unfold jordanWignerAnnihilation jordanWignerLocalSpinLowering
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul]
  rw [show jordanWignerMajoranaX j * jordanWignerParityPrefix j =
      pauliMat (jordanWignerLocalPauliLabel j 1) by
        simpa [jordanWignerMajoranaX] using
          jordanWignerMajorana_mul_parityPrefix j (0 : Fin 2)]
  rw [show jordanWignerMajoranaY j * jordanWignerParityPrefix j =
      pauliMat (jordanWignerLocalPauliLabel j 2) by
        simpa [jordanWignerMajoranaY] using
          jordanWignerMajorana_mul_parityPrefix j (1 : Fin 2)]

/-- Site gauge converting the phase-free `Z` prefix to occupied-state parity `(-Z)` prefix. -/
def jordanWignerOccupationGauge {n : ℕ} (j : Fin n) : ℂ :=
  (-1 : ℂ) ^ j.val

@[simp] theorem jordanWignerOccupationGauge_sq {n : ℕ} (j : Fin n) :
    jordanWignerOccupationGauge j * jordanWignerOccupationGauge j = 1 := by
  rw [jordanWignerOccupationGauge, ← mul_pow]
  norm_num

/-- Occupation-parity string `∏_{l<j} (-Z_l)` from Eq. (20). -/
def jordanWignerOccupationParityPrefix {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  jordanWignerOccupationGauge j • jordanWignerParityPrefix j

/-- Paper-gauge fermion creation operator. -/
def paperJordanWignerCreation {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  jordanWignerOccupationGauge j • jordanWignerCreation j

/-- Paper-gauge fermion annihilation operator. -/
def paperJordanWignerAnnihilation {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  jordanWignerOccupationGauge j • jordanWignerAnnihilation j

/-- Literal occupied-parity form of Eq. (20): `S⁺_j = P_j c†_j`. -/
theorem jordanWignerOccupationParityPrefix_mul_paperCreation
    {n : ℕ} (j : Fin n) :
    jordanWignerOccupationParityPrefix j * paperJordanWignerCreation j =
      jordanWignerLocalSpinRaising j := by
  unfold jordanWignerOccupationParityPrefix paperJordanWignerCreation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    jordanWignerOccupationGauge_sq, one_smul,
    jordanWignerParityPrefix_mul_creation]

/-- Equivalent right-string form of Eq. (20). -/
theorem paperJordanWignerCreation_mul_occupationParityPrefix
    {n : ℕ} (j : Fin n) :
    paperJordanWignerCreation j * jordanWignerOccupationParityPrefix j =
      jordanWignerLocalSpinRaising j := by
  unfold jordanWignerOccupationParityPrefix paperJordanWignerCreation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    jordanWignerOccupationGauge_sq, one_smul,
    jordanWignerCreation_mul_parityPrefix]

/-- Literal occupied-parity annihilation form of Eq. (20): `S⁻_j = P_j c_j`. -/
theorem jordanWignerOccupationParityPrefix_mul_paperAnnihilation
    {n : ℕ} (j : Fin n) :
    jordanWignerOccupationParityPrefix j * paperJordanWignerAnnihilation j =
      jordanWignerLocalSpinLowering j := by
  unfold jordanWignerOccupationParityPrefix paperJordanWignerAnnihilation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    jordanWignerOccupationGauge_sq, one_smul,
    jordanWignerParityPrefix_mul_annihilation]

/-- Equivalent right-string annihilation form of Eq. (20). -/
theorem paperJordanWignerAnnihilation_mul_occupationParityPrefix
    {n : ℕ} (j : Fin n) :
    paperJordanWignerAnnihilation j * jordanWignerOccupationParityPrefix j =
      jordanWignerLocalSpinLowering j := by
  unfold jordanWignerOccupationParityPrefix paperJordanWignerAnnihilation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    jordanWignerOccupationGauge_sq, one_smul,
    jordanWignerAnnihilation_mul_parityPrefix]

/-- Neighboring paper gauges have product `-1`. -/
theorem jordanWignerOccupationGauge_left_mul_right
    {n : ℕ} (j : Fin (n - 1)) :
    jordanWignerOccupationGauge (QuantumAlg.TFIM.leftSite j) *
        jordanWignerOccupationGauge (QuantumAlg.TFIM.rightSite j) = -1 := by
  change (-1 : ℂ) ^ j.val * (-1 : ℂ) ^ (j.val + 1) = -1
  rw [pow_succ, ← mul_assoc, ← mul_pow]
  norm_num

/-- Physical nearest-neighbor `Y_j Y_{j+1}` Pauli label. -/
def jordanWignerYYLabel {n : ℕ} (j : Fin (n - 1)) (k : Fin n) : Fin 4 :=
  if k = QuantumAlg.TFIM.leftSite j ∨ k = QuantumAlg.TFIM.rightSite j then 2 else 0

/-- Ordered neighboring Majoranas `Y_j X_{j+1}` equal `i X_j X_{j+1}`. -/
theorem jordanWignerMajoranaY_left_mul_majoranaX_right
    {n : ℕ} (j : Fin (n - 1)) :
    jordanWignerMajoranaY (QuantumAlg.TFIM.leftSite j) *
        jordanWignerMajoranaX (QuantumAlg.TFIM.rightSite j) =
      Complex.I • pauliMat (QuantumAlg.TFIM.xxLabel j) := by
  let l := QuantumAlg.TFIM.leftSite j
  let r := QuantumAlg.TFIM.rightSite j
  have hlr : l < r := by simp [l, r, QuantumAlg.TFIM.leftSite,
    QuantumAlg.TFIM.rightSite]
  have hphase : pauliPhase (QuantumAlg.TFIM.jwLabel (l, 1))
      (QuantumAlg.TFIM.jwLabel (r, 0)) = Complex.I := by
    rw [pauliPhase, Finset.prod_eq_single l]
    · rw [QuantumAlg.TFIM.jwLabel_at,
        QuantumAlg.TFIM.jwLabel_of_lt (r, 0) hlr]
      simp [phase1]
    · intro k _hkuniv hkl
      by_cases hkl' : k < l
      · rw [QuantumAlg.TFIM.jwLabel_of_lt (l, 1) hkl',
          QuantumAlg.TFIM.jwLabel_of_lt (r, 0) (hkl'.trans hlr)]
        simp [phase1]
      · have hlk : l < k := lt_of_le_of_ne (le_of_not_gt hkl') (Ne.symm hkl)
        rw [QuantumAlg.TFIM.jwLabel_of_gt (l, 1) hlk]
        generalize QuantumAlg.TFIM.jwLabel (r, 0) k = a
        fin_cases a <;> simp [phase1]
    · exact fun h => absurd (Finset.mem_univ l) h
  have hxor : pauliXor (QuantumAlg.TFIM.jwLabel (l, 1))
      (QuantumAlg.TFIM.jwLabel (r, 0)) = QuantumAlg.TFIM.xxLabel j := by
    simpa only [PauliMajoranaFrame.edgeLabel_mk,
      QuantumAlg.TFIM.frame_v_index] using
        QuantumAlg.TFIM.edgeLabel_coupling j
  rw [jordanWignerMajoranaY, jordanWignerMajoranaX,
    jordanWignerMajorana, jordanWignerMajorana,
    pauliMat_mul_closed, hphase, hxor]

/-- Ordered neighboring Majoranas `X_j Y_{j+1}` equal `-i Y_j Y_{j+1}`. -/
theorem jordanWignerMajoranaX_left_mul_majoranaY_right
    {n : ℕ} (j : Fin (n - 1)) :
    jordanWignerMajoranaX (QuantumAlg.TFIM.leftSite j) *
        jordanWignerMajoranaY (QuantumAlg.TFIM.rightSite j) =
      (-Complex.I) • pauliMat (jordanWignerYYLabel j) := by
  let l := QuantumAlg.TFIM.leftSite j
  let r := QuantumAlg.TFIM.rightSite j
  have hlr : l < r := by simp [l, r, QuantumAlg.TFIM.leftSite,
    QuantumAlg.TFIM.rightSite]
  have hphase : pauliPhase (QuantumAlg.TFIM.jwLabel (l, 0))
      (QuantumAlg.TFIM.jwLabel (r, 1)) = -Complex.I := by
    rw [pauliPhase, Finset.prod_eq_single l]
    · rw [QuantumAlg.TFIM.jwLabel_at,
        QuantumAlg.TFIM.jwLabel_of_lt (r, 1) hlr]
      simp [phase1]
    · intro k _hkuniv hkl
      by_cases hkl' : k < l
      · rw [QuantumAlg.TFIM.jwLabel_of_lt (l, 0) hkl',
          QuantumAlg.TFIM.jwLabel_of_lt (r, 1) (hkl'.trans hlr)]
        simp [phase1]
      · have hlk : l < k := lt_of_le_of_ne (le_of_not_gt hkl') (Ne.symm hkl)
        rw [QuantumAlg.TFIM.jwLabel_of_gt (l, 0) hlk]
        generalize QuantumAlg.TFIM.jwLabel (r, 1) k = a
        fin_cases a <;> simp [phase1]
    · exact fun h => absurd (Finset.mem_univ l) h
  have hxor : pauliXor (QuantumAlg.TFIM.jwLabel (l, 0))
      (QuantumAlg.TFIM.jwLabel (r, 1)) = jordanWignerYYLabel j := by
    funext k
    change xor4 (QuantumAlg.TFIM.jwLabel (l, 0) k)
      (QuantumAlg.TFIM.jwLabel (r, 1) k) = jordanWignerYYLabel j k
    by_cases hleft : k = l
    · subst k
      rw [QuantumAlg.TFIM.jwLabel_at,
        QuantumAlg.TFIM.jwLabel_of_lt (r, 1) hlr]
      simp [jordanWignerYYLabel, l, xor4]
    · by_cases hright : k = r
      · subst k
        rw [QuantumAlg.TFIM.jwLabel_of_gt (l, 0) hlr,
          QuantumAlg.TFIM.jwLabel_at]
        simp [jordanWignerYYLabel, r, xor4]
      · have hcases : k < l ∨ r < k := by
          rcases lt_trichotomy k l with hlt | heq | hgt
          · exact Or.inl hlt
          · exact (hleft heq).elim
          · right
            have hneVal : k.val ≠ j.val + 1 := by
              intro hv
              apply hright
              apply Fin.ext
              simpa [r, QuantumAlg.TFIM.rightSite] using hv
            change j.val + 1 < k.val
            change j.val < k.val at hgt
            omega
        rcases hcases with hlt | hgt
        · rw [QuantumAlg.TFIM.jwLabel_of_lt (l, 0) hlt,
            QuantumAlg.TFIM.jwLabel_of_lt (r, 1) (hlt.trans hlr)]
          have hkleft : k ≠ QuantumAlg.TFIM.leftSite j := by
            simpa [l] using hleft
          have hkright : k ≠ QuantumAlg.TFIM.rightSite j := by
            simpa [r] using hright
          simp [jordanWignerYYLabel, hkleft, hkright, xor4]
        · rw [QuantumAlg.TFIM.jwLabel_of_gt (l, 0) (hlr.trans hgt),
            QuantumAlg.TFIM.jwLabel_of_gt (r, 1) hgt]
          have hkleft : k ≠ QuantumAlg.TFIM.leftSite j := by
            simpa [l] using hleft
          have hkright : k ≠ QuantumAlg.TFIM.rightSite j := by
            simpa [r] using hright
          simp [jordanWignerYYLabel, hkleft, hkright, xor4]
  rw [jordanWignerMajoranaX, jordanWignerMajoranaY,
    jordanWignerMajorana, jordanWignerMajorana,
    pauliMat_mul_closed, hphase, hxor]

/-- Raising plus lowering recovers local Pauli `X`. -/
theorem jordanWignerLocalSpinRaising_add_lowering {n : ℕ} (j : Fin n) :
    jordanWignerLocalSpinRaising j + jordanWignerLocalSpinLowering j =
      pauliMat (jordanWignerLocalPauliLabel j 1) := by
  unfold jordanWignerLocalSpinRaising jordanWignerLocalSpinLowering
  module

/-- Raising minus lowering is `i` times local Pauli `Y`. -/
theorem jordanWignerLocalSpinRaising_sub_lowering {n : ℕ} (j : Fin n) :
    jordanWignerLocalSpinRaising j - jordanWignerLocalSpinLowering j =
      Complex.I • pauliMat (jordanWignerLocalPauliLabel j 2) := by
  unfold jordanWignerLocalSpinRaising jordanWignerLocalSpinLowering
  module

/-- The constructed creation operator is the adjoint of annihilation. -/
theorem jordanWignerCreation_conjTranspose {n : ℕ} (j : Fin n) :
    (jordanWignerCreation j)ᴴ = jordanWignerAnnihilation j := by
  unfold jordanWignerCreation jordanWignerAnnihilation
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, jordanWignerMajoranaX_isHermitian,
    jordanWignerMajoranaY_isHermitian]
  simp

/-- Linear combinations of two Majorana pairs at distinct sites anticommute. -/
private theorem majoranaLinearCombinations_anticommute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y U V : Matrix ι ι ℂ) (a b c d : ℂ)
    (hXU : X * U = -(U * X)) (hXV : X * V = -(V * X))
    (hYU : Y * U = -(U * Y)) (hYV : Y * V = -(V * Y)) :
    (a • X + b • Y) * (c • U + d • V) =
      -((c • U + d • V) * (a • X + b • Y)) := by
  simp_rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [hXU, hXV, hYU, hYV]
  module

/-- A Jordan--Wigner creation operator is nilpotent. -/
theorem jordanWignerCreation_sq_zero {n : ℕ} (j : Fin n) :
    jordanWignerCreation j * jordanWignerCreation j = 0 := by
  have hanti : jordanWignerMajoranaX j * jordanWignerMajoranaY j =
      -(jordanWignerMajoranaY j * jordanWignerMajoranaX j) := by
    exact jordanWignerMajorana_anticommutes (by simp)
  unfold jordanWignerCreation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp_rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [jordanWignerMajoranaX_sq, jordanWignerMajoranaY_sq, hanti]
  simp [Complex.I_mul_I]

/-- A Jordan--Wigner annihilation operator is nilpotent. -/
theorem jordanWignerAnnihilation_sq_zero {n : ℕ} (j : Fin n) :
    jordanWignerAnnihilation j * jordanWignerAnnihilation j = 0 := by
  have hanti : jordanWignerMajoranaX j * jordanWignerMajoranaY j =
      -(jordanWignerMajoranaY j * jordanWignerMajoranaX j) := by
    exact jordanWignerMajorana_anticommutes (by simp)
  unfold jordanWignerAnnihilation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp_rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [jordanWignerMajoranaX_sq, jordanWignerMajoranaY_sq, hanti]
  simp [Complex.I_mul_I]

/-- Same-site canonical anticommutation relation. -/
theorem jordanWigner_sameSite_CAR {n : ℕ} (j : Fin n) :
    jordanWignerAnnihilation j * jordanWignerCreation j +
      jordanWignerCreation j * jordanWignerAnnihilation j = 1 := by
  have hanti : jordanWignerMajoranaX j * jordanWignerMajoranaY j =
      -(jordanWignerMajoranaY j * jordanWignerMajoranaX j) := by
    exact jordanWignerMajorana_anticommutes (by simp)
  unfold jordanWignerAnnihilation jordanWignerCreation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp_rw [Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [jordanWignerMajoranaX_sq, jordanWignerMajoranaY_sq, hanti]
  simp [Complex.I_mul_I]
  module

/-- Creation operators at different sites anticommute. -/
theorem jordanWignerCreation_anticommutes_of_ne
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    jordanWignerCreation i * jordanWignerCreation j =
      -(jordanWignerCreation j * jordanWignerCreation i) := by
  unfold jordanWignerCreation
  simp_rw [smul_add, smul_smul]
  apply majoranaLinearCombinations_anticommute
  all_goals apply jordanWignerMajorana_anticommutes
  all_goals intro h
  all_goals exact hij (congrArg Prod.fst h)

/-- Annihilation operators at different sites anticommute. -/
theorem jordanWignerAnnihilation_anticommutes_of_ne
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    jordanWignerAnnihilation i * jordanWignerAnnihilation j =
      -(jordanWignerAnnihilation j * jordanWignerAnnihilation i) := by
  unfold jordanWignerAnnihilation
  simp_rw [smul_add, smul_smul]
  apply majoranaLinearCombinations_anticommute
  all_goals apply jordanWignerMajorana_anticommutes
  all_goals intro h
  all_goals exact hij (congrArg Prod.fst h)

/-- Mixed creation/annihilation operators at different sites anticommute. -/
theorem jordanWignerAnnihilation_creation_anticommutes_of_ne
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    jordanWignerAnnihilation i * jordanWignerCreation j =
      -(jordanWignerCreation j * jordanWignerAnnihilation i) := by
  unfold jordanWignerAnnihilation jordanWignerCreation
  simp_rw [smul_add, smul_smul]
  apply majoranaLinearCombinations_anticommute
  all_goals apply jordanWignerMajorana_anticommutes
  all_goals intro h
  all_goals exact hij (congrArg Prod.fst h)

/-- Phase-free Jordan--Wigner fermions carry a minus sign on nearest-neighbor hopping. -/
theorem jordanWignerPhaseFreeNearestNeighborHopping_eq_neg_transverseExchange
    {n : ℕ} (j : Fin (n - 1)) :
    jordanWignerCreation (QuantumAlg.TFIM.leftSite j) *
          jordanWignerAnnihilation (QuantumAlg.TFIM.rightSite j) +
        jordanWignerCreation (QuantumAlg.TFIM.rightSite j) *
          jordanWignerAnnihilation (QuantumAlg.TFIM.leftSite j) =
      -((2 : ℂ)⁻¹ •
        (pauliMat (QuantumAlg.TFIM.xxLabel j) +
          pauliMat (jordanWignerYYLabel j))) := by
  let l := QuantumAlg.TFIM.leftSite j
  let r := QuantumAlg.TFIM.rightSite j
  have hlr : l < r := by simp [l, r, QuantumAlg.TFIM.leftSite,
    QuantumAlg.TFIM.rightSite]
  have hmix := jordanWignerAnnihilation_creation_anticommutes_of_ne
    (i := l) (j := r) (ne_of_lt hlr)
  have hreverse : jordanWignerCreation r * jordanWignerAnnihilation l =
      -(jordanWignerAnnihilation l * jordanWignerCreation r) := by
    simpa using (congrArg Neg.neg hmix).symm
  change jordanWignerCreation l * jordanWignerAnnihilation r +
      jordanWignerCreation r * jordanWignerAnnihilation l = _
  have halgebra : jordanWignerCreation l * jordanWignerAnnihilation r +
        jordanWignerCreation r * jordanWignerAnnihilation l =
      (Complex.I / 2) •
          (jordanWignerMajoranaY l * jordanWignerMajoranaX r) +
        (-Complex.I / 2) •
          (jordanWignerMajoranaX l * jordanWignerMajoranaY r) := by
    rw [hreverse]
    unfold jordanWignerCreation jordanWignerAnnihilation
    simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.add_mul, Matrix.mul_add]
    simp
    module
  rw [halgebra]
  rw [show jordanWignerMajoranaY l * jordanWignerMajoranaX r =
      Complex.I • pauliMat (QuantumAlg.TFIM.xxLabel j) by
    simpa [l, r] using jordanWignerMajoranaY_left_mul_majoranaX_right j]
  rw [show jordanWignerMajoranaX l * jordanWignerMajoranaY r =
      (-Complex.I) • pauliMat (jordanWignerYYLabel j) by
    simpa [l, r] using jordanWignerMajoranaX_left_mul_majoranaY_right j]
  simp only [smul_smul]
  have hcoefX : (Complex.I / 2) * Complex.I = -(2 : ℂ)⁻¹ := by
    calc
      Complex.I / 2 * Complex.I = Complex.I * Complex.I / 2 := by ring
      _ = -(2 : ℂ)⁻¹ := by rw [Complex.I_mul_I]; norm_num
  have hcoefY : (-Complex.I / 2) * (-Complex.I) = -(2 : ℂ)⁻¹ := by
    calc
      (-Complex.I / 2) * (-Complex.I) = Complex.I * Complex.I / 2 := by ring
      _ = -(2 : ℂ)⁻¹ := by rw [Complex.I_mul_I]; norm_num
  rw [hcoefX, hcoefY]
  module

/-- Nearest-neighbor hopping in paper gauge equals the spin transverse exchange exactly. -/
theorem paperJordanWignerNearestNeighborHopping_eq_transverseExchange
    {n : ℕ} (j : Fin (n - 1)) :
    paperJordanWignerCreation (QuantumAlg.TFIM.leftSite j) *
          paperJordanWignerAnnihilation (QuantumAlg.TFIM.rightSite j) +
        paperJordanWignerCreation (QuantumAlg.TFIM.rightSite j) *
          paperJordanWignerAnnihilation (QuantumAlg.TFIM.leftSite j) =
      (2 : ℂ)⁻¹ •
        (pauliMat (QuantumAlg.TFIM.xxLabel j) +
          pauliMat (jordanWignerYYLabel j)) := by
  let l := QuantumAlg.TFIM.leftSite j
  let r := QuantumAlg.TFIM.rightSite j
  have hg : jordanWignerOccupationGauge l * jordanWignerOccupationGauge r = -1 := by
    simpa [l, r] using jordanWignerOccupationGauge_left_mul_right j
  have hgr : jordanWignerOccupationGauge r * jordanWignerOccupationGauge l = -1 := by
    rw [mul_comm]
    exact hg
  change paperJordanWignerCreation l * paperJordanWignerAnnihilation r +
      paperJordanWignerCreation r * paperJordanWignerAnnihilation l = _
  unfold paperJordanWignerCreation paperJordanWignerAnnihilation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hg, hgr]
  simp only [neg_smul, one_smul]
  rw [show -(jordanWignerCreation l * jordanWignerAnnihilation r) +
      -(jordanWignerCreation r * jordanWignerAnnihilation l) =
    -(jordanWignerCreation l * jordanWignerAnnihilation r +
      jordanWignerCreation r * jordanWignerAnnihilation l) by module]
  rw [show jordanWignerCreation l * jordanWignerAnnihilation r +
      jordanWignerCreation r * jordanWignerAnnihilation l =
    -((2 : ℂ)⁻¹ •
      (pauliMat (QuantumAlg.TFIM.xxLabel j) +
        pauliMat (jordanWignerYYLabel j))) by
      simpa [l, r] using
        jordanWignerPhaseFreeNearestNeighborHopping_eq_neg_transverseExchange j]
  simp

/-- Concrete finite-chain canonical anticommutation system. -/
def jordanWignerFermionSystem (n : ℕ) :
    FermionSystem ℂ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (Fin n) where
  cre := jordanWignerCreation
  ann := jordanWignerAnnihilation
  κ i j := if i = j then 1 else 0
  cre_mul_cre i j := by
    by_cases hij : i = j
    · subst j
      rw [jordanWignerCreation_sq_zero]
      simp
    · exact jordanWignerCreation_anticommutes_of_ne hij
  ann_mul_ann i j := by
    by_cases hij : i = j
    · subst j
      rw [jordanWignerAnnihilation_sq_zero]
      simp
    · exact jordanWignerAnnihilation_anticommutes_of_ne hij
  ann_mul_cre i j := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have h := jordanWigner_sameSite_CAR i
      simpa [sub_eq_add_neg, add_comm] using (eq_sub_of_add_eq h)
    · rw [if_neg hij]
      simpa using jordanWignerAnnihilation_creation_anticommutes_of_ne hij

/-- The concrete fermionic field `c†_j + c_j` is the first Jordan--Wigner Majorana. -/
theorem jordanWignerFermionSystem_field_eq_majoranaX
    (n : ℕ) (j : Fin n) :
    (jordanWignerFermionSystem n).field j = jordanWignerMajoranaX j := by
  unfold FermionSystem.field jordanWignerFermionSystem
    jordanWignerCreation jordanWignerAnnihilation
  module

/-- Unconditional Wick expansion for ordered products of concrete chain Majoranas. -/
theorem jordanWignerMajoranaX_prod_eq_signedPairingExpand
    (n : ℕ) (l : List (Fin n)) :
    (l.map jordanWignerMajoranaX).prod =
      signedPairingExpand ℂ (fun i j : Fin n => if i = j then 1 else 0)
        (jordanWignerFermionSystem n).nordField l := by
  have hwick := (jordanWignerFermionSystem n).prod_field_eq_signedPairingExpand l
  have hfield : (jordanWignerFermionSystem n).field =
      (fun j => jordanWignerMajoranaX j) := by
    funext j
    exact jordanWignerFermionSystem_field_eq_majoranaX n j
  rw [hfield] at hwick
  simpa [jordanWignerFermionSystem] using hwick

/-- Occupation number at `j`. -/
def jordanWignerNumber {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  jordanWignerCreation j * jordanWignerAnnihilation j

/-- Paper's local dictionary: `n_j = c†_j c_j = (1 + Z_j)/2`. -/
theorem jordanWignerNumber_eq_half_one_add_pauliZ {n : ℕ} (j : Fin n) :
    jordanWignerNumber j =
      (2 : ℂ)⁻¹ • (1 + pauliMat (QuantumAlg.TFIM.zLabel j)) := by
  have hanti : jordanWignerMajoranaY j * jordanWignerMajoranaX j =
      -(jordanWignerMajoranaX j * jordanWignerMajoranaY j) := by
    exact jordanWignerMajorana_anticommutes (by simp)
  unfold jordanWignerNumber jordanWignerCreation jordanWignerAnnihilation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_add]
  simp_rw [Matrix.mul_smul]
  rw [jordanWignerMajoranaX_sq, jordanWignerMajoranaY_sq,
    jordanWignerMajoranaX_mul_majoranaY, hanti,
    jordanWignerMajoranaX_mul_majoranaY]
  ext p q
  by_cases hpq : p = q <;>
    simp [Matrix.smul_apply, Matrix.add_apply, hpq] <;>
    ring_nf <;>
    simp <;>
    ring

/-- Local physical spin `Sᶻ_j = Z_j/2`. -/
def jordanWignerLocalSpinZ {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (2 : ℂ)⁻¹ • pauliMat (QuantumAlg.TFIM.zLabel j)

/-- Equivalent local form of the paper's number--magnetization dictionary:
`Sᶻ_j = n_j - 1/2`. -/
theorem jordanWignerLocalSpinZ_eq_number_sub_half {n : ℕ} (j : Fin n) :
    jordanWignerLocalSpinZ j =
      jordanWignerNumber j -
        (2 : ℂ)⁻¹ • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  rw [jordanWignerNumber_eq_half_one_add_pauliZ]
  simp [jordanWignerLocalSpinZ, smul_add]

/-- Equivalent occupation decomposition `n_j = Sᶻ_j + 1/2`. -/
theorem jordanWignerNumber_eq_spinZ_add_half {n : ℕ} (j : Fin n) :
    jordanWignerNumber j =
      jordanWignerLocalSpinZ j +
        (2 : ℂ)⁻¹ • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  rw [jordanWignerLocalSpinZ_eq_number_sub_half]
  module

/-- Exact density-interaction expansion.  It records the linear and scalar corrections hidden
when the spin/fermion Hamiltonians are identified only up to field shifts and energy offset. -/
theorem jordanWignerDensityDensity_eq_spinZZ_add_corrections
    {n : ℕ} (i j : Fin n) :
    jordanWignerNumber i * jordanWignerNumber j =
      jordanWignerLocalSpinZ i * jordanWignerLocalSpinZ j +
        (2 : ℂ)⁻¹ • jordanWignerLocalSpinZ i +
        (2 : ℂ)⁻¹ • jordanWignerLocalSpinZ j +
        (4 : ℂ)⁻¹ •
          (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  rw [jordanWignerNumber_eq_spinZ_add_half,
    jordanWignerNumber_eq_spinZ_add_half]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  module

/-- Occupation number built from paper-gauge fermions. -/
def paperJordanWignerNumber {n : ℕ} (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  paperJordanWignerCreation j * paperJordanWignerAnnihilation j

/-- Site gauge cancels from number operators. -/
theorem paperJordanWignerNumber_eq_jordanWignerNumber
    {n : ℕ} (j : Fin n) :
    paperJordanWignerNumber j = jordanWignerNumber j := by
  unfold paperJordanWignerNumber paperJordanWignerCreation
    paperJordanWignerAnnihilation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    jordanWignerOccupationGauge_sq, one_smul]
  rfl

/-- Open-chain spinless-fermion Hamiltonian from Eq. (18). -/
def paperJordanWignerFermionHamiltonian
    (n : ℕ) (t V : ℂ) (H : Fin n → ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (∑ j : Fin (n - 1), (-t) •
    (paperJordanWignerCreation (QuantumAlg.TFIM.leftSite j) *
        paperJordanWignerAnnihilation (QuantumAlg.TFIM.rightSite j) +
      paperJordanWignerCreation (QuantumAlg.TFIM.rightSite j) *
        paperJordanWignerAnnihilation (QuantumAlg.TFIM.leftSite j))) +
  (∑ j : Fin (n - 1), V •
    (paperJordanWignerNumber (QuantumAlg.TFIM.leftSite j) *
      paperJordanWignerNumber (QuantumAlg.TFIM.rightSite j))) +
  ∑ i : Fin n, H i • paperJordanWignerNumber i

/-- Exact spin image of Eq. (18), retaining interaction-induced field shifts and scalar offsets. -/
def paperJordanWignerCorrectedSpinHamiltonian
    (n : ℕ) (t V : ℂ) (H : Fin n → ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (∑ j : Fin (n - 1), (-t / 2) •
    (pauliMat (QuantumAlg.TFIM.xxLabel j) +
      pauliMat (jordanWignerYYLabel j))) +
  (∑ j : Fin (n - 1), V •
    (jordanWignerLocalSpinZ (QuantumAlg.TFIM.leftSite j) *
        jordanWignerLocalSpinZ (QuantumAlg.TFIM.rightSite j) +
      (2 : ℂ)⁻¹ • jordanWignerLocalSpinZ (QuantumAlg.TFIM.leftSite j) +
      (2 : ℂ)⁻¹ • jordanWignerLocalSpinZ (QuantumAlg.TFIM.rightSite j) +
      (4 : ℂ)⁻¹ • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))) +
  ∑ i : Fin n, H i •
    (jordanWignerLocalSpinZ i +
      (2 : ℂ)⁻¹ • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))

/-- Complete paper-gauge Jordan--Wigner Hamiltonian identity. -/
theorem paperJordanWignerFermionHamiltonian_eq_correctedSpinHamiltonian
    (n : ℕ) (t V : ℂ) (H : Fin n → ℂ) :
    paperJordanWignerFermionHamiltonian n t V H =
      paperJordanWignerCorrectedSpinHamiltonian n t V H := by
  classical
  unfold paperJordanWignerFermionHamiltonian
    paperJordanWignerCorrectedSpinHamiltonian
  simp_rw [paperJordanWignerNearestNeighborHopping_eq_transverseExchange,
    paperJordanWignerNumber_eq_jordanWignerNumber,
    jordanWignerDensityDensity_eq_spinZZ_add_corrections,
    jordanWignerNumber_eq_spinZ_add_half, smul_smul]
  congr 2

/-- Total fermion number. -/
def jordanWignerTotalNumber (n : ℕ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  ∑ j, jordanWignerNumber j

/-- Total spin magnetization `M_z = (1/2) ∑ Z_j`. -/
def jordanWignerTotalMagnetization (n : ℕ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (2 : ℂ)⁻¹ • ∑ j, pauliMat (QuantumAlg.TFIM.zLabel j)

/-- Particle number and spin magnetization differ only by the scalar `n/2`. -/
theorem jordanWignerTotalNumber_eq_magnetization_add_scalar (n : ℕ) :
    jordanWignerTotalNumber n =
      jordanWignerTotalMagnetization n +
        ((n : ℂ) / 2) • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  classical
  unfold jordanWignerTotalNumber jordanWignerTotalMagnetization
  simp_rw [jordanWignerNumber_eq_half_one_add_pauliZ, smul_add]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum]
  simp [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.smul_sum, add_comm]
  congr 1
  ext p q
  by_cases hpq : p = q <;>
    simp [Matrix.smul_apply, Matrix.natCast_apply, hpq, div_eq_mul_inv] ;
    ring

/-- Consequently particle-number and magnetization commutators are identical. -/
theorem jordanWigner_numberCommutator_eq_magnetizationCommutator
    (n : ℕ) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    A * jordanWignerTotalNumber n - jordanWignerTotalNumber n * A =
      A * jordanWignerTotalMagnetization n - jordanWignerTotalMagnetization n * A := by
  rw [jordanWignerTotalNumber_eq_magnetization_add_scalar]
  simp [Matrix.mul_add, Matrix.add_mul]

end

end GaloisForLFunctions.HTGeometry

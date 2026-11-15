import GaloisForLFunctions.HTGeometry.LinearAlgebra.NilpotentDilation
import GaloisForLFunctions.HTGeometry.JordanWignerSpinFermionBridge

/-!
# Fermion scaling rigidity and parity symmetry

A creation/annihilation pair satisfying the canonical anticommutation relation
admits simultaneous scales `q,r` exactly when `q*r = 1`. The occupation operator
is fixed by every such rescaling. Consequently a common positive scale is one,
even though each individual creation or annihilation operator is nilpotent.

For the concrete Jordan--Wigner pair, occupation parity is a nontrivial unitary
involution. Its conjugation flips both fermion generators and fixes the
occupation clock. Thus scalar rigidity coexists with nontrivial operator
holonomy in the clock's commutant.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open NormedSpace
open scoped Matrix Matrix.Norms.Frobenius

section CAR
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Occupation number is an Euler operator for creation. -/
theorem car_number_euler (C A : Matrix ι ι ℂ) (hCC : C * C = 0)
    (hAC : A * C + C * A = 1) : (C * A) * C - C * (C * A) = C := by
  have he := congrArg (fun X => C * X) hAC
  rw [mul_add, mul_one, ← mul_assoc C C A, hCC, zero_mul, add_zero] at he
  rw [mul_assoc C A C, he, ← mul_assoc C C A, hCC, zero_mul, sub_zero]

/-- Negative occupation number is an Euler operator for annihilation. -/
theorem car_negative_number_euler (C A : Matrix ι ι ℂ) (hAA : A * A = 0)
    (hAC : A * C + C * A = 1) : -(C * A) * A - A * -(C * A) = A := by
  have he := congrArg (fun X => X * A) hAC
  rw [add_mul, one_mul, mul_assoc C A A, hAA, mul_zero, add_zero] at he
  rw [neg_mul, mul_neg, mul_assoc C A A, hAA, mul_zero, neg_zero, zero_sub, neg_neg,
    ← mul_assoc A C A, he]

/-- Exponentiating occupation number gives reciprocal scales of a fermion pair. -/
theorem exists_car_scale (C A : Matrix ι ι ℂ) (hCC : C * C = 0) (hAA : A * A = 0)
    (hAC : A * C + C * A = 1) (q : ℂ) (hq : q ≠ 0) :
    ∃ e : Matrix ι ι ℂ ≃ₐ[ℂ] Matrix ι ι ℂ, e C = q • C ∧ e A = q⁻¹ • A := by
  let e := clockInnerAlgEquiv (K := ℂ) (clockExpUnit (K := ℂ) (Complex.log q • (C * A)))
  refine ⟨e, ?_, ?_⟩
  · change clockInnerAlgEquiv _ C = _
    rw [clockEuler_exponential _ _ (car_number_euler C A hCC hAC),
      ← Complex.exp_eq_exp_ℂ, Complex.exp_log hq]
  · have h := clockEuler_exponential (-(C * A)) A
      (car_negative_number_euler C A hAA hAC) (-Complex.log q)
    simp only [neg_smul, smul_neg, neg_neg, ← Complex.exp_eq_exp_ℂ,
      Complex.exp_neg, Complex.exp_log hq] at h
    exact h

/-- The canonical anticommutation relation forces reciprocal simultaneous scales. -/
theorem car_scale_product_eq_one [Nonempty ι] (C A : Matrix ι ι ℂ)
    (hAC : A * C + C * A = 1) (e : Matrix ι ι ℂ ≃ₐ[ℂ] Matrix ι ι ℂ)
    (q r : ℂ) (hC : e C = q • C) (hA : e A = r • A) : q * r = 1 := by
  have he := congrArg e hAC
  rw [map_add, map_mul, map_mul, map_one, hC, hA,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm r q, ← smul_add, hAC] at he
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi := congrFun (congrFun he i) i
  simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hi

/-- Exact simultaneous scaling classification for a finite fermion pair. -/
theorem exists_car_scale_iff [Nonempty ι] (C A : Matrix ι ι ℂ)
    (hCC : C * C = 0) (hAA : A * A = 0) (hAC : A * C + C * A = 1) (q r : ℂ) :
    (∃ e : Matrix ι ι ℂ ≃ₐ[ℂ] Matrix ι ι ℂ, e C = q • C ∧ e A = r • A) ↔ q * r = 1 := by
  constructor
  · rintro ⟨e, hC, hA⟩
    exact car_scale_product_eq_one C A hAC e q r hC hA
  · intro hqr
    have hq : q ≠ 0 := by
      intro h
      rw [h, zero_mul] at hqr
      exact zero_ne_one hqr
    have hr : r = q⁻¹ := by
      calc
        r = q⁻¹ * (q * r) := by rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul]
        _ = q⁻¹ := by rw [hqr, mul_one]
    rw [hr]
    exact exists_car_scale C A hCC hAA hAC q hq

/-- Occupation number is idempotent. -/
theorem car_number_idempotent (C A : Matrix ι ι ℂ) (hCC : C * C = 0)
    (hAC : A * C + C * A = 1) : (C * A) * (C * A) = C * A := by
  have he := congrArg (fun X => C * X) hAC
  rw [mul_add, mul_one, ← mul_assoc C C A, hCC, zero_mul, add_zero] at he
  rw [← mul_assoc (C * A) C A, mul_assoc C A C, he]

/-- Occupation parity, an involutive algebra unit. -/
def carParityUnit (C A : Matrix ι ι ℂ) (hCC : C * C = 0)
    (hAC : A * C + C * A = 1) : (Matrix ι ι ℂ)ˣ := by
  let P := C * A
  have hp : P * P = P := car_number_idempotent C A hCC hAC
  have h : (1 - (2 : ℂ) • P) * (1 - (2 : ℂ) • P) = 1 := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hp]
    module
  exact ⟨1 - (2 : ℂ) • P, 1 - (2 : ℂ) • P, h, h⟩

/-- Occupation parity reverses the creation operator. -/
theorem carParity_creation (C A : Matrix ι ι ℂ) (hCC : C * C = 0)
    (hAC : A * C + C * A = 1) :
    clockInnerAlgEquiv (K := ℂ) (carParityUnit C A hCC hAC) C = -C := by
  have hPC : (C * A) * C = C := by
    have h := car_number_euler C A hCC hAC
    rwa [← mul_assoc C C A, hCC, zero_mul, sub_zero] at h
  have hCP : C * (C * A) = 0 := by rw [← mul_assoc, hCC, zero_mul]
  change (1 - (2 : ℂ) • (C * A)) * C * (1 - (2 : ℂ) • (C * A)) = -C
  rw [sub_mul, one_mul, Matrix.smul_mul, hPC, sub_mul, mul_sub, mul_one,
    Matrix.mul_smul, hCP, smul_zero, sub_zero, Matrix.smul_mul, mul_sub,
    mul_one, Matrix.mul_smul, hCP, smul_zero, sub_zero]
  module

/-- Occupation parity reverses the annihilation operator. -/
theorem carParity_annihilation (C A : Matrix ι ι ℂ) (hCC : C * C = 0)
    (hAA : A * A = 0) (hAC : A * C + C * A = 1) :
    clockInnerAlgEquiv (K := ℂ) (carParityUnit C A hCC hAC) A = -A := by
  have hPA : (C * A) * A = 0 := by rw [mul_assoc, hAA, mul_zero]
  have hAP : A * (C * A) = A := by
    have h := congrArg (fun X => X * A) hAC
    rw [add_mul, one_mul, hPA, add_zero, mul_assoc] at h
    exact h
  change (1 - (2 : ℂ) • (C * A)) * A * (1 - (2 : ℂ) • (C * A)) = -A
  rw [sub_mul, one_mul, Matrix.smul_mul, hPA, smul_zero, sub_zero,
    mul_sub, mul_one, Matrix.mul_smul, hAP]
  module

/-- Conjugation by occupation parity is an involution. -/
theorem carParity_involution (C A : Matrix ι ι ℂ) (hCC : C * C = 0)
    (hAC : A * C + C * A = 1) :
    clockInnerAlgEquiv (K := ℂ) (carParityUnit C A hCC hAC) *
      clockInnerAlgEquiv (K := ℂ) (carParityUnit C A hCC hAC) = 1 := by
  let u := carParityUnit C A hCC hAC
  have hv : u.inv = u.val := rfl
  have hu : u.val * u.val = 1 := by simpa only [hv] using u.val_inv
  apply AlgEquiv.ext
  intro X
  change u.val * (u.val * X * u.inv) * u.inv = X
  rw [hv]
  calc
    u.val * (u.val * X * u.val) * u.val = (u.val * u.val) * X * (u.val * u.val) := by
      simp only [mul_assoc]
    _ = X := by rw [hu, one_mul, mul_one]

end CAR

/-- Reciprocity exactly characterizes simultaneous scaling of the actual Jordan--Wigner pair. -/
theorem jordanWigner_pair_scale_iff {n : ℕ} (j : Fin n) (q r : ℂ) :
    (∃ e : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ ≃ₐ[ℂ]
        Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      e (jordanWignerCreation j) = q • jordanWignerCreation j ∧
      e (jordanWignerAnnihilation j) = r • jordanWignerAnnihilation j) ↔ q * r = 1 :=
  exists_car_scale_iff _ _ (jordanWignerCreation_sq_zero j)
    (jordanWignerAnnihilation_sq_zero j) (jordanWigner_sameSite_CAR j) q r

/-- Every compatible rescaling fixes the actual occupation clock. -/
theorem jordanWigner_number_fixed_of_pair_scale {n : ℕ} (j : Fin n)
    (e : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (q r : ℂ) (hC : e (jordanWignerCreation j) = q • jordanWignerCreation j)
    (hA : e (jordanWignerAnnihilation j) = r • jordanWignerAnnihilation j) :
    e (jordanWignerNumber j) = jordanWignerNumber j := by
  have hqr := car_scale_product_eq_one _ _ (jordanWigner_sameSite_CAR j) e q r hC hA
  rw [jordanWignerNumber, map_mul, hC, hA, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hqr, one_smul]

/-- The actual fermion pair has no common nonunit positive scale. -/
theorem jordanWigner_positive_common_scale_iff {n : ℕ} (j : Fin n)
    (q : ℝ) (hq : 0 < q) :
    (∃ e : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ ≃ₐ[ℂ]
        Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      e (jordanWignerCreation j) = (q : ℂ) • jordanWignerCreation j ∧
      e (jordanWignerAnnihilation j) = (q : ℂ) • jordanWignerAnnihilation j) ↔ q = 1 := by
  rw [jordanWigner_pair_scale_iff]
  constructor
  · intro h
    have hr : q * q = 1 := Complex.ofReal_injective
      (by simpa only [Complex.ofReal_mul, Complex.ofReal_one] using h)
    have hz : (q - 1) * (q + 1) = 0 := by nlinarith only [hr]
    rcases mul_eq_zero.mp hz with hm | hp
    · exact sub_eq_zero.mp hm
    · linarith only [hq, hp]
  · rintro rfl
    simp only [Complex.ofReal_one, one_mul]

/-- A nontrivial involution flips both fermions and fixes their occupation clock. -/
theorem jordanWigner_parity_involution {n : ℕ} (j : Fin n) :
    ∃ e : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ ≃ₐ[ℂ]
        Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      e ≠ 1 ∧ e * e = 1 ∧ e (jordanWignerCreation j) = -jordanWignerCreation j ∧
      e (jordanWignerAnnihilation j) = -jordanWignerAnnihilation j ∧
      e (jordanWignerNumber j) = jordanWignerNumber j := by
  let C := jordanWignerCreation j
  let A := jordanWignerAnnihilation j
  have hCC := jordanWignerCreation_sq_zero j
  have hAA := jordanWignerAnnihilation_sq_zero j
  have hAC := jordanWigner_sameSite_CAR j
  let e := clockInnerAlgEquiv (K := ℂ) (carParityUnit C A hCC hAC)
  have hc := carParity_creation C A hCC hAC
  have ha := carParity_annihilation C A hCC hAA hAC
  have hn := jordanWigner_number_fixed_of_pair_scale j e (-1) (-1)
    (by simpa only [neg_smul, one_smul] using hc)
    (by simpa only [neg_smul, one_smul] using ha)
  refine ⟨e, ?_, carParity_involution C A hCC hAC, hc, ha, hn⟩
  intro he
  have hC : C ≠ 0 := by
    intro hz
    have h := hAC
    change A * C + C * A = 1 at h
    rw [hz, mul_zero, zero_mul, zero_add] at h
    exact zero_ne_one h
  change e C = -C at hc
  rw [he] at hc
  change C = -C at hc
  have hz : (2 : ℂ) • C = 0 := by
    rw [two_smul]
    calc
      C + C = -C + C := congrArg (fun X => X + C) hc
      _ = 0 := neg_add_cancel C
  exact hC ((smul_eq_zero.mp hz).resolve_left (by norm_num))

/-- The explicit occupation-parity unit is unitary. -/
theorem jordanWigner_parity_unitary {n : ℕ} (j : Fin n) :
    let u := carParityUnit (jordanWignerCreation j) (jordanWignerAnnihilation j)
      (jordanWignerCreation_sq_zero j) (jordanWigner_sameSite_CAR j)
    u.valᴴ * u.val = 1 := by
  dsimp only
  let C := jordanWignerCreation j
  let A := jordanWignerAnnihilation j
  let u := carParityUnit C A (jordanWignerCreation_sq_zero j) (jordanWigner_sameSite_CAR j)
  have hA : Aᴴ = C := by
    change (jordanWignerAnnihilation j)ᴴ = jordanWignerCreation j
    rw [← jordanWignerCreation_conjTranspose j, Matrix.conjTranspose_conjTranspose]
  have hN : (C * A)ᴴ = C * A := by
    rw [Matrix.conjTranspose_mul, hA, jordanWignerCreation_conjTranspose]
  have hP : u.valᴴ = u.val := by
    change (1 - (2 : ℂ) • (C * A))ᴴ = 1 - (2 : ℂ) • (C * A)
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hN, star_ofNat]
  have hv : u.inv = u.val := rfl
  change u.valᴴ * u.val = 1
  rw [hP]
  simpa only [hv] using u.val_inv

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.exists_car_scale_iff
#print axioms GaloisForLFunctions.HTGeometry.jordanWigner_pair_scale_iff
#print axioms GaloisForLFunctions.HTGeometry.jordanWigner_number_fixed_of_pair_scale
#print axioms GaloisForLFunctions.HTGeometry.jordanWigner_positive_common_scale_iff
#print axioms GaloisForLFunctions.HTGeometry.jordanWigner_parity_involution
#print axioms GaloisForLFunctions.HTGeometry.jordanWigner_parity_unitary

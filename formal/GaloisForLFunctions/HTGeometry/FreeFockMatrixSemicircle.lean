import GaloisForLFunctions.HTGeometry.MatrixSemicircleDysonFormalAlgebraicity
import GaloisForLFunctions.HTGeometry.HamburgerExistence
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.PowerSeries.Substitution

open scoped BigOperators Matrix
open Matrix
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

abbrev FreeFockVector (I K : Type*) := (I × List K) →₀ ℂ

def freeFockCreationBasisAction (A : K → Matrix I I ℂ) (jw : I × List K) :
    FreeFockVector I K :=
  ∑ k : K, ∑ i : I, Finsupp.single (i, k :: jw.2) (A k i jw.1)

def freeFockAnnihilationBasisAction (A : K → Matrix I I ℂ) (jw : I × List K) :
    FreeFockVector I K :=
  match jw.2 with
  | [] => 0
  | k :: w => ∑ i : I, Finsupp.single (i, w) (A k i jw.1)

def freeFockBasisAction (A : K → Matrix I I ℂ) (jw : I × List K) :
    FreeFockVector I K :=
  freeFockCreationBasisAction A jw + freeFockAnnihilationBasisAction A jw

def freeFockAction (A : K → Matrix I I ℂ) :
    FreeFockVector I K →ₗ[ℂ] FreeFockVector I K :=
  Finsupp.linearCombination ℂ (freeFockBasisAction A)

omit [DecidableEq I] [DecidableEq K] in
@[simp] theorem freeFockAction_single (A : K → Matrix I I ℂ)
    (jw : I × List K) (c : ℂ) :
    freeFockAction A (Finsupp.single jw c) = c • freeFockBasisAction A jw := by
  simp [freeFockAction]

def freeFockInner (x y : FreeFockVector I K) : ℂ :=
  x.sum fun a c => star c * y a

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
@[simp] theorem freeFockInner_single_left (a : I × List K) (c : ℂ)
    (y : FreeFockVector I K) :
    freeFockInner (Finsupp.single a c) y = star c * y a := by
  simp [freeFockInner]

theorem freeFockCreationBasisAction_apply_cons
    (A : K → Matrix I I ℂ) (j i : I) (l : K) (w u : List K) :
    freeFockCreationBasisAction A (j, w) (i, l :: u) =
      if u = w then A l i j else 0 := by
  classical
  change (∑ k : K, ∑ i' : I, Finsupp.single (i', k :: w) (A k i' j))
      (i, l :: u) = _
  simp only [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  by_cases huw : u = w
  · subst u
    simp only [ite_true]
    rw [Finset.sum_eq_single l]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hi'
        simp [hi']
      · simp
    · intro l' _ hl'
      apply Finset.sum_eq_zero
      intro i' _
      simp [hl']
    · simp
  · have hwu : w ≠ u := Ne.symm huw
    simp [hwu]
    intro h
    exact (huw h).elim

omit [Fintype K] in
theorem freeFockAnnihilationBasisAction_apply_cons
    (A : K → Matrix I I ℂ) (j i : I) (l : K) (w u : List K) :
    freeFockAnnihilationBasisAction A (i, l :: u) (j, w) =
      if w = u then A l j i else 0 := by
  classical
  change (∑ i' : I, Finsupp.single (i', u) (A l i' i)) (j, w) = _
  simp only [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  by_cases hwu : w = u
  · subst w
    simp only [ite_true]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [hj']
    · simp
  · have huw : u ≠ w := Ne.symm hwu
    simp [huw]
    intro h
    exact (hwu h).elim

theorem star_freeFockBasisAction_apply
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (a b : I × List K) :
    star (freeFockBasisAction A a b) = freeFockBasisAction A b a := by
  have hentry : ∀ k i j, star (A k i j) = A k j i := by
    intro k i j
    have h := congr_fun (congr_fun (hA k) j) i
    simpa [Matrix.conjTranspose_apply] using h
  have hcreate : ∀ a b : I × List K,
      star (freeFockCreationBasisAction A a b) =
        freeFockAnnihilationBasisAction A b a := by
    intro a b
    rcases a with ⟨j, w⟩
    rcases b with ⟨i, u⟩
    cases u with
    | nil => simp [freeFockCreationBasisAction, freeFockAnnihilationBasisAction]
    | cons l u =>
        rw [freeFockCreationBasisAction_apply_cons,
          freeFockAnnihilationBasisAction_apply_cons]
        by_cases huw : u = w
        · subst w
          simp [hentry]
        · have hwu : w ≠ u := Ne.symm huw
          simp [huw, hwu]
  have hannih : star (freeFockAnnihilationBasisAction A a b) =
      freeFockCreationBasisAction A b a := by
    have h := congrArg star (hcreate b a)
    simpa only [star_star] using h.symm
  rw [freeFockBasisAction, Finsupp.add_apply]
  change (starRingEnd ℂ) (freeFockCreationBasisAction A a b +
      freeFockAnnihilationBasisAction A a b) = _
  rw [map_add]
  change star (freeFockCreationBasisAction A a b) +
      star (freeFockAnnihilationBasisAction A a b) = _
  rw [hcreate a b, hannih, freeFockBasisAction, Finsupp.add_apply, add_comm]

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
@[simp] theorem freeFockInner_zero_left (y : FreeFockVector I K) :
    freeFockInner 0 y = 0 := by
  simp [freeFockInner]

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
@[simp] theorem freeFockInner_zero_right (x : FreeFockVector I K) :
    freeFockInner x 0 = 0 := by
  simp [freeFockInner]

omit [Fintype I] [Fintype K] in
theorem freeFockInner_add_left (x y z : FreeFockVector I K) :
    freeFockInner (x + y) z = freeFockInner x z + freeFockInner y z := by
  rw [freeFockInner, Finsupp.sum_add_index]
  · rfl
  · intro a ha
    simp
  · intro a ha c d
    simp [add_mul]

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem freeFockInner_add_right (x y z : FreeFockVector I K) :
    freeFockInner x (y + z) = freeFockInner x y + freeFockInner x z := by
  simp [freeFockInner, mul_add, Finsupp.sum_add]

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem freeFockInner_smul_left (c : ℂ) (x y : FreeFockVector I K) :
    freeFockInner (c • x) y = star c * freeFockInner x y := by
  rw [freeFockInner, Finsupp.sum_smul_index]
  · rw [freeFockInner, Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro a ha
    change (starRingEnd ℂ) (c * x a) * y a = _
    rw [map_mul]
    simp only [starRingEnd_apply]
    ring_nf
  · intro a
    simp

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem freeFockInner_smul_right (c : ℂ) (x y : FreeFockVector I K) :
    freeFockInner x (c • y) = c * freeFockInner x y := by
  rw [freeFockInner, freeFockInner, Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro a ha
  simp [Finsupp.smul_apply]
  ring

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem freeFockInner_single_right (x : FreeFockVector I K)
    (a : I × List K) (c : ℂ) :
    freeFockInner x (Finsupp.single a c) = star (x a) * c := by
  classical
  rw [freeFockInner]
  by_cases ha : a ∈ x.support
  · rw [Finsupp.sum, Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      simp [hba]
    · intro h
      exact (h ha).elim
  · have hxa : x a = 0 := Finsupp.notMem_support_iff.mp ha
    rw [Finsupp.sum]
    have hz : ∀ b ∈ x.support, star (x b) * Finsupp.single a c b = 0 := by
      intro b hb
      have hba : b ≠ a := by
        intro h
        subst b
        exact ha hb
      simp [hba]
    rw [Finset.sum_eq_zero hz, hxa]
    simp

theorem freeFockInner_basis_single
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (a b : I × List K) (c : ℂ) :
    freeFockInner (freeFockBasisAction A a) (Finsupp.single b c) =
      c * freeFockBasisAction A b a := by
  rw [freeFockInner_single_right, star_freeFockBasisAction_apply A hA a b]
  ring

theorem freeFockInner_basis_action
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (a : I × List K) (y : FreeFockVector I K) :
    freeFockInner (freeFockBasisAction A a) y = freeFockAction A y a := by
  classical
  induction y using Finsupp.induction with
  | zero => simp [freeFockAction]
  | @single_add b c y hb hc ih =>
      rw [freeFockInner_add_right, map_add,
        Finsupp.add_apply, ih, freeFockInner_basis_single A hA a b c,
        freeFockAction_single, Finsupp.smul_apply, smul_eq_mul]

theorem freeFockAction_symmetric
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x y : FreeFockVector I K) :
    freeFockInner (freeFockAction A x) y = freeFockInner x (freeFockAction A y) := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add a c x ha hc ih =>
      rw [map_add, freeFockInner_add_left, freeFockInner_add_left, ih,
        freeFockAction_single, freeFockInner_smul_left, freeFockInner_single_left,
        freeFockInner_basis_action A hA]

noncomputable def evenPowerSeriesSubstHom : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.X_pow (by omega : 2 ≠ 0))

@[simp]
theorem evenPowerSeriesSubstHom_X :
    evenPowerSeriesSubstHom PowerSeries.X = (PowerSeries.X : PowerSeries ℂ) ^ (2 : ℕ) := by
  exact PowerSeries.substAlgHom_X
    (PowerSeries.HasSubst.X_pow (by omega : 2 ≠ 0))

theorem evenPowerSeriesSubstHom_apply (f : PowerSeries ℂ) :
    evenPowerSeriesSubstHom f =
      PowerSeries.subst ((PowerSeries.X : PowerSeries ℂ) ^ (2 : ℕ)) f := by
  exact congrFun (PowerSeries.coe_substAlgHom
    (PowerSeries.HasSubst.X_pow (by omega : 2 ≠ 0))) f

@[simp]
theorem evenPowerSeriesSubstHom_C (c : ℂ) :
    evenPowerSeriesSubstHom (PowerSeries.C c) = PowerSeries.C c := by
  rw [PowerSeries.C_eq_algebraMap]
  exact AlgHom.commutes evenPowerSeriesSubstHom c

def matrixDysonResolventSeries (A : K → Matrix I I ℂ) :
    Matrix I I (PowerSeries ℂ) :=
  fun i j => evenPowerSeriesSubstHom (matrixDysonFormalSeries A i j)

omit [DecidableEq K] in
@[simp]
theorem matrixDysonResolventSeries_coeff (A : K → Matrix I I ℂ) (n : ℕ) (i j : I) :
    PowerSeries.coeff n (matrixDysonResolventSeries A i j) =
      if 2 ∣ n then matrixDysonFormalCoeff A (n / 2) i j else 0 := by
  rw [matrixDysonResolventSeries, evenPowerSeriesSubstHom_apply]
  rw [PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ) (by omega : (2 : ℕ) ≠ 0)]
  simp

omit [DecidableEq I] [DecidableEq K] in
theorem evenPowerSeriesSubstHom_covariance
    (A : K → Matrix I I ℂ) (H : Matrix I I (PowerSeries ℂ)) (i j : I) :
    evenPowerSeriesSubstHom (matrixSemicircleCovariancePowerSeries A H i j) =
      matrixSemicircleCovariancePowerSeries A
        (fun p q => evenPowerSeriesSubstHom (H p q)) i j := by
  simp only [matrixSemicircleCovariancePowerSeries, Matrix.sum_apply, map_sum,
    Matrix.mul_apply, map_mul, constantPowerSeriesMatrix, Matrix.conjTranspose_apply,
    evenPowerSeriesSubstHom_C]

omit [DecidableEq I] [DecidableEq K] in
theorem evenPowerSeriesSubstHom_covariance_mul
    (A : K → Matrix I I ℂ) (H : Matrix I I (PowerSeries ℂ)) (i j : I) :
    evenPowerSeriesSubstHom
        ((matrixSemicircleCovariancePowerSeries A H * H) i j) =
      (matrixSemicircleCovariancePowerSeries A
        (fun p q => evenPowerSeriesSubstHom (H p q)) *
          (show Matrix I I (PowerSeries ℂ) from
            fun p q => evenPowerSeriesSubstHom (H p q))) i j := by
  simp only [Matrix.mul_apply, map_sum, map_mul,
    evenPowerSeriesSubstHom_covariance]

omit [DecidableEq K] in
theorem matrixDysonResolventSeries_eq (A : K → Matrix I I ℂ) :
    matrixDysonResolventSeries A = 1 + (PowerSeries.X ^ (2 : ℕ) : PowerSeries ℂ) •
      (matrixSemicircleCovariancePowerSeries A (matrixDysonResolventSeries A) *
        matrixDysonResolventSeries A) := by
  let φ := evenPowerSeriesSubstHom
  have h := congrArg (fun H : Matrix I I (PowerSeries ℂ) => fun i j => φ (H i j))
    (matrixDysonFormalSeries_eq A)
  funext i j
  have hij := congr_fun (congr_fun h i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul] at hij
  change evenPowerSeriesSubstHom (matrixDysonFormalSeries A i j) = _
  rw [hij]
  rw [show φ PowerSeries.X = (PowerSeries.X : PowerSeries ℂ) ^ (2 : ℕ) by
    exact evenPowerSeriesSubstHom_X]
  rw [show φ ((matrixSemicircleCovariancePowerSeries A (matrixDysonFormalSeries A) *
      matrixDysonFormalSeries A) i j) =
      (matrixSemicircleCovariancePowerSeries A (matrixDysonResolventSeries A) *
        matrixDysonResolventSeries A) i j by
    exact evenPowerSeriesSubstHom_covariance_mul A (matrixDysonFormalSeries A) i j]
  by_cases hij' : i = j
  · subst j
    simp
  · simp [hij']

def freeFockResolventWordMatrix (A : K → Matrix I I ℂ) :
    List K → Matrix I I (PowerSeries ℂ)
  | [] => matrixDysonResolventSeries A
  | k :: w => matrixDysonResolventSeries A * constantPowerSeriesMatrix (A k) *
      freeFockResolventWordMatrix A w

omit [DecidableEq K] in
@[simp]
theorem freeFockResolventWordMatrix_nil (A : K → Matrix I I ℂ) :
    freeFockResolventWordMatrix A [] = matrixDysonResolventSeries A := rfl

omit [DecidableEq K] in
@[simp]
theorem freeFockResolventWordMatrix_cons (A : K → Matrix I I ℂ) (k : K) (w : List K) :
    freeFockResolventWordMatrix A (k :: w) =
      matrixDysonResolventSeries A * constantPowerSeriesMatrix (A k) *
        freeFockResolventWordMatrix A w := rfl

omit [DecidableEq K] in
theorem freeFockResolventWordMatrix_nil_eq
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k) :
    freeFockResolventWordMatrix A [] = 1 +
      (PowerSeries.X ^ (2 : ℕ) : PowerSeries ℂ) •
        ∑ k : K, constantPowerSeriesMatrix (A k) *
          freeFockResolventWordMatrix A [k] := by
  rw [freeFockResolventWordMatrix_nil, matrixDysonResolventSeries_eq]
  congr 2
  rw [matrixSemicircleCovariancePowerSeries]
  simp_rw [hA]
  simp only [freeFockResolventWordMatrix_cons, freeFockResolventWordMatrix_nil]
  rw [Finset.sum_mul]
  simp_rw [Matrix.mul_assoc]

omit [DecidableEq K] in
theorem freeFockResolventWordMatrix_cons_eq
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k) (k : K) (w : List K) :
    freeFockResolventWordMatrix A (k :: w) =
      constantPowerSeriesMatrix (A k) * freeFockResolventWordMatrix A w +
        (PowerSeries.X ^ (2 : ℕ) : PowerSeries ℂ) •
          ∑ l : K, constantPowerSeriesMatrix (A l) *
            freeFockResolventWordMatrix A (l :: k :: w) := by
  rw [freeFockResolventWordMatrix_cons, matrixDysonResolventSeries_eq]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul]
  simp only [Matrix.smul_mul]
  congr 1
  rw [matrixSemicircleCovariancePowerSeries]
  simp_rw [hA]
  simp only [freeFockResolventWordMatrix_cons]
  rw [Finset.sum_mul]
  simp_rw [Matrix.mul_assoc]
  rw [Finset.sum_mul]
  simp_rw [Matrix.mul_assoc]

def freeFockFormalResolvent (A : K → Matrix I I ℂ) (j : I)
    (iw : I × List K) : PowerSeries ℂ :=
  PowerSeries.X ^ iw.2.length * freeFockResolventWordMatrix A iw.2 iw.1 j

def freeFockFormalVacuum (j : I) (iw : I × List K) : PowerSeries ℂ :=
  if iw.2 = [] then PowerSeries.C (if iw.1 = j then 1 else 0) else 0

def freeFockFormalAction (A : K → Matrix I I ℂ)
    (R : I × List K → PowerSeries ℂ) (iw : I × List K) : PowerSeries ℂ :=
  match iw.2 with
  | [] => ∑ k : K, ∑ p : I, PowerSeries.C (A k iw.1 p) * R (p, [k])
  | k :: w =>
      (∑ p : I, PowerSeries.C (A k iw.1 p) * R (p, w)) +
        ∑ l : K, ∑ p : I, PowerSeries.C (A l iw.1 p) * R (p, l :: k :: w)

omit [DecidableEq K] in
theorem freeFockFormalResolvent_eq
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k) (j : I)
    (iw : I × List K) :
    freeFockFormalResolvent A j iw = freeFockFormalVacuum j iw +
      PowerSeries.X * freeFockFormalAction A (freeFockFormalResolvent A j) iw := by
  rcases iw with ⟨i, w⟩
  cases w with
  | nil =>
      have h := congr_fun (congr_fun (freeFockResolventWordMatrix_nil_eq A hA) i) j
      simp only [freeFockFormalResolvent, List.length_nil, pow_zero, one_mul,
        freeFockFormalVacuum, freeFockFormalAction, Matrix.add_apply, Matrix.one_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.mul_apply] at h ⊢
      rw [h]
      by_cases hij : i = j
      · subst j
        simp [constantPowerSeriesMatrix, Finset.mul_sum]
        ring_nf
      · simp [hij, constantPowerSeriesMatrix, Finset.mul_sum]
        ring_nf
  | cons k w =>
      have h := congr_fun (congr_fun (freeFockResolventWordMatrix_cons_eq A hA k w) i) j
      simp only [freeFockFormalResolvent, List.length_cons, freeFockFormalVacuum,
        freeFockFormalAction, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.sum_apply, Matrix.mul_apply] at h ⊢
      simp only [List.cons_ne_nil, ↓reduceIte, zero_add]
      rw [h]
      simp only [constantPowerSeriesMatrix]
      have hfirst :
          (∑ p : I, PowerSeries.C (A k i p) *
              (PowerSeries.X ^ w.length * freeFockResolventWordMatrix A w p j)) =
            PowerSeries.X ^ w.length *
              ∑ p : I, PowerSeries.C (A k i p) *
                freeFockResolventWordMatrix A w p j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      have hsecond :
          (∑ l : K, ∑ p : I, PowerSeries.C (A l i p) *
              (PowerSeries.X ^ (w.length + 1 + 1) *
                freeFockResolventWordMatrix A (l :: k :: w) p j)) =
            PowerSeries.X ^ (w.length + 1 + 1) *
              ∑ l : K, ∑ p : I, PowerSeries.C (A l i p) *
                freeFockResolventWordMatrix A (l :: k :: w) p j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      rw [hfirst, hsecond]
      simp only [pow_succ]
      ring

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem freeFockInner_finset_sum_left
    {L : Type*} (s : Finset L) (f : L → FreeFockVector I K) (y : FreeFockVector I K) :
    freeFockInner (∑ a ∈ s, f a) y = ∑ a ∈ s, freeFockInner (f a) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, freeFockInner_add_left, ih]

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem freeFockInner_finset_sum_right
    {L : Type*} (s : Finset L) (f : L → FreeFockVector I K) (x : FreeFockVector I K) :
    freeFockInner x (∑ a ∈ s, f a) = ∑ a ∈ s, freeFockInner x (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, freeFockInner_add_right, ih]

theorem freeFockAction_apply_nil
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : FreeFockVector I K) (i : I) :
    freeFockAction A x (i, []) = ∑ k : K, ∑ p : I, A k i p * x (p, [k]) := by
  rw [← freeFockInner_basis_action A hA (i, []) x]
  rw [freeFockBasisAction, freeFockInner_add_left]
  simp only [freeFockAnnihilationBasisAction, freeFockInner_zero_left, add_zero,
    freeFockCreationBasisAction, freeFockInner_finset_sum_left]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  rw [freeFockInner_single_left]
  have hentry := congr_fun (congr_fun (hA k) i) p
  simp only [Matrix.conjTranspose_apply] at hentry
  change star (A k p i) * x (p, [k]) = A k i p * x (p, [k])
  rw [hentry]

theorem freeFockAction_apply_cons
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : FreeFockVector I K) (i : I) (k : K) (w : List K) :
    freeFockAction A x (i, k :: w) =
      (∑ p : I, A k i p * x (p, w)) +
        ∑ l : K, ∑ p : I, A l i p * x (p, l :: k :: w) := by
  rw [← freeFockInner_basis_action A hA (i, k :: w) x]
  rw [freeFockBasisAction, freeFockInner_add_left]
  simp only [freeFockCreationBasisAction, freeFockAnnihilationBasisAction,
    freeFockInner_finset_sum_left]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    rw [freeFockInner_single_left]
    have hentry := congr_fun (congr_fun (hA k) i) p
    simp only [Matrix.conjTranspose_apply] at hentry
    change star (A k p i) * x (p, w) = A k i p * x (p, w)
    rw [hentry]
  · apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro p hp
    rw [freeFockInner_single_left]
    have hentry := congr_fun (congr_fun (hA l) i) p
    simp only [Matrix.conjTranspose_apply] at hentry
    change star (A l p i) * x (p, l :: k :: w) = A l i p * x (p, l :: k :: w)
    rw [hentry]

def freeFockVacuum (j : I) : FreeFockVector I K :=
  Finsupp.single (j, []) 1

omit [Fintype I] [Fintype K] [DecidableEq K] in
@[simp]
theorem freeFockVacuum_apply (j i : I) (w : List K) :
    freeFockVacuum (K := K) j (i, w) =
      if i = j ∧ w = [] then 1 else 0 := by
  by_cases hi : i = j
  · subst j
    by_cases hw : w = [] <;> simp [freeFockVacuum, hw]
  · simp [freeFockVacuum, hi]

def freeFockPower (A : K → Matrix I I ℂ) (j : I) : ℕ → FreeFockVector I K
  | 0 => freeFockVacuum j
  | n + 1 => freeFockAction A (freeFockPower A j n)

omit [DecidableEq I] [DecidableEq K] in
@[simp]
theorem freeFockPower_zero (A : K → Matrix I I ℂ) (j : I) :
    freeFockPower A j 0 = freeFockVacuum j := rfl

omit [DecidableEq I] [DecidableEq K] in
@[simp]
theorem freeFockPower_succ (A : K → Matrix I I ℂ) (j : I) (n : ℕ) :
    freeFockPower A j (n + 1) = freeFockAction A (freeFockPower A j n) := rfl

theorem coeff_freeFockFormalAction_eq_freeFockAction
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (R : I × List K → PowerSeries ℂ) (x : FreeFockVector I K) (n : ℕ)
    (hcoeff : ∀ iw, PowerSeries.coeff n (R iw) = x iw) (iw : I × List K) :
    PowerSeries.coeff n (freeFockFormalAction A R iw) = freeFockAction A x iw := by
  rcases iw with ⟨i, w⟩
  cases w with
  | nil =>
      rw [freeFockAction_apply_nil A hA]
      simp only [freeFockFormalAction, map_sum, PowerSeries.coeff_C_mul, hcoeff]
  | cons k w =>
      rw [freeFockAction_apply_cons A hA]
      simp only [freeFockFormalAction, map_add, map_sum, PowerSeries.coeff_C_mul, hcoeff]

omit [Fintype I] [Fintype K] [DecidableEq K] in
@[simp]
theorem coeff_zero_freeFockFormalVacuum (j : I) (iw : I × List K) :
    PowerSeries.coeff 0 (freeFockFormalVacuum (K := K) j iw) = freeFockVacuum j iw := by
  rcases iw with ⟨i, w⟩
  by_cases hw : w = []
  · subst w
    by_cases hij : i = j <;> simp [freeFockFormalVacuum, freeFockVacuum, hij]
  · simp [freeFockFormalVacuum, freeFockVacuum, hw]

omit [Fintype I] [Fintype K] [DecidableEq K] in
@[simp]
theorem coeff_succ_freeFockFormalVacuum (j : I) (iw : I × List K) (n : ℕ) :
    PowerSeries.coeff (n + 1) (freeFockFormalVacuum (K := K) j iw) = 0 := by
  rcases iw with ⟨i, w⟩
  by_cases hw : w = []
  · subst w
    by_cases hij : i = j <;> simp [freeFockFormalVacuum, hij]
  · simp [freeFockFormalVacuum, hw]

theorem coeff_freeFockFormalResolvent_eq_freeFockPower
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k) (j : I) (n : ℕ)
    (iw : I × List K) :
    PowerSeries.coeff n (freeFockFormalResolvent A j iw) = freeFockPower A j n iw := by
  induction n generalizing iw with
  | zero =>
      have h := congrArg (PowerSeries.coeff 0) (freeFockFormalResolvent_eq A hA j iw)
      rw [map_add, PowerSeries.coeff_zero_X_mul] at h
      rw [freeFockPower_zero, ← coeff_zero_freeFockFormalVacuum]
      simpa using h
  | succ n ih =>
      have h := congrArg (PowerSeries.coeff (n + 1))
        (freeFockFormalResolvent_eq A hA j iw)
      rw [map_add, coeff_succ_freeFockFormalVacuum,
        PowerSeries.coeff_succ_X_mul] at h
      calc
        PowerSeries.coeff (n + 1) (freeFockFormalResolvent A j iw) =
            PowerSeries.coeff n
              (freeFockFormalAction A (freeFockFormalResolvent A j) iw) := by simpa using h
        _ = freeFockAction A (freeFockPower A j n) iw :=
          coeff_freeFockFormalAction_eq_freeFockAction A hA
            (freeFockFormalResolvent A j) (freeFockPower A j n) n ih iw
        _ = freeFockPower A j (n + 1) iw := rfl

theorem freeFockPower_vacuumCoefficient
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (n : ℕ) (i j : I) :
    freeFockPower A j n (i, []) =
      if 2 ∣ n then matrixDysonFormalCoeff A (n / 2) i j else 0 := by
  rw [← coeff_freeFockFormalResolvent_eq_freeFockPower A hA j n (i, [])]
  simp only [freeFockFormalResolvent, List.length_nil, pow_zero, one_mul,
    freeFockResolventWordMatrix_nil]
  exact matrixDysonResolventSeries_coeff A n i j

theorem freeFockPower_vacuumCoefficient_even
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (n : ℕ) (i j : I) :
    freeFockPower A j (2 * n) (i, []) = matrixDysonFormalCoeff A n i j := by
  rw [freeFockPower_vacuumCoefficient A hA]
  simp

theorem freeFockPower_vacuumCoefficient_odd
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (n : ℕ) (i j : I) :
    freeFockPower A j (2 * n + 1) (i, []) = 0 := by
  rw [freeFockPower_vacuumCoefficient A hA]
  simp

theorem freeFockInner_power_power
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (m n : ℕ) (i j : I) :
    freeFockInner (freeFockPower A i m) (freeFockPower A j n) =
      freeFockPower A j (m + n) (i, []) := by
  induction m generalizing n with
  | zero =>
      simp [freeFockPower, freeFockVacuum, freeFockInner_single_left]
  | succ m ih =>
      rw [freeFockPower_succ, freeFockAction_symmetric A hA,
        ← freeFockPower_succ, ih]
      congr 2
      omega

def freeFockPolynomialVector (A : K → Matrix I I ℂ)
    (p : Polynomial ℝ) (j : I) : FreeFockVector I K :=
  ∑ n ∈ p.support, ((p.coeff n : ℝ) : ℂ) • freeFockPower A j n

theorem freeFockInner_polynomialVector_self
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (p : Polynomial ℝ) (j : I) :
    freeFockInner (freeFockPolynomialVector A p j)
        (freeFockPolynomialVector A p j) =
      ∑ m ∈ p.support, ∑ n ∈ p.support,
        ((p.coeff m * p.coeff n : ℝ) : ℂ) *
          freeFockPower A j (m + n) (j, []) := by
  rw [freeFockPolynomialVector, freeFockInner_finset_sum_left]
  apply Finset.sum_congr rfl
  intro m hm
  rw [freeFockInner_smul_left]
  rw [freeFockInner_finset_sum_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [freeFockInner_smul_right, freeFockInner_power_power A hA]
  push_cast
  simp
  ring

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem re_freeFockInner_self_eq_sum_normSq (x : FreeFockVector I K) :
    (freeFockInner x x).re = ∑ a ∈ x.support, Complex.normSq (x a) := by
  rw [freeFockInner, Finsupp.sum]
  simp only [Complex.star_def]
  simp_rw [← Complex.normSq_eq_conj_mul_self]
  simp

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem re_freeFockInner_self_nonneg (x : FreeFockVector I K) :
    0 ≤ (freeFockInner x x).re := by
  rw [re_freeFockInner_self_eq_sum_normSq]
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem re_freeFockInner_self_pos (x : FreeFockVector I K) (hx : x ≠ 0) :
    0 < (freeFockInner x x).re := by
  rw [re_freeFockInner_self_eq_sum_normSq]
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hx
  apply Finset.sum_pos'
  · exact fun b hb => Complex.normSq_nonneg _
  · refine ⟨a, Finsupp.mem_support_iff.mpr ha, ?_⟩
    exact Complex.normSq_pos.mpr ha

def freeFockTraceMoment [Nonempty I]
    (A : K → Matrix I I ℂ) (n : ℕ) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ *
    ∑ i : I, (freeFockPower A i n (i, [])).re

omit [DecidableEq I] [DecidableEq K] in
theorem freeFockTraceMoment_zero [Nonempty I] (A : K → Matrix I I ℂ) :
    freeFockTraceMoment A 0 = 1 := by
  rw [freeFockTraceMoment]
  simp [freeFockPower, freeFockVacuum]

theorem momentInner_X_pow_X_pow (s : ℕ → ℝ) (m n : ℕ) :
    HTGeometry.momentInner s (Polynomial.X ^ m) (Polynomial.X ^ n) = s (m + n) := by
  rw [HTGeometry.momentInner, ← pow_add, HTGeometry.momentFunctional_X_pow]

theorem momentInner_eq_double_support_sum (s : ℕ → ℝ) (p : Polynomial ℝ) :
    HTGeometry.momentInner s p p =
      ∑ m ∈ p.support, ∑ n ∈ p.support,
        p.coeff m * p.coeff n * s (m + n) := by
  have hp : p = ∑ n ∈ p.support, p.coeff n • Polynomial.X ^ n := by
    simpa [Algebra.smul_def] using p.as_sum_support_C_mul_X_pow
  conv_lhs => rw [hp]
  rw [HTGeometry.momentInner_sum_left]
  apply Finset.sum_congr rfl
  intro m hm
  rw [HTGeometry.momentInner_smul_left]
  rw [HTGeometry.momentInner_sum_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [HTGeometry.momentInner_smul_right, momentInner_X_pow_X_pow]
  ring

def freeFockPolynomialEnergy [Nonempty I]
    (A : K → Matrix I I ℂ) (p : Polynomial ℝ) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ *
    ∑ j : I, (freeFockInner (freeFockPolynomialVector A p j)
      (freeFockPolynomialVector A p j)).re

theorem momentInner_freeFockTraceMoment_eq_energy [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (p : Polynomial ℝ) :
    HTGeometry.momentInner (freeFockTraceMoment A) p p =
      freeFockPolynomialEnergy A p := by
  rw [momentInner_eq_double_support_sum]
  simp only [freeFockTraceMoment, freeFockPolynomialEnergy,
    freeFockInner_polynomialVector_self A hA]
  have hre (s : Finset ℕ) (f : ℕ → ℂ) :
      (∑ n ∈ s, f n).re = ∑ n ∈ s, (f n).re := by
    exact map_sum Complex.reCLM f s
  simp_rw [hre]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  have hswap (f : ℕ → ℕ → I → ℝ) :
      (∑ m ∈ p.support, ∑ n ∈ p.support, ∑ i, f m n i) =
        ∑ i, ∑ m ∈ p.support, ∑ n ∈ p.support, f m n i := by
    calc
      _ = ∑ m ∈ p.support, ∑ i, ∑ n ∈ p.support, f m n i := by
        apply Finset.sum_congr rfl
        intro m hm
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem freeFockPower_apply_of_lt_length
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (j i : I) (w : List K) (n : ℕ) (h : n < w.length) :
    freeFockPower A j n (i, w) = 0 := by
  induction n generalizing i w with
  | zero =>
      have hw : w ≠ [] := by
        intro hw
        subst w
        simp at h
      simp [freeFockPower, freeFockVacuum, hw]
  | succ n ih =>
      cases w with
      | nil => simp at h
      | cons k w =>
          rw [freeFockPower_succ, freeFockAction_apply_cons A hA]
          have htail : n < w.length := by simpa using h
          have hdeep (l : K) : n < (l :: k :: w).length := by
            simp only [List.length_cons]
            omega
          simp_rw [ih _ _ htail, ih _ _ (hdeep _), mul_zero, Finset.sum_const_zero,
            zero_add]

def freeFockCreationProduct (A : K → Matrix I I ℂ) : List K → Matrix I I ℂ
  | [] => 1
  | k :: w => A k * freeFockCreationProduct A w

theorem freeFockPower_apply_at_length
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (j i : I) (w : List K) :
    freeFockPower A j w.length (i, w) = freeFockCreationProduct A w i j := by
  induction w generalizing i with
  | nil =>
      by_cases hij : i = j
      · subst i
        simp [freeFockVacuum, freeFockCreationProduct]
      · simp [freeFockVacuum, freeFockCreationProduct, hij]
  | cons k w ih =>
      rw [List.length_cons, freeFockPower_succ,
        freeFockAction_apply_cons A hA]
      simp_rw [ih]
      have hdeep (l : K) (p : I) :
          freeFockPower A j w.length (p, l :: k :: w) = 0 :=
        freeFockPower_apply_of_lt_length A hA j p (l :: k :: w) w.length (by simp)
      simp_rw [hdeep, mul_zero, Finset.sum_const_zero, add_zero]
      simp [freeFockCreationProduct, Matrix.mul_apply]

def HasTrivialCommonKernel (A : K → Matrix I I ℂ) : Prop :=
  ∀ x : I → ℂ, (∀ k i, ∑ p : I, A k i p * x p = 0) → x = 0

omit [Fintype K] [DecidableEq K] in
theorem exists_freeFockCreationProduct_entry_ne_zero [Nonempty I]
    (A : K → Matrix I I ℂ) (hker : HasTrivialCommonKernel A)
    (j : I) (n : ℕ) :
    ∃ w : List K, w.length = n ∧ ∃ i : I, freeFockCreationProduct A w i j ≠ 0 := by
  induction n with
  | zero =>
      refine ⟨[], rfl, j, ?_⟩
      simp [freeFockCreationProduct]
  | succ n ih =>
      obtain ⟨w, hw, i, hi⟩ := ih
      let x : I → ℂ := fun p => freeFockCreationProduct A w p j
      have hx : x ≠ 0 := by
        intro hx
        exact hi (congr_fun hx i)
      have hnot : ¬ ∀ k i, ∑ p : I, A k i p * x p = 0 := by
        intro hall
        exact hx (hker x hall)
      push Not at hnot
      obtain ⟨k, i', hki⟩ := hnot
      refine ⟨k :: w, by simp [hw], i', ?_⟩
      simpa [freeFockCreationProduct, Matrix.mul_apply, x] using hki

theorem freeFockPolynomialVector_apply_top
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (p : Polynomial ℝ) (hp : p ≠ 0) (j i : I) (w : List K)
    (hw : w.length = p.natDegree) :
    freeFockPolynomialVector A p j (i, w) =
      (p.leadingCoeff : ℂ) * freeFockCreationProduct A w i j := by
  rw [freeFockPolynomialVector, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single p.natDegree]
  · simp only [Finsupp.smul_apply, smul_eq_mul, Polynomial.coeff_natDegree]
    rw [← hw, freeFockPower_apply_at_length A hA]
  · intro n hn hne
    have hlt : n < w.length := by
      rw [hw]
      exact (Polynomial.le_natDegree_of_mem_supp n hn).lt_of_ne hne
    simp [freeFockPower_apply_of_lt_length A hA j i w n hlt]
  · intro hnot
    exact (hnot (Polynomial.natDegree_mem_support_of_nonzero hp)).elim

theorem freeFockPolynomialVector_ne_zero [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (p : Polynomial ℝ) (hp : p ≠ 0) (j : I) :
    freeFockPolynomialVector A p j ≠ 0 := by
  obtain ⟨w, hw, i, hi⟩ :=
    exists_freeFockCreationProduct_entry_ne_zero A hker j p.natDegree
  apply Finsupp.ne_iff.mpr
  refine ⟨(i, w), ?_⟩
  rw [freeFockPolynomialVector_apply_top A hA p hp j i w hw]
  exact mul_ne_zero (by exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hp) hi

theorem freeFockTraceMoment_positiveMomentForm [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    HTGeometry.PositiveMomentForm (freeFockTraceMoment A) := by
  constructor
  intro p hp
  rw [momentInner_freeFockTraceMoment_eq_energy A hA, freeFockPolynomialEnergy]
  have hcard : 0 < (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply mul_pos (inv_pos.mpr hcard)
  apply Finset.sum_pos'
  · intro j hj
    exact re_freeFockInner_self_nonneg _
  · let j : I := Classical.choice ‹Nonempty I›
    refine ⟨j, Finset.mem_univ j, ?_⟩
    exact re_freeFockInner_self_pos _
      (freeFockPolynomialVector_ne_zero A hA hker p hp j)

end
end GaloisForLFunctions.HTGeometry

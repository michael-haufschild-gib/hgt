import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Trace.Basic

/-!
# Residue duality for monic quotient algebras

The coefficient of the highest basis power defines the residue functional
on a monic polynomial quotient. Successive coefficient tails give its
dual basis, including when the quotient has nilpotents.
-/

noncomputable section
open Polynomial Finset
namespace GaloisForLFunctions.HTGeometry
variable {R : Type*} [CommRing R]

/-- Discard the first `k` coefficients and shift the remaining coefficients down. -/
def coefficientTail (f : R[X]) : ℕ → R[X]
  | 0 => f
  | k + 1 => (coefficientTail f k).divX

theorem coefficientTail_coeff (f : R[X]) (k j : ℕ) :
    (coefficientTail f k).coeff j = f.coeff (j + k) := by
  induction k generalizing j with
  | zero => simp [coefficientTail]
  | succ k ih => simp only [coefficientTail, coeff_divX, ih]; congr 1; omega

theorem coefficientTail_step (f : R[X]) (k : ℕ) :
    X * coefficientTail f (k + 1) + C (f.coeff k) = coefficientTail f k := by
  simpa only [coefficientTail, coefficientTail_coeff, zero_add] using
    X_mul_divX_add (coefficientTail f k)

/-- The highest coefficient of the canonical remainder modulo a monic equation. -/
def monicResidue {f : R[X]} (hf : f.Monic) : AdjoinRoot f →ₗ[R] R :=
  (Polynomial.lcoeff R (f.natDegree - 1)).comp (AdjoinRoot.modByMonicHom hf)

theorem monicResidue_mk_of_degree_lt {f p : R[X]} (hf : f.Monic)
    (hp : p.degree < f.degree) :
    monicResidue hf (AdjoinRoot.mk f p) = p.coeff (f.natDegree - 1) := by
  nontriviality R
  change (AdjoinRoot.modByMonicHom hf (AdjoinRoot.mk f p)).coeff _ = _
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hf).mpr hp]

theorem monicResidue_root_pow {f : R[X]} (hf : f.Monic) {j : ℕ}
    (hj : j < f.natDegree) :
    monicResidue hf (AdjoinRoot.root f ^ j) = if j = f.natDegree - 1 then 1 else 0 := by
  nontriviality R
  rw [← AdjoinRoot.mk_X, ← map_pow]
  rw [monicResidue_mk_of_degree_lt hf]
  · simp only [coeff_X_pow, eq_comm]
  · rw [degree_X_pow, degree_eq_natDegree hf.ne_zero]
    exact_mod_cast hj

/-- Coefficient tails, evaluated in the quotient, are residue-dual to the powers. -/
def monicResidueDual {f : R[X]} (i : ℕ) : AdjoinRoot f :=
  AdjoinRoot.mk f (coefficientTail f (i + 1))

theorem monicResidueDual_step {f : R[X]} (i : ℕ) :
    AdjoinRoot.root f * monicResidueDual (f := f) (i + 1) +
      algebraMap R (AdjoinRoot f) (f.coeff (i + 1)) = monicResidueDual i := by
  simpa only [monicResidueDual, map_add, map_mul, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq] using
    congrArg (AdjoinRoot.mk f) (coefficientTail_step f (i + 1))

theorem monicResidueDual_zero {f : R[X]} :
    AdjoinRoot.root f * monicResidueDual (f := f) 0 +
      algebraMap R (AdjoinRoot f) (f.coeff 0) = 0 := by
  simpa only [monicResidueDual, map_add, map_mul, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq, coefficientTail, AdjoinRoot.mk_self] using
    congrArg (AdjoinRoot.mk f) (coefficientTail_step f 0)

theorem coefficientTail_degree_lt [Nontrivial R] {f : R[X]} (hf : f.Monic) (i : ℕ) :
    (coefficientTail f (i + 1)).degree < f.degree := by
  rw [degree_eq_natDegree hf.ne_zero, degree_lt_iff_coeff_zero]
  intro j hj
  rw [coefficientTail_coeff]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem monicResidue_dual {f : R[X]} (hf : f.Monic) (hd : 0 < f.natDegree) (i : ℕ) :
    monicResidue hf (monicResidueDual (f := f) i) = if i = 0 then 1 else 0 := by
  nontriviality R
  rw [monicResidueDual, monicResidue_mk_of_degree_lt hf (coefficientTail_degree_lt hf i),
    coefficientTail_coeff]
  split_ifs with hi
  · subst i
    have h : f.natDegree - 1 + (0 + 1) = f.natDegree := by omega
    rw [h, hf.coeff_natDegree]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Residue duality holds over every commutative coefficient ring, without separability. -/
theorem monicResidue_root_pow_mul_dual {f : R[X]} (hf : f.Monic)
    (i j : ℕ) (hj : j < f.natDegree) :
    monicResidue hf (AdjoinRoot.root f ^ j * monicResidueDual (f := f) i) =
      if i = j then 1 else 0 := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => simpa using monicResidue_dual hf (by omega) 0
    | succ j =>
      have hz : monicResidue hf (AdjoinRoot.root f ^ j) = 0 := by
        rw [monicResidue_root_pow hf (by omega), if_neg (by omega)]
      have he : AdjoinRoot.root f * monicResidueDual (f := f) 0 =
          -(algebraMap R (AdjoinRoot f) (f.coeff 0)) :=
        eq_neg_of_add_eq_zero_left monicResidueDual_zero
      rw [pow_succ, mul_assoc, he, mul_neg, map_neg, mul_comm,
        ← Algebra.smul_def, map_smul, hz, smul_zero, neg_zero, if_neg (by omega)]
  | succ i ih =>
    cases j with
    | zero => simpa using monicResidue_dual hf (by omega) (i + 1)
    | succ j =>
      have hz : monicResidue hf (AdjoinRoot.root f ^ j) = 0 := by
        rw [monicResidue_root_pow hf (by omega), if_neg (by omega)]
      have he : AdjoinRoot.root f * monicResidueDual (f := f) (i + 1) =
          monicResidueDual i - algebraMap R (AdjoinRoot f) (f.coeff (i + 1)) :=
        eq_sub_of_add_eq (monicResidueDual_step i)
      rw [pow_succ, mul_assoc, he, mul_sub, map_sub, ih j (by omega)]
      rw [mul_comm (AdjoinRoot.root f ^ j), ← Algebra.smul_def, map_smul, hz,
        smul_zero, sub_zero]
      simp only [Nat.add_right_cancel_iff]

theorem coefficientTail_divX (f : R[X]) (i : ℕ) :
    coefficientTail f.divX i = coefficientTail f (i + 1) := by
  ext j
  simp only [coefficientTail_coeff, coeff_divX, Nat.add_assoc]

/-- Multiplying each coefficient tail by its basis monomial and summing gives the derivative. -/
theorem sum_monomial_mul_coefficientTail (f : R[X]) (n : ℕ) (hn : f.natDegree ≤ n) :
    (∑ i ∈ range n, X ^ i * coefficientTail f (i + 1)) = f.derivative := by
  induction n generalizing f with
  | zero =>
    have hf : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    simp only [range_zero, sum_empty]
    rw [hf, derivative_C]
  | succ n ih =>
    have hd : f.divX.natDegree ≤ n := by
      rw [natDegree_divX_eq_natDegree_tsub_one]
      omega
    rw [sum_range_succ']
    simp only [pow_zero, one_mul, coefficientTail]
    change (∑ i ∈ range n, X ^ (i + 1) * (coefficientTail f (i + 1)).divX) +
      f.divX = f.derivative
    have hs : (∑ i ∈ range n, X ^ (i + 1) * (coefficientTail f (i + 1)).divX) =
        X * ∑ i ∈ range n, X ^ i * coefficientTail f.divX (i + 1) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [coefficientTail_divX]
      change X ^ (i + 1) * coefficientTail f (i + 2) =
        X * (X ^ i * coefficientTail f (i + 2))
      rw [pow_succ]
      ring
    rw [hs, ih f.divX hd]
    have he := congrArg derivative (X_mul_divX_add f)
    simpa only [derivative_add, derivative_mul, derivative_X, one_mul,
      derivative_C, add_zero, zero_add, add_comm] using he

/-- The residue Casimir is the derivative of the defining equation in the actual quotient. -/
theorem monicResidue_casimir {f : R[X]} :
    (∑ i : Fin f.natDegree, AdjoinRoot.root f ^ (i : ℕ) * monicResidueDual (f := f) i) =
      AdjoinRoot.mk f f.derivative := by
  have h := congrArg (AdjoinRoot.mk f)
    (sum_monomial_mul_coefficientTail f f.natDegree le_rfl)
  simpa only [map_sum, map_mul, map_pow, AdjoinRoot.mk_X, ← Fin.sum_univ_eq_sum_range,
    monicResidueDual] using h

/-- Residue duality recovers every monomial coordinate of every quotient element. -/
theorem monicResidue_coordinate {f : R[X]} (hf : f.Monic) (x : AdjoinRoot f)
    (i : Fin f.natDegree) :
    monicResidue hf (x * monicResidueDual (f := f) i) =
      (AdjoinRoot.powerBasis' hf).basis.repr x i := by
  classical
  nth_rw 1 [← (AdjoinRoot.powerBasis' hf).basis.sum_repr x]
  rw [sum_mul, map_sum]
  simp only [smul_mul_assoc, map_smul, (AdjoinRoot.powerBasis' hf).basis_eq_pow,
    AdjoinRoot.powerBasis'_gen, monicResidue_root_pow_mul_dual hf _ _ (Fin.isLt _),
    smul_eq_mul]
  simp only [Fin.val_inj, mul_ite, mul_one, mul_zero]
  change (∑ j : Fin f.natDegree,
    if i = j then (AdjoinRoot.powerBasisAux' hf).repr x j else 0) = _
  simp
  rfl

/-- The trace pairing is the residue pairing multiplied by the different element. -/
theorem monic_trace_eq_residue_derivative {f : R[X]} (hf : f.Monic) (x : AdjoinRoot f) :
    Algebra.trace R (AdjoinRoot f) x =
      monicResidue hf (x * AdjoinRoot.mk f f.derivative) := by
  classical
  rw [← monicResidue_casimir, mul_sum, map_sum,
    Algebra.trace_eq_matrix_trace (AdjoinRoot.powerBasis' hf).basis]
  simp only [Algebra.leftMulMatrix_apply, Matrix.trace, Matrix.diag_apply,
    LinearMap.toMatrix_apply]
  change (∑ i, (AdjoinRoot.powerBasis' hf).basis.repr
      (x * (AdjoinRoot.powerBasis' hf).basis i) i) = _
  apply sum_congr rfl
  intro i hi
  rw [← monicResidue_coordinate, (AdjoinRoot.powerBasis' hf).basis_eq_pow]
  congr 1
  exact mul_assoc _ _ _

/-- The residue pairing as a map to the integral linear dual. -/
def monicResidueMap {f : R[X]} (hf : f.Monic) :
    AdjoinRoot f →ₗ[R] Module.Dual R (AdjoinRoot f) where
  toFun x := (monicResidue hf).comp (Algebra.lmul R (AdjoinRoot f) x)
  map_add' x y := by
    ext z
    change monicResidue hf ((x + y) * z) = monicResidue hf (x * z) + monicResidue hf (y * z)
    rw [add_mul, map_add]
  map_smul' c x := by
    ext z
    change monicResidue hf ((c • x) * z) = c • monicResidue hf (x * z)
    rw [smul_mul_assoc, map_smul]

@[simp] theorem monicResidueMap_apply {f : R[X]} (hf : f.Monic) (x y : AdjoinRoot f) :
    monicResidueMap hf x y = monicResidue hf (x * y) := rfl

theorem monicResidueMap_bijective {f : R[X]} (hf : f.Monic) :
    Function.Bijective (monicResidueMap hf) := by
  classical
  constructor
  · intro x y h
    apply (AdjoinRoot.powerBasis' hf).basis.ext_elem
    intro i
    rw [← monicResidue_coordinate, ← monicResidue_coordinate]
    exact congrArg (fun u : Module.Dual R (AdjoinRoot f) => u (monicResidueDual i)) h
  · intro u
    refine ⟨∑ i : Fin f.natDegree,
      u ((AdjoinRoot.powerBasis' hf).basis i) • monicResidueDual (f := f) i, ?_⟩
    apply (AdjoinRoot.powerBasis' hf).basis.ext
    intro j
    rw [monicResidueMap_apply, sum_mul, map_sum,
      (AdjoinRoot.powerBasis' hf).basis_eq_pow]
    simp only [smul_mul_assoc, map_smul, AdjoinRoot.powerBasis'_gen]
    simp_rw [mul_comm (monicResidueDual _),
      monicResidue_root_pow_mul_dual hf _ _ j.isLt]
    simp only [smul_eq_mul, Fin.val_inj, mul_ite, mul_one, mul_zero]
    change (∑ i : Fin f.natDegree,
      if i = j then u ((AdjoinRoot.powerBasisAux' hf) i) else 0) = _
    simp
    exact congrArg u ((AdjoinRoot.powerBasis' hf).basis_eq_pow j)

/-- Monic residue duality is an integral equivalence, even for a nonreduced quotient. -/
def monicResidueEquiv {f : R[X]} (hf : f.Monic) :
    AdjoinRoot f ≃ₗ[R] Module.Dual R (AdjoinRoot f) :=
  LinearEquiv.ofBijective (monicResidueMap hf) (monicResidueMap_bijective hf)

/-- Under residue duality, the trace pairing is multiplication by the different element. -/
theorem monic_traceForm_eq_residueMap_comp {f : R[X]} (hf : f.Monic) :
    Algebra.traceForm R (AdjoinRoot f) =
      (monicResidueMap hf).comp
        (Algebra.lmul R (AdjoinRoot f) (AdjoinRoot.mk f f.derivative)) := by
  ext x y
  change Algebra.trace R (AdjoinRoot f) (x * y) =
    monicResidue hf ((AdjoinRoot.mk f f.derivative * x) * y)
  rw [monic_trace_eq_residue_derivative hf]
  congr 1
  ring

#print axioms monicResidue_root_pow_mul_dual
#print axioms monicResidue_casimir
#print axioms monicResidue_coordinate
#print axioms monic_trace_eq_residue_derivative
#print axioms monicResidueMap_bijective
#print axioms monicResidueEquiv
#print axioms monic_traceForm_eq_residueMap_comp

end GaloisForLFunctions.HTGeometry

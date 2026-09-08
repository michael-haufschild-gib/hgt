import GaloisForLFunctions.HTGeometry.WickFockModel
import Mathlib

/-!
# Arbitrarily many bosonic pairs and the collective Bargmann sector

Equation (20) of arXiv:2601.07437 is realized on the corpus polynomial
Fock space for every finite number of pairs. The collective vacuum sector
has lowest weight `N/2`; its spectrum and lowering coefficients are proved
from the actual coordinate operators, without assumed commutation laws.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV
open MvPolynomial
open scoped BigOperators

abbrev ManyFock (N : ℕ) := MvPolynomial (Fin N × Bool) ℂ
abbrev ManyEnd (N : ℕ) := Module.End ℂ (ManyFock N)

def modeCreate (N : ℕ) (i : Fin N) : ManyEnd N :=
  fockCre ℂ (Fin N × Bool) (i, false) * fockCre ℂ (Fin N × Bool) (i, true)
def modeAnn (N : ℕ) (i : Fin N) : ManyEnd N :=
  fockAnn ℂ (Fin N × Bool) (i, false) * fockAnn ℂ (Fin N × Bool) (i, true)
def modeCartan (N : ℕ) (i : Fin N) : ManyEnd N :=
  fockCre ℂ (Fin N × Bool) (i, false) * fockAnn ℂ (Fin N × Bool) (i, false) +
    fockCre ℂ (Fin N × Bool) (i, true) * fockAnn ℂ (Fin N × Bool) (i, true) + 1

/-- All modewise weight commutators, including independent pairs. -/
theorem modeCartan_create (N : ℕ) (i j : Fin N) :
    modeCartan N i * modeCreate N j - modeCreate N j * modeCartan N i =
      if i = j then (2 : ℂ) • modeCreate N i else 0 := by
  apply LinearMap.ext
  intro p
  by_cases h : i = j
  · subst j
    simp [modeCartan, modeCreate, Module.End.mul_apply, MvPolynomial.smul_eq_C_mul, map_ofNat]
    ring
  · simp [modeCartan, modeCreate, Module.End.mul_apply, h, Ne.symm h]
    ring

/-- Pair creation and annihilation have the exact Kronecker commutator. -/
theorem modeCreate_ann (N : ℕ) (i j : Fin N) :
    modeCreate N i * modeAnn N j - modeAnn N j * modeCreate N i =
      if i = j then -modeCartan N i else 0 := by
  apply LinearMap.ext
  intro p
  by_cases h : i = j
  · subst j
    simp [modeCartan, modeCreate, modeAnn, Module.End.mul_apply]
    ring
  · simp [modeCreate, modeAnn, Module.End.mul_apply, h]

/-- All modewise lowering commutators are derived on the polynomial domain. -/
theorem modeCartan_ann (N : ℕ) (i j : Fin N) :
    modeCartan N i * modeAnn N j - modeAnn N j * modeCartan N i =
      if i = j then (-2 : ℂ) • modeAnn N i else 0 := by
  apply LinearMap.ext
  intro p
  by_cases h : i = j
  · subst j
    simp [modeCartan, modeAnn, Module.End.mul_apply, MvPolynomial.smul_eq_C_mul,
      map_ofNat, GaloisForLFunctions.pderiv_comm]
    ring
  · simp [modeCartan, modeAnn, Module.End.mul_apply, h,
      GaloisForLFunctions.pderiv_comm]

/-- Collective pair-creation operator. -/
def totalCreate (N : ℕ) : ManyEnd N := ∑ i, modeCreate N i
/-- Collective pair-annihilation operator. -/
def totalAnn (N : ℕ) : ManyEnd N := ∑ i, modeAnn N i
/-- Twice the collective unscaled pseudo-spin energy. -/
def totalCartan (N : ℕ) : ManyEnd N := ∑ i, modeCartan N i

/-- The sum of `N` independent pairs is again a pseudo-spin representation. -/
theorem totalCartan_create (N : ℕ) :
    totalCartan N * totalCreate N - totalCreate N * totalCartan N =
      (2 : ℂ) • totalCreate N := by
  simp only [totalCartan, totalCreate, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => modeCartan N i * modeCreate N j)]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, modeCartan_create]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.smul_sum.symm

/-- The collective creation/annihilation commutator includes all vacuum shifts. -/
theorem totalCreate_ann (N : ℕ) :
    totalCreate N * totalAnn N - totalAnn N * totalCreate N = -totalCartan N := by
  simp only [totalCartan, totalCreate, totalAnn, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => modeCreate N i * modeAnn N j)]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, modeCreate_ann]
  simp

/-- Collective lowering commutator. -/
theorem totalCartan_ann (N : ℕ) :
    totalCartan N * totalAnn N - totalAnn N * totalCartan N =
      (-2 : ℂ) • totalAnn N := by
  simp only [totalCartan, totalAnn, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => modeCartan N i * modeAnn N j)]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, modeCartan_ann]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.smul_sum.symm

/-- The vacuum carries Cartan weight `N`, hence Bargmann index `N/2`. -/
theorem totalCartan_vacuum (N : ℕ) : totalCartan N (1 : ManyFock N) = (N : ℂ) • 1 := by
  simp [totalCartan, modeCartan, Module.End.mul_apply, MvPolynomial.smul_eq_C_mul]

/-- The collective vacuum is a lowest-weight vector. -/
theorem totalAnn_vacuum (N : ℕ) : totalAnn N (1 : ManyFock N) = 0 := by
  simp [totalAnn, modeAnn, Module.End.mul_apply]

/-- The collective creation ladder above the vacuum. -/
def collectiveState (N m : ℕ) : ManyFock N := (totalCreate N ^ m) 1

@[simp] theorem collectiveState_zero (N : ℕ) : collectiveState N 0 = 1 := by
  simp [collectiveState]

/-- Raising stays inside the vacuum-generated collective sector. -/
theorem collectiveState_succ (N m : ℕ) :
    collectiveState N (m + 1) = totalCreate N (collectiveState N m) := by
  simp [collectiveState, pow_succ', Module.End.mul_apply]

/-- Cartan eigenvalue at every collective excitation level. -/
theorem totalCartan_collectiveState (N m : ℕ) :
    totalCartan N (collectiveState N m) = ((N + 2 * m : ℕ) : ℂ) • collectiveState N m := by
  induction m with
  | zero => simpa using totalCartan_vacuum N
  | succ m ih =>
    have h := congrArg (fun T : ManyEnd N => T (collectiveState N m)) (totalCartan_create N)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, ih,
      map_smul] at h
    rw [collectiveState_succ]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ] at h ⊢
    simp only [MvPolynomial.smul_eq_C_mul, map_add, map_mul, map_ofNat, map_one] at h ⊢
    linear_combination h

/-- Full collective annihilation coefficient for the Bargmann sector `N/2`. -/
theorem totalAnn_collectiveState_succ (N m : ℕ) :
    totalAnn N (collectiveState N (m + 1)) =
      (((m + 1) * (N + m) : ℕ) : ℂ) • collectiveState N m := by
  induction m with
  | zero =>
    have h := congrArg (fun T : ManyEnd N => T (1 : ManyFock N)) (totalCreate_ann N)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, totalAnn_vacuum, map_zero,
      LinearMap.neg_apply, totalCartan_vacuum] at h
    simp only [zero_sub] at h
    simpa [collectiveState_succ] using (neg_inj.mp h)
  | succ m ih =>
    have h := congrArg (fun T : ManyEnd N => T (collectiveState N (m + 1))) (totalCreate_ann N)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
      totalCartan_collectiveState, ih, map_smul] at h
    rw [collectiveState_succ N (m + 1)]
    rw [← collectiveState_succ] at h
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ] at h ⊢
    simp only [MvPolynomial.smul_eq_C_mul, map_add, map_mul, map_ofNat, map_one] at h ⊢
    linear_combination -h

/-- Collective creation is multiplication by the sum of pair monomials. -/
theorem totalCreate_apply (N : ℕ) (p : ManyFock N) :
    totalCreate N p = (∑ i : Fin N, X (i, false) * X (i, true)) * p := by
  simp [totalCreate, modeCreate, Module.End.mul_apply, Finset.sum_mul, mul_assoc]

/-- The collective sector consists of powers of the pair-creation polynomial. -/
theorem collectiveState_eq_pow (N m : ℕ) :
    collectiveState N m = (∑ i : Fin N, X (i, false) * X (i, true)) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [collectiveState_succ, totalCreate_apply, ih, pow_succ']

/-- Every excitation level of a nonempty collection of pairs is nonzero. -/
theorem collectiveState_ne_zero (N m : ℕ) : collectiveState (N + 1) m ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ => (1 : ℂ))) h
  rw [collectiveState_eq_pow] at he
  simp only [map_pow, map_sum, map_mul, MvPolynomial.eval_X, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, map_zero] at he
  have hn : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  exact pow_ne_zero m hn he

end GaloisForLFunctions.HTGeometry.CPV

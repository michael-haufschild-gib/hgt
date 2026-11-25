import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! Integer degrees allow both positive and negative shifts of graded polynomial modules. -/

noncomputable section

open DirectSum MvPolynomial

namespace GlobalTheory

/-- The total-degree grading indexed by the integers. -/
def polyGrading (ι R : Type*) [CommRing R] : ℤ → Submodule R (MvPolynomial ι R) :=
  weightedHomogeneousSubmodule R fun _ : ι => (1 : ℤ)

instance polyGrading.gradedAlgebra (ι R : Type*) [CommRing R] :
    GradedAlgebra (polyGrading ι R) :=
  weightedGradedAlgebra R fun _ : ι => (1 : ℤ)

variable {ι R : Type*} [CommRing R]

theorem weight_one_int (a : ι →₀ ℕ) :
    Finsupp.weight (fun _ : ι => (1 : ℤ)) a = (a.degree : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]

theorem mem_polyGrading_iff {p : MvPolynomial ι R} {n : ℤ} :
    p ∈ polyGrading ι R n ↔ ∀ a, coeff a p ≠ 0 → (a.degree : ℤ) = n := by
  simp only [polyGrading, mem_weightedHomogeneousSubmodule, IsWeightedHomogeneous, weight_one_int]

theorem mem_polyGrading_natCast {p : MvPolynomial ι R} {d : ℕ} :
    p ∈ polyGrading ι R d ↔ p.IsHomogeneous d := by
  simp only [mem_polyGrading_iff, IsHomogeneous, IsWeightedHomogeneous, Nat.cast_inj,
    Finsupp.degree_eq_weight_one]
  rfl

theorem polyGrading_of_neg (ι R : Type*) [CommRing R] {n : ℤ} (hn : n < 0) :
    polyGrading ι R n = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  ext a
  by_contra h
  have := mem_polyGrading_iff.1 hp a h
  omega

theorem X_mem_polyGrading (i : ι) : (X i : MvPolynomial ι R) ∈ polyGrading ι R 1 :=
  mem_polyGrading_natCast (d := 1) |>.2 (isHomogeneous_X R i)

theorem monomial_mem_polyGrading (a : ι →₀ ℕ) (r : R) :
    monomial a r ∈ polyGrading ι R (a.degree : ℤ) :=
  mem_polyGrading_natCast.2 (isHomogeneous_monomial r rfl)

variable {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]

/-- Homogeneous polynomials act by the corresponding shift on the module grading. -/
abbrev PolyGradedSMul (ι : Type*) {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) : Prop :=
  SetLike.GradedSMul (polyGrading ι R) D

theorem grSMul_mem (D : ℤ → Submodule R M) [PolyGradedSMul ι D]
    {p : MvPolynomial ι R} {d n : ℤ} {m : M} (hp : p ∈ polyGrading ι R d) (hm : m ∈ D n) :
    p • m ∈ D (n + d) := by
  rw [add_comm n d]
  exact SetLike.GradedSMul.smul_mem hp hm

section VariableAction

variable [IsScalarTower R (MvPolynomial ι R) M] (D : ℤ → Submodule R M)
  (hX : ∀ (i : ι) (n : ℤ), ∀ m ∈ D n, (X i : MvPolynomial ι R) • m ∈ D (n + 1))
include hX

omit [IsScalarTower R (MvPolynomial ι R) M] in
private theorem X_pow_smul_mem (i : ι) (k : ℕ) (n : ℤ) (m : M) (hm : m ∈ D n) :
    ((X i : MvPolynomial ι R) ^ k) • m ∈ D (n + k) := by
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    rw [pow_succ', mul_smul, Nat.cast_succ, ← add_assoc]
    exact hX i _ _ ih

private theorem monomial_smul_mem (s : ι →₀ ℕ) (a : R) :
    ∀ n : ℤ, ∀ m ∈ D n, (monomial s a : MvPolynomial ι R) • m ∈ D (n + s.degree) := by
  refine Finsupp.induction s ?_ ?_
  · intro n m hm
    rw [← C_apply, ← MvPolynomial.algebraMap_eq, algebraMap_smul]
    simpa using (D n).smul_mem a hm
  · intro i k s _ _ ih n m hm
    rw [monomial_single_add, mul_smul]
    have e : n + ((Finsupp.single i k + s).degree : ℤ) = n + s.degree + k := by
      rw [map_add, Finsupp.degree_single, Nat.cast_add]
      omega
    rw [e]
    exact X_pow_smul_mem D hX i k _ _ (ih n m hm)

private theorem homogeneous_smul_mem {p : MvPolynomial ι R} {d : ℕ} (hp : p.IsHomogeneous d)
    (n : ℤ) (m : M) (hm : m ∈ D n) : p • m ∈ D (n + d) := by
  rw [p.as_sum, Finset.sum_smul]
  refine Submodule.sum_mem _ (fun s hs => ?_)
  have hsd : s.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.1 hs)
  simpa only [hsd] using monomial_smul_mem D hX s (p.coeff s) n m hm

/-- It suffices to check the grading condition on the variables. -/
theorem polyGradedSMul_of_X_smul_mem : PolyGradedSMul ι D where
  smul_mem d n p m hp hm := by
    change p • m ∈ D (d + n)
    rcases lt_or_ge d 0 with hd | hd
    · rw [polyGrading_of_neg ι R hd, Submodule.mem_bot] at hp
      rw [hp, zero_smul]
      exact zero_mem _
    · lift d to ℕ using hd
      rw [add_comm (d : ℤ) n]
      exact homogeneous_smul_mem D hX (mem_polyGrading_natCast.1 hp) n m hm

end VariableAction

end GlobalTheory

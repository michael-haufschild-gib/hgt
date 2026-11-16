import GaloisForLFunctions.RepresentationLifting.Probability.FittingDegreeCounts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The finite-field nilpotent matrix count

Fitting stratification expresses the normalized endomorphism count in
dimension `n` as the sum of normalized nilpotent counts through dimension
`n`. Subtracting adjacent dimensions isolates the next nilpotent count;
the general linear group recurrence evaluates it exactly.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

/-- Nilpotent matrices, represented as endomorphisms of the coordinate space. -/
def finiteFieldNilpotentCount (K : Type*) [Field K] (n : ℕ) : ℕ :=
  Nat.card (NilpotentEnd K (Fin n → K))

/-- Automorphisms of the coordinate space over a finite field. -/
def finiteFieldAutomorphismCount (K : Type*) [Field K] (n : ℕ) : ℕ :=
  Nat.card ((Fin n → K) ≃ₗ[K] (Fin n → K))

variable (K : Type*) [Field K] [Finite K]

local instance {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    Finite (V ≃ₗ[K] V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective

/-- An identity automorphism makes every automorphism count strictly positive. -/
theorem finiteFieldAutomorphismCount_pos (n : ℕ) : 0 < finiteFieldAutomorphismCount K n :=
  Nat.card_pos

/-- The general linear group product formula in coordinate-space notation. -/
theorem finiteFieldAutomorphismCount_eq_prod (n : ℕ) :
    finiteFieldAutomorphismCount K n =
      ∏ i : Fin n, (Nat.card K ^ n - Nat.card K ^ (i : ℕ)) := by
  have h := card_automorphisms_eq_prod (K := K) (V := Fin n → K)
  rw [Module.finrank_pi, Fintype.card_fin] at h
  exact h

/-- Increasing the dimension contributes the last vector choice and a power of the field size. -/
theorem finiteFieldAutomorphismCount_succ (n : ℕ) :
    finiteFieldAutomorphismCount K (n + 1) =
      Nat.card K ^ n * (Nat.card K ^ (n + 1) - 1) * finiteFieldAutomorphismCount K n := by
  rw [finiteFieldAutomorphismCount_eq_prod, Fin.prod_univ_succ]
  have hfactor (i : Fin n) :
      Nat.card K ^ (n + 1) - Nat.card K ^ ((i : ℕ) + 1) =
        Nat.card K * (Nat.card K ^ n - Nat.card K ^ (i : ℕ)) := by
    rw [pow_succ', pow_succ', Nat.mul_sub_left_distrib]
  simp only [Fin.val_zero, pow_zero, Fin.val_succ, hfactor,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [finiteFieldAutomorphismCount_eq_prod]
  ac_rfl

omit [Finite K] in
/-- There is exactly one nilpotent endomorphism of the zero-dimensional space. -/
theorem finiteFieldNilpotentCount_zero : finiteFieldNilpotentCount K 0 = 1 := by
  letI : Nonempty (NilpotentEnd K (Fin 0 → K)) := ⟨⟨0, ⟨1, pow_one 0⟩⟩⟩
  exact Nat.card_unique

/-- Fitting decomposition converts the normalized total count into a sum of nilpotent counts. -/
theorem sum_nilpotentCount_div_automorphismCount (n : ℕ) :
    (∑ d : Fin (n + 1), (finiteFieldNilpotentCount K (d : ℕ) : ℚ) /
      finiteFieldAutomorphismCount K (d : ℕ)) =
        (Nat.card K : ℚ) ^ (n * n) / finiteFieldAutomorphismCount K n := by
  have hfrac (d : Fin (n + 1)) :
      (Nat.card (FittingDegreeStratum K (Fin n → K) (d : ℕ)) : ℚ) /
        finiteFieldAutomorphismCount K n =
      (finiteFieldNilpotentCount K (d : ℕ) : ℚ) / finiteFieldAutomorphismCount K (d : ℕ) := by
    let d' : Fin (Module.finrank K (Fin n → K) + 1) :=
      ⟨d.val, by simpa only [Module.finrank_pi, Fintype.card_fin] using d.isLt⟩
    have h := card_fittingDegreeStratum_mul_standard_aut (K := K) (V := Fin n → K) d'
    change Nat.card (FittingDegreeStratum K (Fin n → K) (d : ℕ)) *
      finiteFieldAutomorphismCount K (d : ℕ) =
        finiteFieldAutomorphismCount K n * finiteFieldNilpotentCount K (d : ℕ) at h
    apply (div_eq_div_iff
      (by exact_mod_cast (finiteFieldAutomorphismCount_pos K n).ne')
      (by exact_mod_cast (finiteFieldAutomorphismCount_pos K (d : ℕ)).ne')).mpr
    exact_mod_cast h.trans (Nat.mul_comm _ _)
  have hsum : (∑ d : Fin (n + 1), Nat.card (FittingDegreeStratum K (Fin n → K) (d : ℕ))) =
      Nat.card K ^ (n * n) := by
    have h := sum_card_fittingDegreeStratum (K := K) (V := Fin n → K)
    rw [Module.finrank_pi, Fintype.card_fin] at h
    rw [h, Nat.card_congr (LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin n)).toEquiv]
    simp only [Matrix, Nat.card_fun, Nat.card_fin, ← pow_mul]
  calc
    _ = ∑ d : Fin (n + 1),
        (Nat.card (FittingDegreeStratum K (Fin n → K) (d : ℕ)) : ℚ) /
          finiteFieldAutomorphismCount K n := Finset.sum_congr rfl fun d _ => (hfrac d).symm
    _ = (↑(∑ d : Fin (n + 1), Nat.card (FittingDegreeStratum K (Fin n → K) (d : ℕ))) : ℚ) /
        finiteFieldAutomorphismCount K n := by
          simp only [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by rw [hsum, Nat.cast_pow]

/-- Subtraction of adjacent Fitting sums gives the next nilpotent count. -/
theorem finiteFieldNilpotentCount_succ (n : ℕ) :
    finiteFieldNilpotentCount K (n + 1) = Nat.card K ^ (n * n + n) := by
  have hs := sum_nilpotentCount_div_automorphismCount K (n + 1)
  rw [Fin.sum_univ_castSucc] at hs
  simp only [Fin.val_castSucc, Fin.val_last] at hs
  rw [sum_nilpotentCount_div_automorphismCount K n] at hs
  have hg : (finiteFieldAutomorphismCount K n : ℚ) ≠ 0 := by
    exact_mod_cast (finiteFieldAutomorphismCount_pos K n).ne'
  have hh : (finiteFieldAutomorphismCount K (n + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (finiteFieldAutomorphismCount_pos K (n + 1)).ne'
  have hp : 1 ≤ Nat.card K ^ (n + 1) :=
    Nat.succ_le_of_lt (pow_pos (Nat.card_pos (α := K)) (n + 1))
  have hr : (finiteFieldAutomorphismCount K (n + 1) : ℚ) =
      (Nat.card K : ℚ) ^ n * ((Nat.card K : ℚ) ^ (n + 1) - 1) *
        finiteFieldAutomorphismCount K n := by
    rw [finiteFieldAutomorphismCount_succ, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_sub hp, Nat.cast_pow, Nat.cast_one]
  have ht := congrArg (fun z : ℚ => z * finiteFieldAutomorphismCount K (n + 1)) hs
  rw [add_mul, div_mul_cancel₀ _ hh, div_mul_cancel₀ _ hh] at ht
  have hc : (Nat.card K : ℚ) ^ (n * n) / finiteFieldAutomorphismCount K n *
      finiteFieldAutomorphismCount K (n + 1) =
        (Nat.card K : ℚ) ^ (n * n + n) * ((Nat.card K : ℚ) ^ (n + 1) - 1) := by
    rw [hr, pow_add]
    field_simp
    ring
  rw [hc, show (n + 1) * (n + 1) = (n * n + n) + (n + 1) by ring, pow_add] at ht
  have ha : (finiteFieldNilpotentCount K (n + 1) : ℚ) =
      (Nat.card K : ℚ) ^ (n * n + n) := by linear_combination ht
  exact_mod_cast ha

/-- The Fine–Herstein count: exactly `q^(n*(n-1))` nilpotent endomorphisms. -/
theorem finiteFieldNilpotentCount_eq (n : ℕ) :
    finiteFieldNilpotentCount K n = Nat.card K ^ (n * (n - 1)) := by
  cases n with
  | zero => simp only [finiteFieldNilpotentCount_zero, Nat.zero_mul, pow_zero]
  | succ n =>
    rw [finiteFieldNilpotentCount_succ]
    simp only [Nat.add_sub_cancel]
    congr 1
    ring

/-- The endomorphism count is the same count for square matrices in standard coordinates. -/
theorem card_nilpotent_matrices (n : ℕ) :
    Nat.card {A : Matrix (Fin n) (Fin n) K // IsNilpotent A} =
      Nat.card K ^ (n * (n - 1)) := by
  let e := LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin n)
  let eN : NilpotentEnd K (Fin n → K) ≃
      {A : Matrix (Fin n) (Fin n) K // IsNilpotent A} :=
    { toFun := fun N => ⟨e N.1, N.2.map e⟩
      invFun := fun A => ⟨e.symm A.1, A.2.map e.symm⟩
      left_inv := fun N => Subtype.ext (e.symm_apply_apply N.1)
      right_inv := fun A => Subtype.ext (e.apply_symm_apply A.1) }
  rw [← Nat.card_congr eN]
  exact finiteFieldNilpotentCount_eq K n

#print axioms finiteFieldNilpotentCount_eq
#print axioms card_nilpotent_matrices

end GaloisForLFunctions.RepresentationLifting.OperatorKernels

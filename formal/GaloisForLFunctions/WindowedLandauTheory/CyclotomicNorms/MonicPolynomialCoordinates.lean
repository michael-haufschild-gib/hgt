import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.StatementI

/-! The lower coefficients parametrize monic polynomials of a
given degree over a field. -/

noncomputable section

open Polynomial

namespace WindowedLandauTheory.CyclotomicNorms

variable {K : Type} [Field K] {N : ℕ}

@[simp] theorem coeff_monicOf_lt (a : Fin N → K) (i : Fin N) :
    (monicOf a).coeff i.val = a i := by
  classical
  unfold monicOf
  rw [coeff_add, coeff_X_pow, if_neg i.isLt.ne, zero_add, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h).symm
  · simp

@[simp] theorem natDegree_monicOf (a : Fin N → K) : (monicOf a).natDegree = N := by
  rw [monicOf, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt a

theorem monic_monicOf (a : Fin N → K) : (monicOf a).Monic :=
  monic_X_pow_add (degree_sum_fin_lt a)

theorem monicOf_coeffs (f : K[X]) (hf : f.Monic) (hN : f.natDegree = N) :
    monicOf (fun i : Fin N => f.coeff i.val) = f := by
  subst N
  rw [monicOf, Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]
  exact hf.as_sum.symm

theorem monicOf_injective : Function.Injective (monicOf (K := K) (N := N)) := by
  intro a b h
  funext i
  simpa only [coeff_monicOf_lt] using congrArg (fun f : K[X] => f.coeff i.val) h

end WindowedLandauTheory.CyclotomicNorms

#print axioms WindowedLandauTheory.CyclotomicNorms.monicOf_coeffs
#print axioms WindowedLandauTheory.CyclotomicNorms.monicOf_injective

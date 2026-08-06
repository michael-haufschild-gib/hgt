import GaloisForLFunctions.HTGeometry.CriticalFibreUpperBound

/-!
# The critical multiplicity is attained off a finite set of scalings

The exact fibre count over a critical observation holds whenever the target `1 + U V` is separable.
Separability is a generic condition, and along a one-parameter scaling of the observed reciprocal
tail this can be made exact: the target of the scaled observation is `1 + c U V`, and a repeated
root of it forces `c` to be the reciprocal of a critical value of `U V`.  There are finitely many
critical values, so all but finitely many scalings of a critical observation have exactly the
critical binomial multiplicity of compatible source jets.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-! ## Separability from the absence of a common root -/

section Coprime

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- **Over an algebraically closed field a polynomial sharing no root with its derivative is
separable.**  A non-unit greatest common divisor has positive degree, hence a root, and that root
is common to both. -/
theorem separable_of_no_common_root {P : K[X]}
    (h : ∀ z : K, P.IsRoot z → ¬ (derivative P).IsRoot z) : P.Separable := by
  classical
  have hcop : IsCoprime P (derivative P) := by
    rw [← EuclideanDomain.gcd_isUnit_iff]
    by_contra hu
    have hdeg : (EuclideanDomain.gcd P (derivative P)).degree ≠ 0 := fun hd =>
      hu (isUnit_iff_degree_eq_zero.2 hd)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
    exact h z (hz.dvd (EuclideanDomain.gcd_dvd_left _ _))
      (hz.dvd (EuclideanDomain.gcd_dvd_right _ _))
  exact hcop

end Coprime

/-! ## The scalings at which a target degenerates -/

section Scalings

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- **Only finitely many scalings make a shifted polynomial inseparable.**  A repeated root of
`1 + c W` is a critical point of `W` at which `W` takes the value `-c⁻¹`, so `c` is determined by
one of the finitely many roots of the derivative. -/
theorem finite_not_separable_scalings {W : K[X]} (hW : 0 < W.natDegree) :
    {c : K | ¬ (1 + C c * W).Separable}.Finite := by
  classical
  have hdW : derivative W ≠ 0 := fun h => by
    have h0 : W.natDegree = 0 := Polynomial.derivative_eq_zero.1 h
    omega
  refine Set.Finite.subset (Finset.finite_toSet
    (((derivative W).roots.toFinset).image (fun z => -(W.eval z)⁻¹))) ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  have hex : ¬ ∀ z : K, (1 + C c * W).IsRoot z → ¬ (derivative (1 + C c * W)).IsRoot z :=
    fun h => hc (separable_of_no_common_root h)
  push Not at hex
  obtain ⟨z, hz1, hz2⟩ := hex
  have he1 : 1 + c * W.eval z = 0 := by
    have := hz1
    simpa [Polynomial.IsRoot] using this
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_mul, add_zero] at he1
    exact one_ne_zero he1
  have he2 : c * (derivative W).eval z = 0 := by
    have := hz2
    simpa [Polynomial.IsRoot, Polynomial.derivative_C_mul] using this
  have hroot : (derivative W).eval z = 0 := by
    rcases mul_eq_zero.1 he2 with h | h
    · exact absurd h hc0
    · exact h
  have hw0 : W.eval z ≠ 0 := by
    intro h
    rw [h, mul_zero, add_zero] at he1
    exact one_ne_zero he1
  have hcv : c = -(W.eval z)⁻¹ := by
    rw [← one_div, ← neg_div, eq_div_iff hw0]
    linear_combination he1
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨z, ?_, hcv.symm⟩)
  exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hdW).2 hroot)

end Scalings

/-! ## The exact count for all but finitely many observations in a scaling family -/

section Family

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {m n : ℕ}

/-- **All but finitely many scalings of a critical observation have exactly the critical binomial
multiplicity of compatible source jets.**  Scaling the observed reciprocal tail preserves its
degree, its depth and its criticality, and moves the target through the pencil `1 + c U V`, all but
finitely many members of which are separable. -/
theorem finite_scalings_not_exact (hm : 0 < m) (hn : 0 < n) {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0) :
    {c : K | Nat.card (criticalFibre K m n U (C c * V))
      ≠ criticalHorizonMultiplicity m n}.Finite := by
  classical
  have hdU : U.degree = (m : ℕ) := Polynomial.degree_eq_of_le_of_coeff_ne_zero hU hUm
  have hdV : V.degree = (n : ℕ) := Polynomial.degree_eq_of_le_of_coeff_ne_zero hV hVn
  have hdUV : (U * V).natDegree = m + n := by
    refine Polynomial.natDegree_eq_of_degree_eq_some ?_
    rw [Polynomial.degree_mul, hdU, hdV]
    exact (Nat.cast_add m n).symm
  refine Set.Finite.subset ((finite_not_separable_scalings (W := U * V) (by omega)).insert 0) ?_
  intro c hc
  by_contra hcm
  simp only [Set.mem_insert_iff, Set.mem_setOf_eq, not_or, not_not] at hcm
  obtain ⟨hc0, hsep⟩ := hcm
  refine hc ?_
  have hVc : (C c * V).degree ≤ (n : ℕ) :=
    le_trans (by rw [← Polynomial.smul_eq_C_mul]; exact Polynomial.degree_smul_le c V) hV
  have hVcn : (C c * V).coeff n ≠ 0 := by
    rw [Polynomial.coeff_C_mul]
    exact mul_ne_zero hc0 hVn
  have hVc0 : (C c * V).coeff 0 = 0 := by
    rw [Polynomial.coeff_C_mul, hV0, mul_zero]
  have hsep' : (1 + U * (C c * V)).Separable := by
    have hrw : (1 : K[X]) + U * (C c * V) = 1 + C c * (U * V) := by ring
    rw [hrw]
    exact hsep
  exact nat_card_criticalFibre_criticalTails hm hn hU hVc hUm hVcn hU0 hVc0 hsep'

end Family

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.CriticalDegreeTailFibre

/-!
# The critical multiplicity bounds every fibre, separable or not

The exact count of the fibre over a critical-degree observation needs the target to be separable:
the fibre is then in bijection with the monic divisors of the target of the first depth, and a
separable split polynomial has exactly a binomial coefficient of them.

Without separability the bijection survives on one side only — a divisor is still determined by its
root multiset, and that multiset is still a sub-multiset of the target's — so the count can only
drop.  The binomial coefficient is therefore an unconditional ceiling for the number of source jets
compatible with a critical observation, attained exactly on the separable targets.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-! ## Monic divisors of a prescribed degree, without separability -/

section Divisors

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- **A monic split polynomial is determined by its root multiset.** -/
theorem monicDivisor_roots_injective {P : K[X]} {m : ℕ} :
    Function.Injective
      (fun A : {A : K[X] // A.Monic ∧ A ∣ P ∧ A.natDegree = m} => A.1.roots) := by
  intro A B h
  have hr : A.1.roots = B.1.roots := h
  exact Subtype.ext (by
    rw [(IsAlgClosed.splits A.1).eq_prod_roots_of_monic A.2.1,
      (IsAlgClosed.splits B.1).eq_prod_roots_of_monic B.2.1, hr])

/-- **The root multiset of a divisor of prescribed degree is a sub-multiset of that size.** -/
theorem roots_mem_powersetCard [DecidableEq K] {P A : K[X]} (hP : P ≠ 0) {m : ℕ}
    (hdvd : A ∣ P) (hdeg : A.natDegree = m) :
    A.roots ∈ (P.roots.powersetCard m).toFinset := by
  rw [Multiset.mem_toFinset, Multiset.mem_powersetCard]
  refine ⟨Polynomial.roots.le_of_dvd hP hdvd, ?_⟩
  rw [← (IsAlgClosed.splits A).natDegree_eq_card_roots]
  exact hdeg

/-- **A nonzero polynomial has finitely many monic divisors of a prescribed degree.** -/
theorem finite_monic_divisors {P : K[X]} (hP : P ≠ 0) (m : ℕ) :
    Finite {A : K[X] // A.Monic ∧ A ∣ P ∧ A.natDegree = m} := by
  classical
  exact Finite.of_injective
    (fun A => (⟨A.1.roots, roots_mem_powersetCard hP A.2.2.1 A.2.2.2⟩ :
      ((P.roots.powersetCard m).toFinset : Finset (Multiset K))))
    fun A B h => monicDivisor_roots_injective (congrArg Subtype.val h)

/-- **A split polynomial has at most a binomial coefficient of monic divisors of a prescribed
degree.**  A monic split polynomial is the product of the linear factors named by its root
multiset, so it is determined by that multiset; the multiset of a divisor is a sub-multiset of the
divided polynomial's, of the divisor's degree, and there are `choose` many of those. -/
theorem nat_card_monic_divisors_le {P : K[X]} (hP : P ≠ 0) (m : ℕ) :
    Nat.card {A : K[X] // A.Monic ∧ A ∣ P ∧ A.natDegree = m} ≤ P.natDegree.choose m := by
  classical
  calc Nat.card {A : K[X] // A.Monic ∧ A ∣ P ∧ A.natDegree = m}
      ≤ Nat.card ((P.roots.powersetCard m).toFinset : Finset (Multiset K)) :=
        Nat.card_le_card_of_injective
          (fun A => (⟨A.1.roots, roots_mem_powersetCard hP A.2.2.1 A.2.2.2⟩ :
            ((P.roots.powersetCard m).toFinset : Finset (Multiset K))))
          fun A B h => monicDivisor_roots_injective (congrArg Subtype.val h)
    _ = ((P.roots.powersetCard m).toFinset).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Multiset.card (P.roots.powersetCard m) := Multiset.toFinset_card_le _
    _ = (Multiset.card P.roots).choose m := Multiset.card_powersetCard _ _
    _ = P.natDegree.choose m := by
        rw [← (IsAlgClosed.splits P).natDegree_eq_card_roots]

end Divisors

/-! ## The unconditional ceiling on a critical fibre -/

section Fibre

variable {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}

/-- **The fibre over any observation with tails of the critical degrees has at most the critical
binomial multiplicity of points.**  No separability is assumed: the fibre injects into the monic
divisors of the target of the first depth, and those are bounded by the binomial coefficient. -/
theorem nat_card_criticalFibre_le (hm : 0 < m) (hn : 0 < n) {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0) :
    Nat.card (criticalFibre K m n U V) ≤ criticalHorizonMultiplicity m n := by
  classical
  obtain ⟨htdeg, -⟩ := degree_leadingCoeff_target_tail hm hU hV hUm hVn
  have hne : (1 + U * V) ≠ 0 := fun h => by
    rw [h, Polynomial.degree_zero] at htdeg
    exact WithBot.coe_ne_bot htdeg.symm
  have hnat : (1 + U * V).natDegree = m + n :=
    Polynomial.natDegree_eq_of_degree_eq_some htdeg
  have : Finite {A : K[X] // A.Monic ∧ A ∣ (1 + U * V) ∧ A.natDegree = m} :=
    finite_monic_divisors hne m
  calc Nat.card (criticalFibre K m n U V)
      ≤ Nat.card {A : K[X] // A.Monic ∧ A ∣ (1 + U * V) ∧ A.natDegree = m} :=
        Nat.card_le_card_of_injective _ (criticalTailToDivisor_injective hm hn hU hV hUm hU0 hV0)
    _ ≤ (1 + U * V).natDegree.choose m := nat_card_monic_divisors_le hne m
    _ = criticalHorizonMultiplicity m n := by rw [hnat]; rfl

end Fibre

end GaloisForLFunctions.HTGeometry

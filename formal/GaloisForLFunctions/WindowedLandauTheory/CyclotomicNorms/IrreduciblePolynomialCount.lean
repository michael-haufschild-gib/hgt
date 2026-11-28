import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.MonicPolynomialCoordinates
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot

/-! Distinct monic irreducibles are coprime, and each of degree
\(d\) divides the polynomial whose roots form the field of size
\(q^d\). Their total degree bounds their number. -/

noncomputable section

open Finset Polynomial

namespace WindowedLandauTheory.CyclotomicNorms

/-- The total degree of distinct monic irreducible divisors is bounded by the degree. -/
theorem card_mul_le_degree_of_irreducibles_dvd {K : Type} [Field K] {d : ℕ}
    (S : Finset (Fin d → K)) (hS : ∀ c ∈ S, Irreducible (monicOf c))
    (P : K[X]) (hP : P ≠ 0) (hdvd : ∀ c ∈ S, monicOf c ∣ P) :
    d * S.card ≤ P.natDegree := by
  classical
  have hcop : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → IsCoprime (monicOf c) (monicOf c') := by
    intro c hc c' hc' hne
    rw [(hS c hc).coprime_iff_not_dvd]
    intro hdv
    apply hne
    apply monicOf_injective
    exact eq_of_monic_of_associated (monic_monicOf c) (monic_monicOf c')
      ((hS c hc).associated_of_dvd (hS c' hc') hdv)
  have hprod : ∏ c ∈ S, monicOf c ∣ P :=
    Finset.prod_dvd_of_coprime (fun c hc c' hc' hne => hcop c hc c' hc' hne) hdvd
  have hdeg : (∏ c ∈ S, monicOf c).natDegree = d * S.card := by
    rw [natDegree_prod_of_monic _ _ (fun c _ => monic_monicOf c),
      Finset.sum_congr rfl (fun c _ => natDegree_monicOf c), Finset.sum_const, smul_eq_mul, mul_comm]
  rw [← hdeg]
  exact natDegree_le_of_dvd hprod hP

open Classical in
theorem irreducible_count_upper (K : Type) [Field K] [Fintype K] (d : ℕ) (hd : 1 ≤ d) :
    d * ((univ : Finset (Fin d → K)).filter (fun a => Irreducible (monicOf a))).card ≤
      Fintype.card K ^ d := by
  classical
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hd0 : d ≠ 0 := by omega
  have hdvd : ∀ f : K[X], Irreducible f → f.natDegree = d → f ∣ X ^ (Fintype.card K ^ d) - X := by
    intro f hf hfd
    haveI := Fact.mk hf
    haveI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
    haveI : Finite (AdjoinRoot f) := Module.finite_of_finite K
    letI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
    have hcard : Fintype.card (AdjoinRoot f) = Fintype.card K ^ d := by
      rw [Module.card_fintype (AdjoinRoot.powerBasis hf.ne_zero).basis, Fintype.card_fin,
        AdjoinRoot.powerBasis_dim, hfd]
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← hcard, FiniteField.pow_card,
      sub_self]
  rw [← FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hd0 hq1]
  apply card_mul_le_degree_of_irreducibles_dvd _ (fun c hc => (Finset.mem_filter.mp hc).2) _
    (FiniteField.X_pow_card_pow_sub_X_ne_zero K hd0 hq1)
  intro c hc
  exact hdvd _ (Finset.mem_filter.mp hc).2 (natDegree_monicOf c)

open Classical in
def nonzeroIrreducibleCoefficients (K : Type) [Field K] [Fintype K] (d : ℕ) : Finset (Fin d → K) :=
  univ.filter (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)

theorem mem_nonzeroIrreducibleCoefficients {K : Type} [Field K] [Fintype K] {d : ℕ}
    {c : Fin d → K} :
    c ∈ nonzeroIrreducibleCoefficients K d ↔ Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 := by
  simp only [nonzeroIrreducibleCoefficients, Finset.mem_filter, Finset.mem_univ, true_and]

theorem irreducible_count_upper_nonzero (K : Type) [Field K] [Fintype K] (d : ℕ) (hd : 1 ≤ d) :
    d * (nonzeroIrreducibleCoefficients K d).card ≤ Fintype.card K ^ d - 1 := by
  classical
  let q := Fintype.card K
  have hq : 1 < q := Fintype.one_lt_card
  have hn : 0 < q ^ d - 1 := Nat.sub_pos_of_lt (one_lt_pow₀ hq (by omega : d ≠ 0))
  let P : K[X] := X ^ (q ^ d - 1) - C 1
  have hP : P ≠ 0 := X_pow_sub_C_ne_zero hn _
  have hPd : P.natDegree = q ^ d - 1 := natDegree_X_pow_sub_C
  rw [← hPd]
  apply card_mul_le_degree_of_irreducibles_dvd _
    (fun c hc => (Finset.mem_filter.mp hc).2.1) P hP
  intro c hc
  obtain ⟨hc', hc₀⟩ := (Finset.mem_filter.mp hc).2
  let f := monicOf c
  letI : Fact (Irreducible f) := ⟨hc'⟩
  letI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hc'.ne_zero).finite
  letI : Finite (AdjoinRoot f) := Module.finite_of_finite K
  letI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot f) = q ^ d := by
    rw [Module.card_fintype (AdjoinRoot.powerBasis hc'.ne_zero).basis, Fintype.card_fin,
      AdjoinRoot.powerBasis_dim, natDegree_monicOf c]
  have hroot : AdjoinRoot.root f ≠ 0 := by
    intro hz
    have hdvd : f ∣ (X : K[X]) := AdjoinRoot.mk_eq_zero.mp hz
    have hass := hc'.associated_of_dvd (irreducible_X : Irreducible (X : K[X])) hdvd
    have he := eq_of_monic_of_associated (monic_monicOf c) monic_X hass
    exact hc₀ (by rw [show monicOf c = X from he, coeff_X_zero])
  rw [← AdjoinRoot.mk_eq_zero]
  change AdjoinRoot.mk f P = 0
  rw [show P = X ^ (q ^ d - 1) - 1 from by simp [P], map_sub, map_pow, map_one,
    AdjoinRoot.mk_X, ← hcard, FiniteField.pow_card_sub_one_eq_one _ hroot, sub_self]

end WindowedLandauTheory.CyclotomicNorms

#print axioms WindowedLandauTheory.CyclotomicNorms.irreducible_count_upper
#print axioms WindowedLandauTheory.CyclotomicNorms.irreducible_count_upper_nonzero

import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.IrreduciblePolynomialCount
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.SquarefreePolynomialWeights

/-! A squarefree polynomial is determined by the subsets of its
monic irreducible factors in each degree. Their cardinalities
bound the number of polynomials with a prescribed degree type. -/

noncomputable section

open Polynomial Finset UniqueFactorizationMonoid
open WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

open Classical in
private theorem factor_data {K : Type} [Field K] {N : ℕ} (c : Fin N → K)
    (hc : (monicOf c).coeff 0 ≠ 0) {q : K[X]} (hq : q ∈ normalizedFactors (monicOf c)) :
    q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧ q.natDegree ∈ Icc 1 N := by
  have hi := irreducible_of_normalized_factor q hq
  have hm : q.Monic := by
    have h := monic_normalize hi.ne_zero
    rwa [normalize_normalized_factor q hq] at h
  have hd := dvd_of_mem_normalizedFactors hq
  refine ⟨hm, hi, fun h => hc (X_dvd_iff.mp ((X_dvd_iff.mpr h).trans hd)), Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
  · exact hi.natDegree_pos
  · have h := natDegree_le_of_dvd hd (monic_monicOf c).ne_zero
    rwa [natDegree_monicOf] at h

open Classical in
theorem squarefree_type_count_upper (K : Type) [Field K] [Fintype K] (N : ℕ) (n : ℕ → ℕ) :
    ((univ : Finset (Fin N → K)).filter (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧
      ∀ d ∈ Icc 1 N, (degreeType (monicOf c)).count d = n d)).card ≤
      ∏ d ∈ Icc 1 N, (nonzeroIrreducibleCoefficients K d).card.choose (n d) := by
  classical
  let I := Icc 1 N
  let A : ℕ → Finset K[X] := fun d => (nonzeroIrreducibleCoefficients K d).image monicOf
  let S : Finset (Fin N → K) :=
    univ.filter (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧
      ∀ d ∈ I, (degreeType (monicOf c)).count d = n d)
  let T := I.pi (fun d => (A d).powersetCard (n d))
  let factors (c : Fin N → K) := (normalizedFactors (monicOf c)).toFinset
  let F (c : Fin N → K) (d : ℕ) (_ : d ∈ I) :=
    (factors c).filter (fun q => q.natDegree = d)
  have hS (c : Fin N → K) (hc : c ∈ S) : Squarefree (monicOf c) ∧
      (monicOf c).coeff 0 ≠ 0 ∧ ∀ d ∈ I, (degreeType (monicOf c)).count d = n d :=
    (Finset.mem_filter.mp hc).2
  have hfactors (c : Fin N → K) (hc : c ∈ S) : (factors c).val = normalizedFactors (monicOf c) := by
    change (normalizedFactors (monicOf c)).toFinset.val = _
    rw [Multiset.toFinset_val]
    exact Multiset.dedup_eq_self.mpr
      ((squarefree_iff_nodup_normalizedFactors (monic_monicOf c).ne_zero).mp (hS c hc).1)
  have hmap : Set.MapsTo F (S : Set (Fin N → K)) T := by
    intro c hc
    have hc' : c ∈ S := hc
    apply Finset.mem_pi.mpr
    intro d hd
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro q hq
      obtain ⟨hq, hdeg⟩ := Finset.mem_filter.mp hq
      obtain ⟨hm, hi, h0, -⟩ := factor_data c (hS c hc').2.1 (Multiset.mem_toFinset.mp hq)
      have he := monicOf_coeffs q hm hdeg
      apply Finset.mem_image.mpr
      refine ⟨fun j : Fin d => q.coeff j.val, ?_, he⟩
      unfold nonzeroIrreducibleCoefficients
      rw [Finset.mem_filter, he]
      exact ⟨Finset.mem_univ _, hi, h0⟩
    · have he : (degreeType (monicOf c)).count d = (F c d hd).card := by
        rw [degreeType, ← hfactors c hc', Multiset.count_map]
        exact congrArg Multiset.card (Multiset.filter_congr (fun q _ => eq_comm))
      exact he.symm.trans ((hS c hc').2.2 d hd)
  have hinj : Set.InjOn F (S : Set (Fin N → K)) := by
    intro c hc c' hc' he
    have hf (c c' : Fin N → K) (hc : c ∈ S) (he : F c = F c') : factors c ⊆ factors c' := by
      intro q hq
      let d := q.natDegree
      have hd : d ∈ I := (factor_data c (hS c hc).2.1 (Multiset.mem_toFinset.mp hq)).2.2.2
      have hm : q ∈ F c d hd := Finset.mem_filter.mpr ⟨hq, rfl⟩
      have hc' := congrFun (congrFun he d) hd
      rw [hc'] at hm
      exact (Finset.mem_filter.mp hm).1
    have hset := Finset.Subset.antisymm (hf c c' hc he) (hf c' c hc' he.symm)
    apply monicOf_injective
    have h := congrArg (fun U : Finset K[X] => U.val.prod) hset
    rw [hfactors c hc, hfactors c' hc', prod_normalizedFactors_eq (monic_monicOf c).ne_zero,
      prod_normalizedFactors_eq (monic_monicOf c').ne_zero,
      (monic_monicOf c).normalize_eq_self, (monic_monicOf c').normalize_eq_self] at h
    exact h
  have hT : T.card = ∏ d ∈ I, (nonzeroIrreducibleCoefficients K d).card.choose (n d) := by
    change (I.pi (fun d => (A d).powersetCard (n d))).card = _
    rw [Finset.card_pi]
    refine Finset.prod_congr rfl fun d _ => ?_
    rw [Finset.card_powersetCard]
    change ((nonzeroIrreducibleCoefficients K d).image monicOf).card.choose (n d) = _
    rw [Finset.card_image_of_injective _ monicOf_injective]
  have h := (Finset.card_le_card_of_injOn F hmap hinj).trans_eq hT
  convert h using 1 <;> first | rfl | (congr 1; ext c; simp [S, I])

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.squarefree_type_count_upper

import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.CrossFactorCollisionCount
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LocalRowWeightBounds

/-! A prime-to-part collision lies either within one irreducible
factor or across two distinct factors. In both cases the prime
divides one of the relevant residue group orders. -/

noncomputable section

open Polynomial Finset WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

variable (g N : ℕ) [Fact g.Prime]

def divisorEvent (P : (ZMod g)[X]) : Set (Fin N → ZMod g) :=
  {c | c ∈ squarefreeCoefficients g N ∧ P ∣ monicOf c}

def smallPrimaryPrimes (g δ : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.filter (fun l => l ^ (4 * padicValNat l (g ^ δ - 1)) ≤ g ^ δ)

def sameFactorEvents : Set (Fin N → ZMod g) :=
  ⋃ δ ∈ Icc 2 N, ⋃ l ∈ smallPrimaryPrimes g δ (g ^ δ - 1).primeFactors,
    ⋃ a ∈ sameFactorCandidates g δ l, divisorEvent g N (monicOf a)

def crossFactorEvents : Set (Fin N → ZMod g) :=
  ⋃ δ ∈ Icc 1 N, ⋃ δ' ∈ Icc 1 δ,
    ⋃ l ∈ smallPrimaryPrimes g δ ((g ^ δ - 1).primeFactors ∪ (g ^ δ' - 1).primeFactors),
      ⋃ b ∈ nonzeroIrreducibleCoefficients (ZMod g) δ',
        ⋃ a ∈ crossFactorCandidates g δ l (monicOf b),
          divisorEvent g N (monicOf a * monicOf b)

private theorem mem_rootsBar_iff {P : (ZMod g)[X]} (hm : P.Monic) {x : Fbar g} :
    x ∈ rootsBar P ↔ aeval x P = 0 := by
  rw [rootsBar, Polynomial.mem_roots (hm.map _).ne_zero, Polynomial.IsRoot, eval_map_algebraMap]

private theorem primeToPart_eq_of_nondvd {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0)
    {x : Fbar g} (hx : x ^ n = 1) (hln : ¬ l ∣ n) : primeToPart l x = x := by
  have h := primeToPart_pow_ordProj hl hn x hx
  rwa [Nat.factorization_eq_zero_of_not_dvd hln, pow_zero, pow_one, pow_one] at h

private theorem exists_factor_of_aeval {P : (ZMod g)[X]} (hm : P.Monic) (h0 : P.coeff 0 ≠ 0)
    {x : Fbar g} (hx : aeval x P = 0) :
    ∃ (δ : ℕ) (a : Fin δ → ZMod g), δ ∈ Icc 1 P.natDegree ∧
      a ∈ nonzeroIrreducibleCoefficients (ZMod g) δ ∧ monicOf a ∣ P ∧ aeval x (monicOf a) = 0 := by
  have hx0 := root_ne_zero_of_coeff_zero h0 hx
  have hint : IsIntegral (ZMod g) x := ⟨P, hm, hx⟩
  let Q := minpoly (ZMod g) x
  have hQ : Irreducible Q := minpoly.irreducible hint
  have hmon : Q.Monic := minpoly.monic hint
  have hdvd : Q ∣ P := minpoly.dvd _ _ hx
  refine ⟨Q.natDegree, (fun i => Q.coeff i), Finset.mem_Icc.mpr
    ⟨hQ.natDegree_pos, natDegree_le_of_dvd hdvd hm.ne_zero⟩, ?_⟩
  simp only [nonzeroIrreducibleCoefficients, Finset.mem_filter, Finset.mem_univ, true_and,
    monicOf_coeffs Q hmon rfl]
  exact ⟨⟨hQ, minpoly.coeff_zero_ne_zero hint hx0⟩, hdvd, minpoly.aeval _ _⟩

private theorem mem_crossFactorEvents {c : Fin N → ZMod g} (hc : c ∈ squarefreeCoefficients g N)
    {δ δ' l : ℕ} (hδ' : 1 ≤ δ') (hle : δ' ≤ δ) (hδ : δ ∈ Icc 1 N)
    (hl : l.Prime) (hsmall : l ^ (4 * padicValNat l (g ^ δ - 1)) ≤ g ^ δ)
    {a : Fin δ → ZMod g} {b : Fin δ' → ZMod g}
    (ha : a ∈ nonzeroIrreducibleCoefficients (ZMod g) δ)
    (hb : b ∈ nonzeroIrreducibleCoefficients (ZMod g) δ')
    (ha' : monicOf a ∣ monicOf c) (hb' : monicOf b ∣ monicOf c)
    {x y : Fbar g} (hx : aeval x (monicOf a) = 0) (hy : aeval y (monicOf b) = 0)
    (he : primeToPart l x = primeToPart l y) (hne : x ≠ y) (hab : monicOf a ≠ monicOf b) :
    c ∈ crossFactorEvents g N := by
  obtain ⟨hai, ha0⟩ := mem_nonzeroIrreducibleCoefficients.mp ha
  obtain ⟨hbi, hb0⟩ := mem_nonzeroIrreducibleCoefficients.mp hb
  have hm := (prime_field_exp_pos g (Finset.mem_Icc.mp hδ).1).ne'
  have hm' := (prime_field_exp_pos g hδ').ne'
  have hpr : l ∈ (g ^ δ - 1).primeFactors ∪ (g ^ δ' - 1).primeFactors := by
    rw [Finset.mem_union, Nat.mem_primeFactors, Nat.mem_primeFactors]
    by_contra! hn
    have hlx : ¬ l ∣ g ^ δ - 1 := fun h => hm (hn.1 hl h)
    have hly : ¬ l ∣ g ^ δ' - 1 := fun h => hm' (hn.2 hl h)
    have hex := primeToPart_eq_of_nondvd g hl hm (root_pow_monicOf g hai ha0 hx) hlx
    have hey := primeToPart_eq_of_nondvd g hl hm' (root_pow_monicOf g hbi hb0 hy) hly
    exact hne (hex.symm.trans (he.trans hey))
  have hcop : IsCoprime (monicOf a) (monicOf b) := by
    rw [hai.coprime_iff_not_dvd]
    intro hd
    exact hab (eq_of_monic_of_associated (monic_monicOf a) (monic_monicOf b)
      (hai.associated_of_dvd hbi hd))
  simp only [crossFactorEvents, Set.mem_iUnion]
  refine ⟨δ, hδ, δ', Finset.mem_Icc.mpr ⟨hδ', hle⟩, l, Finset.mem_filter.mpr ⟨hpr, hsmall⟩,
    b, hb, a, ?_, hc, hcop.mul_dvd ha' hb'⟩
  exact (mem_crossFactorCandidates g).mpr ⟨ha, x, y, hx, (mem_rootsBar_iff g (monic_monicOf b)).mpr hy, he⟩

theorem root_collision_events_cover :
    {c | c ∈ squarefreeCoefficients g N ∧ ¬ separatesPrimeToParts g N c} ⊆
      sameFactorEvents g N ∪ crossFactorEvents g N := by
  classical
  rintro c ⟨hc, hb⟩
  obtain ⟨-, hc0⟩ := (Finset.mem_filter.mp hc).2
  unfold separatesPrimeToParts at hb
  push Not at hb
  obtain ⟨l, hl, hBB, x, hx, y, hy, he, hne⟩ := hb
  have hs (δ : ℕ) (hd : δ ∈ Icc 1 N) : l ^ (4 * padicValNat l (g ^ δ - 1)) ≤ g ^ δ := by
    have ⟨h1, h2⟩ := Finset.mem_Icc.mp hd
    exact Nat.le_of_not_gt fun h => hBB (Or.inr ⟨δ, h1, h2, hl, h⟩)
  have hfx := (mem_rootsBar_iff g (monic_monicOf c)).mp hx
  have hfy := (mem_rootsBar_iff g (monic_monicOf c)).mp hy
  obtain ⟨δ, a, hδ, ha, ha', hax⟩ := exists_factor_of_aeval g (monic_monicOf c) hc0 hfx
  obtain ⟨δ', b, hδ', hb, hb', hby⟩ := exists_factor_of_aeval g (monic_monicOf c) hc0 hfy
  rw [natDegree_monicOf] at hδ hδ'
  by_cases hab : monicOf a = monicOf b
  · apply Set.mem_union_left
    have hay : aeval y (monicOf a) = 0 := hab.symm ▸ hby
    have hδ2 : 2 ≤ δ := by
      let S := (rootsBar (monicOf a)).toFinset
      have hxS : x ∈ S := Multiset.mem_toFinset.mpr ((mem_rootsBar_iff g (monic_monicOf a)).mpr hax)
      have hyS : y ∈ S := Multiset.mem_toFinset.mpr ((mem_rootsBar_iff g (monic_monicOf a)).mpr hay)
      have hS : 1 < S.card := Finset.one_lt_card.mpr ⟨x, hxS, y, hyS, hne⟩
      have hcard : S.card ≤ δ := by
        calc
          S.card ≤ (rootsBar (monicOf a)).card := Multiset.toFinset_card_le _
          _ ≤ ((monicOf a).map (algebraMap (ZMod g) (Fbar g))).natDegree := Polynomial.card_roots' _
          _ = δ := (natDegree_map _).trans (natDegree_monicOf a)
      omega
    have hn := (prime_field_exp_pos g (Finset.mem_Icc.mp hδ).1).ne'
    have ⟨hai, ha0⟩ := mem_nonzeroIrreducibleCoefficients.mp ha
    have hld : l ∣ g ^ δ - 1 := by
      by_contra h
      have hx' := primeToPart_eq_of_nondvd g hl hn (root_pow_monicOf g hai ha0 hax) h
      have hy' := primeToPart_eq_of_nondvd g hl hn (root_pow_monicOf g hai ha0 hay) h
      exact hne (hx'.symm.trans (he.trans hy'))
    simp only [sameFactorEvents, Set.mem_iUnion]
    refine ⟨δ, Finset.mem_Icc.mpr ⟨hδ2, (Finset.mem_Icc.mp hδ).2⟩, l,
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hl, hld, hn⟩, hs δ hδ⟩,
      a, (mem_sameFactorCandidates g).mpr ⟨ha, x, y, hax, hay, he, hne⟩, hc, ha'⟩
  · apply Set.mem_union_right
    rcases le_total δ' δ with h | h
    · exact mem_crossFactorEvents g N hc (Finset.mem_Icc.mp hδ').1 h hδ hl (hs δ hδ)
        ha hb ha' hb' hax hby he hne hab
    · exact mem_crossFactorEvents g N hc (Finset.mem_Icc.mp hδ).1 h hδ' hl (hs δ' hδ')
        hb ha hb' ha' hby hax he.symm hne.symm (Ne.symm hab)

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.root_collision_events_cover

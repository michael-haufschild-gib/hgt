import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.CollisionFactorCounts

/-! For each root of a second polynomial, first-factor candidates
inject into one fiber of the prime-to-part projection. The degree
of the second polynomial bounds the number of these fibers. -/

noncomputable section

open Polynomial Finset WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

private theorem card_same_prime_to_part_le {L : Type*} [Field L] {l n : ℕ}
    (hl : l.Prime) (hn : n ≠ 0) (z : L) (S : Finset L)
    (hS : ∀ x ∈ S, x ^ n = 1 ∧ primeToPart l x = z) : S.card ≤ l ^ padicValNat l n := by
  classical
  rcases S.eq_empty_or_nonempty with h | ⟨y, hy⟩
  · simp [h]
  have hy0 : y ≠ 0 := by
    intro h0
    have h := (hS y hy).1
    rw [h0, zero_pow hn] at h
    exact zero_ne_one h
  let m := l ^ padicValNat l n
  have hm : 0 < m := pow_pos hl.pos _
  have hmap : Set.MapsTo (fun x : L => x / y) (S : Set L) (nthRootsFinset m (1 : L)) := by
    intro x hx
    change x / y ∈ nthRootsFinset m (1 : L)
    rw [mem_nthRootsFinset hm]
    have h := div_pow_ordProj_max_eq_one hl hn hn (hS x hx).1 (hS y hy).1 hy0
      ((hS x hx).2.trans (hS y hy).2.symm)
    simpa only [m, max_self, Nat.factorization_def _ hl] using h
  have hi : Set.InjOn (fun x : L => x / y) (S : Set L) := fun x _ x' _ h =>
    (div_left_inj' hy0).mp h
  calc
    S.card ≤ (nthRootsFinset m (1 : L)).card := Finset.card_le_card_of_injOn _ hmap hi
    _ ≤ m := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m 1)

variable (g : ℕ) [Fact g.Prime]

open Classical in
def crossFactorCandidates (δ l : ℕ) (P : (ZMod g)[X]) : Finset (Fin δ → ZMod g) :=
  (nonzeroIrreducibleCoefficients (ZMod g) δ).filter (fun c =>
    ∃ (x : Fbar g) (y : Fbar g), aeval x (monicOf c) = 0 ∧ y ∈ rootsBar P ∧
      primeToPart l x = primeToPart l y)

theorem mem_crossFactorCandidates {δ l : ℕ} {c : Fin δ → ZMod g} {P : (ZMod g)[X]} :
    c ∈ crossFactorCandidates g δ l P ↔ c ∈ nonzeroIrreducibleCoefficients (ZMod g) δ ∧
      ∃ (x : Fbar g) (y : Fbar g), aeval x (monicOf c) = 0 ∧ y ∈ rootsBar P ∧
        primeToPart l x = primeToPart l y := by
  simp only [crossFactorCandidates, Finset.mem_filter]

theorem cross_factor_count (δ l : ℕ) (hl : l.Prime) (hδ : 1 ≤ δ) (P : (ZMod g)[X]) :
    (crossFactorCandidates g δ l P).card ≤ P.natDegree * l ^ padicValNat l (g ^ δ - 1) := by
  classical
  let n := g ^ δ - 1
  have hn := prime_field_exp_pos g hδ
  let R := (rootsBar P).toFinset
  let A (y : Fbar g) := (nonzeroIrreducibleCoefficients (ZMod g) δ).filter (fun c =>
    ∃ x : Fbar g, aeval x (monicOf c) = 0 ∧ primeToPart l x = primeToPart l y)
  have hsub : crossFactorCandidates g δ l P ⊆ R.biUnion A := by
    intro c hc
    have ⟨hc0, x, y, hx, hy, hxy⟩ := (mem_crossFactorCandidates g).mp hc
    exact Finset.mem_biUnion.mpr ⟨y, Multiset.mem_toFinset.mpr hy,
      Finset.mem_filter.mpr ⟨hc0, x, hx, hxy⟩⟩
  have hA (y : Fbar g) : (A y).card ≤ l ^ padicValNat l n := by
    let S := (nthRootsFinset n (1 : Fbar g)).filter (fun x => primeToPart l x = primeToPart l y)
    have hS (x : Fbar g) (hx : x ∈ S) : x ^ n = 1 ∧ primeToPart l x = primeToPart l y := by
      have ⟨h, he⟩ := Finset.mem_filter.mp hx
      exact ⟨(mem_nthRootsFinset hn (1 : Fbar g)).mp h, he⟩
    have hx (c : Fin δ → ZMod g) (hc : c ∈ A y) : ∃ x ∈ S, aeval x (monicOf c) = 0 := by
      obtain ⟨hc0, x, hx, hxy⟩ := Finset.mem_filter.mp hc
      have ⟨hi, h0⟩ := mem_nonzeroIrreducibleCoefficients.mp hc0
      exact ⟨x, Finset.mem_filter.mpr ⟨(mem_nthRootsFinset hn (1 : Fbar g)).mpr (root_pow_monicOf g hi h0 hx), hxy⟩, hx⟩
    choose! x hxS hxP using hx
    have hinj : Set.InjOn x (A y : Set (Fin δ → ZMod g)) := by
      intro c hc c' hc' he
      have hi (a : Fin δ → ZMod g) (ha : a ∈ A y) : Irreducible (monicOf a) :=
        (mem_nonzeroIrreducibleCoefficients.mp (Finset.mem_filter.mp ha).1).1
      have h1 := minpoly.eq_of_irreducible_of_monic (hi c hc) (hxP c hc) (monic_monicOf c)
      have h2 := minpoly.eq_of_irreducible_of_monic (hi c' hc') (hxP c' hc') (monic_monicOf c')
      exact monicOf_injective (h1.trans (he ▸ h2.symm))
    exact (Finset.card_le_card_of_injOn x hxS hinj).trans
      (card_same_prime_to_part_le hl hn.ne' _ S hS)
  have hR : R.card ≤ P.natDegree := by
    calc R.card ≤ (rootsBar P).card := Multiset.toFinset_card_le _
      _ ≤ (P.map (algebraMap (ZMod g) (Fbar g))).natDegree := Polynomial.card_roots' _
      _ = P.natDegree := Polynomial.natDegree_map _
  calc
    (crossFactorCandidates g δ l P).card ≤ ∑ y ∈ R, (A y).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ R, l ^ padicValNat l n := Finset.sum_le_sum fun y _ => hA y
    _ = R.card * l ^ padicValNat l n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ P.natDegree * l ^ padicValNat l n := Nat.mul_le_mul_right _ hR

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.cross_factor_count

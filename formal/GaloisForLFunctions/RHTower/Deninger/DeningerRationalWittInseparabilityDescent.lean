import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittPerfectFieldGaloisDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittCanonicalMultiplication
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.Minpoly.IsConjRoot

/-!
# Imperfect-field rational-Witt inseparability descent

For an arbitrary field `K`, this module identifies the image of literal rational-Witt
vectors over `K` inside the algebraic closure.  On the reduced monoid algebra
`ℤ[(AlgebraicClosure K)ˣ]`, the image consists exactly of elements fixed by the absolute
Galois group whose coefficient at every atom `a` is divisible by the inseparability degree
of `K(a)/K`.

The proof retains repeated roots.  Each minimal polynomial contributes one complete Galois
orbit block with multiplicity equal to its inseparability degree.  Invariant divisible
multisets peel into these blocks.  Conversely, minimal-polynomial division proves that every
root multiplicity of a mapped base polynomial is divisible by the same degree.

This is Deninger's imperfect-field source classification.  It uses no perfectness assumption,
no descent premise, and no added primitive.
-/


namespace RHTower
noncomputable section

open Polynomial

local instance deningerRationalWittAlgebraicClosureDecidableEq
    {K : Type*} [Field K] : DecidableEq (AlgebraicClosure K) :=
  Classical.decEq _

attribute [local instance] Classical.propDecidable

noncomputable def deningerRationalWittInsepDegree (K : Type*) [Field K]
    (a : AlgebraicClosure K) : ℕ :=
  Field.finInsepDegree K (IntermediateField.adjoin K {a})

theorem deningerRationalWittInsepDegree_eq_charPow
    (K : Type*) [Field K] (a : AlgebraicClosure K) :
    ∃ n : ℕ, deningerRationalWittInsepDegree K a = (ringExpChar K) ^ n := by
  let q := ringExpChar K
  let f := minpoly K a
  have hi : Irreducible f := minpoly.irreducible (Algebra.IsIntegral.isIntegral a)
  obtain ⟨g, hgsep, n, hgf⟩ := hi.hasSeparableContraction q
  have hsep : Field.finSepDegree K (IntermediateField.adjoin K {a}) = f.natSepDegree :=
    IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree K
      (AlgebraicClosure K) (Algebra.IsAlgebraic.isAlgebraic a)
  have hrank : Module.finrank K (IntermediateField.adjoin K {a}) = f.natDegree :=
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral a)
  have hmul := Field.finSepDegree_mul_finInsepDegree K
    (IntermediateField.adjoin K {a})
  have hisc : Polynomial.IsSeparableContraction q f g := ⟨hgsep, n, hgf⟩
  have hnatsep : f.natSepDegree = g.natDegree := by
    exact hisc.natSepDegree_eq
  have hnatdeg : f.natDegree = g.natDegree * q ^ n := by
    rw [← hgf, Polynomial.natDegree_expand]
  refine ⟨n, ?_⟩
  change Field.finInsepDegree K (IntermediateField.adjoin K {a}) = q ^ n
  rw [hsep, hrank, hnatsep, hnatdeg] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by
    rw [← hnatsep]
    exact (Polynomial.natSepDegree_ne_zero f
      (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral a)).ne').pos) hmul

theorem deningerRationalWittInsepDegree_eq_natDegree_div_natSepDegree
    (K : Type*) [Field K] (a : AlgebraicClosure K) :
    deningerRationalWittInsepDegree K a =
      (minpoly K a).natDegree / (minpoly K a).natSepDegree := by
  let f := minpoly K a
  have hsep : Field.finSepDegree K (IntermediateField.adjoin K {a}) = f.natSepDegree :=
    IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree K
      (AlgebraicClosure K) (Algebra.IsAlgebraic.isAlgebraic a)
  have hrank : Module.finrank K (IntermediateField.adjoin K {a}) = f.natDegree :=
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral a)
  have hmul := Field.finSepDegree_mul_finInsepDegree K
    (IntermediateField.adjoin K {a})
  change Field.finInsepDegree K (IntermediateField.adjoin K {a}) = _
  rw [hsep, hrank] at hmul
  exact Nat.eq_div_of_mul_eq_right
    (Polynomial.natSepDegree_ne_zero f
      (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral a)).ne') hmul

theorem deningerRationalWittInsepDegree_algEquiv
    (K : Type*) [Field K]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (a : AlgebraicClosure K) :
    deningerRationalWittInsepDegree K (g a) = deningerRationalWittInsepDegree K a := by
  rw [deningerRationalWittInsepDegree_eq_natDegree_div_natSepDegree,
    deningerRationalWittInsepDegree_eq_natDegree_div_natSepDegree,
    minpoly.algEquiv_eq g a]

theorem deningerRationalWittMinpolyAroots_count_eq_insepDegree
    (K : Type*) [Field K] (a b : AlgebraicClosure K)
    (hb : b ∈ (minpoly K a).aroots (AlgebraicClosure K)) :
    ((minpoly K a).aroots (AlgebraicClosure K)).count b =
      deningerRationalWittInsepDegree K a := by
  classical
  let L := AlgebraicClosure K
  let q := ringExpChar K
  let f := minpoly K a
  let i := algebraMap K L
  have hi : Irreducible f := minpoly.irreducible (Algebra.IsIntegral.isIntegral a)
  obtain ⟨g, hgsep, n, hgf⟩ := hi.hasSeparableContraction q
  letI : ExpChar L q := expChar_of_injective_ringHom i.injective q
  have hmap : f.map i = Polynomial.expand L (q ^ n) (g.map i) := by
    rw [← hgf, Polynomial.map_expand]
  have hroots : (f.map i).roots =
      q ^ n • (g.map i).roots.map (iterateFrobeniusEquiv L q n).symm := by
    rw [hmap, Polynomial.roots_expand_pow]
  change b ∈ (f.map i).roots at hb
  have hbmap : b ∈ (g.map i).roots.map (iterateFrobeniusEquiv L q n).symm := by
    have hc : 0 < (q ^ n •
        (g.map i).roots.map (iterateFrobeniusEquiv L q n).symm).count b := by
      exact Multiset.count_pos.mpr (hroots ▸ hb)
    rw [Multiset.count_nsmul] at hc
    exact Multiset.count_pos.mp (CanonicallyOrderedAdd.mul_pos.mp hc).2
  obtain ⟨r, hr, hrb⟩ := Multiset.mem_map.mp hbmap
  subst b
  change (f.map i).roots.count ((iterateFrobeniusEquiv L q n).symm r) = _
  rw [hroots, Multiset.count_nsmul,
    Multiset.count_map_eq_count' _ _ (iterateFrobeniusEquiv L q n).symm.injective]
  have hcount : (g.map i).roots.count r = 1 := by
    apply Multiset.count_eq_one_of_mem
    · exact Polynomial.nodup_roots (Polynomial.Separable.map hgsep (f := i))
    · exact hr
  rw [hcount, mul_one]
  have hsep : Field.finSepDegree K (IntermediateField.adjoin K {a}) = f.natSepDegree :=
    IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree K
      (AlgebraicClosure K) (Algebra.IsAlgebraic.isAlgebraic a)
  have hrank : Module.finrank K (IntermediateField.adjoin K {a}) = f.natDegree :=
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral a)
  have hmul := Field.finSepDegree_mul_finInsepDegree K
    (IntermediateField.adjoin K {a})
  have hisc : Polynomial.IsSeparableContraction q f g := ⟨hgsep, n, hgf⟩
  have hnatsep : f.natSepDegree = g.natDegree := hisc.natSepDegree_eq
  have hnatdeg : f.natDegree = g.natDegree * q ^ n := by
    rw [← hgf, Polynomial.natDegree_expand]
  change q ^ n = Field.finInsepDegree K (IntermediateField.adjoin K {a})
  rw [hsep, hrank, hnatsep, hnatdeg] at hmul
  exact (Nat.eq_of_mul_eq_mul_left (by
    rw [← hnatsep]
    exact (Polynomial.natSepDegree_ne_zero f
      (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral a)).ne').pos) hmul).symm

noncomputable def deningerRationalWittMinpolyConjugateUnits
    (K : Type*) [Field K] (a : (AlgebraicClosure K)ˣ) :
    Multiset (AlgebraicClosure K)ˣ :=
  ((minpoly K (a : AlgebraicClosure K)).aroots (AlgebraicClosure K)).attach.map
    fun r => Units.mk0 r.1 ((isConjRoot_iff_mem_minpoly_aroots
      (Algebra.IsIntegral.isIntegral (a : AlgebraicClosure K))).2 r.2 |>.ne_zero a.ne_zero)

theorem deningerRationalWittMinpolyConjugateUnits_map_val
    (K : Type*) [Field K] (a : (AlgebraicClosure K)ˣ) :
    (deningerRationalWittMinpolyConjugateUnits K a).map Units.val =
      (minpoly K (a : AlgebraicClosure K)).aroots (AlgebraicClosure K) := by
  unfold deningerRationalWittMinpolyConjugateUnits
  rw [Multiset.map_map]
  simp

theorem deningerRationalWittMinpolyConjugateUnits_count
    (K : Type*) [Field K] (a b : (AlgebraicClosure K)ˣ) :
    (deningerRationalWittMinpolyConjugateUnits K a).count b =
      if IsConjRoot K (a : AlgebraicClosure K) (b : AlgebraicClosure K)
      then deningerRationalWittInsepDegree K (a : AlgebraicClosure K) else 0 := by
  classical
  have hc := congrArg
    (fun s : Multiset (AlgebraicClosure K) => s.count (b : AlgebraicClosure K))
    (deningerRationalWittMinpolyConjugateUnits_map_val K a)
  rw [Multiset.count_map_eq_count' Units.val _ Units.val_injective] at hc
  by_cases hb : IsConjRoot K (a : AlgebraicClosure K) (b : AlgebraicClosure K)
  · rw [if_pos hb]
    rw [hc]
    exact deningerRationalWittMinpolyAroots_count_eq_insepDegree K (a : AlgebraicClosure K)
      (b : AlgebraicClosure K)
      ((isConjRoot_iff_mem_minpoly_aroots
        (Algebra.IsIntegral.isIntegral (a : AlgebraicClosure K))).1 hb)
  · rw [if_neg hb]
    rw [hc, Multiset.count_eq_zero]
    exact fun hmem => hb ((isConjRoot_iff_mem_minpoly_aroots
      (Algebra.IsIntegral.isIntegral (a : AlgebraicClosure K))).2 hmem)

theorem deningerRationalWittReverse_prod_X_sub_C
    {L : Type*} [Field L] (s : Multiset L)
    (hs : ∀ a ∈ s, a ≠ 0) :
    ((s.map fun a => Polynomial.X - Polynomial.C a).prod).reverse =
      (s.map fun a => deningerRationalWittTeichmullerPolynomial a).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      change (Polynomial.C (1 : L)).reverse = Polynomial.C (1 : L)
      exact Polynomial.reverse_C (1 : L)
  | @cons a s ih =>
      have ha : a ≠ 0 := hs a (by simp)
      have hs' : ∀ b ∈ s, b ≠ 0 := fun b hb => hs b (by simp [hb])
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
        Polynomial.reverse_mul_of_domain]
      rw [ih hs']
      congr 1
      calc
        (Polynomial.X - Polynomial.C a).reverse =
            (Polynomial.X + Polynomial.C (-a)).reverse := by
              rw [sub_eq_add_neg, map_neg]
        _ = Polynomial.X.reverse +
            Polynomial.C (-a) * Polynomial.X ^ Polynomial.X.natDegree := by
              rw [Polynomial.reverse_add_C]
        _ = deningerRationalWittTeichmullerPolynomial a := by
              have hX : (Polynomial.X : Polynomial L).reverse = 1 := by
                calc
                  Polynomial.X.reverse = (Polynomial.X * 1 : Polynomial L).reverse := by rw [mul_one]
                  _ = (1 : Polynomial L).reverse := Polynomial.reverse_X_mul 1
                  _ = 1 := by
                    change (Polynomial.C (1 : L)).reverse = Polynomial.C (1 : L)
                    exact Polynomial.reverse_C (1 : L)
              rw [hX]
              simp [deningerRationalWittTeichmullerPolynomial, sub_eq_add_neg]

theorem deningerRationalWittMinpolyReverse_map_eq_atomPolynomial
    (K : Type*) [Field K] (a : (AlgebraicClosure K)ˣ) :
    (minpoly K (a : AlgebraicClosure K)).reverse.map
        (algebraMap K (AlgebraicClosure K)) =
      deningerRationalWittAtomPolynomial (deningerRationalWittMinpolyConjugateUnits K a) := by
  let f := minpoly K (a : AlgebraicClosure K)
  let i := algebraMap K (AlgebraicClosure K)
  have hmaprev : f.reverse.map i = (f.map i).reverse := by
    rw [Polynomial.reverse, Polynomial.reverse,
      Polynomial.natDegree_map_eq_of_injective i.injective,
      Polynomial.reflect_map]
  rw [hmaprev]
  have hsplit : f.map i =
      (((f.map i).roots).map fun r => Polynomial.X - Polynomial.C r).prod :=
    (IsAlgClosed.splits (f.map i)).eq_prod_roots_of_monic
      ((minpoly.monic (Algebra.IsIntegral.isIntegral (a : AlgebraicClosure K))).map i)
  rw [hsplit, deningerRationalWittReverse_prod_X_sub_C]
  · rw [deningerRationalWittAtomPolynomial]
    have hval := deningerRationalWittMinpolyConjugateUnits_map_val K a
    change (deningerRationalWittMinpolyConjugateUnits K a).map Units.val = (f.map i).roots at hval
    rw [← hval]
    simp only [Multiset.map_map, Function.comp_apply]
  · intro b hb
    exact (isConjRoot_iff_mem_minpoly_aroots
      (Algebra.IsIntegral.isIntegral (a : AlgebraicClosure K))).2 hb |>.ne_zero a.ne_zero

def deningerRationalWittAtomMultisetGaloisInvariant
    (K : Type*) [Field K] (s : Multiset (AlgebraicClosure K)ˣ) : Prop :=
  ∀ g : DeningerRationalWittAbsoluteGalois K,
    s.map (deningerRationalWittUnitGaloisEquiv K g) = s

def deningerRationalWittAtomMultisetInsepDivisible
    (K : Type*) [Field K] (s : Multiset (AlgebraicClosure K)ˣ) : Prop :=
  ∀ a : (AlgebraicClosure K)ˣ,
    deningerRationalWittInsepDegree K (a : AlgebraicClosure K) ∣ s.count a

theorem deningerRationalWittInsepDegree_pos
    (K : Type*) [Field K] (a : AlgebraicClosure K) :
    0 < deningerRationalWittInsepDegree K a := by
  let E := IntermediateField.adjoin K {a}
  letI : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral a)
  have hmul := Field.finSepDegree_mul_finInsepDegree K E
  have hprod :
      0 < Field.finSepDegree K E * Field.finInsepDegree K E := by
    rw [hmul]
    exact Module.finrank_pos
  exact (CanonicallyOrderedAdd.mul_pos.mp hprod).2

theorem deningerRationalWittInsepDegree_conjRoot
    (K : Type*) [Field K] {a b : AlgebraicClosure K}
    (hab : IsConjRoot K a b) :
    deningerRationalWittInsepDegree K a = deningerRationalWittInsepDegree K b := by
  rw [deningerRationalWittInsepDegree_eq_natDegree_div_natSepDegree,
    deningerRationalWittInsepDegree_eq_natDegree_div_natSepDegree, isConjRoot_def.mp hab]

theorem deningerRationalWittMinpolyConjugateUnits_galoisInvariant
    (K : Type*) [Field K] (a : (AlgebraicClosure K)ˣ) :
    deningerRationalWittAtomMultisetGaloisInvariant K (deningerRationalWittMinpolyConjugateUnits K a) := by
  intro g
  apply Multiset.ext.mpr
  intro b
  let e := deningerRationalWittUnitGaloisEquiv K g
  calc
    ((deningerRationalWittMinpolyConjugateUnits K a).map e).count b =
        (deningerRationalWittMinpolyConjugateUnits K a).count (e.symm b) := by
      simpa using (Multiset.count_map_eq_count' e
        (deningerRationalWittMinpolyConjugateUnits K a) e.injective (e.symm b))
    _ = (deningerRationalWittMinpolyConjugateUnits K a).count b := by
      rw [deningerRationalWittMinpolyConjugateUnits_count, deningerRationalWittMinpolyConjugateUnits_count]
      have hconj :
          IsConjRoot K (a : AlgebraicClosure K) (e.symm b : AlgebraicClosure K) ↔
            IsConjRoot K (a : AlgebraicClosure K) (b : AlgebraicClosure K) := by
        constructor
        · intro h
          simpa [e, deningerRationalWittUnitGaloisEquiv] using
            h.trans (isConjRoot_of_algEquiv
              ((e.symm b : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) g)
        · intro h
          simpa [e, deningerRationalWittUnitGaloisEquiv] using
            h.trans (isConjRoot_of_algEquiv (b : AlgebraicClosure K) g.symm)
      rw [if_congr hconj rfl rfl]

theorem deningerRationalWittMinpolyConjugateUnits_insepDivisible
    (K : Type*) [Field K] (a : (AlgebraicClosure K)ˣ) :
    deningerRationalWittAtomMultisetInsepDivisible K (deningerRationalWittMinpolyConjugateUnits K a) := by
  intro b
  rw [deningerRationalWittMinpolyConjugateUnits_count]
  by_cases hab : IsConjRoot K (a : AlgebraicClosure K) (b : AlgebraicClosure K)
  · rw [if_pos hab, ← deningerRationalWittInsepDegree_conjRoot K hab]
  · rw [if_neg hab]
    exact dvd_zero _

theorem deningerRationalWittAtomMultisetGaloisInvariant_count_symm
    (K : Type*) [Field K] (s : Multiset (AlgebraicClosure K)ˣ)
    (hs : deningerRationalWittAtomMultisetGaloisInvariant K s)
    (g : DeningerRationalWittAbsoluteGalois K)
    (b : (AlgebraicClosure K)ˣ) :
    s.count ((deningerRationalWittUnitGaloisEquiv K g).symm b) =
      s.count b := by
  let e := deningerRationalWittUnitGaloisEquiv K g
  have hmap := congrArg (fun t : Multiset (AlgebraicClosure K)ˣ => t.count b) (hs g)
  have hcount := Multiset.count_map_eq_count' e s e.injective (e.symm b)
  rw [e.apply_symm_apply] at hcount
  exact hcount.symm.trans hmap

theorem deningerRationalWittAtomMultisetGaloisInvariant_count_apply
    (K : Type*) [Field K] (s : Multiset (AlgebraicClosure K)ˣ)
    (hs : deningerRationalWittAtomMultisetGaloisInvariant K s)
    (g : DeningerRationalWittAbsoluteGalois K)
    (b : (AlgebraicClosure K)ˣ) :
    s.count (deningerRationalWittUnitGaloisEquiv K g b) = s.count b := by
  let e := deningerRationalWittUnitGaloisEquiv K g
  have hmap := congrArg (fun t : Multiset (AlgebraicClosure K)ˣ => t.count (e b)) (hs g)
  have hcount := Multiset.count_map_eq_count' e s e.injective b
  exact hmap.symm.trans hcount

theorem deningerRationalWittMinpolyConjugateUnits_le_of_mem
    (K : Type*) [Field K] (s : Multiset (AlgebraicClosure K)ˣ)
    (hsG : deningerRationalWittAtomMultisetGaloisInvariant K s)
    (hsd : deningerRationalWittAtomMultisetInsepDivisible K s)
    (a : (AlgebraicClosure K)ˣ) (ha : a ∈ s) :
    deningerRationalWittMinpolyConjugateUnits K a ≤ s := by
  apply Multiset.le_iff_count.mpr
  intro b
  rw [deningerRationalWittMinpolyConjugateUnits_count]
  by_cases hab : IsConjRoot K (a : AlgebraicClosure K) (b : AlgebraicClosure K)
  · rw [if_pos hab]
    obtain ⟨g, hg⟩ := isConjRoot_iff_exists_algEquiv.mp hab
    let e := deningerRationalWittUnitGaloisEquiv K g
    have he : e b = a := Units.ext hg
    have hc : s.count b = s.count a := by
      have h := deningerRationalWittAtomMultisetGaloisInvariant_count_apply K s hsG g b
      simpa [e, he] using h.symm
    rw [hc]
    exact Nat.le_of_dvd (Multiset.count_pos.mpr ha) (hsd a)
  · rw [if_neg hab]
    exact Nat.zero_le _

theorem deningerRationalWittMinpolyConjugateUnits_self_mem
    (K : Type*) [Field K] (a : (AlgebraicClosure K)ˣ) :
    a ∈ deningerRationalWittMinpolyConjugateUnits K a := by
  rw [← Multiset.count_pos, deningerRationalWittMinpolyConjugateUnits_count,
    if_pos IsConjRoot.refl]
  exact deningerRationalWittInsepDegree_pos K a

theorem deningerRationalWittAtomMultisetGaloisInvariant_sub
    (K : Type*) [Field K] (s t : Multiset (AlgebraicClosure K)ˣ)
    (hs : deningerRationalWittAtomMultisetGaloisInvariant K s)
    (ht : deningerRationalWittAtomMultisetGaloisInvariant K t) :
    deningerRationalWittAtomMultisetGaloisInvariant K (s - t) := by
  intro g
  apply Multiset.ext.mpr
  intro b
  let e := deningerRationalWittUnitGaloisEquiv K g
  calc
    ((s - t).map e).count b = (s - t).count (e.symm b) := by
      simpa using (Multiset.count_map_eq_count' e (s - t) e.injective (e.symm b))
    _ = s.count (e.symm b) - t.count (e.symm b) := Multiset.count_sub _ _ _
    _ = s.count b - t.count b := by
      rw [deningerRationalWittAtomMultisetGaloisInvariant_count_symm K s hs g b,
        deningerRationalWittAtomMultisetGaloisInvariant_count_symm K t ht g b]
    _ = (s - t).count b := (Multiset.count_sub _ _ _).symm

theorem deningerRationalWittAtomMultisetInsepDivisible_sub
    (K : Type*) [Field K] (s t : Multiset (AlgebraicClosure K)ˣ)
    (hs : deningerRationalWittAtomMultisetInsepDivisible K s)
    (ht : deningerRationalWittAtomMultisetInsepDivisible K t) :
    deningerRationalWittAtomMultisetInsepDivisible K (s - t) := by
  intro b
  rw [Multiset.count_sub]
  exact Nat.dvd_sub (hs b) (ht b)

theorem deningerRationalWittMinpolyConjugateUnits_sub_card_lt
    (K : Type*) [Field K] (s : Multiset (AlgebraicClosure K)ˣ)
    (a : (AlgebraicClosure K)ˣ) (ha : a ∈ s)
    (hle : deningerRationalWittMinpolyConjugateUnits K a ≤ s) :
    (s - deningerRationalWittMinpolyConjugateUnits K a).card < s.card := by
  rw [Multiset.card_sub hle]
  exact Nat.sub_lt
    (Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha⟩)
    (Multiset.card_pos_iff_exists_mem.mpr
      ⟨a, deningerRationalWittMinpolyConjugateUnits_self_mem K a⟩)

theorem deningerRationalWittAtomPolynomial_exists_base_of_galoisInvariant_insepDivisible
    (K : Type*) [Field K] (s : Multiset (AlgebraicClosure K)ˣ)
    (hsG : deningerRationalWittAtomMultisetGaloisInvariant K s)
    (hsd : deningerRationalWittAtomMultisetInsepDivisible K s) :
    ∃ P : Polynomial K,
      P.coeff 0 = 1 ∧
      P.map (algebraMap K (AlgebraicClosure K)) =
        deningerRationalWittAtomPolynomial s := by
  induction hcard : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hs0 : s = 0
      · subst s
        exact ⟨1, by simp, by simp [deningerRationalWittAtomPolynomial]⟩
      · obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hs0
        let r := deningerRationalWittMinpolyConjugateUnits K a
        let t := s - r
        have hrG : deningerRationalWittAtomMultisetGaloisInvariant K r :=
          deningerRationalWittMinpolyConjugateUnits_galoisInvariant K a
        have hrd : deningerRationalWittAtomMultisetInsepDivisible K r :=
          deningerRationalWittMinpolyConjugateUnits_insepDivisible K a
        have hrs : r ≤ s := deningerRationalWittMinpolyConjugateUnits_le_of_mem K s hsG hsd a ha
        have htG : deningerRationalWittAtomMultisetGaloisInvariant K t :=
          deningerRationalWittAtomMultisetGaloisInvariant_sub K s r hsG hrG
        have htd : deningerRationalWittAtomMultisetInsepDivisible K t :=
          deningerRationalWittAtomMultisetInsepDivisible_sub K s r hsd hrd
        have htn : t.card < n := by
          rw [← hcard]
          simpa [t, r] using
            deningerRationalWittMinpolyConjugateUnits_sub_card_lt K s a ha hrs
        obtain ⟨Q, hQ0, hQmap⟩ := ih t.card htn t htG htd rfl
        refine ⟨(minpoly K (a : AlgebraicClosure K)).reverse * Q, ?_, ?_⟩
        · rw [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_reverse,
            (minpoly.monic (Algebra.IsIntegral.isIntegral
              (a : AlgebraicClosure K))).leadingCoeff, hQ0, one_mul]
        · rw [Polynomial.map_mul, deningerRationalWittMinpolyReverse_map_eq_atomPolynomial K a,
            hQmap, ← show deningerRationalWittAtomPolynomial (r + t) =
              deningerRationalWittAtomPolynomial r *
                deningerRationalWittAtomPolynomial t by
                  simp [deningerRationalWittAtomPolynomial]]
          congr 1
          rw [Multiset.add_comm, Multiset.sub_add_cancel hrs]

theorem deningerRationalWittInsepDegree_dvd_rootMultiplicity_map
    (K : Type*) [Field K] (P : Polynomial K) (x : AlgebraicClosure K) :
    deningerRationalWittInsepDegree K x ∣
      (P.map (algebraMap K (AlgebraicClosure K))).rootMultiplicity x := by
  induction hdeg : P.natDegree using Nat.strong_induction_on generalizing P x with
  | h n ih =>
      let i := algebraMap K (AlgebraicClosure K)
      by_cases hP0 : P = 0
      · subst P
        simp
      · by_cases hx : Polynomial.IsRoot (P.map i) x
        · have heval : Polynomial.aeval x P = 0 := by
            rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
            exact hx
          obtain ⟨Q, hQ⟩ := minpoly.dvd K x heval
          have hQ0 : Q ≠ 0 := by
            intro h
            rw [h, mul_zero] at hQ
            exact hP0 hQ
          have hm0 : minpoly K x ≠ 0 :=
            minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)
          have hmapmul0 :
              (minpoly K x).map i * Q.map i ≠ 0 :=
            mul_ne_zero
              ((Polynomial.map_ne_zero_iff i.injective).mpr hm0)
              ((Polynomial.map_ne_zero_iff i.injective).mpr hQ0)
          have hself : x ∈ (minpoly K x).aroots (AlgebraicClosure K) :=
            (isConjRoot_iff_mem_minpoly_aroots
              (Algebra.IsIntegral.isIntegral x)).mp IsConjRoot.refl
          have hmult :
              ((minpoly K x).map i).rootMultiplicity x = deningerRationalWittInsepDegree K x := by
            simpa [Polynomial.aroots, Polynomial.count_roots] using
              deningerRationalWittMinpolyAroots_count_eq_insepDegree K x x hself
          have hQdeg : Q.natDegree < n := by
            rw [← hdeg, hQ,
              (minpoly.monic (Algebra.IsIntegral.isIntegral x)).natDegree_mul' hQ0]
            exact Nat.lt_add_of_pos_left
              (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x))
          have hQdvd := ih Q.natDegree hQdeg Q x rfl
          rw [hQ, Polynomial.map_mul,
            Polynomial.rootMultiplicity_mul hmapmul0, hmult]
          exact dvd_add (dvd_refl _) hQdvd
        · rw [Polynomial.rootMultiplicity_eq_zero hx]
          exact dvd_zero _

theorem deningerRationalWittPolynomial_reverse_reverse_of_coeff_zero_ne
    {K : Type*} [Field K] (P : Polynomial K) (hP0 : P.coeff 0 ≠ 0) :
    P.reverse.reverse = P := by
  change (P.reflect P.natDegree).reflect (P.reflect P.natDegree).natDegree = P
  have hdegree : (P.reflect P.natDegree).natDegree = P.natDegree := by
    change P.reverse.natDegree = P.natDegree
    rw [Polynomial.reverse_natDegree,
      Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP0), Nat.sub_zero]
  rw [hdegree, Polynomial.reflect_reflect]

theorem deningerRationalWittAtomPolynomial_reverse
    {K : Type*} [Field K] (s : Multiset Kˣ) :
    (deningerRationalWittAtomPolynomial s).reverse =
      (s.map fun a : Kˣ => Polynomial.X - Polynomial.C (a : K)).prod := by
  let F := (s.map fun a : Kˣ => Polynomial.X - Polynomial.C (a : K)).prod
  have hrev : F.reverse = deningerRationalWittAtomPolynomial s := by
    simpa [F, deningerRationalWittAtomPolynomial] using
      deningerRationalWittReverse_prod_X_sub_C (s.map fun a : Kˣ => (a : K)) (by
        intro a ha
        obtain ⟨u, _hu, rfl⟩ := Multiset.mem_map.mp ha
        exact u.ne_zero)
  rw [← hrev]
  apply deningerRationalWittPolynomial_reverse_reverse_of_coeff_zero_ne
  simp [F, Polynomial.coeff_zero_multiset_prod]

theorem deningerRationalWittAtomMultiset_insepDivisible_of_exists_basePolynomial
    (K : Type*) [Field K] (s : Multiset (AlgebraicClosure K)ˣ)
    (P : Polynomial K)
    (hPmap : P.map (algebraMap K (AlgebraicClosure K)) =
      deningerRationalWittAtomPolynomial s) :
    deningerRationalWittAtomMultisetInsepDivisible K s := by
  intro a
  let i := algebraMap K (AlgebraicClosure K)
  have hrevmap : P.reverse.map i = (P.map i).reverse := by
    rw [Polynomial.reverse, Polynomial.reverse,
      Polynomial.natDegree_map_eq_of_injective i.injective,
      Polynomial.reflect_map]
  have hpoly : P.reverse.map i =
      (s.map fun b : (AlgebraicClosure K)ˣ =>
        Polynomial.X - Polynomial.C (b : AlgebraicClosure K)).prod := by
    rw [hrevmap, hPmap, deningerRationalWittAtomPolynomial_reverse]
  have hdvd := deningerRationalWittInsepDegree_dvd_rootMultiplicity_map K P.reverse
    (a : AlgebraicClosure K)
  rw [hpoly, ← Polynomial.count_roots] at hdvd
  have hprod :
      (s.map fun b : (AlgebraicClosure K)ˣ =>
        Polynomial.X - Polynomial.C (b : AlgebraicClosure K)).prod =
      ((s.map Units.val).map fun b : AlgebraicClosure K =>
        Polynomial.X - Polynomial.C b).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hprod,
    Polynomial.roots_multiset_prod_X_sub_C,
    Multiset.count_map_eq_count' Units.val s Units.val_injective a] at hdvd
  exact hdvd

theorem deningerRationalWittInt_natCast_dvd_iff_toNat_and_negToNat
    (d : ℕ) (z : ℤ) :
    ((d : ℤ) ∣ z) ↔ d ∣ z.toNat ∧ d ∣ (-z).toNat := by
  rw [Int.natCast_dvd]
  cases z <;> simp [Nat.succ_eq_add_one]

def deningerRationalWittIntegralAtomInsepDivisible
    (K : Type*) [Field K]
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ) : Prop :=
  ∀ a : (AlgebraicClosure K)ˣ,
    (deningerRationalWittInsepDegree K (a : AlgebraicClosure K) : ℤ) ∣ x.coeff a

theorem deningerRationalWittIntegralAtomInsepDivisible_iff_positive_negative
    (K : Type*) [Field K]
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ) :
    deningerRationalWittIntegralAtomInsepDivisible K x ↔
      deningerRationalWittAtomMultisetInsepDivisible K (deningerRationalWittPositiveAtoms x) ∧
      deningerRationalWittAtomMultisetInsepDivisible K (deningerRationalWittNegativeAtoms x) := by
  constructor
  · intro hx
    constructor <;> intro a
    · simpa [deningerRationalWittIntegralAtomInsepDivisible,
        deningerRationalWittAtomMultisetInsepDivisible,
        deningerRationalWittPositiveAtoms,
        deningerRationalWittPositiveCoefficients] using
          (deningerRationalWittInt_natCast_dvd_iff_toNat_and_negToNat
            (deningerRationalWittInsepDegree K (a : AlgebraicClosure K)) (x.coeff a)).mp (hx a) |>.1
    · simpa [deningerRationalWittIntegralAtomInsepDivisible,
        deningerRationalWittAtomMultisetInsepDivisible,
        deningerRationalWittNegativeAtoms,
        deningerRationalWittNegativeCoefficients] using
          (deningerRationalWittInt_natCast_dvd_iff_toNat_and_negToNat
            (deningerRationalWittInsepDegree K (a : AlgebraicClosure K)) (x.coeff a)).mp (hx a) |>.2
  · rintro ⟨hpos, hneg⟩ a
    apply (deningerRationalWittInt_natCast_dvd_iff_toNat_and_negToNat
      (deningerRationalWittInsepDegree K (a : AlgebraicClosure K)) (x.coeff a)).mpr
    constructor
    · simpa [deningerRationalWittAtomMultisetInsepDivisible,
        deningerRationalWittPositiveAtoms,
        deningerRationalWittPositiveCoefficients] using hpos a
    · simpa [deningerRationalWittAtomMultisetInsepDivisible,
        deningerRationalWittNegativeAtoms,
        deningerRationalWittNegativeCoefficients] using hneg a

theorem deningerRationalWittIntegralGaloisInvariantInsepDivisible_exists_base
    (K : Type*) [Field K]
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ)
    (hxG : ∀ g : DeningerRationalWittAbsoluteGalois K,
      deningerRationalWittIntegralGaloisAction K g x = x)
    (hxd : deningerRationalWittIntegralAtomInsepDivisible K x) :
    ∃ w0 : DeningerRationalWittAdditive K,
      deningerRationalWittAdditiveMap
          (algebraMap K (AlgebraicClosure K)) w0 =
        Additive.toMul
          (deningerRationalWittReducedMonoidAlgebraToAdditive
            (AlgebraicClosure K) x) := by
  let s := deningerRationalWittPositiveAtoms x
  let t := deningerRationalWittNegativeAtoms x
  have hsG : deningerRationalWittAtomMultisetGaloisInvariant K s := fun g =>
    deningerRationalWittPositiveAtoms_galois K g x (hxG g)
  have htG : deningerRationalWittAtomMultisetGaloisInvariant K t := fun g =>
    deningerRationalWittNegativeAtoms_galois K g x (hxG g)
  obtain ⟨hsd, htd⟩ :=
    (deningerRationalWittIntegralAtomInsepDivisible_iff_positive_negative K x).mp hxd
  obtain ⟨P0, hP0, hPmap⟩ :=
    deningerRationalWittAtomPolynomial_exists_base_of_galoisInvariant_insepDivisible K s hsG hsd
  obtain ⟨Q0, hQ0, hQmap⟩ :=
    deningerRationalWittAtomPolynomial_exists_base_of_galoisInvariant_insepDivisible K t htG htd
  refine ⟨deningerRationalWittNormalizedFraction P0 Q0 hP0 hQ0, ?_⟩
  rw [deningerRationalWittNormalizedFraction_map]
  calc
    deningerRationalWittNormalizedFraction
        (P0.map (algebraMap K (AlgebraicClosure K)))
        (Q0.map (algebraMap K (AlgebraicClosure K))) _ _ =
      deningerRationalWittNormalizedFraction
        (deningerRationalWittAtomPolynomial s)
        (deningerRationalWittAtomPolynomial t)
        (deningerRationalWittAtomPolynomial_coeff_zero s)
        (deningerRationalWittAtomPolynomial_coeff_zero t) := by
          simp only [deningerRationalWittNormalizedFraction]
          rw [deningerRationalWittNormalizedPolynomial_congr hPmap,
            deningerRationalWittNormalizedPolynomial_congr hQmap]
    _ = Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive
          (AlgebraicClosure K) x) := by
      simpa [s, t] using deningerRationalWittNormalizedFraction_eq_comparison x

theorem deningerRationalWittIntegralAtomInsepDivisible_atomSum_sub
    (K : Type*) [Field K]
    (s t : Multiset (AlgebraicClosure K)ˣ)
    (hs : deningerRationalWittAtomMultisetInsepDivisible K s)
    (ht : deningerRationalWittAtomMultisetInsepDivisible K t) :
    deningerRationalWittIntegralAtomInsepDivisible K
      (deningerRationalWittAtomSum s - deningerRationalWittAtomSum t) := by
  intro a
  change (deningerRationalWittInsepDegree K (a : AlgebraicClosure K) : ℤ) ∣
    (deningerRationalWittAtomSum s).coeff a -
      (deningerRationalWittAtomSum t).coeff a
  rw [
    deningerRationalWittAtomSum_coeff,
    deningerRationalWittAtomSum_coeff]
  exact dvd_sub
    (Int.natCast_dvd_natCast.mpr (hs a))
    (Int.natCast_dvd_natCast.mpr (ht a))

theorem deningerRationalWittIntegral_exists_base_insepDivisible
    (K : Type*) [Field K]
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ)
    (w0 : DeningerRationalWittAdditive K)
    (hw0 : deningerRationalWittAdditiveMap
        (algebraMap K (AlgebraicClosure K)) w0 =
      Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive
          (AlgebraicClosure K) x)) :
    deningerRationalWittIntegralAtomInsepDivisible K x := by
  let i := algebraMap K (AlgebraicClosure K)
  obtain ⟨P, Q, hQmem, hP0, hQ0, hwval⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction K w0
  have hwfrac : w0 = deningerRationalWittNormalizedFraction P Q hP0 hQ0 := by
    apply Subtype.ext
    apply Units.ext
    rw [hwval, deningerRationalWittNormalizedFraction_val]
  let PL := P.map i
  let QL := Q.map i
  have hPL0 : PL.coeff 0 = 1 := by simp [PL, hP0]
  have hQL0 : QL.coeff 0 = 1 := by simp [QL, hQ0]
  let s := deningerNormalizedPolynomialRootUnits PL hPL0
  let t := deningerNormalizedPolynomialRootUnits QL hQL0
  have hPs : PL = deningerRationalWittAtomPolynomial s := by
    simpa [s, deningerRationalWittAtomPolynomial] using
      deningerPolynomial_eq_prod_normalizedRootUnits PL hPL0
  have hQt : QL = deningerRationalWittAtomPolynomial t := by
    simpa [t, deningerRationalWittAtomPolynomial] using
      deningerPolynomial_eq_prod_normalizedRootUnits QL hQL0
  have hsd : deningerRationalWittAtomMultisetInsepDivisible K s :=
    deningerRationalWittAtomMultiset_insepDivisible_of_exists_basePolynomial K s P (by simpa [PL] using hPs)
  have htd : deningerRationalWittAtomMultisetInsepDivisible K t :=
    deningerRationalWittAtomMultiset_insepDivisible_of_exists_basePolynomial K t Q (by simpa [QL] using hQt)
  let y := deningerRationalWittAtomSum s - deningerRationalWittAtomSum t
  have hycomp : Additive.toMul
      (deningerRationalWittReducedMonoidAlgebraToAdditive
        (AlgebraicClosure K) y) =
      deningerRationalWittAdditiveMap i w0 := by
    rw [hwfrac, deningerRationalWittNormalizedFraction_map]
    change Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive
          (AlgebraicClosure K)
          (deningerRationalWittAtomSum s - deningerRationalWittAtomSum t)) =
      deningerRationalWittNormalizedFraction PL QL hPL0 hQL0
    rw [map_sub]
    change Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive
          (AlgebraicClosure K) (deningerRationalWittAtomSum s)) *
      (Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive
          (AlgebraicClosure K) (deningerRationalWittAtomSum t)))⁻¹ = _
    rw [deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum_toMul,
      deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum_toMul,
      ← deningerRationalWittNormalizedPolynomial_atomPolynomial,
      ← deningerRationalWittNormalizedPolynomial_atomPolynomial]
    simp only [deningerRationalWittNormalizedFraction]
    rw [deningerRationalWittNormalizedPolynomial_congr hPs.symm,
      deningerRationalWittNormalizedPolynomial_congr hQt.symm]
  have hyx : y = x := by
    apply deningerRationalWittReducedMonoidAlgebraToAdditive_injective
      (AlgebraicClosure K)
    apply Additive.toMul.injective
    exact hycomp.trans hw0
  rw [← hyx]
  exact deningerRationalWittIntegralAtomInsepDivisible_atomSum_sub K s t hsd htd

theorem deningerRationalWittIntegral_exists_base_galoisInvariant
    (K : Type*) [Field K]
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ)
    (w0 : DeningerRationalWittAdditive K)
    (hw0 : deningerRationalWittAdditiveMap
        (algebraMap K (AlgebraicClosure K)) w0 =
      Additive.toMul
        (deningerRationalWittReducedMonoidAlgebraToAdditive
          (AlgebraicClosure K) x)) :
    ∀ g : DeningerRationalWittAbsoluteGalois K,
      deningerRationalWittIntegralGaloisAction K g x = x := by
  let e := deningerRationalWittReducedMonoidAlgebraRingEquiv
    (AlgebraicClosure K)
  have hbase : e x = deningerRationalWittPerfectBaseLift K w0 := by
    apply DeningerRationalWittRing.ext
    apply Additive.toMul.injective
    change Additive.toMul (e x).additiveVal =
      deningerRationalWittAdditiveMap
        (algebraMap K (AlgebraicClosure K)) w0
    rw [deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal]
    exact hw0.symm
  intro g
  have hfixed := deningerRationalWittPerfectBaseLift_galoisFixed K w0 g
  rw [← hbase] at hfixed
  have hpre := congrArg e.symm hfixed
  simpa [e, deningerRationalWittLiteralGaloisAction] using hpre

theorem deningerRationalWittIntegralGaloisInvariantInsepDivisible_iff_exists_base
    (K : Type*) [Field K]
    (x : MonoidAlgebra ℤ (AlgebraicClosure K)ˣ) :
    ((∀ g : DeningerRationalWittAbsoluteGalois K,
        deningerRationalWittIntegralGaloisAction K g x = x) ∧
      deningerRationalWittIntegralAtomInsepDivisible K x) ↔
    ∃ w0 : DeningerRationalWittAdditive K,
      deningerRationalWittAdditiveMap
          (algebraMap K (AlgebraicClosure K)) w0 =
        Additive.toMul
          (deningerRationalWittReducedMonoidAlgebraToAdditive
            (AlgebraicClosure K) x) := by
  constructor
  · rintro ⟨hxG, hxd⟩
    exact deningerRationalWittIntegralGaloisInvariantInsepDivisible_exists_base K x hxG hxd
  · rintro ⟨w0, hw0⟩
    exact ⟨deningerRationalWittIntegral_exists_base_galoisInvariant K x w0 hw0,
      deningerRationalWittIntegral_exists_base_insepDivisible K x w0 hw0⟩

end
end RHTower

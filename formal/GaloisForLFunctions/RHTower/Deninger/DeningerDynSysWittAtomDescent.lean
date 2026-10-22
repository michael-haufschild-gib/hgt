import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysAtomDescent

/-!
# The Witt-level atom criterion

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), the lower row.

A rational Witt vector over the perfect closure `L` is a difference `w (P) - w (Q)` of normalized
polynomials, and its atom data is the difference of the two atom multisets.  Replacing `P/Q` by the
*disjoint* representative built from the multiset difference of the factorizations — legitimate
because `S + (T - S) = S ∪ T = T + (S - T)` gives `P · Q' = Q · P'` — the two atom counts no longer
cancel, so the divisibility of their difference by the degrees of inseparability forces each of
them to be divisible.  Both `P'` and `Q'` then descend, hence so does the Witt vector.
-/

namespace RHTower

open Polynomial

variable {F L E : Type*} [Field F] [Field L] [Field E]
variable [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
variable [IsPurelyInseparable F L] [IsAlgClosed E] [PerfectField L]

/-- A normalized fraction is the difference of the two normalized polynomials. -/
theorem deningerFraction_eq_sub {A : Type*} [CommRing A] (P Q : Polynomial A)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    deningerCanonicalRationalWittNormalizedFraction P Q hP hQ
      = deningerCanonicalRationalWittNormalizedPolynomial P hP
        - deningerCanonicalRationalWittNormalizedPolynomial Q hQ := by
  apply deningerCanonicalRationalWittEmbedding_injective
  rw [deningerCanonicalRationalWittEmbedding_normalizedFraction, map_sub,
    deningerCanonicalRationalWittEmbedding_normalizedPolynomial,
    deningerCanonicalRationalWittEmbedding_normalizedPolynomial]

/-- The normalized polynomial depends only on the polynomial. -/
theorem deningerNormalizedPolynomial_congr {A : Type*} [CommRing A] {P Q : Polynomial A}
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) (h : P = Q) :
    deningerCanonicalRationalWittNormalizedPolynomial P hP
      = deningerCanonicalRationalWittNormalizedPolynomial Q hQ := by
  subst h
  rfl

/-- The normalized-polynomial map turns products into sums. -/
theorem deningerNormalizedPolynomial_mul {A : Type*} [CommRing A] (P Q : Polynomial A)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) (hPQ : (P * Q).coeff 0 = 1) :
    deningerCanonicalRationalWittNormalizedPolynomial (P * Q) hPQ
      = deningerCanonicalRationalWittNormalizedPolynomial P hP
        + deningerCanonicalRationalWittNormalizedPolynomial Q hQ := by
  apply deningerCanonicalRationalWittEmbedding_injective
  rw [deningerCanonicalRationalWittEmbedding_normalizedPolynomial, map_add,
    deningerCanonicalRationalWittEmbedding_normalizedPolynomial,
    deningerCanonicalRationalWittEmbedding_normalizedPolynomial]
  exact deningerNormalizedPolynomialBigWitt_add P Q hP hQ

omit [IsAlgClosed E] [PerfectField L] in
/-- Every atom of a product of normalized irreducibles is an atom of one of the factors. -/
theorem deningerRootUnits_prod_exists_factor :
    ∀ (S : Multiset (Polynomial L)), (∀ γ ∈ S, γ.coeff 0 = 1) →
      ∀ (hmap : ((S.prod).map (algebraMap L E)).coeff 0 = 1) (u : Eˣ),
        u ∈ deningerNormalizedPolynomialRootUnits ((S.prod).map (algebraMap L E)) hmap →
        ∃ γ ∈ S, ∃ hγM : (γ.map (algebraMap L E)).coeff 0 = 1,
          u ∈ deningerNormalizedPolynomialRootUnits (γ.map (algebraMap L E)) hγM := by
  classical
  intro S
  induction S using Multiset.induction_on with
  | empty =>
      intro _ hmap u hu
      exfalso
      have h1 : ((0 : Multiset (Polynomial L)).prod).map (algebraMap L E) = 1 := by simp
      have hc := deningerRootUnits_congr
        (P := ((0 : Multiset (Polynomial L)).prod).map (algebraMap L E))
        (Q := (1 : Polynomial E)) hmap (by simp) h1
      rw [hc, deningerRootUnits_one] at hu
      exact (Multiset.notMem_zero u) hu
  | cons γ S ih =>
      intro hS hmap u hu
      have hγ0 := hS γ (Multiset.mem_cons_self γ S)
      have hSmem : ∀ δ ∈ S, δ.coeff 0 = 1 := fun δ hδ => hS δ (Multiset.mem_cons_of_mem hδ)
      have hγM : (γ.map (algebraMap L E)).coeff 0 = 1 := by
        rw [Polynomial.coeff_map, hγ0, map_one]
      have hSM : ((S.prod).map (algebraMap L E)).coeff 0 = 1 := by
        rw [Polynomial.coeff_map, deningerProdCoeffZero S hSmem, map_one]
      have hsplit : ((γ ::ₘ S).prod).map (algebraMap L E)
          = γ.map (algebraMap L E) * (S.prod).map (algebraMap L E) := by
        rw [Multiset.prod_cons, Polynomial.map_mul]
      have hc := deningerRootUnits_congr (P := ((γ ::ₘ S).prod).map (algebraMap L E))
        (Q := γ.map (algebraMap L E) * (S.prod).map (algebraMap L E)) hmap
        (by rw [← hsplit]; exact hmap) hsplit
      rw [hc, deningerRootUnits_mul _ _ hγM hSM, Multiset.mem_add] at hu
      rcases hu with hu | hu
      · exact ⟨γ, Multiset.mem_cons_self γ S, hγM, hu⟩
      · obtain ⟨δ, hδS, hδM, hδu⟩ := ih hSmem hSM u hu
        exact ⟨δ, Multiset.mem_cons_of_mem hδS, hδM, hδu⟩

/-- **Deninger, Proposition 1.3 (`t26n`), the lower row.**  A rational Witt vector over the perfect
closure descends to `κ₀` as soon as, for every atom, the difference of its multiplicities in the
numerator and the denominator is divisible by its degree of inseparability. -/
theorem deningerWittFraction_descends_of_atom_dvd (q : ℕ) [ExpChar F q] [DecidableEq Eˣ]
    [DecidableEq (Polynomial L)]
    (P Q : Polynomial L) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1)
    (hmapP : (P.map (algebraMap L E)).coeff 0 = 1)
    (hmapQ : (Q.map (algebraMap L E)).coeff 0 = 1)
    (h : ∀ u : Eˣ, (deningerInsepDegree F E q (u : E) : ℤ) ∣
      (Multiset.count u (deningerNormalizedPolynomialRootUnits
          (P.map (algebraMap L E)) hmapP) : ℤ)
        - (Multiset.count u (deningerNormalizedPolynomialRootUnits
          (Q.map (algebraMap L E)) hmapQ) : ℤ)) :
    ∃ w₀ : DeningerCanonicalRationalWittRing F,
      deningerCanonicalRationalWittMap (algebraMap F L) w₀
        = deningerCanonicalRationalWittNormalizedFraction P Q hP hQ := by
  classical
  set SP := deningerNormalizedFactors P with hSP
  set SQ := deningerNormalizedFactors Q with hSQ
  have hSPspec := deningerNormalizedFactors_spec hP
  have hSQspec := deningerNormalizedFactors_spec hQ
  set P' : Polynomial L := (SP - SQ).prod with hP'def
  set Q' : Polynomial L := (SQ - SP).prod with hQ'def
  have hsubP : ∀ γ ∈ SP - SQ, γ.coeff 0 = 1 ∧ Irreducible γ :=
    fun γ hγ => hSPspec.1 γ (Multiset.mem_of_le (Multiset.sub_le_self _ _) hγ)
  have hsubQ : ∀ γ ∈ SQ - SP, γ.coeff 0 = 1 ∧ Irreducible γ :=
    fun γ hγ => hSQspec.1 γ (Multiset.mem_of_le (Multiset.sub_le_self _ _) hγ)
  have hP'0 : P'.coeff 0 = 1 := deningerProdCoeffZero _ (fun γ hγ => (hsubP γ hγ).1)
  have hQ'0 : Q'.coeff 0 = 1 := deningerProdCoeffZero _ (fun γ hγ => (hsubQ γ hγ).1)
  -- the cross-product identity
  have hcross : P * Q' = Q * P' := by
    have h1 : SP + (SQ - SP) = SQ + (SP - SQ) := by
      rw [add_comm SP (SQ - SP), add_comm SQ (SP - SQ), ← Multiset.union_def,
        ← Multiset.union_def, Multiset.union_comm]
    have h2 := congrArg Multiset.prod h1
    rwa [Multiset.prod_add, Multiset.prod_add, hSPspec.2, hSQspec.2] at h2
  -- the two fractions agree
  have hfrac : deningerCanonicalRationalWittNormalizedFraction P Q hP hQ
      = deningerCanonicalRationalWittNormalizedFraction P' Q' hP'0 hQ'0 := by
    have hPQ' : (P * Q').coeff 0 = 1 := by
      rw [Polynomial.mul_coeff_zero, hP, hQ'0, one_mul]
    have hQP' : (Q * P').coeff 0 = 1 := by
      rw [Polynomial.mul_coeff_zero, hQ, hP'0, one_mul]
    have hsum : deningerCanonicalRationalWittNormalizedPolynomial P hP
        + deningerCanonicalRationalWittNormalizedPolynomial Q' hQ'0
        = deningerCanonicalRationalWittNormalizedPolynomial P' hP'0
          + deningerCanonicalRationalWittNormalizedPolynomial Q hQ := by
      rw [← deningerNormalizedPolynomial_mul P Q' hP hQ'0 hPQ',
        ← deningerNormalizedPolynomial_mul P' Q hP'0 hQ (by
          rw [Polynomial.mul_coeff_zero, hP'0, hQ, one_mul])]
      refine deningerNormalizedPolynomial_congr _ _ ?_
      rw [hcross, mul_comm]
    rw [deningerFraction_eq_sub, deningerFraction_eq_sub]
    exact sub_eq_sub_iff_add_eq_add.2 hsum
  have hmapP' : (P'.map (algebraMap L E)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hP'0, map_one]
  have hmapQ' : (Q'.map (algebraMap L E)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hQ'0, map_one]
  -- the atom counts of the original data, read off a factor
  have hcount_orig : ∀ (β : Polynomial L) (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β)
      (hβM : (β.map (algebraMap L E)).coeff 0 = 1) (u : Eˣ),
      u ∈ deningerNormalizedPolynomialRootUnits (β.map (algebraMap L E)) hβM →
      Multiset.count u (deningerNormalizedPolynomialRootUnits (P.map (algebraMap L E)) hmapP)
          = Multiset.count β SP ∧
        Multiset.count u (deningerNormalizedPolynomialRootUnits (Q.map (algebraMap L E)) hmapQ)
          = Multiset.count β SQ := by
    intro β hβ0 hβirr hβM u hu
    constructor
    · have hmap' : ((SP.prod).map (algebraMap L E)).coeff 0 = 1 := by
        rw [hSPspec.2]; exact hmapP
      have hres := deningerRootUnits_prod_count (E := E) hβ0 hβirr hβM hu SP hSPspec.1 hmap'
      have hc := deningerRootUnits_congr (P := (SP.prod).map (algebraMap L E))
        (Q := P.map (algebraMap L E)) hmap' hmapP (by rw [hSPspec.2])
      rwa [hc] at hres
    · have hmap' : ((SQ.prod).map (algebraMap L E)).coeff 0 = 1 := by
        rw [hSQspec.2]; exact hmapQ
      have hres := deningerRootUnits_prod_count (E := E) hβ0 hβirr hβM hu SQ hSQspec.1 hmap'
      have hc := deningerRootUnits_congr (P := (SQ.prod).map (algebraMap L E))
        (Q := Q.map (algebraMap L E)) hmap' hmapQ (by rw [hSQspec.2])
      rwa [hc] at hres
  -- divisibility for the disjoint numerator
  have hdivP' : ∀ u : Eˣ,
      u ∈ deningerNormalizedPolynomialRootUnits (P'.map (algebraMap L E)) hmapP' →
      deningerInsepDegree F E q (u : E) ∣ Multiset.count u
        (deningerNormalizedPolynomialRootUnits (P'.map (algebraMap L E)) hmapP') := by
    intro u hu
    obtain ⟨β, hβS, hβM, hβu⟩ := deningerRootUnits_prod_exists_factor (E := E) (SP - SQ)
      (fun γ hγ => (hsubP γ hγ).1) hmapP' u hu
    have hβ0 := (hsubP β hβS).1
    have hβirr := (hsubP β hβS).2
    have hcP' : Multiset.count u
        (deningerNormalizedPolynomialRootUnits (P'.map (algebraMap L E)) hmapP')
        = Multiset.count β (SP - SQ) :=
      deningerRootUnits_prod_count (E := E) hβ0 hβirr hβM hβu (SP - SQ) hsubP hmapP'
    obtain ⟨hcP, hcQ⟩ := hcount_orig β hβ0 hβirr hβM u hβu
    have hz := h u
    rw [hcP, hcQ] at hz
    rw [hcP', Multiset.count_sub]
    rcases le_or_gt (Multiset.count β SP) (Multiset.count β SQ) with hle | hlt
    · rw [Nat.sub_eq_zero_of_le hle]
      exact dvd_zero _
    · have hcast : ((Multiset.count β SP - Multiset.count β SQ : ℕ) : ℤ)
          = (Multiset.count β SP : ℤ) - (Multiset.count β SQ : ℤ) := by
        omega
      have : ((deningerInsepDegree F E q (u : E) : ℕ) : ℤ)
          ∣ ((Multiset.count β SP - Multiset.count β SQ : ℕ) : ℤ) := by
        rw [hcast]; exact hz
      exact_mod_cast this
  -- divisibility for the disjoint denominator
  have hdivQ' : ∀ u : Eˣ,
      u ∈ deningerNormalizedPolynomialRootUnits (Q'.map (algebraMap L E)) hmapQ' →
      deningerInsepDegree F E q (u : E) ∣ Multiset.count u
        (deningerNormalizedPolynomialRootUnits (Q'.map (algebraMap L E)) hmapQ') := by
    intro u hu
    obtain ⟨β, hβS, hβM, hβu⟩ := deningerRootUnits_prod_exists_factor (E := E) (SQ - SP)
      (fun γ hγ => (hsubQ γ hγ).1) hmapQ' u hu
    have hβ0 := (hsubQ β hβS).1
    have hβirr := (hsubQ β hβS).2
    have hcQ' : Multiset.count u
        (deningerNormalizedPolynomialRootUnits (Q'.map (algebraMap L E)) hmapQ')
        = Multiset.count β (SQ - SP) :=
      deningerRootUnits_prod_count (E := E) hβ0 hβirr hβM hβu (SQ - SP) hsubQ hmapQ'
    obtain ⟨hcP, hcQ⟩ := hcount_orig β hβ0 hβirr hβM u hβu
    have hz := h u
    rw [hcP, hcQ] at hz
    rw [hcQ', Multiset.count_sub]
    rcases le_or_gt (Multiset.count β SQ) (Multiset.count β SP) with hle | hlt
    · rw [Nat.sub_eq_zero_of_le hle]
      exact dvd_zero _
    · have hcast : ((Multiset.count β SQ - Multiset.count β SP : ℕ) : ℤ)
          = -((Multiset.count β SP : ℤ) - (Multiset.count β SQ : ℤ)) := by
        omega
      have : ((deningerInsepDegree F E q (u : E) : ℕ) : ℤ)
          ∣ ((Multiset.count β SQ - Multiset.count β SP : ℕ) : ℤ) := by
        rw [hcast]
        exact hz.neg_right
      exact_mod_cast this
  obtain ⟨P₀, hP₀0, hP₀map⟩ :=
    deningerNormalized_descends_of_atom_dvd (E := E) q P' hP'0 hmapP' hdivP'
  obtain ⟨Q₀, hQ₀0, hQ₀map⟩ :=
    deningerNormalized_descends_of_atom_dvd (E := E) q Q' hQ'0 hmapQ' hdivQ'
  refine ⟨deningerCanonicalRationalWittNormalizedFraction P₀ Q₀ hP₀0 hQ₀0, ?_⟩
  rw [deningerCanonicalRationalWittMap_normalizedFraction, hfrac]
  exact deningerCanonicalRationalWittNormalizedFraction_congr _ _ _ _ hP₀map hQ₀map

end RHTower

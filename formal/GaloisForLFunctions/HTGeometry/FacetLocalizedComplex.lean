import GaloisForLFunctions.HTGeometry.FacetQuotientComplex

/-!
# The localized facet complex

Coordinate-facet descent is used after inverting a multiplicative set -- for the structural modules
of the multiple-gamma hierarchy, the coordinates `t_j = 1 + x_j`.  This module carries the exactness
of the facet complex through that localization.

The terms are the quotients of the localized ring by the extensions of the sums of the coordinate
ideals, and the differential is again the alternating sum of the canonical projections.  Exactness
is proved by clearing denominators: a localized cochain has a common denominator over the finitely
many sets of facets involved, the cocycle condition descends to a polynomial cocycle after
multiplying by one further element of the multiplicative set, and the polynomial primitive divided
by the accumulated denominator is a primitive upstairs.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {ι α : Type*} [DecidableEq ι] [LinearOrder ι] [DecidableEq α]

/-- The extension of the sum of coordinate-facet ideals to a ring over the polynomial ring. -/
def locCapIdeal (k : Type*) [CommRing k] (Fam : ι → Finset α) (L : Type*) [CommRing L]
    [Algebra (MvPolynomial α k) L] (T : Finset ι) : Ideal L :=
  (capIdeal k Fam T).map (algebraMap (MvPolynomial α k) L)

/-- The term of the localized facet complex belonging to a set of facets. -/
abbrev locFacetQuot (k : Type*) [CommRing k] (Fam : ι → Finset α) (L : Type*) [CommRing L]
    [Algebra (MvPolynomial α k) L] (T : Finset ι) : Type _ :=
  L ⧸ locCapIdeal k Fam L T

variable (k : Type*) [CommRing k] (Fam : ι → Finset α) (L : Type*) [CommRing L]
  [Algebra (MvPolynomial α k) L]

omit [DecidableEq ι] [LinearOrder ι] [DecidableEq α] in
theorem locCapIdeal_mono {S T : Finset ι} (h : S ⊆ T) :
    locCapIdeal k Fam L S ≤ locCapIdeal k Fam L T :=
  Ideal.map_mono (capIdeal_mono Fam h)

/-- The canonical projection between two terms of the localized facet complex. -/
def locFacetFactor (k : Type*) [CommRing k] (Fam : ι → Finset α) (L : Type*) [CommRing L]
    [Algebra (MvPolynomial α k) L] {S T : Finset ι} (h : S ⊆ T) :
    locFacetQuot k Fam L S →+* locFacetQuot k Fam L T :=
  Ideal.Quotient.factor (locCapIdeal_mono k Fam L h)

omit [DecidableEq ι] [LinearOrder ι] [DecidableEq α] in
@[simp]
theorem locFacetFactor_mk {S T : Finset ι} (h : S ⊆ T) (x : L) :
    locFacetFactor k Fam L h (Ideal.Quotient.mk (locCapIdeal k Fam L S) x)
      = Ideal.Quotient.mk (locCapIdeal k Fam L T) x :=
  Ideal.Quotient.factor_mk _ x

/-- The differential of the localized facet complex. -/
def locQuotCoboundary (k : Type*) [CommRing k] (Fam : ι → Finset α) (L : Type*) [CommRing L]
    [Algebra (MvPolynomial α k) L] (om : ∀ T : Finset ι, locFacetQuot k Fam L T) (T : Finset ι) :
    locFacetQuot k Fam L T :=
  ∑ i ∈ T, faceSign (locFacetQuot k Fam L T) T i
    * locFacetFactor k Fam L (Finset.erase_subset i T) (om (T.erase i))

omit [DecidableEq ι] [DecidableEq α] in
theorem algebraMap_faceSign (T : Finset ι) (i : ι) :
    algebraMap (MvPolynomial α k) L (faceSign (MvPolynomial α k) T i) = faceSign L T i := by
  rw [faceSign, faceSign, map_pow, map_neg, map_one]

omit [DecidableEq ι] [DecidableEq α] in
theorem mk_faceSign_loc (T : Finset ι) (i : ι) :
    Ideal.Quotient.mk (locCapIdeal k Fam L T) (faceSign L T i)
      = faceSign (locFacetQuot k Fam L T) T i := by
  rw [faceSign, faceSign, map_pow, map_neg, map_one]

omit [DecidableEq α] in
/-- The differential of a cochain given by representatives is represented by the alternating sum of
those representatives. -/
theorem locQuotCoboundary_mk (om : Finset ι → L) (T : Finset ι) :
    locQuotCoboundary k Fam L (fun S => Ideal.Quotient.mk (locCapIdeal k Fam L S) (om S)) T
      = Ideal.Quotient.mk (locCapIdeal k Fam L T) (∑ i ∈ T, faceSign L T i * om (T.erase i)) := by
  rw [locQuotCoboundary, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, mk_faceSign_loc, locFacetFactor_mk]

/-- **The localized facet complex is exact in every positive degree.**

The localization of the augmented facet complex at any multiplicative set of the polynomial ring
stays exact: a cochain on the `c+1`-element sets of facets, vanishing off the given family and
killed by the differential, is the differential of a cochain one degree lower with the same
vanishing properties.

The proof clears denominators.  A common denominator exists because only the finitely many subsets
of the given facet family matter; one further element of the multiplicative set turns the localized
cocycle condition into a polynomial one; the polynomial primitive, divided by the accumulated
denominator, is the primitive upstairs. -/
theorem locFacetComplex_exact (M : Submonoid (MvPolynomial α k)) [IsLocalization M L]
    (facets : Finset ι) (c : ℕ)
    (om : ∀ T : Finset ι, locFacetQuot k Fam L T)
    (hdeg : ∀ T : Finset ι, T.card ≠ c + 1 → om T = 0)
    (hsub : ∀ T : Finset ι, ¬ T ⊆ facets → om T = 0)
    (hcoc : ∀ T : Finset ι, T ⊆ facets → locQuotCoboundary k Fam L om T = 0) :
    ∃ eta : ∀ T : Finset ι, locFacetQuot k Fam L T,
      (∀ T : Finset ι, T.card ≠ c → eta T = 0) ∧ (∀ T : Finset ι, ¬ T ⊆ facets → eta T = 0)
        ∧ ∀ T : Finset ι, T ⊆ facets → locQuotCoboundary k Fam L eta T = om T := by
  classical
  choose z hz using fun T : Finset ι =>
    Ideal.Quotient.mk_surjective (I := locCapIdeal k Fam L T) (om T)
  have homz : om = fun S => Ideal.Quotient.mk (locCapIdeal k Fam L S) (z S) := (funext hz).symm
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M
    (facets.powerset.image z)
  have hzb : ∀ T : Finset ι, ∃ pT : MvPolynomial α k,
      T ⊆ facets → IsLocalization.mk' L pT b = z T := by
    intro T
    by_cases hT : T ⊆ facets
    · obtain ⟨w, hw⟩ := hb (z T) (Finset.mem_image_of_mem z (Finset.mem_powerset.mpr hT))
      refine ⟨w, fun _ => ?_⟩
      rw [IsLocalization.mk'_eq_iff_eq_mul, hw, Algebra.smul_def]
      ring
    · exact ⟨0, fun h => absurd h hT⟩
  choose p hp using hzb
  have hpz : ∀ T : Finset ι, T ⊆ facets →
      z T * algebraMap (MvPolynomial α k) L (b : MvPolynomial α k)
        = algebraMap (MvPolynomial α k) L (p T) := by
    intro T hT
    rw [← hp T hT, IsLocalization.mk'_spec]
  -- the localized cocycle condition, on representatives
  have hsum : ∀ T : Finset ι, T ⊆ facets →
      (∑ i ∈ T, faceSign L T i * z (T.erase i)) ∈ locCapIdeal k Fam L T := by
    intro T hT
    have hzero := hcoc T hT
    rw [homz, locQuotCoboundary_mk] at hzero
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  -- after multiplying by the common denominator it is a polynomial statement
  have hpsum : ∀ T : Finset ι, T ⊆ facets →
      algebraMap (MvPolynomial α k) L
          (∑ i ∈ T, faceSign (MvPolynomial α k) T i * p (T.erase i))
        ∈ locCapIdeal k Fam L T := by
    intro T hT
    have hmul := Ideal.mul_mem_right
      (algebraMap (MvPolynomial α k) L (b : MvPolynomial α k)) _ (hsum T hT)
    have hrw : (∑ i ∈ T, faceSign L T i * z (T.erase i))
          * algebraMap (MvPolynomial α k) L (b : MvPolynomial α k)
        = algebraMap (MvPolynomial α k) L
          (∑ i ∈ T, faceSign (MvPolynomial α k) T i * p (T.erase i)) := by
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hsubi : T.erase i ⊆ facets := (Finset.erase_subset i T).trans hT
      rw [map_mul, algebraMap_faceSign, mul_assoc, hpz _ hsubi]
    rwa [hrw] at hmul
  -- one further denominator makes it a polynomial cocycle
  have hex : ∀ T : Finset ι, ∃ nT : MvPolynomial α k, nT ∈ M ∧ (T ⊆ facets →
      nT * (∑ i ∈ T, faceSign (MvPolynomial α k) T i * p (T.erase i)) ∈ capIdeal k Fam T) := by
    intro T
    by_cases hT : T ⊆ facets
    · have hmem := hpsum T hT
      rw [← IsLocalization.mk'_one (M := M) L, locCapIdeal,
        IsLocalization.mk'_mem_map_algebraMap_iff M L] at hmem
      obtain ⟨s, hsM, hs⟩ := hmem
      exact ⟨s, hsM, fun _ => hs⟩
    · exact ⟨1, one_mem M, fun h => absurd h hT⟩
  choose n hnM hn using hex
  set N : MvPolynomial α k := ∏ S ∈ facets.powerset, n S with hN
  have hNM : N ∈ M := Submonoid.prod_mem M (fun S _ => hnM S)
  set d : M := ⟨N * (b : MvPolynomial α k), M.mul_mem hNM b.2⟩ with hd
  -- the polynomial cochain
  set q : Finset ι → MvPolynomial α k :=
    fun T => if T.card = c + 1 ∧ T ⊆ facets then N * p T else 0 with hq
  set mu : ∀ T : Finset ι, facetQuot k Fam T :=
    fun T => Ideal.Quotient.mk (capIdeal k Fam T) (q T) with hmu
  have hqzero : ∀ T : Finset ι, ¬ (T.card = c + 1 ∧ T ⊆ facets) → q T = 0 := by
    intro T hT
    rw [hq]
    exact if_neg hT
  have hmudeg : ∀ T : Finset ι, T.card ≠ c + 1 → mu T = 0 := by
    intro T hT
    rw [hmu]
    simp only
    rw [hqzero T (fun hc => hT hc.1), map_zero]
  have hmusub : ∀ T : Finset ι, ¬ T ⊆ facets → mu T = 0 := by
    intro T hT
    rw [hmu]
    simp only
    rw [hqzero T (fun hc => hT hc.2), map_zero]
  have hmucoc : ∀ T : Finset ι, T ⊆ facets → quotCoboundary k Fam mu T = 0 := by
    intro T hT
    rw [hmu, quotCoboundary_mk_sum, Ideal.Quotient.eq_zero_iff_mem]
    by_cases hcard : T.card = c + 2
    · have hterm : ∀ i ∈ T, faceSign (MvPolynomial α k) T i * q (T.erase i)
          = N * (faceSign (MvPolynomial α k) T i * p (T.erase i)) := by
        intro i hi
        have hc1 : (T.erase i).card = c + 1 := by
          rw [Finset.card_erase_of_mem hi, hcard]
          omega
        have hs1 : T.erase i ⊆ facets := (Finset.erase_subset i T).trans hT
        rw [hq]
        simp only
        rw [if_pos ⟨hc1, hs1⟩]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have hmemT : T ∈ facets.powerset := Finset.mem_powerset.mpr hT
      have hfac : N * (∑ i ∈ T, faceSign (MvPolynomial α k) T i * p (T.erase i))
          = (∏ S ∈ facets.powerset.erase T, n S)
            * (n T * ∑ i ∈ T, faceSign (MvPolynomial α k) T i * p (T.erase i)) := by
        rw [hN, ← Finset.mul_prod_erase _ _ hmemT]
        ring
      rw [hfac]
      exact Ideal.mul_mem_left _ _ (hn T hT)
    · have hterm : ∀ i ∈ T, faceSign (MvPolynomial α k) T i * q (T.erase i) = 0 := by
        intro i hi
        have hc1 : (T.erase i).card ≠ c + 1 := by
          rw [Finset.card_erase_of_mem hi]
          have hpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨i, hi⟩
          omega
        rw [hqzero (T.erase i) (fun hc => hc1 hc.1), mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero]
      exact Ideal.zero_mem _
  obtain ⟨nu, k1, k2, k3⟩ := facetQuotientComplex_exact Fam facets c mu hmudeg hmusub hmucoc
  choose r hr using fun T : Finset ι =>
    Ideal.Quotient.mk_surjective (I := capIdeal k Fam T) (nu T)
  set r' : Finset ι → MvPolynomial α k :=
    fun T => if T.card = c ∧ T ⊆ facets then r T else 0 with hr'
  have hr'mk : ∀ T : Finset ι, Ideal.Quotient.mk (capIdeal k Fam T) (r' T) = nu T := by
    intro T
    rw [hr']
    simp only
    by_cases hT : T.card = c ∧ T ⊆ facets
    · rw [if_pos hT, hr T]
    · rw [if_neg hT, map_zero]
      by_cases hcard : T.card = c
      · exact (k2 T (fun hc => hT ⟨hcard, hc⟩)).symm
      · exact (k1 T hcard).symm
  have hnumk : nu = fun S => Ideal.Quotient.mk (capIdeal k Fam S) (r' S) := (funext hr'mk).symm
  refine ⟨fun T => Ideal.Quotient.mk (locCapIdeal k Fam L T) (IsLocalization.mk' L (r' T) d),
    ?_, ?_, ?_⟩
  · intro T hT
    show Ideal.Quotient.mk (locCapIdeal k Fam L T) (IsLocalization.mk' L (r' T) d) = 0
    rw [hr']
    simp only
    rw [if_neg (fun hc => hT hc.1), IsLocalization.mk'_zero, map_zero]
  · intro T hT
    show Ideal.Quotient.mk (locCapIdeal k Fam L T) (IsLocalization.mk' L (r' T) d) = 0
    rw [hr']
    simp only
    rw [if_neg (fun hc => hT hc.2), IsLocalization.mk'_zero, map_zero]
  · intro T hT
    rw [locQuotCoboundary_mk]
    -- the alternating sum of the primitive has the same denominator
    have hsumk : (∑ i ∈ T, faceSign L T i * IsLocalization.mk' L (r' (T.erase i)) d)
        = IsLocalization.mk' L
          (∑ i ∈ T, faceSign (MvPolynomial α k) T i * r' (T.erase i)) d := by
      refine (IsLocalization.mk'_eq_iff_eq_mul.mpr ?_).symm
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_mul, algebraMap_faceSign, mul_assoc, IsLocalization.mk'_spec]
    rw [hsumk]
    -- the primitive differs from the cochain by an element of the ideal
    have hdiff : (∑ i ∈ T, faceSign (MvPolynomial α k) T i * r' (T.erase i)) - q T
        ∈ capIdeal k Fam T := by
      have hk := k3 T hT
      rw [hnumk, quotCoboundary_mk_sum, hmu] at hk
      simp only at hk
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hk
    by_cases hcard : T.card = c + 1
    · have hqT : q T = N * p T := by
        rw [hq]
        simp only
        rw [if_pos ⟨hcard, hT⟩]
      have hzd : z T * algebraMap (MvPolynomial α k) L (d : MvPolynomial α k)
          = algebraMap (MvPolynomial α k) L (q T) := by
        rw [hqT, hd]
        simp only
        rw [map_mul, map_mul, ← mul_assoc, mul_comm (z T), mul_assoc, hpz T hT]
      have hmemdiff : IsLocalization.mk' L
          ((∑ i ∈ T, faceSign (MvPolynomial α k) T i * r' (T.erase i)) - q T) d
            ∈ locCapIdeal k Fam L T := by
        rw [locCapIdeal, IsLocalization.mk'_mem_map_algebraMap_iff M L]
        exact ⟨1, one_mem M, by rw [one_mul]; exact hdiff⟩
      have heq : IsLocalization.mk' L
          (∑ i ∈ T, faceSign (MvPolynomial α k) T i * r' (T.erase i)) d - z T
            = IsLocalization.mk' L
              ((∑ i ∈ T, faceSign (MvPolynomial α k) T i * r' (T.erase i)) - q T) d := by
        refine (IsLocalization.mk'_eq_iff_eq_mul.mpr ?_).symm
        rw [map_sub, sub_mul, IsLocalization.mk'_spec, hzd]
      rw [homz]
      refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
      rw [heq]
      exact hmemdiff
    · have hqT : q T = 0 := hqzero T (fun hc => hcard hc.1)
      have hmemsum : (∑ i ∈ T, faceSign (MvPolynomial α k) T i * r' (T.erase i))
          ∈ capIdeal k Fam T := by
        have := hdiff
        rwa [hqT, sub_zero] at this
      have hzero : IsLocalization.mk' L
          (∑ i ∈ T, faceSign (MvPolynomial α k) T i * r' (T.erase i)) d
            ∈ locCapIdeal k Fam L T := by
        rw [locCapIdeal, IsLocalization.mk'_mem_map_algebraMap_iff M L]
        exact ⟨1, one_mem M, by rw [one_mul]; exact hmemsum⟩
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hzero, hdeg T hcard]

end

end GaloisForLFunctions.HTGeometry

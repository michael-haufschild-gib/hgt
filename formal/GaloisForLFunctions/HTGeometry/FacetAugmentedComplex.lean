import GaloisForLFunctions.HTGeometry.FacetSupportedRestriction
import GaloisForLFunctions.HTGeometry.SimplexConeContraction

/-!
# The augmented facet complex of coordinate descent

Coordinate-facet descent for a family of facets `Fam : ι → Finset α` uses the complex whose degree
`c` term is the direct sum, over the `c`-element sets `T` of facets, of the quotient of the
polynomial ring by the sum of their coordinate ideals, with the alternating sum of the canonical
projections as differential.

In the truncation model of `FacetSupportedRestriction` all of that is explicit: a term is a
polynomial truncated to the multidegrees supported in every facet of `T`, and the differential is
the alternating sum of truncations.  The sum of the coordinate ideals of `T` is exactly the kernel
of that truncation, so no quotient has to be formed.

Splitting a cochain by multidegree turns the complex into a direct sum of blocks: the multidegree
`b` contributes the reduced simplicial cochain complex of the *full* simplex on the facets
containing the support of `b`.  Each block is contracted by `SimplexConeContraction`, with the
smallest such facet as base vertex; assembling those contractions multidegree by multidegree gives
an explicit primitive and proves the complex exact in every positive degree.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-! ### Multidegrees supported in a family of facets -/

section Support

variable {ι α : Type*} (Fam : ι → Finset α)

/-- A multidegree supported in every facet of a finite family. -/
def capSupported (Fam : ι → Finset α) (T : Finset ι) (b : α →₀ ℕ) : Prop :=
  ∀ i ∈ T, b.support ⊆ Fam i

theorem capSupported_mono {T S : Finset ι} (h : S ⊆ T) {b : α →₀ ℕ}
    (hb : capSupported Fam T b) : capSupported Fam S b :=
  fun i hi => hb i (h hi)

theorem capSupported_empty (b : α →₀ ℕ) : capSupported Fam ∅ b :=
  fun i hi => absurd hi (Finset.notMem_empty i)

end Support

/-! ### Terms of the complex -/

section Terms

variable {ι α k : Type*} [DecidableEq α] [CommRing k] (Fam : ι → Finset α)

instance capSupported_decidable (T : Finset ι) : DecidablePred (capSupported Fam T) :=
  fun _ => Finset.decidableDforallFinset

/-- The canonical representative modulo the sum of the coordinate ideals of a family of facets. -/
def capRestrict (k : Type*) [CommRing k] (Fam : ι → Finset α) (T : Finset ι)
    (p : MvPolynomial α k) : MvPolynomial α k :=
  suppRestrict k (capSupported Fam T) p

theorem coeff_capRestrict (T : Finset ι) (p : MvPolynomial α k) (b : α →₀ ℕ) :
    coeff b (capRestrict k Fam T p) = if capSupported Fam T b then coeff b p else 0 :=
  coeff_suppRestrict p b

theorem capRestrict_eq_self_iff (T : Finset ι) (p : MvPolynomial α k) :
    capRestrict k Fam T p = p ↔ ∀ b : α →₀ ℕ, coeff b p ≠ 0 → capSupported Fam T b :=
  suppRestrict_eq_self_iff p

theorem capRestrict_zero (T : Finset ι) : capRestrict k Fam T (0 : MvPolynomial α k) = 0 :=
  suppRestrict_zero

/-- The sum of the coordinate ideals of a family of facets. -/
def capIdeal (k : Type*) [CommRing k] (Fam : ι → Finset α) (T : Finset ι) :
    Ideal (MvPolynomial α k) :=
  T.sup fun i => facetIdeal k (Fam i)

/-- The polynomials carrying no multidegree supported in all facets of `T`. -/
def capKerIdeal (k : Type*) [CommRing k] (Fam : ι → Finset α) (T : Finset ι) :
    Ideal (MvPolynomial α k) where
  carrier := {p | ∀ b : α →₀ ℕ, capSupported Fam T b → coeff b p = 0}
  zero_mem' := by
    intro b _
    rw [coeff_zero]
  add_mem' hp hq := by
    intro b hb
    rw [coeff_add, hp b hb, hq b hb, add_zero]
  smul_mem' c p hp := by
    intro b hb
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero (fun uv huv => ?_)
    have hsum := Finset.mem_antidiagonal.mp huv
    have hle : uv.2 ≤ b := hsum ▸ le_add_self
    have hsub : uv.2.support ⊆ b.support := by
      intro x hx
      refine Finsupp.mem_support_iff.mpr (fun hzero => ?_)
      have hxle : uv.2 x ≤ b x := hle x
      rw [hzero] at hxle
      exact Finsupp.mem_support_iff.mp hx (Nat.le_zero.mp hxle)
    have hb2 : capSupported Fam T uv.2 := fun i hi => hsub.trans (hb i hi)
    rw [hp uv.2 hb2, mul_zero]

theorem mem_capKerIdeal_iff {T : Finset ι} {p : MvPolynomial α k} :
    p ∈ capKerIdeal k Fam T ↔ ∀ b : α →₀ ℕ, capSupported Fam T b → coeff b p = 0 := Iff.rfl

/-- **The sum of coordinate-facet ideals is a coefficient condition.**  A polynomial lies in it
exactly when it carries no multidegree supported in every facet of the family. -/
theorem mem_capIdeal_iff_coeff (T : Finset ι) (p : MvPolynomial α k) :
    p ∈ capIdeal k Fam T ↔ ∀ b : α →₀ ℕ, capSupported Fam T b → coeff b p = 0 := by
  constructor
  · intro hp
    refine (mem_capKerIdeal_iff Fam).mp ?_
    refine (Finset.sup_le (f := fun i => facetIdeal k (Fam i)) (a := capKerIdeal k Fam T)
      (fun i hi => ?_)) hp
    intro q hq b hb
    exact (mem_facetIdeal_iff_coeff (Fam i) q).mp hq b (hb i hi)
  · intro hp
    rw [as_sum p]
    refine Ideal.sum_mem _ (fun b hb => ?_)
    have hnot : ¬ capSupported Fam T b := fun hcon => mem_support_iff.mp hb (hp b hcon)
    obtain ⟨i, hiT, hfail⟩ : ∃ i ∈ T, ¬ b.support ⊆ Fam i := by
      by_contra hcon
      exact hnot (fun i hi => not_not.mp (fun h => hcon ⟨i, hi, h⟩))
    refine Finset.le_sup (f := fun j => facetIdeal k (Fam j)) hiT ?_
    rw [mem_facetIdeal_iff_coeff]
    intro c hc
    rw [coeff_monomial]
    exact if_neg (fun hbc => hfail (by rw [hbc]; exact hc))

/-- **Truncation computes the quotient by the sum of the coordinate ideals.** -/
theorem capRestrict_eq_zero_iff_mem (T : Finset ι) (p : MvPolynomial α k) :
    capRestrict k Fam T p = 0 ↔ p ∈ capIdeal k Fam T := by
  rw [capRestrict, suppRestrict_eq_zero_iff, mem_capIdeal_iff_coeff]

end Terms

/-! ### The differential -/

section Differential

variable {ι α k : Type*} [DecidableEq ι] [LinearOrder ι] [DecidableEq α] [CommRing k]
variable (Fam : ι → Finset α)

/-- The differential of the facet complex: the alternating sum of the canonical projections. -/
def facetCoboundary (k : Type*) [CommRing k] (Fam : ι → Finset α)
    (ω : Finset ι → MvPolynomial α k) (T : Finset ι) : MvPolynomial α k :=
  ∑ i ∈ T, faceSign (MvPolynomial α k) T i * capRestrict k Fam T (ω (T.erase i))

omit [DecidableEq ι] [DecidableEq α] in
theorem coeff_faceSign_mul (T : Finset ι) (i : ι) (q : MvPolynomial α k) (b : α →₀ ℕ) :
    coeff b (faceSign (MvPolynomial α k) T i * q) = faceSign k T i * coeff b q := by
  have hC : (faceSign (MvPolynomial α k) T i) = C (faceSign k T i) := by
    rw [faceSign, faceSign, map_pow, map_neg, map_one]
  rw [hC, coeff_C_mul]

/-- The multidegree component of a facet cochain: a scalar cochain on the facet index. -/
def multiComponent (ω : Finset ι → MvPolynomial α k) (b : α →₀ ℕ) : Finset ι → k :=
  fun T => coeff b (ω T)

/-- **The differential is the simplicial coboundary in every multidegree.** -/
theorem coeff_facetCoboundary (ω : Finset ι → MvPolynomial α k) (T : Finset ι) (b : α →₀ ℕ) :
    coeff b (facetCoboundary k Fam ω T)
      = if capSupported Fam T b then simplicialCoboundary k (multiComponent ω b) T else 0 := by
  rw [facetCoboundary, coeff_sum, simplicialCoboundary]
  by_cases hb : capSupported Fam T b
  · rw [if_pos hb]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [coeff_faceSign_mul, coeff_capRestrict, if_pos hb]
    rfl
  · rw [if_neg hb]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [coeff_faceSign_mul, coeff_capRestrict, if_neg hb, mul_zero]

/-- **The facet complex is a complex.** -/
theorem facetCoboundary_facetCoboundary (ω : Finset ι → MvPolynomial α k) (T : Finset ι) :
    facetCoboundary k Fam (facetCoboundary k Fam ω) T = 0 := by
  ext b
  rw [coeff_facetCoboundary, coeff_zero]
  by_cases hb : capSupported Fam T b
  · rw [if_pos hb]
    have hcomp : multiComponent (facetCoboundary k Fam ω) b
        = fun S => if capSupported Fam S b then simplicialCoboundary k (multiComponent ω b) S
            else 0 := by
      funext S
      exact coeff_facetCoboundary Fam ω S b
    rw [simplicialCoboundary, hcomp]
    have hterm : ∀ i ∈ T, faceSign k T i
        * (if capSupported Fam (T.erase i) b then
            simplicialCoboundary k (multiComponent ω b) (T.erase i) else 0)
        = faceSign k T i * simplicialCoboundary k (multiComponent ω b) (T.erase i) := by
      intro i _
      rw [if_pos (capSupported_mono Fam (Finset.erase_subset i T) hb)]
    rw [Finset.sum_congr rfl hterm]
    have hdd := congrFun (simplicialCoboundary_simplicialCoboundary (F := k)
      (multiComponent ω b)) T
    rw [simplicialCoboundary] at hdd
    simpa using hdd
  · rw [if_neg hb]


/-! ### The block of a multidegree and its contraction -/

/-- The facets of the family that carry a given multidegree. -/
def facetBlock (Fam : ι → Finset α) (facets : Finset ι) (b : α →₀ ℕ) : Finset ι :=
  facets.filter fun i => b.support ⊆ Fam i

omit [DecidableEq ι] [LinearOrder ι] in
theorem mem_facetBlock {facets : Finset ι} {b : α →₀ ℕ} {i : ι} :
    i ∈ facetBlock Fam facets b ↔ i ∈ facets ∧ b.support ⊆ Fam i :=
  Finset.mem_filter

omit [DecidableEq ι] [LinearOrder ι] in
theorem facetBlock_subset (facets : Finset ι) (b : α →₀ ℕ) :
    facetBlock Fam facets b ⊆ facets :=
  Finset.filter_subset _ _

omit [DecidableEq ι] [LinearOrder ι] in
theorem subset_facetBlock {facets T : Finset ι} {b : α →₀ ℕ} (hT : T ⊆ facets)
    (hb : capSupported Fam T b) : T ⊆ facetBlock Fam facets b :=
  fun i hi => mem_facetBlock Fam |>.mpr ⟨hT hi, hb i hi⟩

omit [DecidableEq ι] [LinearOrder ι] in
theorem capSupported_of_subset_facetBlock {facets T : Finset ι} {b : α →₀ ℕ}
    (hT : T ⊆ facetBlock Fam facets b) : capSupported Fam T b :=
  fun _ hi => (mem_facetBlock Fam |>.mp (hT hi)).2

/-- The part of a polynomial whose multidegrees have a prescribed smallest carrying facet. -/
def basePart (k : Type*) [CommRing k] (Fam : ι → Finset α) (facets : Finset ι) (i : ι)
    (p : MvPolynomial α k) : MvPolynomial α k :=
  suppRestrict k (fun b => (facetBlock Fam facets b).min = (i : WithTop ι)) p

theorem coeff_basePart (facets : Finset ι) (i : ι) (p : MvPolynomial α k) (b : α →₀ ℕ) :
    coeff b (basePart k Fam facets i p)
      = if (facetBlock Fam facets b).min = (i : WithTop ι) then coeff b p else 0 :=
  coeff_suppRestrict p b

/-- The cone primitive of a facet cochain: in each multidegree it is the cone contraction of that
multidegree's block, based at the smallest facet carrying the multidegree. -/
def coneAssemble (k : Type*) [CommRing k] (Fam : ι → Finset α) (facets : Finset ι)
    (om : Finset ι → MvPolynomial α k) (T : Finset ι) : MvPolynomial α k :=
  ∑ i ∈ facets.filter fun i => i ∉ T,
    faceSign (MvPolynomial α k) (insert i T) i * basePart k Fam facets i (om (insert i T))

/-- In a multidegree whose block is empty the primitive vanishes. -/
theorem coeff_coneAssemble_of_min_top {facets : Finset ι} {b : α →₀ ℕ}
    (hb : (facetBlock Fam facets b).min = ⊤) (om : Finset ι → MvPolynomial α k) (T : Finset ι) :
    coeff b (coneAssemble k Fam facets om T) = 0 := by
  rw [coneAssemble, coeff_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [coeff_faceSign_mul, coeff_basePart, if_neg (fun hc => ?_), mul_zero]
  rw [hb] at hc
  exact WithTop.top_ne_coe hc

/-- **In every multidegree the primitive is the cone contraction of the block.** -/
theorem coeff_coneAssemble_of_min {facets : Finset ι} {b : α →₀ ℕ} {i0 : ι}
    (hmin : (facetBlock Fam facets b).min = (i0 : WithTop ι))
    (om : Finset ι → MvPolynomial α k) (T : Finset ι) :
    coeff b (coneAssemble k Fam facets om T)
      = simplicialCone k i0 (multiComponent om b) T := by
  have hi0 : i0 ∈ facetBlock Fam facets b := Finset.mem_of_min hmin
  have hi0F : i0 ∈ facets := facetBlock_subset Fam facets b hi0
  rw [coneAssemble, coeff_sum]
  by_cases hmem : i0 ∈ T
  · rw [simplicialCone_of_mem _ hmem]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hiT : i ∉ T := (Finset.mem_filter.mp hi).2
    have hne : (i0 : WithTop ι) ≠ (i : WithTop ι) := by
      intro hc
      exact hiT (by rw [← WithTop.coe_inj.mp hc]; exact hmem)
    rw [coeff_faceSign_mul, coeff_basePart, if_neg (fun hc => hne (hmin ▸ hc)), mul_zero]
  · rw [simplicialCone_of_notMem _ hmem]
    rw [Finset.sum_eq_single i0]
    · rw [coeff_faceSign_mul, coeff_basePart, if_pos hmin]
      rfl
    · intro i _ hne
      have hne' : (i0 : WithTop ι) ≠ (i : WithTop ι) := fun hc => hne (WithTop.coe_inj.mp hc).symm
      rw [coeff_faceSign_mul, coeff_basePart, if_neg (fun hc => hne' (hmin ▸ hc)), mul_zero]
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨hi0F, hmem⟩) hnot

/-! ### Exactness -/

/-- **The augmented facet complex is exact in every positive degree.**

A cochain of the facet complex living on the `c+1`-element sets of facets, with entries truncated to
the multidegrees their facets carry, and with vanishing differential on all sets of facets, is the
differential of the explicit cone primitive, which lives one degree lower and satisfies the same
support and truncation conditions.

Splitting by multidegree turns this into the contraction of the full simplex on the facets carrying
that multidegree, based at the smallest of them. -/
theorem facetComplex_exact (facets : Finset ι) (c : ℕ) (om : Finset ι → MvPolynomial α k)
    (hdeg : ∀ T : Finset ι, T.card ≠ c + 1 → om T = 0)
    (hsub : ∀ T : Finset ι, ¬ T ⊆ facets → om T = 0)
    (hcap : ∀ T : Finset ι, capRestrict k Fam T (om T) = om T)
    (hcoc : ∀ T : Finset ι, T ⊆ facets → facetCoboundary k Fam om T = 0) :
    (∀ T : Finset ι, T.card ≠ c → coneAssemble k Fam facets om T = 0)
      ∧ (∀ T : Finset ι, ¬ T ⊆ facets → coneAssemble k Fam facets om T = 0)
      ∧ (∀ T : Finset ι, capRestrict k Fam T (coneAssemble k Fam facets om T)
          = coneAssemble k Fam facets om T)
      ∧ ∀ T : Finset ι, T ⊆ facets →
          facetCoboundary k Fam (coneAssemble k Fam facets om) T = om T := by
  have hzero : ∀ (i : ι) (T : Finset ι), om (insert i T) = 0 →
      faceSign (MvPolynomial α k) (insert i T) i * basePart k Fam facets i (om (insert i T))
        = 0 := by
    intro i T h
    rw [h, basePart, suppRestrict_zero, mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T hT
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hiT : i ∉ T := (Finset.mem_filter.mp hi).2
    refine hzero i T (hdeg _ ?_)
    rw [Finset.card_insert_of_notMem hiT]
    omega
  · intro T hT
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine hzero i T (hsub _ (fun hcon => hT (fun x hx => hcon (Finset.mem_insert_of_mem hx))))
  · intro T
    rw [capRestrict_eq_self_iff]
    intro b hb
    rcases Option.eq_none_or_eq_some ((facetBlock Fam facets b).min) with hnone | ⟨i0, hi0⟩
    · exact absurd (coeff_coneAssemble_of_min_top Fam hnone om T) hb
    · rw [coeff_coneAssemble_of_min Fam hi0] at hb
      by_cases hmem : i0 ∈ T
      · exact absurd (simplicialCone_of_mem _ hmem) hb
      · rw [simplicialCone_of_notMem _ hmem] at hb
        have hne : coeff b (om (insert i0 T)) ≠ 0 := by
          intro h
          exact hb (by rw [multiComponent, h, mul_zero])
        have hcapins := (capRestrict_eq_self_iff Fam (insert i0 T) (om (insert i0 T))).mp
          (hcap (insert i0 T)) b hne
        exact capSupported_mono Fam (Finset.subset_insert i0 T) hcapins
  · intro T hT
    ext b
    rw [coeff_facetCoboundary]
    have hom : coeff b (om T) = if capSupported Fam T b then coeff b (om T) else 0 := by
      by_cases hb : capSupported Fam T b
      · rw [if_pos hb]
      · rw [if_neg hb]
        by_contra hne
        exact hb ((capRestrict_eq_self_iff Fam T (om T)).mp (hcap T) b (fun h => hne h))
    rw [hom]
    by_cases hb : capSupported Fam T b
    · rw [if_pos hb, if_pos hb]
      rcases Option.eq_none_or_eq_some ((facetBlock Fam facets b).min) with hnone | ⟨i0, hi0⟩
      · have hempty : facetBlock Fam facets b = ∅ := Finset.min_eq_top.mp hnone
        have hTempty : T = ∅ := by
          have := subset_facetBlock Fam hT hb
          rw [hempty] at this
          exact Finset.subset_empty.mp this
        rw [hTempty, simplicialCoboundary, Finset.sum_empty, hdeg ∅ (by simp), coeff_zero]
      · have hcomp : multiComponent (coneAssemble k Fam facets om) b
            = simplicialCone k i0 (multiComponent om b) := by
          funext S
          exact coeff_coneAssemble_of_min Fam hi0 om S
        have hi0mem : i0 ∈ facetBlock Fam facets b := Finset.mem_of_min hi0
        have hcocb : ∀ S : Finset ι, S ⊆ facetBlock Fam facets b →
            simplicialCoboundary k (multiComponent om b) S = 0 := by
          intro S hS
          have hScap : capSupported Fam S b := capSupported_of_subset_facetBlock Fam hS
          have hSF : S ⊆ facets := hS.trans (facetBlock_subset Fam facets b)
          have := congrArg (coeff b) (hcoc S hSF)
          rw [coeff_facetCoboundary, if_pos hScap, coeff_zero] at this
          exact this
        rw [hcomp]
        exact simplicialCoboundary_simplicialCone_of_subset hi0mem hcocb
          (subset_facetBlock Fam hT hb)
    · rw [if_neg hb, if_neg hb]

end Differential

end

end GaloisForLFunctions.HTGeometry

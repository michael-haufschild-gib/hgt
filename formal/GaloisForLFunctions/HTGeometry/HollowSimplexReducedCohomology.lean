import GaloisForLFunctions.HTGeometry.SimplicialCochainComplex
import GaloisForLFunctions.HTGeometry.StanleyReisnerHollowSimplexRank

/-!
# Exact reduced cohomology of a hollow simplex, and the uniform-degree Hochster correspondence

The algebraic half of the Hochster source-coherence duality at the `Tor₁` strand is already exact in
the corpus: `srHollowSimplexSyzygyVec_boundary_iff` (`StanleyReisnerHollowSimplexRank`) shows that for
a hollow simplex `σ` (a minimal nonface, `∂Δ^{|σ|−1}`) the multidegree-`σ` Koszul syzygy `w(l)` is a
first Koszul boundary **iff** `∑_{i∈σ} l_i = 0`, so `Tor_{1,σ}` is exactly one-dimensional in every
dimension `|σ|`.

The topological half was available only in degree `1` and only through graph-specific Betti formulas
(`finrank_reducedH1_cycleGraph3/4/5/6`, `ReducedH1FirstBetti`).  Using the general reduced simplicial
cochain complex of `SimplicialCochainComplex` this file supplies the topological half **in every
degree at once**:

`(∃ h, ∀ i ∈ σ, (δh)(σ ∖ i) = a i) ↔ ∑_{i∈σ} faceSign σ i · a i = 0`

(`hollowSimplex_coboundary_iff`).  Only the values of a cochain on the `(|σ|−2)`-subsets of `σ` enter,
so no degree bookkeeping is needed: the criterion *is* the exact statement
`H̃^{|σ|−2}(∂Δ^{|σ|−1}) ≅ F`, for every `|σ|`.

* the forward direction is `δ² = 0` evaluated at `σ` — the top-degree functional `g ↦ (δg)(σ)` is the
  cohomology detector, and it kills coboundaries automatically;
* the converse is an explicit primitive `hollowPrimitive`, the cochain supported on the
  codimension-two faces `σ ∖ {i₀, k}` through a fixed base vertex `i₀`, with coefficients corrected by
  the incidence signs — the exact topological mirror of the algebraic spanning construction
  `srHollowSimplexSyzygyVec_boundary_of_sum_zero`.

Combining the two halves gives `hochster_hollowSimplex_boundary_iff`: for a hollow simplex, a Koszul
syzygy is a boundary exactly when the matching top cochain is a coboundary — an exact, unconditional
Hochster correspondence at the `Tor₁` strand valid in **every** dimension, not just the cycle graphs
`C₃…C₆` treated concretely in `HochsterCycleRealization`.  The concrete boundary complex `hollowFacets`
discharges the structural hypotheses, so the correspondence also holds with no hypotheses at all
(`hochster_hollowFacets_boundary_iff`).
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] {F : Type*} [CommRing F]

/-! ### The boundary complex of a simplex -/

/-- The boundary complex `∂σ`: the complex whose facets are the codimension-one faces of `σ`. -/
def hollowFacets (σ : Finset α) : Finset (Finset α) :=
  σ.image (fun i => σ.erase i)

omit [LinearOrder α] in
/-- The faces of `∂σ` are exactly the proper subsets of `σ`. -/
theorem isFaceOf_hollowFacets_iff {σ ρ : Finset α} :
    IsFaceOf (↑(hollowFacets σ) : Set (Finset α)) ρ ↔ ρ ⊆ σ ∧ ρ ≠ σ := by
  constructor
  · rintro ⟨G, hG, hρG⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (by simpa [hollowFacets] using hG)
    refine ⟨hρG.trans (Finset.erase_subset i σ), ?_⟩
    rintro rfl
    exact (Finset.notMem_erase i _) (hρG hi)
  · rintro ⟨hsub, hne⟩
    obtain ⟨i, hiσ, hiρ⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hne)
    refine ⟨σ.erase i, ?_, ?_⟩
    · simpa [hollowFacets] using Finset.mem_image.mpr ⟨i, hiσ, rfl⟩
    · exact fun x hx => Finset.mem_erase.mpr ⟨fun h => hiρ (h ▸ hx), hsub hx⟩

omit [LinearOrder α] in
/-- Every codimension-one face of `σ` is a face of `∂σ`. -/
theorem isFaceOf_hollowFacets_erase {σ : Finset α} {i : α} (hi : i ∈ σ) :
    IsFaceOf (↑(hollowFacets σ) : Set (Finset α)) (σ.erase i) := by
  refine isFaceOf_hollowFacets_iff.mpr ⟨Finset.erase_subset i σ, fun h => ?_⟩
  rw [← h] at hi
  exact (Finset.notMem_erase i σ) hi

omit [LinearOrder α] in
/-- `σ` itself is not a face of `∂σ`: the boundary complex is a genuine hollow simplex. -/
theorem not_isFaceOf_hollowFacets_self {σ : Finset α} :
    ¬ IsFaceOf (↑(hollowFacets σ) : Set (Finset α)) σ :=
  fun h => (isFaceOf_hollowFacets_iff.mp h).2 rfl

/-! ### Top cochains of a hollow simplex are cocycles -/

/-- **Top-degree cochains of a hollow simplex are cocycles.**  A cochain supported in cardinality
`c` has coboundary supported in cardinality `c+1`; on the boundary complex `∂σ` every face has
cardinality at most `|σ|−1`, so the coboundary of a top cochain vanishes on all of `∂σ`. -/
theorem simplicialCoboundary_mem_faceVanishing_of_card {σ : Finset α} {c : ℕ}
    (hc : σ.card ≤ c + 1) {g : Finset α → F} (hg : g ∈ cardCochains F c) :
    simplicialCoboundary F g ∈ faceVanishingCochains F (hollowFacets σ) := by
  intro ρ hρ
  obtain ⟨hsub, hne⟩ := isFaceOf_hollowFacets_iff.mp hρ
  have hlt : ρ.card < σ.card := Finset.card_lt_card (lt_of_le_of_ne hsub hne)
  show ∑ v ∈ ρ, faceSign F ρ v * g (ρ.erase v) = 0
  refine Finset.sum_eq_zero (fun v hv => ?_)
  have hpos : 1 ≤ ρ.card := Finset.card_pos.mpr ⟨v, hv⟩
  have hcard : (ρ.erase v).card ≠ c := by
    rw [Finset.card_erase_of_mem hv]; omega
  rw [hg _ hcard, mul_zero]

/-! ### The explicit primitive -/

/-- The explicit primitive of a sign-balanced top cochain of `∂σ`: the cochain supported on the
codimension-two faces `σ ∖ {i₀, k}` through the base vertex `i₀`, with the incidence-sign correction.
This is the topological mirror of the algebraic spanning `2`-chain in
`srHollowSimplexSyzygyVec_boundary_of_sum_zero`. -/
def hollowPrimitive (F : Type*) [CommRing F] (σ : Finset α) (i₀ : α) (a : α → F) :
    Finset α → F :=
  fun τ => ∑ k ∈ σ.erase i₀,
    if τ = (σ.erase i₀).erase k then faceSign F (σ.erase k) i₀ * a k else 0

/-- Off the base vertex, the primitive reproduces the prescribed value: `(δ h)(σ ∖ m) = a m`. -/
theorem simplicialCoboundary_hollowPrimitive_of_ne {σ : Finset α} {i₀ m : α}
    (hi₀ : i₀ ∈ σ) (hm : m ∈ σ) (hmi : m ≠ i₀) (a : α → F) :
    simplicialCoboundary F (hollowPrimitive F σ i₀ a) (σ.erase m) = a m := by
  show ∑ v ∈ σ.erase m,
      faceSign F (σ.erase m) v * hollowPrimitive F σ i₀ a ((σ.erase m).erase v) = a m
  have key : ∀ v ∈ σ.erase m,
      faceSign F (σ.erase m) v * hollowPrimitive F σ i₀ a ((σ.erase m).erase v)
        = if v = i₀ then a m else 0 := by
    intro v hv
    rw [Finset.mem_erase] at hv
    by_cases hvi : v = i₀
    · subst hvi
      rw [if_pos rfl]
      have hprim : hollowPrimitive F σ v a ((σ.erase m).erase v)
          = faceSign F (σ.erase m) v * a m := by
        show (∑ k ∈ σ.erase v,
            if (σ.erase m).erase v = (σ.erase v).erase k then
              faceSign F (σ.erase k) v * a k else 0) = _
        rw [Finset.sum_eq_single m]
        · rw [if_pos (Finset.erase_right_comm (a := m) (b := v) (s := σ))]
        · intro k hk hkm
          refine if_neg (fun hcon => ?_)
          have hkmem : k ∈ (σ.erase m).erase v :=
            Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hk).1,
              Finset.mem_erase.mpr ⟨hkm, (Finset.mem_erase.mp hk).2⟩⟩
          exact (Finset.notMem_erase k (σ.erase v)) (hcon ▸ hkmem)
        · intro hmem
          exact absurd (Finset.mem_erase.mpr ⟨hmi, hm⟩) hmem
      rw [hprim, ← mul_assoc, faceSign_mul_self, one_mul]
    · rw [if_neg hvi]
      have hzero : hollowPrimitive F σ i₀ a ((σ.erase m).erase v) = 0 := by
        show (∑ k ∈ σ.erase i₀,
            if (σ.erase m).erase v = (σ.erase i₀).erase k then
              faceSign F (σ.erase k) i₀ * a k else 0) = 0
        refine Finset.sum_eq_zero (fun k _ => if_neg (fun hcon => ?_))
        have hmem : i₀ ∈ (σ.erase m).erase v :=
          Finset.mem_erase.mpr ⟨fun h => hvi h.symm,
            Finset.mem_erase.mpr ⟨fun h => hmi h.symm, hi₀⟩⟩
        exact (Finset.notMem_erase i₀ σ) (Finset.mem_of_mem_erase (hcon ▸ hmem))
      rw [hzero, mul_zero]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (σ.erase m) i₀ (fun _ => a m),
    if_pos (Finset.mem_erase.mpr ⟨fun h => hmi h.symm, hi₀⟩)]

/-- At the base vertex, the primitive reproduces the prescribed value provided the top cochain is
sign-balanced: `(δ h)(σ ∖ i₀) = a i₀`. -/
theorem simplicialCoboundary_hollowPrimitive_base {σ : Finset α} {i₀ : α} (hi₀ : i₀ ∈ σ)
    (a : α → F) (hsum : ∑ i ∈ σ, faceSign F σ i * a i = 0) :
    simplicialCoboundary F (hollowPrimitive F σ i₀ a) (σ.erase i₀) = a i₀ := by
  show ∑ v ∈ σ.erase i₀,
      faceSign F (σ.erase i₀) v * hollowPrimitive F σ i₀ a ((σ.erase i₀).erase v) = a i₀
  have key : ∀ v ∈ σ.erase i₀,
      faceSign F (σ.erase i₀) v * hollowPrimitive F σ i₀ a ((σ.erase i₀).erase v)
        = - (faceSign F σ i₀ * (faceSign F σ v * a v)) := by
    intro v hv
    have hvi : v ≠ i₀ := (Finset.mem_erase.mp hv).1
    have hvσ : v ∈ σ := (Finset.mem_erase.mp hv).2
    have hprim : hollowPrimitive F σ i₀ a ((σ.erase i₀).erase v)
        = faceSign F (σ.erase v) i₀ * a v := by
      show (∑ k ∈ σ.erase i₀,
          if (σ.erase i₀).erase v = (σ.erase i₀).erase k then
            faceSign F (σ.erase k) i₀ * a k else 0) = _
      rw [Finset.sum_eq_single v]
      · rw [if_pos rfl]
      · intro k hk hkv
        refine if_neg (fun hcon => ?_)
        have hkmem : k ∈ (σ.erase i₀).erase v := Finset.mem_erase.mpr ⟨hkv, hk⟩
        exact (Finset.notMem_erase k (σ.erase i₀)) (hcon ▸ hkmem)
      · intro hmem; exact absurd hv hmem
    have hanti := faceSign_mul_faceSign_erase_antisymm (F := F) hi₀ hvσ (Ne.symm hvi)
    have hsq₀ : faceSign F σ i₀ * faceSign F σ i₀ = 1 := faceSign_mul_self σ i₀
    have hsqv : faceSign F (σ.erase v) i₀ * faceSign F (σ.erase v) i₀ = 1 :=
      faceSign_mul_self (σ.erase v) i₀
    rw [hprim]
    linear_combination (faceSign F σ i₀ * faceSign F (σ.erase v) i₀ * a v) * hanti
      - (faceSign F (σ.erase i₀) v * faceSign F (σ.erase v) i₀ * a v) * hsq₀
      - (faceSign F σ i₀ * faceSign F σ v * a v) * hsqv
  have hfac : ∑ v ∈ σ.erase i₀, -(faceSign F σ i₀ * (faceSign F σ v * a v))
      = -(faceSign F σ i₀ * ∑ v ∈ σ.erase i₀, faceSign F σ v * a v) := by
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
  have hsplit : faceSign F σ i₀ * a i₀ + ∑ v ∈ σ.erase i₀, faceSign F σ v * a v
      = ∑ i ∈ σ, faceSign F σ i * a i :=
    Finset.add_sum_erase σ (fun i => faceSign F σ i * a i) hi₀
  have hrest : ∑ v ∈ σ.erase i₀, faceSign F σ v * a v = - (faceSign F σ i₀ * a i₀) := by
    linear_combination hsplit + hsum
  have hsq₀ : faceSign F σ i₀ * faceSign F σ i₀ = 1 := faceSign_mul_self σ i₀
  rw [Finset.sum_congr rfl key, hfac, hrest]
  linear_combination (a i₀) * hsq₀

/-! ### The exact reduced cohomology of a hollow simplex, in every degree -/

/-- **Exact reduced cohomology of a hollow simplex, uniformly in the dimension.**  A prescribed
family of values `a` on the codimension-one faces of `σ` is realized as the coboundary of a cochain
**iff** it is annihilated by the top-degree incidence functional `a ↦ ∑_{i∈σ} faceSign σ i · a i`.

Since only the values on `(|σ|−2)`-subsets of `σ` can contribute, this is exactly the statement that
the reduced cohomology of the boundary complex `∂Δ^{|σ|−1}` in its top degree `|σ|−2` is the
one-dimensional space cut out by that single functional — for every `|σ|`, over any commutative ring,
unconditionally.  It is the topological mirror of `srHollowSimplexSyzygyVec_boundary_iff`. -/
theorem hollowSimplex_coboundary_iff {σ : Finset α} (hσ : σ.Nonempty) (a : α → F) :
    (∃ h : Finset α → F, ∀ i ∈ σ, simplicialCoboundary F h (σ.erase i) = a i)
      ↔ ∑ i ∈ σ, faceSign F σ i * a i = 0 := by
  constructor
  · rintro ⟨h, hh⟩
    have : ∑ i ∈ σ, faceSign F σ i * simplicialCoboundary F h (σ.erase i) = 0 := by
      have := congrFun (simplicialCoboundary_simplicialCoboundary (F := F) h) σ
      simpa [simplicialCoboundary] using this
    rw [← this]
    exact Finset.sum_congr rfl (fun i hi => by rw [hh i hi])
  · intro hsum
    obtain ⟨i₀, hi₀⟩ := hσ
    refine ⟨hollowPrimitive F σ i₀ a, fun i hi => ?_⟩
    by_cases hii : i = i₀
    · subst hii
      exact simplicialCoboundary_hollowPrimitive_base hi₀ a hsum
    · exact simplicialCoboundary_hollowPrimitive_of_ne hi₀ hi hii a

/-- **Nonvanishing reduced cohomology of a hollow simplex in every degree.**  The top cochain
concentrated on one codimension-one face of `σ` is not a coboundary, so
`H̃^{|σ|−2}(∂Δ^{|σ|−1}) ≠ 0` for every nonempty `σ`, over any nontrivial commutative ring. -/
theorem hollowSimplex_reducedCohomology_nonzero [Nontrivial F] {σ : Finset α} {i₀ : α}
    (hi₀ : i₀ ∈ σ) :
    ¬ ∃ h : Finset α → F,
        ∀ i ∈ σ, simplicialCoboundary F h (σ.erase i) = (if i = i₀ then 1 else 0) := by
  rw [hollowSimplex_coboundary_iff ⟨i₀, hi₀⟩]
  rw [Finset.sum_congr rfl (fun i _ => by
    show faceSign F σ i * (if i = i₀ then 1 else 0)
      = if i = i₀ then faceSign F σ i₀ else 0
    by_cases h : i = i₀ <;> simp [h]), Finset.sum_ite_eq' σ i₀ (fun _ => faceSign F σ i₀),
    if_pos hi₀]
  intro hzero
  have : (1 : F) = 0 := by
    have := faceSign_mul_self (F := F) σ i₀
    rw [hzero, mul_zero] at this
    exact this.symm
  exact one_ne_zero this

/-! ### The uniform-degree Hochster correspondence -/

variable [Fintype α]

/-- **Exact Hochster correspondence at a hollow simplex, in every dimension.**  For a hollow simplex
`σ` — a nonface all of whose codimension-one faces are faces — the multidegree-`σ` first Koszul
syzygy `w(l)` is a Koszul boundary **exactly when** the matching top simplicial cochain
`i ↦ faceSign σ i · l i` on `∂σ` is a simplicial coboundary.

Both sides are cut out by one linear functional, so both `Tor_{1,σ}` and `H̃^{|σ|−2}(Δ_σ)` are exactly
one-dimensional and the correspondence is an equivalence, unconditionally and uniformly in `|σ|`.
This upgrades the concrete degree-`1` cycle-graph instances `hochster_C3/C4/C5/C6_*` of
`HochsterCycleRealization` to every dimension at once. -/
theorem hochster_hollowSimplex_boundary_iff (facets : Finset (Finset α)) (σ : Finset α)
    (hσ : σ.Nonempty) (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i))
    (l : α → F) :
    (∃ cc : α → α → stanleyReisnerRing F facets,
        srKoszulBoundary facets cc = srHollowSimplexSyzygyVec F facets σ l)
      ↔ (∃ h : Finset α → F,
          ∀ i ∈ σ, simplicialCoboundary F h (σ.erase i) = faceSign F σ i * l i) := by
  rw [srHollowSimplexSyzygyVec_boundary_iff facets σ hσ hface l,
    hollowSimplex_coboundary_iff hσ (fun i => faceSign F σ i * l i)]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [← mul_assoc, faceSign_mul_self, one_mul])
  · rw [← h]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [← mul_assoc, faceSign_mul_self, one_mul])

/-- **The correspondence with all structural hypotheses discharged.**  On the explicit boundary
complex `∂σ` of any nonempty finite vertex set, the exact Hochster correspondence between the
algebraic `Tor₁` side and the topological reduced-cohomology side holds with no hypotheses beyond
nonemptiness — a concrete unconditional realization in every dimension. -/
theorem hochster_hollowFacets_boundary_iff (σ : Finset α) (hσ : σ.Nonempty) (l : α → F) :
    (∃ cc : α → α → stanleyReisnerRing F (hollowFacets σ),
        srKoszulBoundary (hollowFacets σ) cc
          = srHollowSimplexSyzygyVec F (hollowFacets σ) σ l)
      ↔ (∃ h : Finset α → F,
          ∀ i ∈ σ, simplicialCoboundary F h (σ.erase i) = faceSign F σ i * l i) :=
  hochster_hollowSimplex_boundary_iff (hollowFacets σ) σ hσ
    (fun _ hi => isFaceOf_hollowFacets_erase hi) l

/-- **Both sides nonzero, in every dimension.**  On the explicit boundary complex `∂σ` the
multidegree-`σ` basis syzygy at any vertex is not a Koszul boundary, and the matching top cochain is
not a simplicial coboundary: the Hochster class is nonzero on both sides simultaneously, for every
dimension `|σ|`, over any nontrivial commutative ring. -/
theorem hochster_hollowFacets_both_nonzero [Nontrivial F] (σ : Finset α) {i₀ : α} (hi₀ : i₀ ∈ σ) :
    (¬ ∃ cc : α → α → stanleyReisnerRing F (hollowFacets σ),
        srKoszulBoundary (hollowFacets σ) cc
          = srHollowSimplexSyzygyVec F (hollowFacets σ) σ (fun i => if i = i₀ then 1 else 0))
      ∧ (¬ ∃ h : Finset α → F,
          ∀ i ∈ σ, simplicialCoboundary F h (σ.erase i) = (if i = i₀ then 1 else 0)) := by
  constructor
  · rw [srHollowSimplexSyzygyVec_boundary_iff (hollowFacets σ) σ ⟨i₀, hi₀⟩
      (fun _ hi => isFaceOf_hollowFacets_erase hi)]
    rw [Finset.sum_ite_eq' σ i₀ (fun _ => (1 : F)), if_pos hi₀]
    exact one_ne_zero
  · exact hollowSimplex_reducedCohomology_nonzero hi₀

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.StanleyReisnerHollowSimplexRank

/-!
# Bouquet of hollow simplices: unbounded source-coherence rank at every reduced degree

The triangle bouquet (`bouquet_classes_independent`) realizes arbitrarily high first Koszul homology
rank at reduced degree `1`.  This file frees the degree as well: a family of `k` **pairwise disjoint**
hollow simplices `σ₀, …, σ_{k-1}` (each with every proper face present) carries `k` **linearly
independent** first Koszul homology classes, one per simplex, each living at reduced cohomological degree
`|σ_m| − 2`.  Taking all `σ_m` of the same size realizes `H̃ⁿ⁻¹` at rank `k` — an arbitrary
`(dimension, rank)` cell of the multigraded Betti profile of one HT source.

The separation is read off by the hollow-simplex detectors `srHollowDetectorₗ σ_m`, which sum face
detectors over the vertices of `σ_m`: on its own base class it is `1`, on a disjoint simplex's class it
vanishes termwise (the class is supported off `σ_m`), and on every first Koszul boundary it is `0`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R α : Type*} [CommRing R] [DecidableEq α] [Fintype α]

omit [Fintype α] in
/-- The hollow-simplex detector evaluates its own base syzygy to `1`. -/
theorem srHollowDetectorₗ_base (facets : Finset (Finset α)) (σ : Finset α)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)) {i₀ : α} (hi₀ : i₀ ∈ σ) :
    srHollowDetectorₗ R facets σ
        (srHollowSimplexSyzygyVec R facets σ (fun i => if i = i₀ then (1 : R) else 0)) = 1 := by
  classical
  show (∑ i ∈ σ, if h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) then
      srFaceDetector R facets (σ.erase i) h
        (srHollowSimplexSyzygyVec R facets σ (fun i => if i = i₀ then (1 : R) else 0) i) else 0) = 1
  rw [Finset.sum_congr rfl (fun i hi => show
    (if h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) then
        srFaceDetector R facets (σ.erase i) h
          (srHollowSimplexSyzygyVec R facets σ (fun i => if i = i₀ then (1 : R) else 0) i) else 0)
      = if i = i₀ then (1 : R) else 0 from by
    rw [dif_pos (hface i hi), srHollowSimplexSyzygyVec, if_pos hi, map_smul, srFaceDetector_prod,
      smul_eq_mul, mul_one]), Finset.sum_ite_eq' σ i₀ (fun _ => (1 : R)), if_pos hi₀]

omit [Fintype α] in
/-- The hollow-simplex detector of `σ` vanishes on a syzygy supported on a disjoint simplex `τ`. -/
theorem srHollowDetectorₗ_disjoint (facets : Finset (Finset α)) (σ τ : Finset α)
    (hd : Disjoint σ τ) (l : α → R) :
    srHollowDetectorₗ R facets σ (srHollowSimplexSyzygyVec R facets τ l) = 0 := by
  classical
  show (∑ i ∈ σ, if h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) then
      srFaceDetector R facets (σ.erase i) h
        (srHollowSimplexSyzygyVec R facets τ l i) else 0) = 0
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hz : srHollowSimplexSyzygyVec R facets τ l i = 0 := by
    rw [srHollowSimplexSyzygyVec, if_neg (fun hit => Finset.disjoint_left.mp hd hi hit)]
  rw [hz]; simp

/-- **Unbounded source-coherence rank at every reduced degree.**  For `k` pairwise disjoint hollow
simplices in one complex, the `k` base first Koszul homology classes are linearly independent modulo
Koszul boundaries: any boundary equal to a combination `∑ c m · classₘ` forces every `c m = 0`.  With all
simplices of size `n+1` this realizes `H̃ⁿ⁻¹` at rank `k` — an arbitrary `(dimension, rank)` cell of the
multigraded Betti profile. -/
theorem hollow_bouquet_independent (F : Type*) [Field F] (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α)
    (hface : ∀ m, ∀ v ∈ σ m, IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (hmem : ∀ m, i₀ m ∈ σ m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (σ m) (σ n))
    (c : Fin k → F) (cc : α → α → stanleyReisnerRing F facets)
    (hcc : (∑ m, c m •
        srHollowSimplexSyzygyVec F facets (σ m) (fun i => if i = i₀ m then (1 : F) else 0))
      = srKoszulBoundary facets cc) :
    ∀ m, c m = 0 := by
  intro m
  have hL : srHollowDetectorₗ F facets (σ m)
      (∑ n, c n • srHollowSimplexSyzygyVec F facets (σ n)
        (fun i => if i = i₀ n then (1 : F) else 0)) = 0 := by
    rw [hcc]; exact srHollowDetectorₗ_apply_boundary facets (σ m) (hface m) cc
  rw [map_sum, Finset.sum_eq_single_of_mem m (Finset.mem_univ m)
    (fun n _ hnm => by
      rw [map_smul, srHollowDetectorₗ_disjoint facets (σ m) (σ n) (hdisj m n (Ne.symm hnm)),
        smul_zero]),
    map_smul, srHollowDetectorₗ_base facets (σ m) (hface m) (hmem m), smul_eq_mul, mul_one] at hL
  exact hL

/-- **§3.2 universality in canonical form.**  For any finite family of pairwise disjoint hollow simplices
(arbitrary sizes, hence an arbitrary reduced-cohomology-dimension pattern), the base first Koszul homology
classes are `F`-linearly independent in the Koszul homology module.  So the source coherence of one HT
source realizes any finite `(dimension, rank)` Betti pattern as a genuine independent family. -/
theorem hollow_bouquet_linearIndependent (F : Type*) [Field F] (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α)
    (hface : ∀ m, ∀ v ∈ σ m, IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (hmem : ∀ m, i₀ m ∈ σ m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (σ m) (σ n)) :
    LinearIndependent F (fun m => srHollowBaseClass F facets (σ m) (i₀ m)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmk : (Submodule.Quotient.mk
      (∑ m, c m • srHollowSimplexSyzygyVec F facets (σ m)
        (fun i => if i = i₀ m then (1 : F) else 0)) :
      (α → stanleyReisnerRing F facets) ⧸ srKoszulBoundaries facets) = 0 := by
    rw [← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply]
    exact hc
  rw [Submodule.Quotient.mk_eq_zero] at hmk
  simp only [srKoszulBoundaries, LinearMap.mem_range] at hmk
  obtain ⟨cc, hcc⟩ := hmk
  exact hollow_bouquet_independent F facets σ i₀ hface hmem hdisj c cc hcc.symm

/-- **Source-coherence rank lower bound in `Module.rank`.**  For any `k` pairwise disjoint hollow
simplices, the first Koszul homology module has `F`-rank at least `k`.  So the degree-one source coherence
of one HT source has arbitrarily large `F`-dimension — the unbounded-rank statement in mathlib's
dimension language. -/
theorem hollow_bouquet_rank_ge (F : Type*) [Field F] (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α)
    (hface : ∀ m, ∀ v ∈ σ m, IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (hmem : ∀ m, i₀ m ∈ σ m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (σ m) (σ n)) :
    (k : Cardinal) ≤
      Module.rank F ((α → stanleyReisnerRing F facets) ⧸ srKoszulBoundaries facets) := by
  have h := (hollow_bouquet_linearIndependent F facets σ i₀ hface hmem hdisj).cardinal_le_rank
  rwa [Cardinal.mk_fin] at h

/-! ## A concrete unconditional disjoint-`∂Δⁿ` bouquet realizing `(dimension, rank)` for every `(n, k)` -/

/-- The `m`-th hollow `n`-simplex: the `n+1` vertices `(m, ·)`, on vertex type `Fin k × Fin (n+1)`. -/
def hbSigma (k n : ℕ) (m : Fin k) : Finset (Fin k × Fin (n + 1)) := {m} ×ˢ Finset.univ

/-- The disjoint-`∂Δⁿ` bouquet complex: the codimension-one faces of each of the `k` simplices (so each
`hbSigma m` is a hollow simplex — all proper faces present, the simplex itself absent). -/
def hbFacets (k n : ℕ) : Finset (Finset (Fin k × Fin (n + 1))) :=
  Finset.univ.biUnion fun m => (hbSigma k n m).image fun v => (hbSigma k n m).erase v

theorem hbFacets_erase_mem {k n : ℕ} (m : Fin k) {v : Fin k × Fin (n + 1)}
    (hv : v ∈ hbSigma k n m) : (hbSigma k n m).erase v ∈ hbFacets k n :=
  Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ m, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

theorem hbSigma_disjoint {k n : ℕ} {m m' : Fin k} (h : m ≠ m') :
    Disjoint (hbSigma k n m) (hbSigma k n m') := by
  rw [Finset.disjoint_left]
  rintro ⟨a, b⟩ hx hx'
  rw [hbSigma, Finset.mem_product, Finset.mem_singleton] at hx
  rw [hbSigma, Finset.mem_product, Finset.mem_singleton] at hx'
  exact h (hx.1.symm.trans hx'.1)

/-- **Unbounded `(dimension, rank)` realized unconditionally.**  On the concrete disjoint-`∂Δⁿ` bouquet
`hbFacets k n`, the `k` base first Koszul homology classes — each at reduced cohomological degree `n − 1`
— are linearly independent modulo Koszul boundaries, with no remaining hypotheses.  So every
`(dimension, rank) = (n − 1, k)` cell of the multigraded Betti profile is realized by an explicit finite
Stanley–Reisner complex. -/
theorem hollow_bouquet_concrete_independent (F : Type*) [Field F] {k n : ℕ} (c : Fin k → F)
    (cc : (Fin k × Fin (n + 1)) → (Fin k × Fin (n + 1)) → stanleyReisnerRing F (hbFacets k n))
    (hcc : (∑ m, c m • srHollowSimplexSyzygyVec F (hbFacets k n) (hbSigma k n m)
        (fun i => if i = (m, 0) then (1 : F) else 0)) = srKoszulBoundary (hbFacets k n) cc) :
    ∀ m, c m = 0 :=
  hollow_bouquet_independent F (hbFacets k n) (hbSigma k n) (fun m => (m, 0))
    (fun m v hv => ⟨(hbSigma k n m).erase v, Finset.mem_coe.mpr (hbFacets_erase_mem m hv),
      Finset.Subset.refl _⟩)
    (fun m => Finset.mem_product.mpr ⟨Finset.mem_singleton_self m, Finset.mem_univ 0⟩)
    (fun _ _ h => hbSigma_disjoint h) c cc hcc

/-- **Source-coherence rank `k` as `LinearIndependent`.**  On the concrete disjoint-`∂Δⁿ` bouquet the `k`
base first Koszul homology classes are `F`-linearly independent in the Koszul homology module — the
module-theoretic form of the rank realization, so the degree-`(n−1)` source coherence of one HT source
has `F`-dimension at least `k`. -/
theorem hollow_bouquet_concrete_linearIndependent (F : Type*) [Field F] {k n : ℕ} :
    LinearIndependent F (fun m : Fin k =>
      srHollowBaseClass F (hbFacets k n) (hbSigma k n m) ((m, 0) : Fin k × Fin (n + 1))) :=
  hollow_bouquet_linearIndependent F (hbFacets k n) (hbSigma k n) (fun m => (m, 0))
    (fun m v hv => ⟨(hbSigma k n m).erase v, Finset.mem_coe.mpr (hbFacets_erase_mem m hv),
      Finset.Subset.refl _⟩)
    (fun m => Finset.mem_product.mpr ⟨Finset.mem_singleton_self m, Finset.mem_univ 0⟩)
    (fun _ _ h => hbSigma_disjoint h)

/-! ## Arbitrary Betti pattern: mixed-dimension bouquet realizing any multiset of dimensions -/

/-- Vertex type for the mixed-dimension bouquet: block `m` has `s m + 1` vertices (a hollow
`(s m)`-simplex, realizing reduced degree `s m − 1`). -/
abbrev mbVtx {k : ℕ} (s : Fin k → ℕ) : Type := Σ m : Fin k, Fin (s m + 1)

/-- The `m`-th block simplex of the mixed bouquet: the fiber over `m`. -/
def mbSigma {k : ℕ} (s : Fin k → ℕ) (m : Fin k) : Finset (mbVtx s) :=
  Finset.univ.image (Sigma.mk m)

/-- The mixed-dimension bouquet complex: the codimension-one faces of each block simplex. -/
def mbFacets {k : ℕ} (s : Fin k → ℕ) : Finset (Finset (mbVtx s)) :=
  Finset.univ.biUnion fun m => (mbSigma s m).image fun v => (mbSigma s m).erase v

theorem mbFacets_erase_mem {k : ℕ} (s : Fin k → ℕ) (m : Fin k) {v : mbVtx s}
    (hv : v ∈ mbSigma s m) : (mbSigma s m).erase v ∈ mbFacets s :=
  Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ m, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

theorem mbSigma_disjoint {k : ℕ} (s : Fin k → ℕ) {m m' : Fin k} (h : m ≠ m') :
    Disjoint (mbSigma s m) (mbSigma s m') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [mbSigma, Finset.mem_image] at hp hp'
  obtain ⟨j, _, hj⟩ := hp
  obtain ⟨j', _, hj'⟩ := hp'
  exact h (congrArg Sigma.fst (hj.trans hj'.symm))

/-- **Arbitrary Betti pattern realized unconditionally.**  For any dimension assignment `s : Fin k → ℕ`,
the mixed-dimension bouquet carries `k` linearly independent base first Koszul homology classes, the
`m`-th living at reduced cohomological degree `s m − 1`.  So one explicit HT source realizes any finite
multiset of `(dimension)` requirements as an independent source-coherence family — the full concrete §3.2
positive-universality statement. -/
theorem mixed_bouquet_concrete_linearIndependent (F : Type*) [Field F] {k : ℕ} (s : Fin k → ℕ) :
    LinearIndependent F (fun m : Fin k =>
      srHollowBaseClass F (mbFacets s) (mbSigma s m) (⟨m, 0⟩ : mbVtx s)) :=
  hollow_bouquet_linearIndependent F (mbFacets s) (mbSigma s) (fun m => ⟨m, 0⟩)
    (fun m v hv => ⟨(mbSigma s m).erase v, Finset.mem_coe.mpr (mbFacets_erase_mem s m hv),
      Finset.Subset.refl _⟩)
    (fun _ => Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩)
    (fun _ _ h => mbSigma_disjoint s h)

end GaloisForLFunctions.HTGeometry

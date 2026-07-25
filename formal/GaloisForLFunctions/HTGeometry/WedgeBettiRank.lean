import GaloisForLFunctions.HTGeometry.StanleyReisnerCycleClasses

/-!
# Rank-two reduced `H̃¹` source coherence: two independent `Tor₁` classes in one connected complex

The reduced-`H⁰` independent-class family (`isolatedDisconnectCycleBasis_independent_mod_koszulBoundary`)
shows a discrete complex can carry several independent degree-`0` Hochster classes.  This file gives the
degree-`1` analogue: a single **connected** complex — the wedge of two empty triangles `{0,1,2}` and
`{0,3,4}` at the shared apex `0`, whose reduced first cohomology is `H̃¹ = F²` — carries two **linearly
independent** first Koszul homology classes, one per triangle hole.  So the multigraded Betti profile of
one HT source can have coherence rank `> 1` at reduced cohomological degree `1`.

The independence is read off by the triangle detectors: the `{0,1,2}` detector is `1` on its own class
and `0` on the `{0,3,4}` class (a different squarefree multidegree), and vanishes on every first Koszul
boundary, so a boundary combination forces both coefficients to zero.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {R α : Type*} [CommRing R] [DecidableEq α] [Fintype α]

omit [Fintype α] in
/-- **Pair detector of a disjoint product is zero.**  Reading the `x_u x_v` coefficient of a product
`x_p x_q` at a *different* squarefree multidegree returns `0`. -/
theorem srPairDetector_srVertexX_mul_eq_zero (facets : Finset (Finset α)) {u v p q : α} (huv : u ≠ v)
    (hf : IsFaceOf (↑facets : Set (Finset α)) {u, v})
    (hne : Finsupp.single u 1 + Finsupp.single v 1 ≠ Finsupp.single p 1 + Finsupp.single q 1) :
    srPairDetector R facets u v huv hf (srVertexX R facets p * srVertexX R facets q) = 0 := by
  rw [srVertexX, srVertexX, ← map_mul, srPairDetector_mk,
    show (X p * X q : MvPolynomial α R) = monomial (Finsupp.single p 1 + Finsupp.single q 1) 1 by
      rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul]; simp,
    MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)]

/-- **The empty-triangle alternating detector vanishes on every first Koszul boundary.**  Reusable form
of the boundary cancellation inside `srEmptyTriangleSyzygy_not_koszulBoundary`. -/
theorem srEmptyTriangleDetector_koszulBoundary_zero (facets : Finset (Finset α)) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfab : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hfbc : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hfac : IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (cc : α → α → stanleyReisnerRing R facets) :
    srPairDetector R facets b c hbc hfbc (srKoszulBoundary facets cc a)
      + (srPairDetector R facets a c hac hfac (srKoszulBoundary facets cc b)
         + srPairDetector R facets a b hab hfab (srKoszulBoundary facets cc c)) = 0 := by
  rw [srPairDetector_srKoszulBoundary facets hbc hfbc hb hc,
    srPairDetector_srKoszulBoundary facets hac hfac ha hc,
    srPairDetector_srKoszulBoundary facets hab hfab ha hb]
  have ec : srH0Detector R facets c hc (cc a b - cc b a)
      + srH0Detector R facets c hc (cc b a - cc a b) = 0 := by
    rw [← map_add, show cc a b - cc b a + (cc b a - cc a b) = 0 by abel, map_zero]
  have eb : srH0Detector R facets b hb (cc a c - cc c a)
      + srH0Detector R facets b hb (cc c a - cc a c) = 0 := by
    rw [← map_add, show cc a c - cc c a + (cc c a - cc a c) = 0 by abel, map_zero]
  have ea : srH0Detector R facets a ha (cc b c - cc c b)
      + srH0Detector R facets a ha (cc c b - cc b c) = 0 := by
    rw [← map_add, show cc b c - cc c b + (cc c b - cc b c) = 0 by abel, map_zero]
  linear_combination ec + eb + ea

/-- The wedge of two empty triangles `{0,1,2}` and `{0,3,4}` sharing the apex `0`: a connected
one-dimensional complex with reduced first cohomology `H̃¹ = F²`. -/
def wedgeCircleFacets : Finset (Finset (Fin 5)) := {{0, 1}, {1, 2}, {0, 2}, {0, 3}, {3, 4}, {0, 4}}

/-- **Rank-two reduced `H̃¹` source coherence.**  In the connected wedge complex the two empty-triangle
first Koszul classes `x₁x₂ · e₀` and `x₃x₄ · e₀` are linearly independent modulo Koszul boundaries: any
boundary equal to their combination forces both scalars to zero.  So the degree-`1` Hochster source
coherence of one connected HT source has rank `≥ 2`. -/
theorem hochster_wedge_classes_independent (F : Type*) [Field F] {α β : F}
    (cc : Fin 5 → Fin 5 → stanleyReisnerRing F wedgeCircleFacets)
    (hcc : srKoszulBoundary wedgeCircleFacets cc
      = fun v => α • (if v = 0 then srVertexX F wedgeCircleFacets 1 * srVertexX F wedgeCircleFacets 2 else 0)
          + β • (if v = 0 then srVertexX F wedgeCircleFacets 3 * srVertexX F wedgeCircleFacets 4 else 0)) :
    α = 0 ∧ β = 0 := by
  have h0 : srKoszulBoundary wedgeCircleFacets cc 0
      = α • (srVertexX F wedgeCircleFacets 1 * srVertexX F wedgeCircleFacets 2)
        + β • (srVertexX F wedgeCircleFacets 3 * srVertexX F wedgeCircleFacets 4) := by rw [hcc]; simp
  have h1 : srKoszulBoundary wedgeCircleFacets cc 1 = 0 := by
    rw [hcc]; simp [show (1 : Fin 5) ≠ 0 by decide]
  have h2 : srKoszulBoundary wedgeCircleFacets cc 2 = 0 := by
    rw [hcc]; simp [show (2 : Fin 5) ≠ 0 by decide]
  have h3 : srKoszulBoundary wedgeCircleFacets cc 3 = 0 := by
    rw [hcc]; simp [show (3 : Fin 5) ≠ 0 by decide]
  have h4 : srKoszulBoundary wedgeCircleFacets cc 4 = 0 := by
    rw [hcc]; simp [show (4 : Fin 5) ≠ 0 by decide]
  refine ⟨?_, ?_⟩
  · -- α = 0 via the {0,1,2} detector
    have hA := srEmptyTriangleDetector_koszulBoundary_zero wedgeCircleFacets (a := (0 : Fin 5)) (b := 1)
      (c := 2) (by decide) (by decide) (by decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide) cc
    rw [h0, h1, h2, map_zero, map_zero, add_zero, map_add, map_smul, map_smul,
      srPairDetector_srVertexX_mul wedgeCircleFacets (show (1 : Fin 5) ≠ 2 by decide)
        (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide),
      srPairDetector_srVertexX_mul_eq_zero wedgeCircleFacets (show (1 : Fin 5) ≠ 2 by decide)
        (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
        (Finsupp.ne_iff.mpr ⟨1, by simp⟩)] at hA
    simpa using hA
  · -- β = 0 via the {0,3,4} detector
    have hB := srEmptyTriangleDetector_koszulBoundary_zero wedgeCircleFacets (a := (0 : Fin 5)) (b := 3)
      (c := 4) (by decide) (by decide) (by decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
      (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide) cc
    rw [h0, h3, h4, map_zero, map_zero, add_zero, map_add, map_smul, map_smul,
      srPairDetector_srVertexX_mul_eq_zero wedgeCircleFacets (show (3 : Fin 5) ≠ 4 by decide)
        (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)
        (Finsupp.ne_iff.mpr ⟨3, by simp⟩),
      srPairDetector_srVertexX_mul wedgeCircleFacets (show (3 : Fin 5) ≠ 4 by decide)
        (by simp only [IsFaceOf, wedgeCircleFacets, Finset.mem_coe]; decide)] at hB
    simpa using hB

/-- **Unbounded source-coherence rank at fixed reduced degree `1`.**  A bouquet of `k` empty triangles
sharing one apex — apex `apex`, petal pairs `(p i, q i)` giving pairwise-distinct squarefree
multidegrees — carries `k` **linearly independent** first Koszul homology classes `x_{p i} x_{q i}·e_apex`.
Any first Koszul boundary equal to a combination `∑ c i · classᵢ` forces every coefficient to zero, read
off by the triangle detectors: the `i`-th detector is `1` on `classᵢ`, `0` on every other class (a
different multidegree), and vanishes on boundaries.  So the degree-`1` Hochster source coherence of one
connected HT source has arbitrarily large rank `k`, at fixed reduced cohomological degree. -/
theorem bouquet_classes_independent {α : Type*} [DecidableEq α] [Fintype α] (F : Type*) [Field F]
    (facets : Finset (Finset α)) (apex : α) {k : ℕ} (p q : Fin k → α)
    (hp : ∀ i, apex ≠ p i) (hq : ∀ i, apex ≠ q i) (hpq : ∀ i, p i ≠ q i)
    (hface_ap : ∀ i, IsFaceOf (↑facets : Set (Finset α)) {apex, p i})
    (hface_aq : ∀ i, IsFaceOf (↑facets : Set (Finset α)) {apex, q i})
    (hface_pq : ∀ i, IsFaceOf (↑facets : Set (Finset α)) {p i, q i})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {apex})
    (hpv : ∀ i, IsFaceOf (↑facets : Set (Finset α)) {p i})
    (hqv : ∀ i, IsFaceOf (↑facets : Set (Finset α)) {q i})
    (hdisj : ∀ i j, i ≠ j →
      Finsupp.single (p i) 1 + Finsupp.single (q i) 1
        ≠ Finsupp.single (p j) 1 + Finsupp.single (q j) 1)
    (c : Fin k → F) (cc : α → α → stanleyReisnerRing F facets)
    (hcc : srKoszulBoundary facets cc
      = fun v => ∑ i, c i •
          (if v = apex then srVertexX F facets (p i) * srVertexX F facets (q i) else 0)) :
    ∀ i, c i = 0 := by
  intro i
  have hapex : srKoszulBoundary facets cc apex
      = ∑ j, c j • (srVertexX F facets (p j) * srVertexX F facets (q j)) := by
    rw [hcc]; simp
  have hpi : srKoszulBoundary facets cc (p i) = 0 := by
    rw [hcc]; simp [Ne.symm (hp i)]
  have hqi : srKoszulBoundary facets cc (q i) = 0 := by
    rw [hcc]; simp [Ne.symm (hq i)]
  have key : srPairDetector F facets (p i) (q i) (hpq i) (hface_pq i)
      (∑ j, c j • (srVertexX F facets (p j) * srVertexX F facets (q j))) = c i := by
    rw [map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hji => by
        rw [map_smul, srPairDetector_srVertexX_mul_eq_zero facets (hpq i) (hface_pq i)
          (hdisj i j (Ne.symm hji)), smul_zero]),
      map_smul, srPairDetector_srVertexX_mul facets (hpq i) (hface_pq i), smul_eq_mul, mul_one]
  have hΨ := srEmptyTriangleDetector_koszulBoundary_zero facets (hp i) (hq i) (hpq i)
    (hface_ap i) (hface_pq i) (hface_aq i) ha (hpv i) (hqv i) cc
  rw [hapex, hpi, hqi, map_zero, map_zero, add_zero, add_zero, key] at hΨ
  exact hΨ

/-! ## A concrete unconditional bouquet realizing rank `k` for every `k` -/

/-- Vertex type for the concrete `k`-triangle bouquet: `none` is the shared apex, `some (i, b)` is the
`b`-petal of triangle `i`. -/
abbrev bqVtx (k : ℕ) := Option (Fin k × Bool)

/-- The `k`-triangle bouquet complex on `bqVtx k`: for each `i`, the three edges of triangle `i`. -/
def bqFacets (k : ℕ) : Finset (Finset (bqVtx k)) :=
  Finset.univ.biUnion fun i =>
    {{none, some (i, false)}, {none, some (i, true)}, {some (i, false), some (i, true)}}

theorem bqFacets_ap_mem {k : ℕ} (i : Fin k) :
    ({none, some (i, false)} : Finset (bqVtx k)) ∈ bqFacets k :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_insert_self _ _⟩

theorem bqFacets_aq_mem {k : ℕ} (i : Fin k) :
    ({none, some (i, true)} : Finset (bqVtx k)) ∈ bqFacets k :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp⟩

theorem bqFacets_pq_mem {k : ℕ} (i : Fin k) :
    ({some (i, false), some (i, true)} : Finset (bqVtx k)) ∈ bqFacets k :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp⟩

/-- **Unbounded source-coherence rank, unconditionally, for every `k`.**  On the concrete `k`-triangle
bouquet the `k` first Koszul homology classes `x_{some(i,false)} x_{some(i,true)} · e_none` are linearly
independent modulo Koszul boundaries — a single connected complex whose degree-`1` Hochster source
coherence has rank exactly `k`, with no remaining hypotheses. -/
theorem bouquet_concrete_independent (F : Type*) [Field F] {k : ℕ} (c : Fin k → F)
    (cc : bqVtx k → bqVtx k → stanleyReisnerRing F (bqFacets k))
    (hcc : srKoszulBoundary (bqFacets k) cc
      = fun v => ∑ i, c i • (if v = none then
          srVertexX F (bqFacets k) (some (i, false)) * srVertexX F (bqFacets k) (some (i, true))
        else 0)) :
    ∀ i, c i = 0 := by
  intro i
  exact bouquet_classes_independent F (bqFacets k) none (fun j => some (j, false))
    (fun j => some (j, true)) (fun j => by simp) (fun j => by simp) (fun j => by simp)
    (fun j => ⟨_, Finset.mem_coe.mpr (bqFacets_ap_mem j), Finset.Subset.refl _⟩)
    (fun j => ⟨_, Finset.mem_coe.mpr (bqFacets_aq_mem j), Finset.Subset.refl _⟩)
    (fun j => ⟨_, Finset.mem_coe.mpr (bqFacets_pq_mem j), Finset.Subset.refl _⟩)
    ⟨_, Finset.mem_coe.mpr (bqFacets_ap_mem i), by simp⟩
    (fun j => ⟨_, Finset.mem_coe.mpr (bqFacets_ap_mem j), by simp⟩)
    (fun j => ⟨_, Finset.mem_coe.mpr (bqFacets_aq_mem j), by simp⟩)
    (fun a b hab => Finsupp.ne_iff.mpr ⟨some (a, false), by simp [hab]⟩)
    c cc hcc i

end GaloisForLFunctions.HTGeometry

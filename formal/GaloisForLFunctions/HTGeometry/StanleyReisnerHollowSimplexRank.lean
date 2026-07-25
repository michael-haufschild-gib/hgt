import GaloisForLFunctions.HTGeometry.StanleyReisnerEmptyTriangleRank

/-!
# Exact first-Koszul rank at a hollow simplex (uniform degree Hochster equality)

For a minimal nonface `σ` (a hollow simplex `∂Δ^{|σ|−1}`, every proper face present) the
multidegree-`σ` first Koszul syzygies form the `|σ|`-parameter family

`w(λ) = ∑_{i∈σ} λ_i · (∏_{w∈σ∖i} x_w) · e_i`.

Every such `w` is a first Koszul cycle (because `∏_{w∈σ} x_w = 0`).  This file builds the reusable core
toward the exact-rank statement `w(λ) is a boundary ↔ ∑_{i∈σ} λ_i = 0`: the general single-entry
boundary lemma, which generalizes the three-vertex `srEmptyTriangle_cyclic_syzygy_homologous` to every
`σ` — the boundary of the single `2`-chain `⟨i₀,k⟩⊗∏_{σ∖{i₀,k}} x_w` is the difference of the two basis
syzygies `∏_{σ∖i₀}·e_{i₀} − ∏_{σ∖k}·e_k`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R α : Type*} [CommRing R] [DecidableEq α] [Fintype α]

/-- The multidegree-`σ` first Koszul syzygy with coefficient family `l`: `∑_{i∈σ} l_i (∏_{σ∖i} x) e_i`. -/
noncomputable def srHollowSimplexSyzygyVec (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (σ : Finset α) (l : α → R) : α → stanleyReisnerRing R facets :=
  fun v => if v ∈ σ then l v • ∏ w ∈ σ.erase v, srVertexX R facets w else 0

/-- Every hollow-simplex syzygy is a first Koszul cycle: each term is a multiple of `∏_{σ} x = 0`. -/
theorem srHollowSimplexSyzygyVec_isCycle (facets : Finset (Finset α)) (σ : Finset α)
    (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) σ) (l : α → R) :
    srKoszulRelation facets (srHollowSimplexSyzygyVec R facets σ l) = 0 := by
  have hprod : ∏ w ∈ σ, srVertexX R facets w = 0 := srProd_eq_zero_of_not_isFace facets hnf
  rw [srKoszulRelation]
  apply Finset.sum_eq_zero
  intro v _
  simp only [srHollowSimplexSyzygyVec]
  by_cases hv : v ∈ σ
  · rw [if_pos hv, smul_mul_assoc, Finset.prod_erase_mul σ (srVertexX R facets) hv, hprod, smul_zero]
  · rw [if_neg hv, zero_mul]

/-- **General single-entry boundary lemma.**  The first Koszul boundary of the single `2`-chain
`⟨i₀,k⟩ ⊗ ∏_{w∈σ∖{i₀,k}} x_w` is the difference `∏_{σ∖i₀}·e_{i₀} − ∏_{σ∖k}·e_k` of the two basis
hollow-simplex syzygies.  Generalizes `srEmptyTriangle_cyclic_syzygy_homologous` to all `σ`. -/
theorem srHollowSyzygy_single_boundary (facets : Finset (Finset α)) (σ : Finset α) {i₀ k : α}
    (hi₀ : i₀ ∈ σ) (hk : k ∈ σ) (hne : i₀ ≠ k) :
    srKoszulBoundary facets (fun i j => if i = i₀ ∧ j = k then
        ∏ w ∈ (σ.erase i₀).erase k, srVertexX R facets w else 0)
      = (fun v => if v = i₀ then ∏ w ∈ σ.erase i₀, srVertexX R facets w else 0)
        - fun v => if v = k then ∏ w ∈ σ.erase k, srVertexX R facets w else 0 := by
  funext v
  rw [srKoszulBoundary, Pi.sub_apply]
  by_cases hvi : v = i₀
  · rw [if_pos hvi, if_neg (ne_of_eq_of_ne hvi hne),
      Finset.sum_eq_single k (fun j _ hjk => by simp [hvi, hne, hjk])
        (fun h => absurd (Finset.mem_univ _) h)]
    rw [if_pos ⟨hvi, rfl⟩, if_neg (fun h : k = i₀ ∧ v = k => hne h.1.symm), sub_zero, mul_comm,
      Finset.mul_prod_erase (σ.erase i₀) (srVertexX R facets)
        (Finset.mem_erase.mpr ⟨Ne.symm hne, hk⟩), sub_zero]
  · by_cases hvk : v = k
    · rw [if_neg hvi, if_pos hvk,
        Finset.sum_eq_single i₀ (fun j _ hji => by simp [hvk, hne.symm, hji])
          (fun h => absurd (Finset.mem_univ _) h)]
      rw [if_neg (fun h : v = i₀ ∧ i₀ = k => hne h.2), if_pos ⟨rfl, hvk⟩, sub_mul, zero_mul,
        show (σ.erase i₀).erase k = (σ.erase k).erase i₀ from Finset.erase_right_comm,
        Finset.prod_erase_mul (σ.erase k) (srVertexX R facets)
          (Finset.mem_erase.mpr ⟨hne, hi₀⟩)]
    · rw [if_neg hvi, if_neg hvk, sub_zero,
        Finset.sum_eq_zero (fun j _ => by simp [hvi, hvk])]

/-- **Detector direction:** a hollow-simplex syzygy that is a first Koszul boundary has coefficient sum
zero.  The uniform face detector `Φ_σ = ∑_{i∈σ} srFaceDetector(σ∖i)` reads `w(l)` as `∑_{i∈σ} l_i` and
annihilates every boundary (its double sum over ordered pairs cancels by the `(i,j)↔(j,i)` involution). -/
theorem srHollowSimplexSyzygyVec_sum_zero_of_boundary (facets : Finset (Finset α)) (σ : Finset α)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)) {l : α → R}
    (h : ∃ cc : α → α → stanleyReisnerRing R facets,
      srKoszulBoundary facets cc = srHollowSimplexSyzygyVec R facets σ l) :
    ∑ i ∈ σ, l i = 0 := by
  classical
  obtain ⟨cc, hcc⟩ := h
  set f : α → α → R := fun i j =>
    if h : IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j) then
      srFaceDetector R facets ((σ.erase i).erase j) h (cc i j - cc j i) else 0 with hf
  have f_anti : ∀ i j, f i j + f j i = 0 := by
    intro i j
    simp only [hf]
    rw [show (σ.erase j).erase i = (σ.erase i).erase j from Finset.erase_right_comm]
    by_cases hfc : IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j)
    · rw [dif_pos hfc, dif_pos hfc, ← map_add,
        show (cc i j - cc j i) + (cc j i - cc i j) = 0 by abel, map_zero]
    · rw [dif_neg hfc, dif_neg hfc, add_zero]
  have hbdry : (∑ i ∈ σ, if h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) then
        srFaceDetector R facets (σ.erase i) h (srKoszulBoundary facets cc i) else 0) = 0 := by
    rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_sigma']
    · exact antisym_sigma_sum_zero σ f f_anti
    · rw [dif_pos (hface i hi), srFaceDetector_srKoszulBoundary facets (hface i hi) cc i]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [hf]
      rw [dif_pos (isFaceOf_mono (Finset.erase_subset j (σ.erase i)) (hface i hi))]
  have hsyz : (∑ i ∈ σ, if h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) then
        srFaceDetector R facets (σ.erase i) h (srHollowSimplexSyzygyVec R facets σ l i) else 0)
      = ∑ i ∈ σ, l i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [dif_pos (hface i hi), srHollowSimplexSyzygyVec, if_pos hi, map_smul,
      srFaceDetector_prod, smul_eq_mul, mul_one]
  rw [hcc] at hbdry
  exact hsyz.symm.trans hbdry

/-- **Spanning direction:** every sum-zero hollow-simplex syzygy is a first Koszul boundary.  Fixing a
base vertex `i₀ ∈ σ`, the `2`-chain `∑_{j∈σ∖i₀} −l_j·⟨i₀,j⟩⊗∏_{σ∖{i₀,j}} x` has boundary `w(l)` when
`∑_{i∈σ} l_i = 0`. -/
theorem srHollowSimplexSyzygyVec_boundary_of_sum_zero (facets : Finset (Finset α)) (σ : Finset α)
    {i₀ : α} (hi₀ : i₀ ∈ σ) {l : α → R} (hsum : ∑ i ∈ σ, l i = 0) :
    ∃ cc : α → α → stanleyReisnerRing R facets,
      srKoszulBoundary facets cc = srHollowSimplexSyzygyVec R facets σ l := by
  classical
  have hsum' : ∑ j ∈ σ.erase i₀, l j = -l i₀ := by
    have hh := Finset.add_sum_erase σ l hi₀; rw [hsum] at hh; linear_combination hh
  refine ⟨fun i j => if i = i₀ ∧ j ∈ σ.erase i₀ then
      -(l j) • ∏ w ∈ (σ.erase i₀).erase j, srVertexX R facets w else 0, ?_⟩
  funext v
  rw [srKoszulBoundary, srHollowSimplexSyzygyVec]
  by_cases hvi : v = i₀
  · rw [hvi, if_pos hi₀, Finset.sum_congr rfl (fun j _ =>
      show ((if i₀ = i₀ ∧ j ∈ σ.erase i₀ then
              -(l j) • ∏ w ∈ (σ.erase i₀).erase j, srVertexX R facets w else 0)
            - (if j = i₀ ∧ i₀ ∈ σ.erase i₀ then
              -(l i₀) • ∏ w ∈ (σ.erase i₀).erase i₀, srVertexX R facets w else 0))
            * srVertexX R facets j
          = if j ∈ σ.erase i₀ then
              -(l j) • ∏ w ∈ σ.erase i₀, srVertexX R facets w else 0 from by
        rw [if_neg (show ¬(j = i₀ ∧ i₀ ∈ σ.erase i₀) from fun h => (Finset.mem_erase.mp h.2).1 rfl),
          sub_zero]
        by_cases hj : j ∈ σ.erase i₀
        · rw [if_pos ⟨rfl, hj⟩, if_pos hj, smul_mul_assoc,
            Finset.prod_erase_mul (σ.erase i₀) (srVertexX R facets) hj]
        · rw [if_neg (fun h => hj h.2), if_neg hj, zero_mul]),
      Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_smul, Finset.sum_neg_distrib, hsum',
      neg_neg]
  · by_cases hvs : v ∈ σ
    · have hve : v ∈ σ.erase i₀ := Finset.mem_erase.mpr ⟨hvi, hvs⟩
      rw [if_pos hvs, Finset.sum_eq_single i₀
        (fun j _ hji => by
          rw [if_neg (fun h => hvi h.1), if_neg (fun h => hji h.1), sub_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ i₀) h),
        if_neg (fun h => hvi h.1), if_pos ⟨rfl, hve⟩, zero_sub, neg_smul, neg_neg, smul_mul_assoc,
        show (σ.erase i₀).erase v = (σ.erase v).erase i₀ from Finset.erase_right_comm,
        Finset.prod_erase_mul (σ.erase v) (srVertexX R facets)
          (Finset.mem_erase.mpr ⟨Ne.symm hvi, hi₀⟩)]
    · rw [if_neg hvs, Finset.sum_eq_zero (fun j _ => by
        rw [if_neg (fun h => hvi h.1),
          if_neg (fun h => hvs (Finset.mem_of_mem_erase h.2)), sub_zero, zero_mul])]

/-- **Exact first-Koszul rank at a hollow simplex (uniform degree Hochster equality).**  For a hollow
simplex `σ` (`∂Δ^{|σ|−1}`, every proper face present) the multidegree-`σ` syzygy `w(l)` is a first
Koszul boundary **iff** `∑_{i∈σ} l_i = 0`.  Hence the `|σ|`-parameter syzygy space collapses to the
one-dimensional `Tor_{1,σ} ≅ H̃^{|σ|−2}(∂Δ^{|σ|−1})`, in every dimension `|σ|`. -/
theorem srHollowSimplexSyzygyVec_boundary_iff (facets : Finset (Finset α)) (σ : Finset α)
    (hσ : σ.Nonempty)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)) (l : α → R) :
    (∃ cc : α → α → stanleyReisnerRing R facets,
        srKoszulBoundary facets cc = srHollowSimplexSyzygyVec R facets σ l)
      ↔ ∑ i ∈ σ, l i = 0 :=
  ⟨fun h => srHollowSimplexSyzygyVec_sum_zero_of_boundary facets σ hface h,
    fun h => srHollowSimplexSyzygyVec_boundary_of_sum_zero facets σ hσ.choose_spec h⟩

omit [Fintype α] in
/-- The hollow-simplex syzygy is `R`-linear in its coefficient family: `w(l) − w(l') = w(l − l')`. -/
theorem srHollowSimplexSyzygyVec_sub (facets : Finset (Finset α)) (σ : Finset α) (l l' : α → R) :
    srHollowSimplexSyzygyVec R facets σ l - srHollowSimplexSyzygyVec R facets σ l'
      = srHollowSimplexSyzygyVec R facets σ (l - l') := by
  funext v
  simp only [srHollowSimplexSyzygyVec, Pi.sub_apply]
  by_cases hv : v ∈ σ
  · rw [if_pos hv, if_pos hv, if_pos hv, sub_smul]
  · rw [if_neg hv, if_neg hv, if_neg hv, sub_zero]

/-- **Homology class is determined by the coefficient sum.**  Two hollow-simplex syzygies are
homologous (differ by a first Koszul boundary) **iff** their coefficient sums agree.  Hence the
homology class of `w(l)` depends only on `∑_{i∈σ} l_i` — the exact one-dimensionality of
`Tor_{1,σ} ≅ H̃^{|σ|−2}(∂Δ^{|σ|−1})` at the class level. -/
theorem srHollowSimplexSyzygy_homologous_iff (facets : Finset (Finset α)) (σ : Finset α)
    (hσ : σ.Nonempty)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)) (l l' : α → R) :
    (∃ cc : α → α → stanleyReisnerRing R facets,
        srKoszulBoundary facets cc
          = srHollowSimplexSyzygyVec R facets σ l - srHollowSimplexSyzygyVec R facets σ l')
      ↔ ∑ i ∈ σ, l i = ∑ i ∈ σ, l' i := by
  rw [srHollowSimplexSyzygyVec_sub, srHollowSimplexSyzygyVec_boundary_iff facets σ hσ hface (l - l'),
    show (∑ i ∈ σ, (l - l') i) = ∑ i ∈ σ, l i - ∑ i ∈ σ, l' i from by
      simp only [Pi.sub_apply]; exact Finset.sum_sub_distrib l l', sub_eq_zero]

/-- The first Koszul boundary map as an `R`-linear map on `2`-chains. -/
noncomputable def srKoszulBoundaryₗ (facets : Finset (Finset α)) :
    (α → α → stanleyReisnerRing R facets) →ₗ[R] (α → stanleyReisnerRing R facets) where
  toFun c := srKoszulBoundary facets c
  map_add' c c' := by
    funext v
    simp only [srKoszulBoundary, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  map_smul' r c := by
    funext v
    simp only [srKoszulBoundary, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [← smul_sub, smul_mul_assoc])

/-- The submodule of first Koszul boundaries (the image of the boundary map). -/
noncomputable def srKoszulBoundaries (facets : Finset (Finset α)) :
    Submodule R (α → stanleyReisnerRing R facets) :=
  LinearMap.range (srKoszulBoundaryₗ facets)

/-- **Module-level exact rank.**  In the first Koszul homology module
`(α → S) ⧸ srKoszulBoundaries`, the class of a hollow-simplex syzygy `w(l)` is zero **iff** its
coefficient sum vanishes. -/
theorem srHollowSimplexSyzygy_mk_eq_zero_iff (facets : Finset (Finset α)) (σ : Finset α)
    (hσ : σ.Nonempty)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)) (l : α → R) :
    (Submodule.Quotient.mk (srHollowSimplexSyzygyVec R facets σ l) :
        (α → stanleyReisnerRing R facets) ⧸ srKoszulBoundaries facets) = 0
      ↔ ∑ i ∈ σ, l i = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, srKoszulBoundaries, LinearMap.mem_range]
  exact srHollowSimplexSyzygyVec_boundary_iff facets σ hσ hface l

/-- **Module-level one-dimensionality.**  Two hollow-simplex syzygy classes coincide in the first
Koszul homology module **iff** their coefficient sums agree — so the syzygy classes form a copy of `R`
inside `Tor_{1,σ}`, parametrized by the coefficient sum. -/
theorem srHollowSimplexSyzygy_mk_eq_iff (facets : Finset (Finset α)) (σ : Finset α)
    (hσ : σ.Nonempty)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)) (l l' : α → R) :
    (Submodule.Quotient.mk (srHollowSimplexSyzygyVec R facets σ l) :
        (α → stanleyReisnerRing R facets) ⧸ srKoszulBoundaries facets)
        = Submodule.Quotient.mk (srHollowSimplexSyzygyVec R facets σ l')
      ↔ ∑ i ∈ σ, l i = ∑ i ∈ σ, l' i := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, srHollowSimplexSyzygyVec_sub,
    srHollowSimplexSyzygy_mk_eq_zero_iff facets σ hσ hface (l - l'),
    show (∑ i ∈ σ, (l - l') i) = ∑ i ∈ σ, l i - ∑ i ∈ σ, l' i from by
      simp only [Pi.sub_apply]; exact Finset.sum_sub_distrib l l', sub_eq_zero]

omit [Fintype α] in
/-- The hollow-simplex syzygy is homogeneous in its coefficient family: `r • w(l) = w(r • l)`. -/
theorem srHollowSimplexSyzygyVec_smul (facets : Finset (Finset α)) (σ : Finset α) (r : R)
    (l : α → R) :
    r • srHollowSimplexSyzygyVec R facets σ l = srHollowSimplexSyzygyVec R facets σ (r • l) := by
  funext v
  simp only [srHollowSimplexSyzygyVec, Pi.smul_apply]
  by_cases hv : v ∈ σ
  · rw [if_pos hv, if_pos hv, smul_smul, smul_eq_mul]
  · rw [if_neg hv, if_neg hv, smul_zero]

/-- The base first Koszul homology class of a hollow simplex: the class of the unit-coefficient syzygy
`w(𝟙_{i₀})`. -/
noncomputable def srHollowBaseClass (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (σ : Finset α) (i₀ : α) :
    (α → stanleyReisnerRing R facets) ⧸ srKoszulBoundaries (R := R) facets :=
  Submodule.Quotient.mk (srHollowSimplexSyzygyVec R facets σ (fun i => if i = i₀ then (1 : R) else 0))

/-- The base syzygy class generates a free rank-one submodule: `r ↦ r • [base]` is injective, since
`r • [base]` vanishes exactly when `r = ∑_{i∈σ} (r·𝟙_{i₀})_i = 0`. -/
theorem srHollowBaseClass_toSpanSingleton_injective (facets : Finset (Finset α)) (σ : Finset α)
    (hσ : σ.Nonempty) (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i))
    {i₀ : α} (hi₀ : i₀ ∈ σ) :
    Function.Injective (LinearMap.toSpanSingleton R
      ((α → stanleyReisnerRing R facets) ⧸ srKoszulBoundaries facets)
      (srHollowBaseClass R facets σ i₀)) := by
  intro a b hab
  simp only [LinearMap.toSpanSingleton_apply] at hab
  have h0 : (a - b) • srHollowBaseClass R facets σ i₀ = 0 := by rw [sub_smul, hab, sub_self]
  rw [srHollowBaseClass, ← Submodule.Quotient.mk_smul, srHollowSimplexSyzygyVec_smul,
    srHollowSimplexSyzygy_mk_eq_zero_iff facets σ hσ hface,
    show ∑ i ∈ σ, ((a - b) • fun j => if j = i₀ then (1 : R) else 0) i = a - b from by
      simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' σ i₀ (fun _ => a - b), if_pos hi₀]] at h0
  exact sub_eq_zero.mp h0

/-- **The degree-1 Hochster iso as a `LinearEquiv`.**  For a hollow simplex `σ`, the syzygy classes
form a free rank-one `R`-module inside the first Koszul homology: `R ≃ₗ R·[base class]` — the strongest
(isomorphism) form of the exact-rank `Tor_{1,σ} ≅ H̃^{|σ|−2}(∂Δ^{|σ|−1})`. -/
noncomputable def srHollowClassEquiv (facets : Finset (Finset α)) (σ : Finset α)
    (hσ : σ.Nonempty) (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i))
    {i₀ : α} (hi₀ : i₀ ∈ σ) :
    R ≃ₗ[R] ↥(LinearMap.range (LinearMap.toSpanSingleton R
      ((α → stanleyReisnerRing R facets) ⧸ srKoszulBoundaries facets)
      (srHollowBaseClass R facets σ i₀))) :=
  LinearEquiv.ofInjective _ (srHollowBaseClass_toSpanSingleton_injective facets σ hσ hface hi₀)

open Classical in
/-- The uniform `σ`-detector `Φ_σ = ∑_{i∈σ} srFaceDetector(σ∖i)`, as an `R`-linear functional on
`1`-chains. -/
noncomputable def srHollowDetectorₗ (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (σ : Finset α) :
    (α → stanleyReisnerRing R facets) →ₗ[R] R where
  toFun a := ∑ i ∈ σ, if h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) then
    srFaceDetector R facets (σ.erase i) h (a i) else 0
  map_add' a a' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)
    · rw [dif_pos h, dif_pos h, dif_pos h, Pi.add_apply, map_add]
    · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]
  map_smul' r a := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)
    · rw [dif_pos h, dif_pos h, RingHom.id_apply, Pi.smul_apply, map_smul, smul_eq_mul]
    · rw [dif_neg h, dif_neg h, smul_zero]

/-- The `σ`-detector annihilates every first Koszul boundary (its double sum over ordered pairs cancels
by the `(i,j)↔(j,i)` involution). -/
theorem srHollowDetectorₗ_apply_boundary (facets : Finset (Finset α)) (σ : Finset α)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i))
    (c : α → α → stanleyReisnerRing R facets) :
    srHollowDetectorₗ R facets σ (srKoszulBoundary facets c) = 0 := by
  classical
  set f : α → α → R := fun i j =>
    if h : IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j) then
      srFaceDetector R facets ((σ.erase i).erase j) h (c i j - c j i) else 0 with hf
  have f_anti : ∀ i j, f i j + f j i = 0 := by
    intro i j
    simp only [hf]
    rw [show (σ.erase j).erase i = (σ.erase i).erase j from Finset.erase_right_comm]
    by_cases hfc : IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j)
    · rw [dif_pos hfc, dif_pos hfc, ← map_add,
        show (c i j - c j i) + (c j i - c i j) = 0 by abel, map_zero]
    · rw [dif_neg hfc, dif_neg hfc, add_zero]
  show (∑ i ∈ σ, if h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) then
      srFaceDetector R facets (σ.erase i) h (srKoszulBoundary facets c i) else 0) = 0
  rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_sigma']
  · exact antisym_sigma_sum_zero σ f f_anti
  · rw [dif_pos (hface i hi), srFaceDetector_srKoszulBoundary facets (hface i hi) c i]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [hf]
    rw [dif_pos (isFaceOf_mono (Finset.erase_subset j (σ.erase i)) (hface i hi))]

/-- The `σ`-detector descends to the first Koszul homology module as an `R`-linear retraction
`Tor₁ →ₗ[R] R`. -/
noncomputable def srHollowDetectorTor (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (σ : Finset α) (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)) :
    ((α → stanleyReisnerRing R facets) ⧸ srKoszulBoundaries (R := R) facets) →ₗ[R] R :=
  Submodule.liftQ (srKoszulBoundaries (R := R) facets) (srHollowDetectorₗ R facets σ)
    (fun x hx => by
      obtain ⟨c, rfl⟩ := hx
      exact LinearMap.mem_ker.mpr (srHollowDetectorₗ_apply_boundary facets σ hface c))

/-- **`R` is a direct summand of the first Koszul homology.**  The descended `σ`-detector is `1` on the
base hollow-simplex syzygy class, so it splits the base-class embedding `R → Tor₁` — combined with
`srHollowClassEquiv` this exhibits `R` as a direct summand of `Tor_{1,σ}`. -/
theorem srHollowDetectorTor_base (facets : Finset (Finset α)) (σ : Finset α)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)) {i₀ : α} (hi₀ : i₀ ∈ σ) :
    srHollowDetectorTor R facets σ hface (srHollowBaseClass R facets σ i₀) = 1 := by
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

end GaloisForLFunctions.HTGeometry

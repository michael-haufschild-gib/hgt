import GaloisForLFunctions.HTGeometry.VertexIndependenceCochain

/-!
# Joins of path independence complexes have the reduced cohomology of odd spheres

An independent block support with the separating gaps held at zero is a disjoint union of paths,
and the independence complex of a disjoint union of graphs is the join of the independence
complexes. So the `n`-fold join of `Ind(P_5)` is the independence complex of the induced subgraph
of the path on

  `joinVertsFrom a n = {a + 6i + q : i < n, q < 5}`,

that is, `n` blocks of five consecutive vertices separated by one deleted vertex. Two applications
of the leaf reduction of `VertexIndependenceCochain` strip one block and lower the occupation
degree by two, so by induction the reduced cohomology is one dimensional in occupation `2n` and
zero in every other occupation. Occupation `2n` is topological degree `2n - 1`: the reduced
cohomology of `S^(2n-1)`, as the classical homotopy equivalence predicts.

The base case is the empty vertex set, whose independence complex is the single empty face: one
class in occupation zero, the reduced cohomology of `S^(-1)`.
-/

namespace GaloisForLFunctions.HTGeometry
namespace VertexIndependence

noncomputable section
open Finset

variable {F : Type*} [CommRing F]

/-! ### Transport along an equality of vertex sets -/

/-- Equal vertex sets have the same reduced cohomology. -/
def cohomologyCongr (F : Type*) [CommRing F] {V W : Finset ℕ} (h : V = W) (j : ℕ) :
    cohomology F V j ≃ₗ[F] cohomology F W j := by
  subst h; exact LinearEquiv.refl F _

/-- Equal occupation degrees give the same reduced cohomology. -/
def cohomologyDegreeCongr (F : Type*) [CommRing F] (V : Finset ℕ) {i j : ℕ} (h : i = j) :
    cohomology F V i ≃ₗ[F] cohomology F V j := by
  subst h; exact LinearEquiv.refl F _

/-! ### Vanishing criteria -/

theorem supported_eq_bot (F : Type*) [CommRing F] {V : Finset ℕ} {j : ℕ}
    (h : ∀ σ : Finset ℕ, IsFace V σ → σ.card ≠ j) : supported F V j = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  rw [Submodule.mem_bot]
  funext σ
  show f σ = 0
  by_cases hface : IsFace V σ
  · exact hf σ (Or.inl (h σ hface))
  · exact hf σ (Or.inr hface)

theorem cocycles_eq_bot_of_supported_eq_bot {V : Finset ℕ} {j : ℕ}
    (h : supported F V j = ⊥) : cocycles F V j = ⊥ :=
  le_antisymm (fun _ hf => h.le hf.1) bot_le

theorem cohomology_subsingleton_of_le {V : Finset ℕ} {j : ℕ}
    (h : cocycles F V j ≤ coboundaries F V j) : Subsingleton (cohomology F V j) := by
  have htop : Submodule.comap (cocycles F V j).subtype (coboundaries F V j) = ⊤ :=
    Submodule.comap_subtype_eq_top.mpr h
  constructor
  intro x y
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Submodule.Quotient.eq, htop]
  exact Submodule.mem_top

theorem cohomology_subsingleton_of_cocycles_eq_bot {V : Finset ℕ} {j : ℕ}
    (h : cocycles F V j = ⊥) : Subsingleton (cohomology F V j) :=
  cohomology_subsingleton_of_le (by rw [h]; exact bot_le)

theorem cohomology_subsingleton_of_card_lt (F : Type*) [CommRing F] {V : Finset ℕ} {j : ℕ}
    (hj : V.card < j) : Subsingleton (cohomology F V j) :=
  cohomology_subsingleton_of_cocycles_eq_bot
    (cocycles_eq_bot_of_supported_eq_bot (supported_eq_bot F (fun σ hσ hc => by
      have hsub : σ ⊆ V := fun v hv => hσ.1 v hv
      have := Finset.card_le_card hsub
      omega)))

/-! ### Occupation zero on a nonempty vertex set -/

theorem isFace_singleton {V : Finset ℕ} {a : ℕ} (ha : a ∈ V) : IsFace V ({a} : Finset ℕ) := by
  refine ⟨fun v hv => ?_, fun v hv hv1 => ?_⟩
  · rw [Finset.mem_singleton] at hv; exact hv ▸ ha
  · rw [Finset.mem_singleton] at hv
    subst hv
    rw [Finset.mem_singleton] at hv1
    omega

theorem coboundary_singleton {V : Finset ℕ} {a : ℕ} (ha : a ∈ V)
    (f : Finset ℕ → F) : coboundary F V f {a} = f ∅ := by
  have hsm : ∀ u ∈ ({a} : Finset ℕ), a ≤ u := fun u hu => by
    rw [Finset.mem_singleton] at hu; omega
  rw [coboundary_of_face (isFace_singleton ha), simplicialCoboundary_apply,
    Finset.sum_singleton, faceSign_min hsm, one_mul, Finset.erase_singleton]

theorem cocycles_occupation_zero_eq_bot (F : Type*) [CommRing F] {V : Finset ℕ}
    (hV : V.Nonempty) : cocycles F V 0 = ⊥ := by
  obtain ⟨a, ha⟩ := hV
  refine le_antisymm (fun f hf => ?_) bot_le
  rw [Submodule.mem_bot]
  have hδ : coboundary F V f = 0 := coboundary_eq_zero_of_mem_cocycles hf
  have hemp : f ∅ = 0 := by
    have h := congrFun hδ {a}
    rw [coboundary_singleton ha] at h
    exact h
  funext σ
  show f σ = 0
  by_cases hσ : σ = ∅
  · subst hσ; exact hemp
  · exact hf.1 σ (Or.inl fun h => hσ (Finset.card_eq_zero.mp h))

theorem cohomology_occupation_zero_subsingleton (F : Type*) [CommRing F] {V : Finset ℕ}
    (hV : V.Nonempty) : Subsingleton (cohomology F V 0) :=
  cohomology_subsingleton_of_cocycles_eq_bot (cocycles_occupation_zero_eq_bot F hV)

/-! ### The empty vertex set -/

theorem isFace_empty_verts_iff {σ : Finset ℕ} : IsFace (∅ : Finset ℕ) σ ↔ σ = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact absurd (h.1 v hv) (by simp)
  · intro h
    subst h
    exact isFace_empty _

theorem coboundary_empty_verts (f : Finset ℕ → F) : coboundary F (∅ : Finset ℕ) f = 0 := by
  funext σ
  show coboundary F ∅ f σ = 0
  by_cases hface : IsFace (∅ : Finset ℕ) σ
  · have hσ : σ = ∅ := isFace_empty_verts_iff.mp hface
    subst hσ
    rw [coboundary_of_face hface, simplicialCoboundary_apply, Finset.sum_empty]
  · rw [coboundary_of_not_face hface]

theorem supported_empty_verts_eq_bot (F : Type*) [CommRing F] {j : ℕ} (hj : 1 ≤ j) :
    supported F (∅ : Finset ℕ) j = ⊥ :=
  supported_eq_bot F fun σ hσ hc => by
    rw [isFace_empty_verts_iff.mp hσ, Finset.card_empty] at hc
    omega

theorem cohomology_empty_verts_subsingleton (F : Type*) [CommRing F] {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (cohomology F (∅ : Finset ℕ) j) :=
  cohomology_subsingleton_of_cocycles_eq_bot
    (cocycles_eq_bot_of_supported_eq_bot (supported_empty_verts_eq_bot F hj))

theorem coboundaries_occupation_zero (V : Finset ℕ) : coboundaries F V 0 = ⊥ := rfl

theorem comap_coboundaries_occupation_zero (V : Finset ℕ) :
    Submodule.comap (cocycles F V 0).subtype (coboundaries F V 0) = ⊥ := by
  rw [coboundaries_occupation_zero, Submodule.comap_bot, Submodule.ker_subtype]

/-- Evaluation at the empty face on the occupation-zero cocycles. -/
def emptyEval (F : Type*) [CommRing F] (V : Finset ℕ) : cocycles F V 0 →ₗ[F] F :=
  LinearMap.proj (∅ : Finset ℕ) ∘ₗ (cocycles F V 0).subtype

theorem emptyEval_apply (V : Finset ℕ) (f : cocycles F V 0) :
    emptyEval F V f = (f : Finset ℕ → F) ∅ := rfl

theorem mem_cocycles_empty_verts {f : Finset ℕ → F} (hf : f ∈ supported F (∅ : Finset ℕ) 0) :
    f ∈ cocycles F (∅ : Finset ℕ) 0 := by
  refine ⟨hf, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, coboundaryₗ_apply]
  exact coboundary_empty_verts f

/-- The cochain supported on a single face. -/
def faceUnit (F : Type*) [CommRing F] (σ₀ : Finset ℕ) (c : F) (σ : Finset ℕ) : F :=
  if σ = σ₀ then c else 0

theorem faceUnit_self (σ₀ : Finset ℕ) (c : F) : faceUnit F σ₀ c σ₀ = c := by
  rw [faceUnit, if_pos rfl]

theorem faceUnit_of_ne {σ σ₀ : Finset ℕ} (h : σ ≠ σ₀) (c : F) : faceUnit F σ₀ c σ = 0 := by
  rw [faceUnit, if_neg h]

theorem faceUnit_mem_supported {V : Finset ℕ} {j : ℕ} {σ₀ : Finset ℕ} (c : F)
    (hface : IsFace V σ₀) (hc : σ₀.card = j) : faceUnit F σ₀ c ∈ supported F V j := by
  intro σ hσ
  by_cases h : σ = σ₀
  · subst h
    rcases hσ with h1 | h1
    · exact absurd hc h1
    · exact absurd hface h1
  · exact faceUnit_of_ne h c

theorem emptyEval_empty_verts_bijective (F : Type*) [CommRing F] :
    Function.Bijective (emptyEval F (∅ : Finset ℕ)) := by
  constructor
  · intro f g hfg
    rw [emptyEval_apply, emptyEval_apply] at hfg
    refine Subtype.ext (funext fun σ => ?_)
    by_cases hσ : σ = ∅
    · subst hσ; exact hfg
    · have hc : σ.card ≠ 0 := fun h => hσ (Finset.card_eq_zero.mp h)
      rw [f.2.1 σ (Or.inl hc), g.2.1 σ (Or.inl hc)]
  · intro c
    refine ⟨⟨faceUnit F ∅ c, mem_cocycles_empty_verts
      (faceUnit_mem_supported c (isFace_empty _) Finset.card_empty)⟩, ?_⟩
    rw [emptyEval_apply]
    exact faceUnit_self ∅ c

/-- **The empty vertex set.** Its independence complex is the single empty face, with one class in
occupation zero. -/
def cohomologyEmptyEquiv (F : Type*) [CommRing F] :
    cohomology F (∅ : Finset ℕ) 0 ≃ₗ[F] F :=
  (Submodule.quotEquivOfEqBot _ (comap_coboundaries_occupation_zero (∅ : Finset ℕ))).trans
    (LinearEquiv.ofBijective (emptyEval F (∅ : Finset ℕ)) (emptyEval_empty_verts_bijective F))

/-! ### The block vertex sets -/

/-- `n` blocks of five consecutive vertices, separated by one deleted vertex, starting at `a`.
The induced subgraph of the path on this set is a disjoint union of `n` copies of `P_5`. -/
def joinVertsFrom (a n : ℕ) : Finset ℕ :=
  (Finset.range n).biUnion (fun i => (Finset.range 5).image (fun q => a + 6 * i + q))

theorem mem_joinVertsFrom {a n v : ℕ} :
    v ∈ joinVertsFrom a n ↔ ∃ i < n, ∃ q < 5, v = a + 6 * i + q := by
  simp only [joinVertsFrom, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, q, hq, rfl⟩
    exact ⟨i, hi, q, hq, rfl⟩
  · rintro ⟨i, hi, q, hq, rfl⟩
    exact ⟨i, hi, q, hq, rfl⟩

theorem joinVertsFrom_zero (a : ℕ) : joinVertsFrom a 0 = ∅ := by
  rw [joinVertsFrom, Finset.range_zero, Finset.biUnion_empty]

theorem joinVertsFrom_min {a n : ℕ} : ∀ v ∈ joinVertsFrom a n, a ≤ v := by
  intro v hv
  obtain ⟨i, -, q, -, rfl⟩ := mem_joinVertsFrom.mp hv
  omega

theorem mem_joinVertsFrom_of_lt_five {a n q : ℕ} (hn : 0 < n) (hq : q < 5) :
    a + q ∈ joinVertsFrom a n :=
  mem_joinVertsFrom.mpr ⟨0, hn, q, hq, by omega⟩

/-- The vertex set after one leaf reduction: the two remaining vertices of the first block,
followed by the other `n` blocks. -/
def midVertsFrom (a n : ℕ) : Finset ℕ :=
  insert (a + 3) (insert (a + 4) (joinVertsFrom (a + 6) n))

theorem mem_midVertsFrom {a n v : ℕ} :
    v ∈ midVertsFrom a n ↔ v = a + 3 ∨ v = a + 4 ∨ v ∈ joinVertsFrom (a + 6) n := by
  rw [midVertsFrom, Finset.mem_insert, Finset.mem_insert]

theorem midVertsFrom_min {a n : ℕ} : ∀ v ∈ midVertsFrom a n, a + 3 ≤ v := by
  intro v hv
  rcases mem_midVertsFrom.mp hv with rfl | rfl | hv
  · omega
  · omega
  · have := joinVertsFrom_min v hv; omega

theorem tailVerts_joinVertsFrom (a n : ℕ) :
    tailVerts (joinVertsFrom a (n + 1)) a = midVertsFrom a n := by
  ext v
  rw [mem_tailVerts, mem_joinVertsFrom, mem_midVertsFrom]
  constructor
  · rintro ⟨⟨i, hi, q, hq, rfl⟩, hge⟩
    match i with
    | 0 =>
      have hq3 : q = 3 ∨ q = 4 := by omega
      rcases hq3 with rfl | rfl
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
    | (k + 1) =>
      refine Or.inr (Or.inr (mem_joinVertsFrom.mpr ⟨k, by omega, q, hq, by omega⟩))
  · rintro (rfl | rfl | hv)
    · exact ⟨⟨0, by omega, 3, by omega, by omega⟩, by omega⟩
    · exact ⟨⟨0, by omega, 4, by omega, by omega⟩, by omega⟩
    · obtain ⟨i, hi, q, hq, rfl⟩ := mem_joinVertsFrom.mp hv
      exact ⟨⟨i + 1, by omega, q, hq, by omega⟩, by omega⟩

theorem tailVerts_midVertsFrom (a n : ℕ) :
    tailVerts (midVertsFrom a n) (a + 3) = joinVertsFrom (a + 6) n := by
  ext v
  rw [mem_tailVerts, mem_midVertsFrom]
  constructor
  · rintro ⟨rfl | rfl | hv, hge⟩
    · omega
    · omega
    · exact hv
  · intro hv
    have := joinVertsFrom_min v hv
    exact ⟨Or.inr (Or.inr hv), by omega⟩

theorem isLeaf_joinVertsFrom (a n : ℕ) : IsLeaf (joinVertsFrom a (n + 1)) a := by
  refine ⟨joinVertsFrom_min, ?_, ?_⟩
  · have h : a + 0 ∈ joinVertsFrom a (n + 1) :=
      mem_joinVertsFrom_of_lt_five (by omega) (by omega)
    simpa using h
  · exact mem_joinVertsFrom_of_lt_five (by omega) (by omega)

theorem isLeaf_midVertsFrom (a n : ℕ) : IsLeaf (midVertsFrom a n) (a + 3) := by
  refine ⟨midVertsFrom_min, ?_, ?_⟩
  · exact mem_midVertsFrom.mpr (Or.inl rfl)
  · exact mem_midVertsFrom.mpr (Or.inr (Or.inl (by omega)))

/-! ### Stripping one block lowers the occupation degree by two -/

/-- **One block costs two occupation degrees.** Two leaf reductions delete the first block of five
vertices, which is one join factor `Ind(P_5)`, and lower the occupation degree by two. -/
def joinCohomologyEquiv (F : Type*) [CommRing F] (a n j : ℕ) :
    cohomology F (joinVertsFrom a (n + 1)) (j + 2)
      ≃ₗ[F] cohomology F (joinVertsFrom (a + 6) n) j :=
  (cohomologyEquiv F (joinVertsFrom a (n + 1)) a (j + 1) (isLeaf_joinVertsFrom a n)).trans
    ((cohomologyCongr F (tailVerts_joinVertsFrom a n) (j + 1)).trans
      ((cohomologyEquiv F (midVertsFrom a n) (a + 3) j (isLeaf_midVertsFrom a n)).trans
        (cohomologyCongr F (tailVerts_midVertsFrom a n) j)))

/-- The reduction by one leaf only, used for occupation one. -/
def joinCohomologyEquivOne (F : Type*) [CommRing F] (a n j : ℕ) :
    cohomology F (joinVertsFrom a (n + 1)) (j + 1)
      ≃ₗ[F] cohomology F (midVertsFrom a n) j :=
  (cohomologyEquiv F (joinVertsFrom a (n + 1)) a j (isLeaf_joinVertsFrom a n)).trans
    (cohomologyCongr F (tailVerts_joinVertsFrom a n) j)

/-! ### The sphere classification -/

/-- **The `n`-fold join has one class, in occupation `2n`.** -/
theorem joinCohomology_nonempty_equiv (F : Type*) [CommRing F] (n : ℕ) :
    ∀ a : ℕ, Nonempty (cohomology F (joinVertsFrom a n) (2 * n) ≃ₗ[F] F) := by
  induction n with
  | zero =>
    intro a
    exact ⟨(cohomologyCongr F (joinVertsFrom_zero a) 0).trans (cohomologyEmptyEquiv F)⟩
  | succ m ih =>
    intro a
    obtain ⟨e⟩ := ih (a + 6)
    exact ⟨(cohomologyDegreeCongr F (joinVertsFrom a (m + 1))
        (show 2 * (m + 1) = 2 * m + 2 by omega)).trans
      ((joinCohomologyEquiv F a m (2 * m)).trans e)⟩

/-- **The `n`-fold join has no class in any other occupation.** -/
theorem joinCohomology_subsingleton (F : Type*) [CommRing F] (n : ℕ) :
    ∀ (a j : ℕ), j ≠ 2 * n → Subsingleton (cohomology F (joinVertsFrom a n) j) := by
  induction n with
  | zero =>
    intro a j hj
    haveI : Subsingleton (cohomology F (∅ : Finset ℕ) j) :=
      cohomology_empty_verts_subsingleton F (by omega)
    exact (cohomologyCongr F (joinVertsFrom_zero a) j).toEquiv.subsingleton
  | succ m ih =>
    intro a j hj
    match j with
    | 0 =>
      exact cohomology_occupation_zero_subsingleton F
        ⟨a, (isLeaf_joinVertsFrom a m).mem⟩
    | 1 =>
      haveI : Subsingleton (cohomology F (midVertsFrom a m) 0) :=
        cohomology_occupation_zero_subsingleton F
          ⟨a + 3, (isLeaf_midVertsFrom a m).mem⟩
      exact (joinCohomologyEquivOne F a m 0).toEquiv.subsingleton
    | (i + 2) =>
      haveI : Subsingleton (cohomology F (joinVertsFrom (a + 6) m) i) :=
        ih (a + 6) i (by omega)
      exact (joinCohomologyEquiv F a m i).toEquiv.subsingleton

/-- **The graded multiplicity of the `n`-fold join.** -/
theorem joinCohomology_finrank (F : Type*) [Field F] (a n j : ℕ) :
    Module.finrank F (cohomology F (joinVertsFrom a n) j) = if j = 2 * n then 1 else 0 := by
  by_cases h : j = 2 * n
  · subst h
    obtain ⟨e⟩ := joinCohomology_nonempty_equiv F n a
    rw [if_pos rfl, e.finrank_eq, Module.finrank_self]
  · haveI := joinCohomology_subsingleton F n a j h
    rw [if_neg h, Module.finrank_zero_of_subsingleton]

end
end VertexIndependence
end GaloisForLFunctions.HTGeometry

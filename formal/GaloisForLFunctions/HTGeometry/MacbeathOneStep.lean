import GaloisForLFunctions.HTGeometry.MacbeathDevelopingSpace
import GaloisForLFunctions.HTGeometry.SimplyConnectedCovering

/-!
# The gluing relation of the developing space is already an equivalence

The elementary gluing move of Macbeath's developing space generates an equivalence relation that is
still **one step**: two sheets are identified exactly when a single group element relates them.
Reflexivity is `s_1 = 1`, symmetry is `s_{γ⁻¹} = s_γ⁻¹`, and transitivity is precisely Macbeath's
defining relation `s_γ · s_δ = s_{γδ}` — whose triple-overlap hypothesis is supplied by the common
point of the two moves.

This gives an explicit description of the points of the developed space, which is what the covering
property is read off from.

* `DevOneStep` : the one-step relation.
* `devOneStep_equivalence` : **it is an equivalence relation.**
* `devSpace_mk_eq_iff` : **two sheets have the same class exactly when they are related in one
  step.**
-/

namespace GaloisForLFunctions.HTGeometry

open Set Pointwise

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- The one-step relation on sheets. -/
def DevOneStep (V : Set X) (p q : DevSheet (G := G) V) : Prop :=
  ∃ (γ : G) (hγ : γ ∈ meetSet (G := G) V),
    ((q.2 : X) = γ⁻¹ • (p.2 : X)) ∧ q.1 = p.1 * macbeathOf V ⟨γ, hγ⟩

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem devRel_le_devOneStep {V : Set X} {p q : DevSheet (G := G) V} (h : DevRel V p q) :
    DevOneStep V p q := by
  cases h with
  | move g γ x y hxy => exact ⟨(γ : G), γ.2, hxy, rfl⟩

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem devOneStep_refl {V : Set X} (hVne : V.Nonempty) (p : DevSheet (G := G) V) :
    DevOneStep V p p := by
  refine ⟨1, one_mem_meetSet hVne, by simp, ?_⟩
  rw [macbeathOf_one hVne, mul_one]

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem devOneStep_symm {V : Set X} (hVne : V.Nonempty) {p q : DevSheet (G := G) V}
    (h : DevOneStep V p q) : DevOneStep V q p := by
  obtain ⟨γ, hγ, hx, hg⟩ := h
  refine ⟨γ⁻¹, inv_mem_meetSet hγ, ?_, ?_⟩
  · rw [hx, inv_inv, smul_inv_smul]
  · rw [hg, mul_assoc, macbeathOf_inv hVne ⟨γ, hγ⟩]
    simp

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem devOneStep_trans {V : Set X} {p q r : DevSheet (G := G) V}
    (hpq : DevOneStep V p q) (hqr : DevOneStep V q r) : DevOneStep V p r := by
  obtain ⟨γ, hγ, hxq, hgq⟩ := hpq
  obtain ⟨δ, hδ, hxr, hgr⟩ := hqr
  have hxr' : (r.2 : X) = (γ * δ)⁻¹ • (p.2 : X) := by
    rw [hxr, hxq, mul_inv_rev, mul_smul]
  have hmem : (γ * δ) ∈ meetSet (G := G) V := by
    refine ⟨(p.2 : X), ?_, p.2.2⟩
    have : (γ * δ) • (r.2 : X) ∈ (γ * δ) • V := smul_mem_smul_set r.2.2
    rwa [hxr', smul_inv_smul] at this
  have hov : ((γ • V) ∩ ((γ * δ) • V) ∩ V).Nonempty := by
    refine ⟨(p.2 : X), ⟨?_, ?_⟩, p.2.2⟩
    · have : γ • (q.2 : X) ∈ γ • V := smul_mem_smul_set q.2.2
      rwa [hxq, smul_inv_smul] at this
    · have : (γ * δ) • (r.2 : X) ∈ (γ * δ) • V := smul_mem_smul_set r.2.2
      rwa [hxr', smul_inv_smul] at this
  refine ⟨γ * δ, hmem, hxr', ?_⟩
  rw [hgr, hgq, mul_assoc, macbeathOf_mul V ⟨γ, hγ⟩ ⟨δ, hδ⟩ ⟨γ * δ, hmem⟩ rfl hov]

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- **The one-step relation is an equivalence relation.** -/
theorem devOneStep_equivalence {V : Set X} (hVne : V.Nonempty) :
    Equivalence (DevOneStep (G := G) V) :=
  ⟨devOneStep_refl hVne, devOneStep_symm hVne, devOneStep_trans⟩

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- **Two sheets have the same class exactly when they are related in one step.** -/
theorem devSpace_mk_eq_iff {V : Set X} (hVne : V.Nonempty) (p q : DevSheet (G := G) V) :
    (Quot.mk (DevRel (G := G) V) p = Quot.mk _ q) ↔ DevOneStep V p q := by
  constructor
  · intro h
    have hgen : Relation.EqvGen (DevRel (G := G) V) p q := Quot.eq.1 h
    clear h
    induction hgen with
    | rel a b hab => exact devRel_le_devOneStep hab
    | refl a => exact devOneStep_refl hVne a
    | symm a b _ ih => exact devOneStep_symm hVne ih
    | trans a b c _ _ ih₁ ih₂ => exact devOneStep_trans ih₁ ih₂
  · rintro ⟨γ, hγ, hx, hg⟩
    refine Quot.sound ?_
    have hmove := DevRel.move (V := V) p.1 ⟨γ, hγ⟩ p.2 q.2 hx
    have hq : q = ⟨p.1 * macbeathOf V ⟨γ, hγ⟩, q.2⟩ := by
      refine Sigma.ext hg ?_
      simp
    rw [hq]
    exact hmove

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- **Injectivity of the developing map forces injectivity of `macbeathHom`.**  If `g` is killed by
`macbeathHom` then its sheet over a point of `V` is glued to the sheet at the identity, so
`g = s_γ⁻¹` with `γ⁻¹ = macbeathHom g = 1`, whence `g = s_1 = 1`. -/
theorem macbeathHom_injective_of_devMap_injective {V : Set X} (hVne : V.Nonempty)
    (hinj : Function.Injective (devMap (G := G) V)) :
    Function.Injective (macbeathHom (G := G) V) := by
  refine (injective_iff_map_eq_one _).2 ?_
  intro g hg
  obtain ⟨x, hx⟩ := hVne
  have h1 : devMap V (Quot.mk _ (⟨g, ⟨x, hx⟩⟩ : DevSheet (G := G) V))
      = devMap V (Quot.mk _ (⟨1, ⟨x, hx⟩⟩ : DevSheet (G := G) V)) := by
    rw [devMap_mk, devMap_mk, hg, map_one, one_smul]
  have h2 := hinj h1
  rw [devSpace_mk_eq_iff ⟨x, hx⟩] at h2
  obtain ⟨γ, hγ, -, hgg⟩ := h2
  have hginv : g = (macbeathOf V ⟨γ, hγ⟩)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    exact hgg.symm
  have hφ : macbeathHom V g = γ⁻¹ := by
    rw [hginv, map_inv, macbeathHom_of]
  rw [hg] at hφ
  have hγ1 : γ = 1 := by
    have hinv1 : γ⁻¹ = 1 := hφ.symm
    simpa using hinv1
  subst hγ1
  rw [hginv, show (⟨(1 : G), hγ⟩ : meetSet (G := G) V)
      = ⟨(1 : G), one_mem_meetSet ⟨x, hx⟩⟩ from rfl,
    macbeathOf_one ⟨x, hx⟩, inv_one]

omit [ContinuousConstSMul G X] in
/-- **Macbeath's theorem, modulo the covering property.**  If the developing map is a covering map
and the developed space is connected, simple connectivity of `X` makes `macbeathHom` injective. -/
theorem macbeathHom_injective_of_isCoveringMap [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] {V : Set X} (hVne : V.Nonempty)
    [PreconnectedSpace (DevSpace (G := G) V)]
    (hcov : IsCoveringMap (devMap (G := G) V)) (y₀ : DevSpace (G := G) V) :
    Function.Injective (macbeathHom (G := G) V) :=
  macbeathHom_injective_of_devMap_injective hVne
    (isCoveringMap_injective_of_simplyConnected hcov y₀)

end GaloisForLFunctions.HTGeometry

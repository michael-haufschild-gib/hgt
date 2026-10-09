import GaloisForLFunctions.RHTower.XiMarkedFiniteMonodromy
import GaloisForLFunctions.RHTower.XiMarkedImageCover

/-!
# Finite-cover monodromy of one exponentially tilted Xi source

Let `d_a(s) = ξ(s) e^{-as}`, `V = ℂ ∖ {0, -1}` and `U_a = d_a⁻¹(V)`.  The monodromy of
`d_a : U_a → V` reaches every finite quotient of `π₁(V)`: for every homomorphism `f` from `π₁(V)` to
a finite group, `f(d_a(π₁(U_a))) = f(π₁(V))`.  Equivalently the image is dense for the profinite
topology: it meets every coset of every normal subgroup of finite index.

Consequently, for every connected covering `Y → V` with finite fibres, the pullback
`U_a ×_V Y = {(s, y) : d_a(s) = p(y)}` is path connected.  Indeed `Y` is path connected, so `π₁(V)`
permutes the fibre transitively; this action factors through a finite permutation group, which
the source monodromy already exhausts, and lifting source loops joins every two points of the
pullback.
-/

open Topology

namespace RHTower.XiMarkedMonodromy

noncomputable section

/-- The slope `a` as an element of the one-point mark set. -/
def singleSlope (a : ℝ) : ({a} : Finset ℝ) := ⟨a, Finset.mem_singleton_self a⟩

/-- `d_a : U_a → ℂ ∖ {0, -1}`. -/
abbrev tilt (a : ℝ) : C(Source {a}, Target) := coordinate {a} (singleSlope a)

/-- The monodromy homomorphism `π₁(U_a, 0) → π₁(V, 1/2)` of `d_a`. -/
def singleMap (a : ℝ) : FundamentalGroup (Source {a}) (sourceZero {a}) →* TargetGroup :=
  FundamentalGroup.mapOfEq (tilt a) (coordinate_sourceZero {a} _)

theorem singleMap_eq_comp (a : ℝ) :
    singleMap a = (Pi.evalMonoidHom (fun _ : ({a} : Finset ℝ) => TargetGroup) (singleSlope a)).comp
      (jointMap {a}) := rfl

theorem diagonalWindingSubgroup_singleton (a : ℝ) : diagonalWindingSubgroup {a} = ⊤ := by
  ext q
  simp only [Subgroup.mem_top, iff_true]
  refine ⟨zeroWinding (q (singleSlope a)), fun b => ?_⟩
  have hb : b = singleSlope a := Subtype.ext (Finset.mem_singleton.mp b.2)
  rw [hb]

/-- **Every finite quotient receives the full monodromy image.** -/
theorem finite_image_singleMap (a : ℝ) {G : Type*} [Group G] [Finite G] (f : TargetGroup →* G) :
    (singleMap a).range.map f = f.range := by
  set e := Pi.evalMonoidHom (fun _ : ({a} : Finset ℝ) => TargetGroup) (singleSlope a)
  have h := finite_image_jointMap_eq_diagonal {a} (f.comp e)
  rw [diagonalWindingSubgroup_singleton] at h
  have he : (⊤ : Subgroup (JointGroup {a})).map e = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr fun x => ⟨fun _ => x, rfl⟩
  calc (singleMap a).range.map f = ((jointMap {a}).range.map e).map f := by
        rw [singleMap_eq_comp, MonoidHom.range_comp]
    _ = (jointMap {a}).range.map (f.comp e) := Subgroup.map_map _ _ _
    _ = (⊤ : Subgroup (JointGroup {a})).map (f.comp e) := h
    _ = ((⊤ : Subgroup (JointGroup {a})).map e).map f := (Subgroup.map_map _ _ _).symm
    _ = f.range := by rw [he, MonoidHom.range_eq_map]

/-- **Profinite density.**  The monodromy image meets every coset of every normal subgroup of
finite index. -/
theorem singleMap_range_sup_eq_top (a : ℝ) (N : Subgroup TargetGroup) [N.Normal]
    [N.FiniteIndex] : (singleMap a).range ⊔ N = ⊤ := by
  have hfin := finite_image_singleMap a (QuotientGroup.mk' N)
  rw [QuotientGroup.range_mk'] at hfin
  rw [eq_top_iff]
  intro g _
  have hg : (QuotientGroup.mk' N g) ∈ (singleMap a).range.map (QuotientGroup.mk' N) := by
    rw [hfin]; exact Subgroup.mem_top _
  obtain ⟨x, hx, hxg⟩ := hg
  have hn : x⁻¹ * g ∈ N := by
    rw [← QuotientGroup.eq]
    exact hxg
  have : g = x * (x⁻¹ * g) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hx hn

/-! ## Connected pullbacks of finite coverings -/

/-- A covering space of a locally path-connected space is locally path connected. -/
theorem locallyPathConnectedSpace_of_isCoveringMap {Z X : Type*} [TopologicalSpace Z]
    [TopologicalSpace X] [LocallyPathConnectedSpace X] {q : Z → X} (hq : IsCoveringMap q) :
    LocallyPathConnectedSpace Z := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro z u hu hzu
  obtain ⟨e, hze, hqe⟩ := hq.isLocalHomeomorph z
  set W := u ∩ e.source
  have hW : IsOpen W := hu.inter e.open_source
  have hWs : W ⊆ e.source := Set.inter_subset_right
  have hzW : z ∈ W := ⟨hzu, hze⟩
  have hEW : IsOpen (e '' W) := e.isOpen_image_of_subset_source hW hWs
  have hN : pathComponentIn (e '' W) (e z) ∈ 𝓝 (e z) :=
    (hEW.pathComponentIn (e z)).mem_nhds (mem_pathComponentIn_self ⟨z, hzW, rfl⟩)
  have hM : e.source ∩ e ⁻¹' pathComponentIn (e '' W) (e z) ∈ 𝓝 z :=
    Filter.inter_mem (e.open_source.mem_nhds hze) (e.continuousAt hze hN)
  refine Filter.mem_of_superset hM ?_
  rintro m ⟨hms, hmN⟩
  have hJ : JoinedIn (e '' W) (e z) (e m) := hmN
  have hcont : ContinuousOn e.symm (e '' W) :=
    e.continuousOn_symm.mono (by rintro _ ⟨w, hw, rfl⟩; exact e.map_source (hWs hw))
  have hJ' := hJ.map_continuousOn hcont
  have himg : e.symm '' (e '' W) = W := by
    ext w
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      rwa [e.left_inv (hWs hv)]
    · intro hw
      exact ⟨e w, ⟨w, hw, rfl⟩, e.left_inv (hWs hw)⟩
  rw [himg, e.left_inv hze, e.left_inv hms] at hJ'
  exact hJ'.mono Set.inter_subset_left

instance target_pathConnectedSpace : PathConnectedSpace Target := by
  have hc : ({0, -1} : Set ℂ).Countable := (Set.countable_singleton _).insert _
  have hp := hc.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)
  have he : ({0, -1} : Set ℂ)ᶜ = {z : ℂ | z ≠ 0 ∧ z ≠ -1} := by
    ext z; simp [not_or]
  rw [he] at hp
  exact isPathConnected_iff_pathConnectedSpace.mp hp

variable {Y : Type*} [TopologicalSpace Y] {p : Y → Target}

/-- The pullback `U_a ×_V Y` of a covering `p : Y → V` along `d_a`. -/
def tiltPullback (a : ℝ) (p : Y → Target) : Set (Source {a} × Y) := {q | tilt a q.1 = p q.2}

private theorem joined_to_base (a : ℝ) (hp : IsCoveringMap p) {q : Source {a} × Y}
    (hq : q ∈ tiltPullback a p) :
    ∃ e : p ⁻¹' {targetHalf}, JoinedIn (tiltPullback a p) q (sourceZero {a}, e.1) := by
  obtain ⟨u, y⟩ := q
  set σ := PathConnectedSpace.somePath u (sourceZero {a})
  set γ := σ.map (tilt a).continuous
  have h0 : γ 0 = p y := γ.source.trans hq
  set Γ := hp.liftPath γ.toContinuousMap y h0
  have hΓ : ∀ t, p (Γ t) = tilt a (σ t) := fun t => by
    have := congrFun (hp.liftPath_lifts γ.toContinuousMap y h0) t
    simpa [γ] using this
  have hfib : Γ 1 ∈ p ⁻¹' {targetHalf} := by
    change p (Γ 1) = targetHalf
    rw [hΓ 1, Path.target, coordinate_sourceZero]
  have hΓ0 : Γ 0 = y := hp.liftPath_zero ..
  refine ⟨⟨Γ 1, hfib⟩, ?_⟩
  refine ⟨⟨⟨fun t => (σ t, Γ t), σ.continuous.prodMk Γ.continuous⟩, ?_, ?_⟩, fun t => ?_⟩
  · simp [hΓ0]
  · simp
  · exact (hΓ t).symm

private theorem joined_in_fiber (a : ℝ) (hp : IsCoveringMap p) [PathConnectedSpace Y]
    [Finite (p ⁻¹' {targetHalf})] (e e' : p ⁻¹' {targetHalf}) :
    JoinedIn (tiltPullback a p) (sourceZero {a}, e.1) (sourceZero {a}, e'.1) := by
  have he : p e.1 = targetHalf := e.2
  have he' : p e'.1 = targetHalf := e'.2
  set ρ := PathConnectedSpace.somePath e.1 e'.1
  set g : TargetGroup := FundamentalGroup.fromPath
    (((Path.Homotopic.Quotient.mk ρ).map ⟨p, hp.continuous⟩).cast he.symm he'.symm)
  have hg : hp.monodromy g e = e' := by
    apply hp.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk ρ)
    simp [g]
  set f := hp.monodromyPerm targetHalf
  have hmem : f g ∈ (singleMap a).range.map f := by
    rw [finite_image_singleMap]; exact ⟨g, rfl⟩
  obtain ⟨_, ⟨β, rfl⟩, hβ⟩ := hmem
  obtain ⟨b, rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath β)
  have hmono : hp.monodromy (singleMap a ⟦b⟧) e = e' := by
    have := congrArg (fun π : Equiv.Perm (p ⁻¹' {targetHalf}) => π e) hβ
    simpa [f, hg] using this
  set γ : Path targetHalf targetHalf := (b.map (tilt a).continuous).cast
    (coordinate_sourceZero {a} _).symm (coordinate_sourceZero {a} _).symm
  have hsingle : singleMap a ⟦b⟧ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) := by
    rw [singleMap, FundamentalGroup.mapOfEq_apply]
    rfl
  have h0 : γ.toContinuousMap 0 = p e.1 := by rw [he]; exact γ.source
  set Γ := hp.liftPath γ.toContinuousMap e.1 h0
  have hΓ : ∀ t, p (Γ t) = tilt a (b t) := fun t => by
    have := congrFun (hp.liftPath_lifts γ.toContinuousMap e.1 h0) t
    simpa [γ] using this
  have hend : Γ 1 = e'.1 := by
    have := congrArg Subtype.val hmono
    rw [hsingle] at this
    exact this
  have hΓ0 : Γ 0 = e.1 := hp.liftPath_zero ..
  refine ⟨⟨⟨fun t => (b t, Γ t), b.continuous.prodMk Γ.continuous⟩, ?_, ?_⟩, fun t => ?_⟩
  · simp [hΓ0]
  · simp [hend]
  · exact (hΓ t).symm

/-- **Connected pullbacks.**  For every connected covering `Y → ℂ ∖ {0, -1}` with finite fibres,
the pullback along `d_a` is path connected. -/
theorem tiltPullback_isPathConnected (a : ℝ) (hp : IsCoveringMap p) [ConnectedSpace Y]
    [Finite (p ⁻¹' {targetHalf})] : IsPathConnected (tiltPullback a p) := by
  haveI := locallyPathConnectedSpace_of_isCoveringMap hp
  haveI : PathConnectedSpace Y := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  -- a point of the fibre over `1/2`
  set τ := PathConnectedSpace.somePath (p y) targetHalf
  set Γ := hp.liftPath τ.toContinuousMap y τ.source
  have hfib : Γ 1 ∈ p ⁻¹' {targetHalf} := by
    change p (Γ 1) = targetHalf
    have := congrFun (hp.liftPath_lifts τ.toContinuousMap y τ.source) 1
    simpa using this
  set e₀ : p ⁻¹' {targetHalf} := ⟨Γ 1, hfib⟩
  have hbase : (sourceZero {a}, e₀.1) ∈ tiltPullback a p := by
    change tilt a (sourceZero {a}) = p e₀.1
    rw [coordinate_sourceZero]; exact e₀.2.symm
  refine ⟨(sourceZero {a}, e₀.1), hbase, fun {q} hq => ?_⟩
  obtain ⟨e, hqe⟩ := joined_to_base a hp hq
  exact (joined_in_fiber a hp e₀ e).trans hqe.symm

theorem tiltPullback_isConnected (a : ℝ) (hp : IsCoveringMap p) [ConnectedSpace Y]
    [Finite (p ⁻¹' {targetHalf})] : IsConnected (tiltPullback a p) :=
  (tiltPullback_isPathConnected a hp).isConnected

end

end RHTower.XiMarkedMonodromy

import GaloisForLFunctions.HTGeometry.FinsetCechDatum
import GaloisForLFunctions.RHTower.Deninger.DeningerFineSurjective

/-!
# The alternating Čech complex of a sheaf on a finite cover

For a sheaf `F` of abelian groups on `X`, an open set `V` and a finite family of opens
`U : T → Opens X`, the Čech datum assigns to a finite subset `s` the sections of `F` over
`V ∩ ⋂_{i ∈ s} U_i` (so the empty subset carries the sections over `V`).

The sheaf of arbitrary sections of the stalks (the Godement sheaf) has an exact augmented Čech
complex as soon as the family covers `V`: at a point `x`, pick an index `k(x)` whose member
contains `x`; the cone operator of `k(x)` applied to the germs at `x` is a contracting homotopy,
and its pointwise values assemble into arbitrary sections of the stalks, which is all the Godement
sheaf asks for.

* `HTGeometry.coverInter` : `V ∩ ⋂_{i ∈ s} U_i`.
* `HTGeometry.sheafCech` : the Čech datum of a sheaf.
* `HTGeometry.godementCech_exactAt`, `HTGeometry.godementCech_exactBot` : the Godement sheaf is
  Čech-exact.
* `HTGeometry.sheafCech_exactBot` : a sheaf is separated over a cover.
-/

namespace HTGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat RHTower
open GaloisForLFunctions.HTGeometry.BorelWeil

universe u

variable {X : TopCat.{u}} {T : Type*} [DecidableEq T] [LinearOrder T]

/-- The intersection of an open set with the members of a family indexed by a finite subset. -/
def coverInter (V : Opens X) (U : T → Opens X) (s : Finset T) : Opens X := V ⊓ s.inf U

omit [DecidableEq T] [LinearOrder T] in
theorem coverInter_anti {V : Opens X} {U : T → Opens X} {s t : Finset T} (h : s ⊆ t) :
    coverInter V U t ≤ coverInter V U s :=
  inf_le_inf_left V (Finset.inf_mono h)

omit [LinearOrder T] in
theorem mem_finsetInf_opens {U : T → Opens X} {s : Finset T} {x : X} :
    x ∈ s.inf U ↔ ∀ i ∈ s, x ∈ U i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    rw [Finset.inf_insert, Opens.mem_inf, ih, Finset.forall_mem_insert]

omit [LinearOrder T] in
theorem mem_coverInter {V : Opens X} {U : T → Opens X} {s : Finset T} {x : X} :
    x ∈ coverInter V U s ↔ x ∈ V ∧ ∀ i ∈ s, x ∈ U i := by
  rw [coverInter, Opens.mem_inf, mem_finsetInf_opens]

omit [DecidableEq T] [LinearOrder T] in
theorem coverInter_empty (V : Opens X) (U : T → Opens X) : coverInter V U ∅ = V := by
  simp [coverInter]

omit [DecidableEq T] [LinearOrder T] in
theorem coverInter_singleton (V : Opens X) (U : T → Opens X) (i : T) :
    coverInter V U {i} = V ⊓ U i := by
  simp [coverInter]

/-- **The Čech datum of a sheaf** on a finite family of opens relative to an open set. -/
noncomputable def sheafCech (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X)
    (U : T → Opens X) : FinsetCechDatum.{u} T where
  obj s := ToType (F.1.obj (op (coverInter V U s)))
  res h := ConcreteCategory.hom (F.1.map (homOfLE (coverInter_anti h)).op)
  res_refl _ x := deningerRes_self _ x
  res_res _ _ x := deningerRes_res _ _ x

/-- A morphism of sheaves induces a morphism of Čech data. -/
noncomputable def sheafCechMap {F F' : TopCat.Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ F')
    (V : Opens X) (U : T → Opens X) : (sheafCech F V U).Hom (sheafCech F' V U) where
  app s := ConcreteCategory.hom (φ.1.app (op (coverInter V U s)))
  comm h x := deningerRes_app φ (coverInter_anti h) x

/-! ## Separation over a cover -/

/-- **A sheaf is separated over a cover**: the augmented Čech complex is exact in degree `-1`. -/
theorem sheafCech_exactBot (F : TopCat.Sheaf AddCommGrpCat.{u} X) {V : Opens X}
    {U : T → Opens X} (hcov : V ≤ ⨆ i, U i) : (sheafCech F V U).ExactBot := by
  intro c hc hdc
  funext s
  by_cases hs : s.Nonempty
  · exact hc s hs
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    subst hs
    -- every restriction of `c ∅` to a member of the cover vanishes
    have hloc : ∀ i : T, deningerRes F (coverInter_anti (Finset.empty_subset {i})) (c ∅) = 0 := by
      intro i
      have h := congrFun hdc {i}
      simp only [FinsetCechDatum.d, Finset.sum_singleton, Pi.zero_apply] at h
      rw [FinsetCechDatum.res_cochain_congr c (Finset.erase_singleton i) _
        (Finset.empty_subset _)] at h
      have hsign : (cechSign ({i} : Finset T) i : ℤ) = 1 := by
        simp [cechSign, belowCard, Finset.filter_singleton]
      rw [hsign, one_smul] at h
      exact h
    let W : T → Opens X := fun i => coverInter V U {i}
    have hcovW : coverInter V U ∅ ≤ iSup W := by
      intro x hx
      have hxV : x ∈ V := (mem_coverInter.mp hx).1
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov hxV)
      exact Opens.mem_iSup.mpr ⟨i, mem_coverInter.mpr ⟨hxV, fun j hj => by
        rw [Finset.mem_singleton.mp hj]; exact hi⟩⟩
    refine TopCat.Sheaf.eq_of_locally_eq' F W (coverInter V U ∅)
      (fun i => homOfLE (coverInter_anti (Finset.empty_subset {i}))) hcovW (c ∅) 0 fun i => ?_
    rw [map_zero]
    exact hloc i

/-! ## The Godement sheaf is Čech-exact -/

section Godement

variable (F : TopCat.Sheaf AddCommGrpCat.{u} X) {V : Opens X} {U : T → Opens X}

open scoped Classical in
/-- The germs at `x` of a cochain of the Godement sheaf, on the subsets whose intersection
contains `x`. -/
noncomputable def godementGerms (c : (sheafCech (deningerGodementSheaf F) V U).Cochain) (x : X) :
    Finset T → ToType (F.presheaf.stalk x) := fun s =>
  if h : x ∈ coverInter V U s then (c s : ∀ y : (coverInter V U s : Opens X),
    ToType (F.presheaf.stalk y.1)) ⟨x, h⟩ else 0

omit [DecidableEq T] [LinearOrder T] in
open scoped Classical in
theorem godementGerms_of_mem (c : (sheafCech (deningerGodementSheaf F) V U).Cochain) {x : X}
    {s : Finset T} (h : x ∈ coverInter V U s) :
    godementGerms F c x s = (c s : ∀ y : (coverInter V U s : Opens X),
      ToType (F.presheaf.stalk y.1)) ⟨x, h⟩ := dif_pos h

/-- The differential of a Godement cochain, evaluated at a point, is the constant-coefficient
differential of its germs. -/
theorem godement_d_apply (c : (sheafCech (deningerGodementSheaf F) V U).Cochain) {s : Finset T}
    {x : X} (hx : x ∈ coverInter V U s) :
    ((sheafCech (deningerGodementSheaf F) V U).d c s : ∀ y : (coverInter V U s : Opens X),
      ToType (F.presheaf.stalk y.1)) ⟨x, hx⟩ = cechDModule ℤ (godementGerms F c x) s := by
  rw [FinsetCechDatum.d, cechDModule]
  change (∑ u ∈ s, (cechSign s u : ℤ) • _ : ∀ y : (coverInter V U s : Opens X),
      ToType (F.presheaf.stalk y.1)) ⟨x, hx⟩ = _
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Pi.smul_apply, godementGerms_of_mem F c (coverInter_anti (Finset.erase_subset u s) hx)]
  rfl

variable {F}

/-- A choice of member of the cover through each point of `V`. -/
noncomputable def coverIndex (hcov : V ≤ ⨆ i, U i) {x : X} (hx : x ∈ V) : T :=
  Classical.choose (Opens.mem_iSup.mp (hcov hx))

omit [DecidableEq T] [LinearOrder T] in
theorem mem_coverIndex (hcov : V ≤ ⨆ i, U i) {x : X} (hx : x ∈ V) :
    x ∈ U (coverIndex hcov hx) :=
  Classical.choose_spec (Opens.mem_iSup.mp (hcov hx))

/-- **The pointwise contracting homotopy of the Godement sheaf.** -/
noncomputable def godementHomotopy (hcov : V ≤ ⨆ i, U i)
    (c : (sheafCech (deningerGodementSheaf F) V U).Cochain) :
    (sheafCech (deningerGodementSheaf F) V U).Cochain := fun t =>
  (fun y : (coverInter V U t : Opens X) =>
    cechHModule ℤ (coverIndex hcov (mem_coverInter.mp y.2).1) (godementGerms F c y.1) t :
    ∀ y : (coverInter V U t : Opens X), ToType (F.presheaf.stalk y.1))

/-- **A cocycle of the Godement sheaf is the differential of its homotopy.** -/
theorem godement_d_homotopy (hcov : V ≤ ⨆ i, U i)
    (c : (sheafCech (deningerGodementSheaf F) V U).Cochain)
    (hdc : (sheafCech (deningerGodementSheaf F) V U).d c = 0) :
    (sheafCech (deningerGodementSheaf F) V U).d (godementHomotopy hcov c) = c := by
  funext s
  refine funext fun y => ?_
  obtain ⟨x, hx⟩ := y
  have hxV : x ∈ V := (mem_coverInter.mp hx).1
  set k := coverIndex hcov hxV with hk
  rw [godement_d_apply]
  -- the germs of the homotopy agree with the cone operator on the subsets of `s`
  have hgerm : cechDModule ℤ (godementGerms F (godementHomotopy hcov c) x) s
      = cechDModule ℤ (cechHModule ℤ k (godementGerms F c x)) s := by
    rw [cechDModule, cechDModule]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [godementGerms_of_mem F _ (coverInter_anti (Finset.erase_subset u s) hx)]
    rfl
  rw [hgerm]
  have hid := cechDModule_cechHModule_add ℤ k (godementGerms F c x) s
  have hzero : cechHModule ℤ k (cechDModule ℤ (godementGerms F c x)) s = 0 := by
    rw [cechHModule]
    split_ifs with hks
    · rfl
    · have hxk : x ∈ coverInter V U (insert k s) :=
        mem_coverInter.mpr ⟨hxV, fun i hi => by
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact mem_coverIndex hcov hxV
          · exact (mem_coverInter.mp hx).2 i hi⟩
      rw [← godement_d_apply F c hxk, hdc]
      change _ • (0 : ToType (F.presheaf.stalk x)) = 0
      exact smul_zero _
  rw [hzero, add_zero] at hid
  rw [hid, godementGerms_of_mem F c hx]

/-- **The Godement sheaf is Čech-exact in every degree.** -/
theorem godementCech_exactAt (hcov : V ≤ ⨆ i, U i) (p : ℕ) :
    (sheafCech (deningerGodementSheaf F) V U).ExactAt p := by
  intro c hc hdc
  refine ⟨godementHomotopy hcov c, fun t ht => ?_, godement_d_homotopy hcov c hdc⟩
  refine funext fun y => ?_
  refine cechHModule_eq_zero_of_card ℤ (p := p + 1) (fun I hI => ?_) t (by omega)
  rw [godementGerms]
  split_ifs
  · rw [hc I hI]
    rfl
  · rfl

/-- **The Godement sheaf is Čech-exact in degree `-1`.** -/
theorem godementCech_exactBot (hcov : V ≤ ⨆ i, U i) :
    (sheafCech (deningerGodementSheaf F) V U).ExactBot := by
  intro c hc hdc
  rw [← godement_d_homotopy hcov c hdc]
  have hH : godementHomotopy hcov c = 0 := by
    funext t
    refine funext fun y => ?_
    refine cechHModule_eq_zero_of_card ℤ (p := 0) (fun I hI => ?_) t (by omega)
    rw [godementGerms]
    split_ifs
    · rw [hc I (Finset.card_pos.mp (Nat.pos_of_ne_zero hI))]
      rfl
    · rfl
  rw [hH, FinsetCechDatum.d_zero]

end Godement

end HTGeometry

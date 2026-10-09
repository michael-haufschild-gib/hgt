import GaloisForLFunctions.HTGeometry.SheafFinsetCech

/-!
# Leray's theorem and Cartan's criterion for finite covers

Sheaf cohomology here is the corpus `Ext` cohomology `H^q(W, F) = Ext^q(ℤ_W, F)` of sheaves of
abelian groups.

**Leray.**  Let `U` be a finite family of opens covering `V`.  If a sheaf `F` has no higher
cohomology on any of the intersections `V ∩ U_s` (`s ≠ ∅`) and its augmented Čech complex is exact
in all positive degrees, then `H^q(V, F) = 0` for every `q > 0`.

**Cartan.**  Let `B` be a family of quasi-compact opens, closed under finite intersections, which is
a basis of the topology inside each of its members.  If for every member `W` and every finite cover
of `W` by members the augmented Čech complex of `F` is exact in all positive degrees, then
`H^q(W, F) = 0` for every member `W` and every `q > 0`.

Both proofs embed `F` into the flasque sheaf `G` of arbitrary sections of its stalks with quotient
`Q`.  The Čech complex of `G` is contractible (`godementCech_exactAt`); the snake chase
(`FinsetCechDatum.chase_lift`) transfers Čech exactness to `Q` and lifts sections of `Q` over the
covered set; that lift kills `H¹(F)`, and dimension shifting along `0 → F → G → Q → 0` reduces
`H^{q+2}(F)` to `H^{q+1}(Q)`.  For Cartan's criterion the sections of `Q` over a member only lift
locally; quasi-compactness turns the local lifts into a finite cover by members.

* `HTGeometry.LerayCover`, `HTGeometry.leray_vanishing`.
* `HTGeometry.CartanBasis`, `HTGeometry.CartanExact`, `HTGeometry.cartan_vanishing`.
-/

namespace HTGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat
  RHTower

universe w u

variable {X : TopCat.{u}}

/-! ## Short exact sequences on sections -/

section ShortExact

variable {T : Type*}
  {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (V : Opens X) (U : T → Opens X)

theorem sheafCech_comp_zero (s : Finset T) (x : (sheafCech S.X₁ V U).obj s) :
    (sheafCechMap S.g V U).app s ((sheafCechMap S.f V U).app s x) = 0 := by
  change ConcreteCategory.hom (S.g.1.app _) (ConcreteCategory.hom (S.f.1.app _) x) = 0
  rw [← ConcreteCategory.comp_apply,
    show S.f.1.app (op (coverInter V U s)) ≫ S.g.1.app (op (coverInter V U s))
      = (S.f ≫ S.g).1.app (op (coverInter V U s)) from rfl, S.zero]
  rfl

variable {V U}

theorem sheafCech_exact (hS : S.ShortExact) (s : Finset T) (y : (sheafCech S.X₂ V U).obj s)
    (hy : (sheafCechMap S.g V U).app s y = 0) :
    ∃ x, (sheafCechMap S.f V U).app s x = y :=
  deningerSections_exact hS _ y hy

theorem sheafCech_injective (hS : S.ShortExact) (s : Finset T) :
    Function.Injective ((sheafCechMap S.f V U).app s) := fun _ _ h => by
  haveI := hS.mono_f
  exact deningerSections_injective S.f _ h

end ShortExact

variable [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- The Godement sheaf has no higher cohomology on any open set. -/
theorem godement_acyclicOn (F : TopCat.Sheaf AddCommGrpCat.{u} X) (W : Opens X) :
    DeningerAcyclicOn.{w} (deningerGodementSheaf F) W :=
  fun n x => deningerFlasque_ext_eq_zero n _ (deningerGodementSheaf_isFlasque F) W x

/-- **The quotient by the Godement embedding inherits acyclicity**: `H^n(W, Q) = H^{n+1}(W, F)`. -/
theorem godementQuotient_acyclicOn {F : TopCat.Sheaf AddCommGrpCat.{u} X} {W : Opens X}
    (hF : DeningerAcyclicOn.{w} F W) :
    DeningerAcyclicOn.{w} (deningerGodementComplex F).X₃ W := by
  intro n y
  have hS := deningerGodementShortExact F
  obtain ⟨y₂, hy₂⟩ := Ext.covariant_sequence_exact₃ (deningerOpenFree W) hS y rfl (hF (n + 1) _)
  rw [← hy₂, godement_acyclicOn F W n y₂]
  apply Ext.zero_comp

/-! ## Leray's theorem -/

section Leray

variable {T : Type*} [DecidableEq T] [LinearOrder T]

/-- **The hypotheses of Leray's theorem**: no higher cohomology on the intersections of the cover,
and an augmented Čech complex exact in every positive degree. -/
structure LerayCover (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) (U : T → Opens X) :
    Prop where
  acyclic : ∀ s : Finset T, s.Nonempty → DeningerAcyclicOn.{w} F (coverInter V U s)
  exact : ∀ p : ℕ, (sheafCech F V U).ExactAt (p + 1)

variable {V : Opens X} {U : T → Opens X}

/-- Sections of the Godement quotient over the intersections of the cover lift. -/
theorem LerayCover.surjective {F : TopCat.Sheaf AddCommGrpCat.{u} X} (hF : LerayCover.{w} F V U)
    {s : Finset T} (hs : s.Nonempty) :
    Function.Surjective
      ((sheafCechMap (deningerGodementComplex F).g V U).app s) :=
  deningerSections_surjective_of_acyclic (deningerGodementShortExact F) _ (hF.acyclic s hs)

/-- **Leray's hypotheses pass to the Godement quotient.** -/
theorem LerayCover.godementQuotient (hcov : V ≤ ⨆ i, U i) {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hF : LerayCover.{w} F V U) : LerayCover.{w} (deningerGodementComplex F).X₃ V U where
  acyclic s hs := godementQuotient_acyclicOn (hF.acyclic s hs)
  exact p := FinsetCechDatum.exactAt_of_chase (sheafCechMap (deningerGodementComplex F).f V U)
    (sheafCechMap (deningerGodementComplex F).g V U) (p + 1)
    (fun s _ x => sheafCech_comp_zero V U s x)
    (fun s hs => hF.surjective (Finset.card_pos.mp (by omega)))
    (fun s _ y hy => sheafCech_exact (deningerGodementShortExact F) s y hy)
    (fun s _ => sheafCech_injective (deningerGodementShortExact F) s)
    (hF.exact (p + 1)) (godementCech_exactAt hcov (p + 1))

/-- **Sections of the Godement quotient over the covered set lift.** -/
theorem LerayCover.surjective_bot (hcov : V ≤ ⨆ i, U i) {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hF : LerayCover.{w} F V U) :
    Function.Surjective
      ((sheafCechMap (deningerGodementComplex F).g V U).app ∅) :=
  FinsetCechDatum.surjective_bot_of_chase (sheafCechMap (deningerGodementComplex F).f V U)
    (sheafCechMap (deningerGodementComplex F).g V U)
    (fun s _ x => sheafCech_comp_zero V U s x)
    (fun s hs => hF.surjective (Finset.card_pos.mp (by omega)))
    (fun s _ y hy => sheafCech_exact (deningerGodementShortExact F) s y hy)
    (fun s _ => sheafCech_injective (deningerGodementShortExact F) s)
    (hF.exact 0) (godementCech_exactAt hcov 0) (sheafCech_exactBot _ hcov)

/-- Leray's theorem over the open set `V ∩ ⋂ ∅ = V`. -/
theorem leray_vanishing_aux (hcov : V ≤ ⨆ i, U i) :
    ∀ (q : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X), LerayCover.{w} F V U →
      ∀ x : deningerSheafCohomology.{w} (coverInter V U ∅) F (q + 1), x = 0 := by
  intro q
  induction q with
  | zero =>
    intro F hF x
    exact deningerExt_one_eq_zero_of_lift (deningerGodementShortExact F) _
      (godement_acyclicOn F _) (hF.surjective_bot hcov) x
  | succ q ih =>
    intro F hF x
    exact deningerExt_eq_zero_of_shift (deningerGodementShortExact F) _ (godement_acyclicOn F _)
      q (ih _ (hF.godementQuotient hcov)) x

/-- **Leray's theorem.**  A sheaf with no higher cohomology on the intersections of a finite cover
of `V`, whose augmented Čech complex is exact in positive degrees, has no higher cohomology
on `V`. -/
theorem leray_vanishing (hcov : V ≤ ⨆ i, U i) {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hF : LerayCover.{w} F V U) (q : ℕ) (x : deningerSheafCohomology.{w} V F (q + 1)) : x = 0 := by
  have h := leray_vanishing_aux hcov q F hF
  rw [coverInter_empty] at h
  exact h x

end Leray

/-! ## Cartan's criterion -/

section Cartan

/-- **Cartan's basis**: quasi-compact opens, closed under binary intersections, forming a basis of
the topology inside each member. -/
structure CartanBasis (B : Set (Opens X)) : Prop where
  inf_mem : ∀ W W' : Opens X, W ∈ B → W' ∈ B → W ⊓ W' ∈ B
  isCompact : ∀ W ∈ B, IsCompact (W : Set X)
  basis : ∀ W ∈ B, ∀ (O : Opens X) (x : X), x ∈ W → x ∈ O → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W ⊓ O

/-- **Cartan's hypothesis**: Čech exactness in positive degrees for every finite cover of a member
by members. -/
def CartanExact (B : Set (Opens X)) (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ W ∈ B, ∀ (n : ℕ) (U : Fin n → Opens X), (∀ i, U i ∈ B) → (∀ i, U i ≤ W) →
    W ≤ ⨆ i, U i → ∀ p : ℕ, (sheafCech F W U).ExactAt (p + 1)

variable {B : Set (Opens X)}

omit [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)] in
/-- The intersections of a cover of a member by members are members. -/
theorem CartanBasis.coverInter_mem (hB : CartanBasis B) {W : Opens X} (hW : W ∈ B) {n : ℕ}
    {U : Fin n → Opens X} (hU : ∀ i, U i ∈ B) (s : Finset (Fin n)) : coverInter W U s ∈ B := by
  induction s using Finset.induction_on with
  | empty => rw [coverInter_empty]; exact hW
  | insert a s _ ih =>
    have : coverInter W U (insert a s) = U a ⊓ coverInter W U s := by
      rw [coverInter, coverInter, Finset.inf_insert]
      ac_rfl
    rw [this]
    exact hB.inf_mem _ _ (hU a) ih

omit [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)] in
/-- **Local lifts assemble over a member.**  The sections of the Godement quotient over a member of
Cartan's basis lift, as soon as `F` is Čech exact in degree one for covers by members. -/
theorem cartan_surjective (hB : CartanBasis B) {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hF : CartanExact B F) {W : Opens X} (hW : W ∈ B) :
    Function.Surjective
      (ConcreteCategory.hom ((deningerGodementComplex F).g.1.app (op W))) := by
  classical
  set S := deningerGodementComplex F with hSdef
  have hS : S.ShortExact := deningerGodementShortExact F
  intro q
  -- local lifts on members of the basis
  have hloc : TopCat.Presheaf.IsLocallySurjective S.g.1 :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).2 hS.epi_g
  have hlift : ∀ x : W, ∃ W' : Opens X, W' ∈ B ∧ x.1 ∈ W' ∧ ∃ hW' : W' ≤ W,
      ∃ t : ToType (S.X₂.1.obj (op W')),
        ConcreteCategory.hom (S.g.1.app (op W')) t = deningerRes S.X₃ hW' q := by
    intro x
    obtain ⟨O, hOW, ⟨t, ht⟩, hxO⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff S.g.1).1 hloc W q x.1 x.2
    obtain ⟨W', hW'B, hxW', hW'le⟩ := hB.basis W hW O x.1 x.2 hxO
    have hW'O : W' ≤ O := hW'le.trans inf_le_right
    refine ⟨W', hW'B, hxW', hW'le.trans inf_le_left, deningerRes S.X₂ hW'O t, ?_⟩
    rw [← deningerRes_app S.g hW'O t]
    change deningerRes S.X₃ hW'O (ConcreteCategory.hom (S.g.1.app (op O)) t) = _
    rw [ht]
    exact deningerRes_res _ _ q
  choose W' hW'B hxW' hW'le t ht using hlift
  -- a finite subcover
  obtain ⟨I, hI⟩ := (hB.isCompact W hW).elim_finite_subcover (fun x : W => (W' x : Set X))
    (fun x => (W' x).2) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW' ⟨x, hx⟩⟩)
  set n := I.card
  let e : Fin n ≃ I := I.equivFin.symm
  let U : Fin n → Opens X := fun i => W' (e i)
  have hUB : ∀ i, U i ∈ B := fun i => hW'B _
  have hUW : ∀ i, U i ≤ W := fun i => hW'le _
  have hcov : W ≤ ⨆ i, U i := by
    intro x hx
    obtain ⟨y, hyI, hxy⟩ := Set.mem_iUnion₂.mp (hI hx)
    exact Opens.mem_iSup.mpr ⟨e.symm ⟨y, hyI⟩, by
      change x ∈ W' (e (e.symm ⟨y, hyI⟩))
      rw [Equiv.apply_symm_apply]
      exact hxy⟩
  -- the lift through the chase, over `W ∩ ⋂ ∅`
  have hW0 : coverInter W U ∅ = W := coverInter_empty W U
  let q₀ : (sheafCech S.X₃ W U).obj ∅ := deningerRes S.X₃ (le_of_eq hW0) q
  let g : (sheafCech S.X₂ W U).Cochain := fun s =>
    if hs : s.card = 1 then
      deningerRes S.X₂ (show coverInter W U s ≤ U (s.min' (Finset.card_pos.mp (by omega))) from
        fun x hx => (mem_coverInter.mp hx).2 _ (Finset.min'_mem _ _))
        (t (e (s.min' (Finset.card_pos.mp (by omega)))))
    else 0
  have hg : (sheafCech S.X₂ W U).IsDeg g 0 := fun s hs => dif_neg hs
  have hπg : ∀ s : Finset (Fin n), s.card = 1 →
      (sheafCechMap S.g W U).app s (g s)
        = (sheafCech S.X₃ W U).res (Finset.empty_subset s) q₀ := by
    intro s hs
    change ConcreteCategory.hom (S.g.1.app _) (g s) = deningerRes S.X₃ _ (deningerRes S.X₃ _ q)
    simp only [g, dif_pos hs]
    rw [← deningerRes_app, ht, deningerRes_res, deningerRes_res]
  obtain ⟨t₀, ht₀⟩ := FinsetCechDatum.lift_bot_of_chase (sheafCechMap S.f W U)
    (sheafCechMap S.g W U) (fun s _ x => sheafCech_comp_zero W U s x)
    (fun s _ y hy => sheafCech_exact hS s y hy) (fun s _ => sheafCech_injective hS s)
    (hF W hW n U hUB hUW hcov 0) (godementCech_exactAt hcov 0) (sheafCech_exactBot _ hcov) q₀ g hg
    hπg
  refine ⟨deningerRes S.X₂ (le_of_eq hW0.symm) t₀, ?_⟩
  rw [← deningerRes_app]
  rw [show ConcreteCategory.hom (S.g.1.app (op (coverInter W U ∅))) t₀ = q₀ from ht₀,
    deningerRes_res, deningerRes_self]

omit [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)] in
/-- **Cartan's hypothesis passes to the Godement quotient.** -/
theorem CartanExact.godementQuotient (hB : CartanBasis B) {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hF : CartanExact B F) : CartanExact B (deningerGodementComplex F).X₃ := by
  intro W hW n U hUB hUW hcov p
  exact FinsetCechDatum.exactAt_of_chase (sheafCechMap (deningerGodementComplex F).f W U)
    (sheafCechMap (deningerGodementComplex F).g W U) (p + 1)
    (fun s _ x => sheafCech_comp_zero W U s x)
    (fun s _ => cartan_surjective hB hF (hB.coverInter_mem hW hUB s))
    (fun s _ y hy => sheafCech_exact (deningerGodementShortExact F) s y hy)
    (fun s _ => sheafCech_injective (deningerGodementShortExact F) s)
    (hF W hW n U hUB hUW hcov (p + 1)) (godementCech_exactAt hcov (p + 1))

/-- **Cartan's criterion.**  A sheaf whose Čech complexes for finite covers of members of a Cartan
basis by members are exact in positive degrees has no higher cohomology on any member. -/
theorem cartan_vanishing (hB : CartanBasis B) :
    ∀ (q : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X), CartanExact B F →
      ∀ W ∈ B, ∀ x : deningerSheafCohomology.{w} W F (q + 1), x = 0 := by
  intro q
  induction q with
  | zero =>
    intro F hF W hW x
    exact deningerExt_one_eq_zero_of_lift (deningerGodementShortExact F) W
      (godement_acyclicOn F W) (cartan_surjective hB hF hW) x
  | succ q ih =>
    intro F hF W hW x
    exact deningerExt_eq_zero_of_shift (deningerGodementShortExact F) W (godement_acyclicOn F W)
      q (ih _ (hF.godementQuotient hB) W hW) x

end Cartan

end HTGeometry

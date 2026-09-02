import GaloisForLFunctions.HTGeometry.AlgebraSpectrumPrincipalOpen
import GaloisForLFunctions.HTGeometry.AdjoinRootSpectrumCovering

/-!
# Ambient spectrum charts from principal-open root presentations

A monic `AdjoinRoot` presentation after one principal localization gives a local chart only on an
open subtype at first.  This file transports that chart through scalar extension and then promotes
it back to an `OpenPartialHomeomorph` of the ambient complex-point spaces.  The promotion keeps the
original ambient projection as the chart's global `toFun`, which is the exact interface required by
`IsLocalHomeomorph`.
-/

open Set Topology Polynomial

/-- A chart for the restriction of a continuous map to an open subtype promotes to an ambient
chart with the original map as its global forward function. -/
theorem liftOpenRestrictedChart
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set X} (hs : IsOpen s) (hf : Continuous f)
    {x : X} (hx : x ∈ s)
    (e : OpenPartialHomeomorph s Y)
    (hxe : (⟨x, hx⟩ : s) ∈ e.source)
    (he : f ∘ (Subtype.val : s → X) = e) :
    ∃ e' : OpenPartialHomeomorph X Y, x ∈ e'.source ∧ f = e' := by
  let e' : OpenPartialHomeomorph X Y :=
    { toFun := f
      invFun := fun y => (e.invFun y).1
      source := Subtype.val '' e.source
      target := e.target
      map_source' := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := hz
        rw [show f w.1 = e w by exact congrFun he w]
        exact e.map_source hw
      map_target' := by
        intro y hy
        exact ⟨e.invFun y, e.map_target hy, rfl⟩
      left_inv' := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := hz
        rw [show f w.1 = e w by exact congrFun he w]
        exact congrArg Subtype.val (e.left_inv hw)
      right_inv' := by
        intro y hy
        rw [show f (e.invFun y).1 = e (e.invFun y) by exact congrFun he (e.invFun y)]
        exact e.right_inv hy
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := continuous_subtype_val.comp_continuousOn e.continuousOn_symm
      open_source := hs.isOpenEmbedding_subtypeVal.isOpenMap _ e.open_source
      open_target := e.open_target }
  exact ⟨e', ⟨⟨x, hx⟩, hxe, rfl⟩, rfl⟩

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

namespace AlgSpec

set_option maxHeartbeats 4000000

variable {R B : Type*} [CommRing R] [CommRing B]
variable [Algebra ℂ R] [Algebra ℂ B] [Algebra R B] [IsScalarTower ℂ R B]

/-- Projection on complex points induced by a tower of complex algebras. -/
def algebraSpectrumProjection (chi : AlgSpec B) : AlgSpec R :=
  AlgSpec.precomp (IsScalarTower.toAlgHom ℂ R B) chi

theorem continuous_algebraSpectrumProjection :
    Continuous (algebraSpectrumProjection (R := R) (B := B)) :=
  continuous_precomp _

omit [Algebra ℂ R] [IsScalarTower ℂ R B] in
theorem isOpen_algebraSpectrumPrincipalOpen (g : R) :
    IsOpen {chi : AlgSpec B | chi (algebraMap R B g) ≠ 0} := by
  exact isOpen_ne.preimage (continuous_eval _)

/-- On the principal open, a root presentation identifies the original total spectrum with the
monogenic spectrum. -/
def principalOpenAdjoinRootHomeomorph (g : R)
    (q : Polynomial (Localization.Away g))
    (e : AdjoinRoot q ≃ₐ[Localization.Away g]
      TensorProduct R (Localization.Away g) B) :
    {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0} ≃ₜ AlgSpec (AdjoinRoot q) :=
  (homeomorphTensorLocalizationAway (B := B) g).symm.trans
    (homeomorphOfAlgEquiv (e.restrictScalars ℂ))

theorem principalOpenAdjoinRootHomeomorph_base (g : R)
    (q : Polynomial (Localization.Away g))
    (e : AdjoinRoot q ≃ₐ[Localization.Away g]
      TensorProduct R (Localization.Away g) B)
    (chi : {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0}) :
    (homeomorphLocalizationAway g)
        (adjoinRootBase q (principalOpenAdjoinRootHomeomorph g q e chi)) =
      tensorLocalizationAwayBasePoint g chi := by
  apply Subtype.ext
  apply DFunLike.ext
  intro r
  change (homeomorphTensorLocalizationAway (B := B) g).symm chi
      (e (algebraMap (Localization.Away g) (AdjoinRoot q)
        (algebraMap R (Localization.Away g) r))) = chi.1 (algebraMap R B r)
  rw [e.commutes]
  change tensorLocalizationAwayLift g chi
      ((algebraMap R (Localization.Away g) r) ⊗ₜ[R] (1 : B)) = _
  rw [tensorLocalizationAwayLift_tmul, localizationAwayLift_algebraMap]
  simp [tensorLocalizationAwayBasePoint]
  rfl

/-- A separable specialization in a principal-open monic presentation supplies an ambient local
homeomorphism chart for the original spectrum projection at the selected total-space point. -/
theorem exists_chart_algebraSpectrumProjection_of_principalOpen_adjoinRoot
    (g : R) (q : Polynomial (Localization.Away g)) (hq : q.Monic)
    (e : AdjoinRoot q ≃ₐ[Localization.Away g]
      TensorProduct R (Localization.Away g) B)
    (chi : AlgSpec B) (hchi : chi (algebraMap R B g) ≠ 0)
    (hsep : (q.map (pointRingHom
      (adjoinRootBase q
        (principalOpenAdjoinRootHomeomorph g q e ⟨chi, hchi⟩)))).Separable) :
    ∃ phi : OpenPartialHomeomorph (AlgSpec B) (AlgSpec R),
      chi ∈ phi.source ∧ algebraSpectrumProjection = phi := by
  let H := principalOpenAdjoinRootHomeomorph g q e
  let J := homeomorphLocalizationAway g
  let x : {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0} := ⟨chi, hchi⟩
  obtain ⟨rootChart, hroot, hrootEq⟩ :=
    exists_chart_adjoinRootBase q hq (H x) hsep
  let localChart : OpenPartialHomeomorph
      {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0}
      {chi : AlgSpec R // chi g ≠ 0} :=
    H.toOpenPartialHomeomorph.trans (rootChart.trans J.toOpenPartialHomeomorph)
  have hxlocal : x ∈ localChart.source := by
    simpa [localChart] using hroot
  have hlocalEq :
      (fun z : {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0} =>
        tensorLocalizationAwayBasePoint g z) = localChart := by
    funext z
    change tensorLocalizationAwayBasePoint g z = J (rootChart (H z))
    rw [← congrFun hrootEq (H z), principalOpenAdjoinRootHomeomorph_base]
  have htargetOpen : IsOpen {chi : AlgSpec R | chi g ≠ 0} :=
    isOpen_ne.preimage (continuous_eval g)
  letI : Nonempty {chi : AlgSpec R // chi g ≠ 0} :=
    ⟨tensorLocalizationAwayBasePoint g x⟩
  let targetVal : OpenPartialHomeomorph
      {chi : AlgSpec R // chi g ≠ 0} (AlgSpec R) :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : {chi : AlgSpec R // chi g ≠ 0} → AlgSpec R)
      htargetOpen.isOpenEmbedding_subtypeVal
  let ambientTargetChart : OpenPartialHomeomorph
      {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0} (AlgSpec R) :=
    localChart.trans targetVal
  have hxambientTarget : x ∈ ambientTargetChart.source := by
    simpa [ambientTargetChart, targetVal] using hxlocal
  have hambientTargetEq :
      algebraSpectrumProjection ∘
          (Subtype.val : {chi : AlgSpec B // chi (algebraMap R B g) ≠ 0} → AlgSpec B) =
        ambientTargetChart := by
    funext z
    change algebraSpectrumProjection z.1 = targetVal (localChart z)
    rw [← congrFun hlocalEq z]
    apply DFunLike.ext
    intro r
    rfl
  exact liftOpenRestrictedChart
    (isOpen_algebraSpectrumPrincipalOpen (B := B) g)
    continuous_algebraSpectrumProjection hchi ambientTargetChart hxambientTarget hambientTargetEq

/-- Pointwise principal-open separable presentations assemble to a local homeomorphism of the
original ambient spectrum projection. -/
theorem isLocalHomeomorph_algebraSpectrumProjection_of_principalOpen_adjoinRoot
    (hpresent : ∀ chi : AlgSpec B,
      ∃ g : R, ∃ hchi : chi (algebraMap R B g) ≠ 0,
        ∃ q : Polynomial (Localization.Away g), q.Monic ∧
        ∃ e : AdjoinRoot q ≃ₐ[Localization.Away g]
            TensorProduct R (Localization.Away g) B,
          (q.map (pointRingHom
            (adjoinRootBase q
              (principalOpenAdjoinRootHomeomorph g q e ⟨chi, hchi⟩)))).Separable) :
    IsLocalHomeomorph (algebraSpectrumProjection (R := R) (B := B)) := by
  intro chi
  obtain ⟨g, hchi, q, hq, e, hsep⟩ := hpresent chi
  exact exists_chart_algebraSpectrumProjection_of_principalOpen_adjoinRoot
    g q hq e chi hchi hsep

end AlgSpec

end

end GaloisForLFunctions.HTGeometry

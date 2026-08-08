import GaloisForLFunctions.RHTower.DeningerDivisorExtension
import GaloisForLFunctions.HTGeometry.HolomorphicCoordinateDivision

/-!
# The ideal of a coordinate divisor

The sections of the structure sheaf that vanish on the divisor of the last coordinate form a
subsheaf, cut out by a pointwise condition, and that subsheaf is a kernel of restriction to the
divisor: restriction is evaluation at the points of the divisor, so a section killed by it vanishes
there.  Multiplication by the coordinate factors through this subsheaf, and the factorisation is a
monomorphism.

* `RHTower.deningerVanishSheaf` : the sections vanishing on the divisor.
* `RHTower.deningerVanishIncl_isKernel` : it is a kernel of restriction to the divisor.
* `RHTower.deningerCoordMulVanish` : the factorisation of multiplication by the coordinate.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat Complex HTGeometry

section VanishSheaf

variable {n : ℕ} {Ω : Opens (Fin (n + 1) → ℂ)}

/-- A holomorphic section vanishing on the divisor of the last coordinate. -/
def DeningerVanishPred {U : Opens (deningerSpace Ω)} (f : ↥U → DeningerFormVal (n + 1)) : Prop :=
  DeningerClosedFormPred 0 f ∧
    ∀ (x : ↥U) (S : Finset (Fin (n + 1))),
      (x.1.1 : Fin (n + 1) → ℂ) (Fin.last n) = 0 → f x S = 0

theorem DeningerVanishPred.res {U W : Opens (deningerSpace Ω)} (h : W ≤ U)
    {f : ↥U → DeningerFormVal (n + 1)} (hf : DeningerVanishPred f) :
    DeningerVanishPred (fun x : ↥W => f ⟨x.1, h x.2⟩) :=
  ⟨DeningerClosedFormPred.res 0 h hf.1, fun x S hx => hf.2 ⟨x.1, h x.2⟩ S hx⟩

theorem DeningerVanishPred.locality {U : Opens (deningerSpace Ω)}
    (f : ↥U → DeningerFormVal (n + 1))
    (hloc : ∀ x : ↥U, ∃ (W : Opens (deningerSpace Ω)) (hW : W ≤ U), x.1 ∈ W ∧
      DeningerVanishPred (fun y : ↥W => f ⟨y.1, hW y.2⟩)) :
    DeningerVanishPred f := by
  refine ⟨DeningerClosedFormPred.locality 0 f fun x => ?_, fun x S hx => ?_⟩
  · obtain ⟨W, hW, hxW, hpred⟩ := hloc x
    exact ⟨W, hW, hxW, hpred.1⟩
  · obtain ⟨W, hW, hxW, hpred⟩ := hloc x
    exact hpred.2 ⟨x.1, hxW⟩ S hx

theorem DeningerVanishPred.zero (U : Opens (deningerSpace Ω)) :
    DeningerVanishPred (fun _ : ↥U => (0 : DeningerFormVal (n + 1))) :=
  ⟨DeningerClosedFormPred.zero 0 U, fun _ _ _ => rfl⟩

theorem DeningerVanishPred.add {U : Opens (deningerSpace Ω)}
    {f g : ↥U → DeningerFormVal (n + 1)} (hf : DeningerVanishPred f)
    (hg : DeningerVanishPred g) : DeningerVanishPred (fun x => f x + g x) := by
  refine ⟨DeningerClosedFormPred.add 0 hf.1 hg.1, fun x S hx => ?_⟩
  show f x S + g x S = 0
  rw [hf.2 x S hx, hg.2 x S hx, add_zero]

theorem DeningerVanishPred.neg {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal (n + 1)} (hf : DeningerVanishPred f) :
    DeningerVanishPred (fun x => -f x) := by
  refine ⟨DeningerClosedFormPred.neg 0 hf.1, fun x S hx => ?_⟩
  show -f x S = 0
  rw [hf.2 x S hx, neg_zero]

/-- The local predicate cutting out the sections vanishing on the divisor. -/
noncomputable def deningerVanishLocalPredicate (Ω : Opens (Fin (n + 1) → ℂ)) :
    TopCat.LocalPredicate (fun _ : (deningerSpace Ω : Type) => DeningerFormVal (n + 1)) where
  pred {_} f := DeningerVanishPred f
  res {_ _} i _ hf := DeningerVanishPred.res i.le hf
  locality {_} f hf := by
    refine DeningerVanishPred.locality f fun x => ?_
    obtain ⟨W, hxW, i, hpred⟩ := hf x
    exact ⟨W, i.le, hxW, hpred⟩

/-- The data cutting out the ideal sheaf of the divisor. -/
noncomputable def deningerVanishData (Ω : Opens (Fin (n + 1) → ℂ)) :
    DeningerLocalGroupData (deningerSpace Ω) (DeningerFormVal (n + 1)) where
  toLocalPredicate := deningerVanishLocalPredicate Ω
  pred_zero U := DeningerVanishPred.zero U
  pred_add _ _ _ hf hg := DeningerVanishPred.add hf hg
  pred_neg _ _ hf := DeningerVanishPred.neg hf

/-- **The ideal sheaf of the divisor of the last coordinate**: the holomorphic functions vanishing
on it. -/
noncomputable def deningerVanishSheaf (Ω : Opens (Fin (n + 1) → ℂ)) :
    TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω) :=
  (deningerVanishData Ω).sheaf

/-- **The inclusion of the ideal sheaf into the structure sheaf.** -/
noncomputable def deningerVanishIncl (Ω : Opens (Fin (n + 1) → ℂ)) :
    deningerVanishSheaf Ω ⟶ deningerClosedFormSheaf Ω 0 :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
      { toFun := fun f => ⟨f.1, f.2.1⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
     naturality := fun _ _ _ => rfl }⟩

instance deningerVanishIncl_mono (Ω : Opens (Fin (n + 1) → ℂ)) :
    Mono (deningerVanishIncl Ω) := by
  haveI : ∀ U, Mono ((deningerVanishIncl Ω).1.app U) := by
    intro U
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    have h : (ConcreteCategory.hom ((deningerVanishIncl Ω).1.app U) a).1
        = (ConcreteCategory.hom ((deningerVanishIncl Ω).1.app U) b).1 := by rw [hab]
    exact Subtype.ext h
  haveI : Mono (deningerVanishIncl Ω).1 := NatTrans.mono_of_mono_app _
  exact CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono _ _ _

end VanishSheaf

end RHTower

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat Complex HTGeometry

section Kernel

variable {n : ℕ} {Ω : Opens (Fin (n + 1) → ℂ)} {Ω' : Opens (Fin n → ℂ)}
  (hmap : ∀ w ∈ Ω', deningerDivisorMap w ∈ Ω)

/-- **A section vanishing on the divisor restricts to zero.** -/
theorem deningerVanishIncl_comp_restrict :
    deningerVanishIncl Ω ≫ deningerDivisorRestrict hmap = 0 := by
  refine CategoryTheory.ObjectProperty.hom_ext _ ?_
  ext U f
  refine Subtype.ext (funext fun y => funext fun S => ?_)
  show deningerRestrictVal (f.1 ⟨(deningerDivisorInclusion hmap) y.1, y.2⟩) S = 0
  by_cases hS : S = ∅
  · subst hS
    rw [deningerRestrictVal_empty]
    exact f.2.2 ⟨(deningerDivisorInclusion hmap) y.1, y.2⟩ ∅
      (deningerDivisorMap_last (y.1.1 : Fin n → ℂ))
  · rw [deningerRestrictVal_ne _ hS]

/-- A section killed by restriction to the divisor vanishes on the divisor. -/
theorem deningerVanishPred_of_restrict_eq_zero
    (hfull : ∀ w : Fin n → ℂ, deningerDivisorMap w ∈ Ω → w ∈ Ω')
    {T : TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω)}
    (k : T ⟶ deningerClosedFormSheaf Ω 0) (hk : k ≫ deningerDivisorRestrict hmap = 0)
    (U : (Opens (deningerSpace Ω))ᵒᵖ) (t : ToType (T.1.obj U)) :
    DeningerVanishPred (ConcreteCategory.hom (k.1.app U) t).1 := by
  refine ⟨(ConcreteCategory.hom (k.1.app U) t).2, fun x S hx => ?_⟩
  by_cases hS : S = ∅
  · subst hS
    have hwΩ' : deningerChopMap (x.1.1 : Fin (n + 1) → ℂ) ∈ Ω' :=
      hfull _ (by rw [deningerDivisorMap_chopMap hx]; exact x.1.2)
    have hxpt : (deningerDivisorInclusion hmap)
        (⟨deningerChopMap (x.1.1 : Fin (n + 1) → ℂ), hwΩ'⟩ : deningerSpace Ω') = x.1 :=
      Subtype.ext (deningerDivisorMap_chopMap hx)
    have hyU : (⟨deningerChopMap (x.1.1 : Fin (n + 1) → ℂ), hwΩ'⟩ : deningerSpace Ω')
        ∈ (Opens.map (deningerDivisorInclusion hmap)).obj U.unop := by
      show (deningerDivisorInclusion hmap) _ ∈ U.unop
      rw [hxpt]
      exact x.2
    have h0 := congrArg
      (fun ψ : T ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0}
          (deningerDivisorInclusion hmap)).obj (deningerClosedFormSheaf Ω' 0) =>
        ConcreteCategory.hom (ψ.1.app U) t) hk
    have h1 := congrFun (congrFun (Subtype.ext_iff.1 h0)
      (⟨⟨deningerChopMap (x.1.1 : Fin (n + 1) → ℂ), hwΩ'⟩, hyU⟩)) ∅
    show (ConcreteCategory.hom (k.1.app U) t).1 x ∅ = 0
    have hx' : x = ⟨(deningerDivisorInclusion hmap)
        (⟨deningerChopMap (x.1.1 : Fin (n + 1) → ℂ), hwΩ'⟩ : deningerSpace Ω'), hyU⟩ :=
      Subtype.ext hxpt.symm
    rw [hx']
    exact h1
  · exact (ConcreteCategory.hom (k.1.app U) t).2.1.1 x S (fun hc => hS (Finset.card_eq_zero.1 hc))

/-- The factorisation of a map killed by restriction through the ideal sheaf. -/
noncomputable def deningerVanishKernelLift
    (hfull : ∀ w : Fin n → ℂ, deningerDivisorMap w ∈ Ω → w ∈ Ω')
    {T : TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω)}
    (k : T ⟶ deningerClosedFormSheaf Ω 0) (hk : k ≫ deningerDivisorRestrict hmap = 0) :
    T ⟶ deningerVanishSheaf Ω :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom
      { toFun := fun t => ⟨(ConcreteCategory.hom (k.1.app U) t).1,
          deningerVanishPred_of_restrict_eq_zero hmap hfull k hk U t⟩
        map_zero' := by
          refine Subtype.ext (funext fun x => funext fun S => ?_)
          show (ConcreteCategory.hom (k.1.app U) 0).1 x S = _
          rw [map_zero]
          rfl
        map_add' := fun a b => by
          refine Subtype.ext (funext fun x => funext fun S => ?_)
          show (ConcreteCategory.hom (k.1.app U) (a + b)).1 x S = _
          rw [map_add]
          rfl }
     naturality := fun U W i => by
       ext t
       refine Subtype.ext (funext fun x => ?_)
       have hnat := congrFun (congrArg
         (fun ψ : T.1.obj U ⟶ (deningerClosedFormSheaf Ω 0).1.obj W =>
           (ConcreteCategory.hom ψ :
             ToType (T.1.obj U) → ToType ((deningerClosedFormSheaf Ω 0).1.obj W)))
         (k.1.naturality i)) t
       exact congrFun (congrArg Subtype.val hnat) x }⟩

theorem deningerVanishKernelLift_comp
    (hfull : ∀ w : Fin n → ℂ, deningerDivisorMap w ∈ Ω → w ∈ Ω')
    {T : TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω)}
    (k : T ⟶ deningerClosedFormSheaf Ω 0) (hk : k ≫ deningerDivisorRestrict hmap = 0) :
    deningerVanishKernelLift hmap hfull k hk ≫ deningerVanishIncl Ω = k := by
  refine CategoryTheory.ObjectProperty.hom_ext _ ?_
  ext U t
  rfl

/-- **The ideal sheaf is a kernel of restriction to the divisor.** -/
noncomputable def deningerVanishIncl_isKernel
    (hfull : ∀ w : Fin n → ℂ, deningerDivisorMap w ∈ Ω → w ∈ Ω') :
    IsLimit (KernelFork.ofι (deningerVanishIncl Ω) (deningerVanishIncl_comp_restrict hmap)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {_} k hk => deningerVanishKernelLift hmap hfull k hk)
    (fun {_} k hk => deningerVanishKernelLift_comp hmap hfull k hk)
    (fun {_} k hk l hl => by
      have hmono := deningerVanishIncl_mono Ω
      refine (cancel_mono (deningerVanishIncl Ω)).1 ?_
      rw [hl, deningerVanishKernelLift_comp])

end Kernel

end RHTower

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat Complex HTGeometry

section Factorisation

variable {n : ℕ} (Ω : Opens (Fin (n + 1) → ℂ))

theorem DeningerClosedFormPred.coordVanish {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal (n + 1)} (hf : DeningerClosedFormPred 0 f) :
    DeningerVanishPred (deningerCoordSection (Fin.last n) f) := by
  refine ⟨hf.coord (Fin.last n), fun x S hx => ?_⟩
  show (x.1.1 : Fin (n + 1) → ℂ) (Fin.last n) * f x S = 0
  rw [hx, zero_mul]

/-- **Multiplication by the last coordinate, into the ideal sheaf of its divisor.** -/
noncomputable def deningerCoordMulVanish :
    deningerClosedFormSheaf Ω 0 ⟶ deningerVanishSheaf Ω :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
      { toFun := fun f => ⟨deningerCoordSection (Fin.last n) f.1, f.2.coordVanish⟩
        map_zero' := Subtype.ext (funext fun x => funext fun S => by
          show (x.1.1 : Fin (n + 1) → ℂ) (Fin.last n) * 0 = 0
          rw [mul_zero])
        map_add' := fun a b => Subtype.ext (funext fun x => funext fun S => by
          show (x.1.1 : Fin (n + 1) → ℂ) (Fin.last n) * (a.1 x S + b.1 x S)
            = (x.1.1 : Fin (n + 1) → ℂ) (Fin.last n) * a.1 x S
              + (x.1.1 : Fin (n + 1) → ℂ) (Fin.last n) * b.1 x S
          rw [mul_add]) }
     naturality := fun _ _ _ => rfl }⟩

/-- The factorisation recovers multiplication by the coordinate. -/
theorem deningerCoordMulVanish_comp :
    deningerCoordMulVanish Ω ≫ deningerVanishIncl Ω = deningerCoordMul Ω 0 (Fin.last n) := by
  refine CategoryTheory.ObjectProperty.hom_ext _ ?_
  ext U f
  rfl

instance deningerCoordMulVanish_mono : Mono (deningerCoordMulVanish Ω) := by
  haveI : Mono (deningerCoordMulVanish Ω ≫ deningerVanishIncl Ω) := by
    rw [deningerCoordMulVanish_comp]
    exact deningerCoordMul_mono Ω 0 (Fin.last n)
  exact mono_of_mono (deningerCoordMulVanish Ω) (deningerVanishIncl Ω)

end Factorisation

end RHTower

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat Complex HTGeometry

section Surjective

variable {n : ℕ} {Ω : Opens (Fin (n + 1) → ℂ)}

/-- **A local quotient by the last coordinate.**  On a small ball around a point of the domain the
model of a section vanishing on the divisor is the coordinate times an analytic function: at a point
of the divisor this is the division theorem on a polydisc centred there, and away from it the
coordinate does not vanish. -/
theorem exists_local_coord_quotient {g : SetForm (n + 1)} {Wset : Set (Fin (n + 1) → ℂ)}
    (hWopen : IsOpen Wset) (han : AnalyticOnNhd ℂ (g ∅) Wset)
    (hvan : ∀ z ∈ Wset, z (Fin.last n) = 0 → g ∅ z = 0)
    {c : Fin (n + 1) → ℂ} (hc : c ∈ Wset) :
    ∃ R > 0, Metric.ball c R ⊆ Wset ∧ ∃ u : (Fin (n + 1) → ℂ) → ℂ,
      AnalyticOnNhd ℂ u (Metric.ball c R) ∧
      ∀ z ∈ Metric.ball c R, z (Fin.last n) * u z = g ∅ z := by
  obtain ⟨R₀, hR₀, hR₀sub⟩ := Metric.isOpen_iff.1 hWopen c hc
  by_cases hlast : c (Fin.last n) = 0
  · refine ⟨R₀, hR₀, hR₀sub, coordDivQuotient (g ∅), ?_, ?_⟩
    · exact coordDivQuotient_analyticOnNhd (han.mono hR₀sub) hlast
    · exact fun z hz => coordDivQuotient_mul (han.mono hR₀sub) hlast
        (fun w hw hw0 => hvan w (hR₀sub hw) hw0) hz
  · obtain ⟨R₁, hR₁, hR₁ball⟩ : ∃ R₁ > 0, ∀ z ∈ Metric.ball c R₁, z (Fin.last n) ≠ 0 := by
      obtain ⟨R₁, hR₁, hsub⟩ := Metric.isOpen_iff.1
        ((isOpen_compl_singleton).preimage (continuous_apply (Fin.last n))) c hlast
      exact ⟨R₁, hR₁, fun z hz => hsub hz⟩
    refine ⟨min R₀ R₁, lt_min hR₀ hR₁,
      subset_trans (Metric.ball_subset_ball (min_le_left _ _)) hR₀sub,
      fun z => g ∅ z / z (Fin.last n), ?_, ?_⟩
    · intro z hz
      refine AnalyticAt.div (han z (hR₀sub (Metric.ball_subset_ball (min_le_left _ _) hz))) ?_ ?_
      · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
          (Fin.last n)).analyticAt z
      · exact hR₁ball z (Metric.ball_subset_ball (min_le_right _ _) hz)
    · intro z hz
      exact mul_div_cancel₀ _ (hR₁ball z (Metric.ball_subset_ball (min_le_right _ _) hz))

/-- The global smooth model of a local quotient: cut off with a bump. -/
noncomputable def deningerQuotientModel (c : Fin (n + 1) → ℂ) (R : ℝ) (hR : 0 < R)
    (u : (Fin (n + 1) → ℂ) → ℂ) : SetForm (n + 1) :=
  fun S z => if S = ∅ then
    (((⟨R / 3, R / 2, by positivity, by linarith⟩ : ContDiffBump c) : (Fin (n + 1) → ℂ) → ℝ) z : ℂ)
      * u z else 0

theorem deningerQuotientModel_deg (c : Fin (n + 1) → ℂ) (R : ℝ) (hR : 0 < R)
    (u : (Fin (n + 1) → ℂ) → ℂ) : SetFormDeg 0 (deningerQuotientModel c R hR u) := by
  intro S hS z
  exact if_neg (fun hc => hS (by rw [hc]; rfl))

theorem deningerQuotientModel_eq_of_mem {c : Fin (n + 1) → ℂ} {R : ℝ} (hR : 0 < R)
    {u : (Fin (n + 1) → ℂ) → ℂ} {z : Fin (n + 1) → ℂ}
    (hz : z ∈ Metric.closedBall c (R / 3)) :
    deningerQuotientModel c R hR u ∅ z = u z := by
  rw [deningerQuotientModel, if_pos rfl,
    (⟨R / 3, R / 2, by positivity, by linarith⟩ : ContDiffBump c).one_of_mem_closedBall hz]
  norm_num

theorem deningerQuotientModel_smooth {c : Fin (n + 1) → ℂ} {R : ℝ} (hR : 0 < R)
    {u : (Fin (n + 1) → ℂ) → ℂ} (hu : AnalyticOnNhd ℂ u (Metric.ball c R)) :
    SmoothSetForm (deningerQuotientModel c R hR u) := by
  intro S
  by_cases hS : S = ∅
  · subst hS
    set bp : ContDiffBump c := ⟨R / 3, R / 2, by positivity, by linarith⟩ with hbp
    have hfun : deningerQuotientModel c R hR u ∅
        = fun z => (((bp : (Fin (n + 1) → ℂ) → ℝ) z : ℂ)) * u z := by
      funext z
      rw [deningerQuotientModel, if_pos rfl]
    rw [hfun]
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z ∈ Metric.ball c R
    · exact ((Complex.ofRealCLM.contDiff.comp bp.contDiff).contDiffAt).mul
        (((hu z hz).contDiffAt).restrict_scalars ℝ)
    · have hout : (fun w => (((bp : (Fin (n + 1) → ℂ) → ℝ) w : ℂ)) * u w)
          =ᶠ[nhds z] fun _ => (0 : ℂ) := by
        have hopen : IsOpen ((Metric.closedBall c (R / 2))ᶜ) :=
          Metric.isClosed_closedBall.isOpen_compl
        have hzc : z ∈ (Metric.closedBall c (R / 2))ᶜ := by
          intro hzin
          exact hz (Metric.mem_ball.2
            (lt_of_le_of_lt (Metric.mem_closedBall.1 hzin) (by linarith)))
        filter_upwards [hopen.mem_nhds hzc] with w hw
        have hbz : (bp : (Fin (n + 1) → ℂ) → ℝ) w = 0 := by
          by_contra hne
          have hsupp : w ∈ Function.support (bp : (Fin (n + 1) → ℂ) → ℝ) := hne
          rw [bp.support_eq] at hsupp
          exact hw (Metric.ball_subset_closedBall hsupp)
        rw [hbz]
        norm_num
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hout
  · rw [show deningerQuotientModel c R hR u S = fun _ => (0 : ℂ) from funext fun w => if_neg hS]
    exact contDiff_const

theorem setDbar_deningerQuotientModel {c : Fin (n + 1) → ℂ} {R : ℝ} (hR : 0 < R)
    {u : (Fin (n + 1) → ℂ) → ℂ} (hu : AnalyticOnNhd ℂ u (Metric.ball c R))
    {z : Fin (n + 1) → ℂ} (hz : z ∈ Metric.ball c (R / 3)) (S : Finset (Fin (n + 1))) :
    setDbar (deningerQuotientModel c R hR u) S z = 0 := by
  refine Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ ?_
  by_cases hk : S.erase k = ∅
  · rw [hk]
    have heq : deningerQuotientModel c R hR u ∅ =ᶠ[nhds z] u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact deningerQuotientModel_eq_of_mem hR (Metric.ball_subset_closedBall hw)
    rw [dzbarAt_congr_of_eventuallyEq heq]
    exact dzbarAt_eq_zero_of_differentiableAt
      ((hu z (Metric.ball_subset_ball (by linarith) hz)).differentiableAt) k
  · rw [show deningerQuotientModel c R hR u (S.erase k) = fun _ => (0 : ℂ) from
      funext fun w => if_neg hk]
    exact dzbarAt_zero k z

set_option maxHeartbeats 1000000 in
/-- **Multiplication by the last coordinate is locally surjective onto the ideal sheaf of its
divisor.**  A section vanishing on the divisor is, near each point, the coordinate times a
holomorphic function: its local model is analytic, the division theorem divides it on a polydisc
centred at the point, and a bump turns the quotient into a global smooth model. -/
theorem deningerCoordMulVanish_locallySurjective (Ω : Opens (Fin (n + 1) → ℂ)) :
    TopCat.Presheaf.IsLocallySurjective (deningerCoordMulVanish Ω).1 := by
  refine (TopCat.Presheaf.isLocallySurjective_iff _).2 ?_
  intro U h x hx
  obtain ⟨g, N, hg, hgd, hNopen, hxN, hNeq⟩ := h.2.1.1.exists_model_open ⟨x, hx⟩
  set Wset : Set (Fin (n + 1) → ℂ) := N ∩ (deningerAmb U : Set (Fin (n + 1) → ℂ)) with hWdef
  have hWopen : IsOpen Wset := hNopen.inter (deningerAmb U).2
  have hxW : (x.1 : Fin (n + 1) → ℂ) ∈ Wset := ⟨hxN, deningerAmb_mem_of_mem (⟨x, hx⟩ : ↥U)⟩
  have hdz : ∀ z ∈ Wset, ∀ j, dzbarAt (g ∅) j z = 0 := fun z hz j =>
    deningerDivisorModel_dzbar_eq_zero h.2.1 hNopen hNeq hz.1 hz.2 j
  have han : AnalyticOnNhd ℂ (g ∅) Wset :=
    analyticOnNhd_of_dzbarAt_eq_zero_on (hg.differentiable ∅) hWopen hdz
  have hvan : ∀ z ∈ Wset, z (Fin.last n) = 0 → g ∅ z = 0 := by
    intro z hz hz0
    rw [← hNeq z hz.1 ∅, deningerExtend_of_mem h.1 hz.2]
    exact h.2.2 (deningerPt hz.2) ∅ (by rw [deningerPt_val hz.2]; exact hz0)
  obtain ⟨R, hR, hRsub, u, hu, humul⟩ := exists_local_coord_quotient hWopen han hvan hxW
  set V : Opens (deningerSpace Ω) :=
    deningerRestrictOpen Ω ⟨Metric.ball (x.1 : Fin (n + 1) → ℂ) (R / 3), Metric.isOpen_ball⟩ ⊓ U
    with hVdef
  have hxV : x ∈ V := ⟨Metric.mem_ball_self (by linarith), hx⟩
  have hamb : ∀ z ∈ deningerAmb V, z ∈ Metric.ball (x.1 : Fin (n + 1) → ℂ) (R / 3) := fun z hz =>
    deningerAmb_restrictOpen_le hz
  have hmodel : ∀ y : ↥V, ∀ᶠ z in nhds ((y.1.1 : Fin (n + 1) → ℂ)), ∀ S,
      deningerExtend (fun w : ↥V => fun S => if S = ∅ then u (w.1.1 : Fin (n + 1) → ℂ) else 0)
        z S = deningerQuotientModel (x.1 : Fin (n + 1) → ℂ) R hR u S z := by
    intro y
    filter_upwards [(deningerAmb V).2.mem_nhds (deningerAmb_mem_of_mem y)] with z hz
    intro S
    rw [deningerExtend_of_mem _ hz]
    by_cases hS : S = ∅
    · subst hS
      show (if (∅ : Finset (Fin (n + 1))) = ∅ then u ((deningerPt hz).1.1 : Fin (n + 1) → ℂ)
        else 0) = _
      rw [if_pos rfl, deningerPt_val hz,
        deningerQuotientModel_eq_of_mem hR (Metric.ball_subset_closedBall (hamb z hz))]
    · show (if S = ∅ then u ((deningerPt hz).1.1 : Fin (n + 1) → ℂ) else 0) = _
      rw [if_neg hS, deningerQuotientModel, if_neg hS]
  refine ⟨V, inf_le_right,
    ⟨⟨fun y => fun S => if S = ∅ then u (y.1.1 : Fin (n + 1) → ℂ) else 0, ?_⟩, ?_⟩, hxV⟩
  · refine ⟨⟨fun y S hS => if_neg (fun hc => hS (by rw [hc]; rfl)), fun y => ?_⟩, fun y S => ?_⟩
    · exact ⟨deningerQuotientModel (x.1 : Fin (n + 1) → ℂ) R hR u,
        deningerQuotientModel_smooth hR hu, deningerQuotientModel_deg _ _ hR u, hmodel y⟩
    · rw [deningerSetDbar_model (hmodel y) S]
      exact setDbar_deningerQuotientModel hR hu (hamb _ (deningerAmb_mem_of_mem y)) S
  · refine Subtype.ext (funext fun y => funext fun S => ?_)
    show (y.1.1 : Fin (n + 1) → ℂ) (Fin.last n)
      * (if S = ∅ then u (y.1.1 : Fin (n + 1) → ℂ) else 0) = h.1 ⟨y.1, y.2.2⟩ S
    by_cases hS : S = ∅
    · subst hS
      have hball : (y.1.1 : Fin (n + 1) → ℂ) ∈ Metric.ball (x.1 : Fin (n + 1) → ℂ) R :=
        Metric.ball_subset_ball (by linarith) y.2.1
      have hzN : (y.1.1 : Fin (n + 1) → ℂ) ∈ N := (hRsub hball).1
      rw [if_pos rfl, humul _ hball, ← hNeq _ hzN ∅,
        deningerExtend_apply h.1 (⟨y.1, y.2.2⟩ : ↥U)]
    · rw [if_neg hS, mul_zero]
      exact (h.2.1.1.1 ⟨y.1, y.2.2⟩ S (fun hc => hS (Finset.card_eq_zero.1 hc))).symm

end Surjective

end RHTower

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat Complex HTGeometry

section Exactness

variable {n : ℕ} {Ω : Opens (Fin (n + 1) → ℂ)} {Ω' : Opens (Fin n → ℂ)}
  (hmap : ∀ w ∈ Ω', deningerDivisorMap w ∈ Ω)

theorem deningerCoordMulVanish_epi (Ω : Opens (Fin (n + 1) → ℂ)) :
    Epi (deningerCoordMulVanish Ω) :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi _).1 (deningerCoordMulVanish_locallySurjective Ω)

/-- **Multiplication by the coordinate is an isomorphism onto the ideal sheaf of its divisor.** -/
instance deningerCoordMulVanish_isIso (Ω : Opens (Fin (n + 1) → ℂ)) :
    IsIso (deningerCoordMulVanish Ω) := by
  haveI := deningerCoordMulVanish_mono Ω
  haveI := deningerCoordMulVanish_epi Ω
  exact isIso_of_mono_of_epi _

/-- **Multiplication by the last coordinate is a kernel of restriction to its divisor.** -/
noncomputable def deningerCoordMul_isKernel
    (hfull : ∀ w : Fin n → ℂ, deningerDivisorMap w ∈ Ω → w ∈ Ω') :
    IsLimit (KernelFork.ofι (deningerCoordMul Ω 0 (Fin.last n))
      (deningerCoordMul_comp_restrict hmap)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {_} k hk => deningerVanishKernelLift hmap hfull k hk ≫ inv (deningerCoordMulVanish Ω))
    (fun {_} k hk => by
      rw [← deningerCoordMulVanish_comp Ω, Category.assoc, IsIso.inv_hom_id_assoc]
      exact deningerVanishKernelLift_comp hmap hfull k hk)
    (fun {_} k hk l hl => by
      haveI := deningerCoordMul_mono Ω 0 (Fin.last n)
      refine (cancel_mono (deningerCoordMul Ω 0 (Fin.last n))).1 ?_
      rw [hl, ← deningerCoordMulVanish_comp Ω, Category.assoc, IsIso.inv_hom_id_assoc]
      exact (deningerVanishKernelLift_comp hmap hfull k hk).symm)

/-- The ideal sequence of the divisor of the last coordinate. -/
noncomputable def deningerIdealSequence :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω)) :=
  ShortComplex.mk (deningerCoordMul Ω 0 (Fin.last n)) (deningerDivisorRestrict hmap)
    (deningerCoordMul_comp_restrict hmap)

theorem deningerIdealSequence_exact
    (hfull : ∀ w : Fin n → ℂ, deningerDivisorMap w ∈ Ω → w ∈ Ω') :
    (deningerIdealSequence hmap).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (deningerCoordMul_isKernel hmap hfull)

/-- **The ideal sequence of a coordinate divisor is short exact**:
`0 → O --·z--> O --restrict--> i_* O_D → 0`. -/
theorem deningerIdealSequence_shortExact
    (hfull : ∀ w : Fin n → ℂ, deningerDivisorMap w ∈ Ω → w ∈ Ω') :
    (deningerIdealSequence hmap).ShortExact where
  exact := deningerIdealSequence_exact hmap hfull
  mono_f := deningerCoordMul_mono Ω 0 (Fin.last n)
  epi_g := deningerDivisorRestrict_epi hmap hfull

end Exactness

end RHTower

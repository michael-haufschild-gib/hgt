import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ThetaLiftBaseRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TorsionThetaLifts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ThetaCommutatorScalar
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ThetaCommutatorRoots
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELWeilUniqueness

/-! Scalar commutators of local theta lifts agree on overlaps and define the Weil pairing. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

private noncomputable def overIncl {V U : T.left.Opens} (h : V ≤ U) : overRes V ⟶ overRes U :=
  Over.homMk (T.left.homOfLE h)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ T.hom) (T.left.homOfLE_ι h)))

@[reassoc]
private theorem overIncl_comp {V U : T.left.Opens} (h : V ≤ U) :
    overIncl h ≫ overResι U = overResι V :=
  Over.OverMorphism.ext (T.left.homOfLE_ι h)

private theorem restrict_topIso_hom {X : Scheme.{0}} {V U : X.Opens} (h : V ≤ U)
    (c : Γ(U.toScheme, ⊤)ˣ) :
    res h (Units.map U.topIso.hom.hom.toMonoidHom c) =
      Units.map V.topIso.hom.hom.toMonoidHom (Units.map (X.homOfLE h).appTop.hom.toMonoidHom c) := by
  apply Units.ext
  let F : X.Opensᵒᵖ ⥤ CommRingCat := X.presheaf
  have he : U.topIso.hom ≫ F.map (homOfLE h).op =
      (X.homOfLE h).appTop ≫ V.topIso.hom := by
    rw [X.homOfLE_appTop]
    change F.map (eqToHom U.ι_image_top.symm).op ≫ F.map (homOfLE h).op =
      F.map (homOfLE (X.ι_image_homOfLE_le_ι_image h ⊤)).op ≫
        F.map (eqToHom V.ι_image_top.symm).op
    rw [← F.map_comp, ← F.map_comp]
    rfl
  exact congrArg (fun q : Γ(U.toScheme, ⊤) ⟶ Γ(X, V) => q c.val) he

private theorem unitRes_topIso_hom (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) :
    Units.map V.topIso.hom.hom.toMonoidHom (unitRes V c) = res le_top c := by
  apply Units.ext
  let F : T.left.Opensᵒᵖ ⥤ CommRingCat := T.left.presheaf
  have he : V.ι.appTop ≫ V.topIso.hom = F.map (homOfLE (le_top : V ≤ ⊤)).op := by
    change F.map (homOfLE (x := V.ι ''ᵁ ⊤) le_top).op ≫ F.map (eqToHom V.ι_image_top.symm).op = _
    rw [← F.map_comp]
    rfl
  exact congrArg (fun q : Γ(T.left, ⊤) ⟶ Γ(T.left, V) => q c.val) he

private theorem unitRes_of_overIncl {V U : T.left.Opens} (h : V ≤ U) (c : Γ(T.left, ⊤)ˣ) :
    Units.map (overIncl h).left.appTop.hom.toMonoidHom (unitRes U c) = unitRes V c := by
  apply Units.ext
  change (T.left.homOfLE h).appTop (U.ι.appTop c.val) = V.ι.appTop c.val
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]

private theorem scalar_eq_on_overlap (hA : IsAbelianScheme A) (hL : L.IsLB)
    {U V : T.left.Opens} {x y : T ⟶ A}
    {x₁ y₁ : ThetaGrp A L k (overRes U)} {x₂ y₂ : ThetaGrp A L k (overRes V)}
    (hx₁ : x₁.pt = overResι U ≫ x) (hy₁ : y₁.pt = overResι U ≫ y)
    (hx₂ : x₂.pt = overResι V ≫ x) (hy₂ : y₂.pt = overResι V ≫ y)
    {c : Γ(U.toScheme, ⊤)ˣ} {d : Γ(V.toScheme, ⊤)ˣ}
    (hc : CommIsOf A L k x₁ y₁ c) (hd : CommIsOf A L k x₂ y₂ d) :
    Units.map (overIncl (inf_le_left : U ⊓ V ≤ U)).left.appTop.hom.toMonoidHom c =
      Units.map (overIncl (inf_le_right : U ⊓ V ≤ V)).left.appTop.hom.toMonoidHom d := by
  let a := overIncl (inf_le_left : U ⊓ V ≤ U)
  let b := overIncl (inf_le_right : U ⊓ V ≤ V)
  obtain ⟨x₁', e₁, v₁⟩ := exists_theta_restrict hL a x₁
  obtain ⟨y₁', f₁, w₁⟩ := exists_theta_restrict hL a y₁
  obtain ⟨x₂', e₂, v₂⟩ := exists_theta_restrict hL b x₂
  obtain ⟨y₂', f₂, w₂⟩ := exists_theta_restrict hL b y₂
  have ex : x₂'.pt = x₁'.pt := by
    rw [e₂, hx₂, e₁, hx₁]
    simp only [a, b, overIncl_comp_assoc]
  have ey : y₂'.pt = y₁'.pt := by
    rw [f₂, hy₂, f₁, hy₁]
    simp only [a, b, overIncl_comp_assoc]
  exact commIsOf_scalar_unique hL
    (commIsOf_of_same_points hA hL ex ey (commIsOf_of_restrict hL a e₁ f₁ v₁ w₁ hc))
    (commIsOf_of_restrict hL b e₂ f₂ v₂ w₂ hd)

/-- Two Weil scalars agree because their local commutators agree on every overlap. -/
theorem weilIs_unique_of_local_lifts (hA : IsAbelianScheme A) (hL : L.IsLB)
    {x y : T ⟶ A} {c d : Γ(T.left, ⊤)ˣ}
    (hc : WeilIs A L k x y c) (hd : WeilIs A L k x y d) : c = d := by
  apply unit_ext
  intro p _
  obtain ⟨U, hpU, ⟨x₁, y₁, hx₁, hy₁⟩, h₁⟩ := hc p
  obtain ⟨V, hpV, ⟨x₂, y₂, hx₂, hy₂⟩, h₂⟩ := hd p
  have he := scalar_eq_on_overlap hA hL hx₁ hy₁ hx₂ hy₂ (h₁ x₁ y₁ hx₁ hy₁) (h₂ x₂ y₂ hx₂ hy₂)
  rw [unitRes_of_overIncl, unitRes_of_overIncl] at he
  have er : res (le_top : U ⊓ V ≤ ⊤) c = res (le_top : U ⊓ V ≤ ⊤) d :=
    (unitRes_topIso_hom (U ⊓ V) c).symm.trans
      ((congrArg (Units.map (U ⊓ V).topIso.hom.hom.toMonoidHom) he).trans (unitRes_topIso_hom (U ⊓ V) d))
  have hp : (𝟙 T.left : T.left ⟶ T.left) p ∈ U ⊓ V := ⟨hpU, hpV⟩
  exact (gm_res (𝟙 T.left) p le_top hp c).symm.trans
    ((congrArg (gm (𝟙 T.left) p (U ⊓ V)) er).trans (gm_res (𝟙 T.left) p le_top hp d))

/-- Any pair of points admitting local theta lifts has a unique global Weil scalar. -/
theorem existsUnique_weilIs_of_local_lifts (hA : IsAbelianScheme A) (hL : L.IsLB)
    (x y : T ⟶ A)
    (hx : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      ∃ θ : ThetaGrp A L k (overRes U), θ.pt = overResι U ≫ x)
    (hy : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      ∃ θ : ThetaGrp A L k (overRes U), θ.pt = overResι U ≫ y) :
    ∃! c : Γ(T.left, ⊤)ˣ, WeilIs A L k x y c := by
  have hloc (p : T.left) : ∃ W : T.left.Opens, p ∈ W ∧
      ∃ u v : ThetaGrp A L k (overRes W), u.pt = overResι W ≫ x ∧ v.pt = overResι W ≫ y := by
    obtain ⟨U, hpU, u, hu⟩ := hx p
    obtain ⟨V, hpV, v, hv⟩ := hy p
    obtain ⟨u', eu, -⟩ := exists_theta_restrict hL (overIncl (inf_le_left : U ⊓ V ≤ U)) u
    obtain ⟨v', ev, -⟩ := exists_theta_restrict hL (overIncl (inf_le_right : U ⊓ V ≤ V)) v
    exact ⟨U ⊓ V, ⟨hpU, hpV⟩, u', v', by rw [eu, hu, overIncl_comp_assoc],
      by rw [ev, hv, overIncl_comp_assoc]⟩
  choose W hW u v eu ev using hloc
  choose c hc using fun p => exists_commIsOf hA hL (u p) (v p)
  let a (p : T.left) : Γ(T.left, W p)ˣ := Units.map (W p).topIso.hom.hom.toMonoidHom (c p)
  have hcov : (⊤ : T.left.Opens) ≤ ⨆ p, W p := fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hW p⟩
  obtain ⟨s, hs, -⟩ := existsUnique_glueUnits W (fun _ => le_top) hcov a fun p q => by
    have h := scalar_eq_on_overlap hA hL (eu p) (ev p) (eu q) (ev q) (hc p) (hc q)
    exact (restrict_topIso_hom inf_le_left (c p)).trans
      ((congrArg (Units.map (W p ⊓ W q).topIso.hom.hom.toMonoidHom) h).trans
        (restrict_topIso_hom inf_le_right (c q)).symm)
  have hw : WeilIs A L k x y s := by
    intro p
    refine ⟨W p, hW p, ⟨u p, v p, eu p, ev p⟩, fun u' v' hu' hv' => ?_⟩
    have he : unitRes (W p) s = c p := by
      apply Units.map_injective
        (show Function.Injective (W p).topIso.hom.hom.toMonoidHom from
          (W p).topIso.commRingCatIsoToRingEquiv.injective)
      exact (unitRes_topIso_hom (W p) s).trans (hs p)
    rw [he]
    exact commIsOf_of_same_points hA hL (hu'.trans (eu p).symm) (hv'.trans (ev p).symm) (hc p)
  exact ⟨s, hw, fun _ hd => weilIs_unique_of_local_lifts hA hL hd hw⟩

/-- Torsion points admit a Weil scalar at the tensor exponent that kills them. -/
theorem existsUnique_weilIs_of_pow_eq_one (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hAmp : RelAmple A L) (x y : T ⟶ A) (n : ℕ) (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃! c : Γ(T.left, ⊤)ˣ, WeilIs A L (n : ℤ) x y c :=
  existsUnique_weilIs_of_local_lifts hA hL x y
    (AbLaw.Cube.exists_local_theta_lift_of_pow_eq_one hA hL hAmp x n hx)
    (AbLaw.Cube.exists_local_theta_lift_of_pow_eq_one hA hL hAmp y n hy)

private theorem eq_one_of_locally_unitRes_eq_one {c : Γ(T.left, ⊤)ˣ}
    (h : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧ unitRes U c = 1) : c = 1 := by
  apply unit_ext
  intro p _
  obtain ⟨U, hp, hU⟩ := h p
  have he : res (le_top : U ≤ ⊤) c = 1 := (unitRes_topIso_hom U c).symm.trans
    ((congrArg (Units.map U.topIso.hom.hom.toMonoidHom) hU).trans (map_one _))
  rw [← gm_res (𝟙 T.left) p le_top (show (𝟙 T.left : T.left ⟶ T.left) p ∈ U from hp) c,
    he, map_one, map_one]

/-- Taking the Weil pairing with a point killed by n gives an n-th root of unity. -/
theorem weilIs_pow_eq_one_of_pow_eq_one (hA : IsAbelianScheme A) (hL : L.IsLB)
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs A L k x y c) {n : ℕ} (hx : x ^ n = 1) :
    c ^ n = 1 := by
  letI := hA.comm
  apply eq_one_of_locally_unitRes_eq_one
  intro p
  obtain ⟨U, hp, ⟨u, v, hu, hv⟩, h⟩ := hc p
  have hpow : u.pt ^ n = 1 := by
    rw [hu, ← MonObj.comp_pow, hx, MonObj.comp_one]
  have e : unitRes U (c ^ n) = (unitRes U c) ^ n :=
    (Units.map U.ι.appTop.hom.toMonoidHom).map_pow c n
  exact ⟨U, hp, e.trans (commIsOf_pow_eq_one hA hL (h u v hu hv) hpow)⟩

/-- The Weil scalar inverts when the two arguments are exchanged. -/
theorem weilIs_swap_of_local_lifts (hA : IsAbelianScheme A) (hL : L.IsLB)
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs A L k x y c) :
    WeilIs A L k y x c⁻¹ := by
  letI := hA.comm
  intro p
  obtain ⟨U, hp, ⟨u, v, hu, hv⟩, h⟩ := hc p
  refine ⟨U, hp, ⟨v, u, hv, hu⟩, fun v' u' hv' hu' => ?_⟩
  have e : unitRes U c⁻¹ = (unitRes U c)⁻¹ :=
    (Units.map U.ι.appTop.hom.toMonoidHom).map_inv c
  exact e.symm ▸ commIsOf_swap hL (h u' v' hu' hv')

/-- Pairing a point with itself gives the identity scalar. -/
theorem weilIs_self_eq_one (hL : L.IsLB) {x : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (hc : WeilIs A L k x x c) : c = 1 := by
  apply eq_one_of_locally_unitRes_eq_one
  intro p
  obtain ⟨U, hp, ⟨u, _, hu, _⟩, h⟩ := hc p
  have hone : CommIsOf A L k u u 1 :=
    (commIsOf_iff hL _ _ _).2 fun Z r z J hJ => by rw [map_one, _root_.mul_one]
  exact ⟨U, hp, commIsOf_scalar_unique hL (h u u hu hu) hone⟩

/-- The Weil scalar multiplies when multiplying the first two points paired with a third. -/
theorem weilIs_mul_left_of_local_lifts (hA : IsAbelianScheme A) (hL : L.IsLB)
    {x y z : T ⟶ A} {c d : Γ(T.left, ⊤)ˣ}
    (hc : WeilIs A L k x z c) (hd : WeilIs A L k y z d) :
    WeilIs A L k (x * y) z (c * d) := by
  letI := hA.comm
  intro p
  obtain ⟨U, hpU, ⟨x₀, z₀, hx₀, hz₀⟩, h₁⟩ := hc p
  obtain ⟨V, hpV, ⟨y₀, z₁, hy₀, hz₁⟩, h₂⟩ := hd p
  let W := U ⊓ V
  let a := overIncl (show W ≤ U from inf_le_left)
  let b := overIncl (show W ≤ V from inf_le_right)
  obtain ⟨x', hx', vx⟩ := exists_theta_restrict hL a x₀
  obtain ⟨z', hz', vz⟩ := exists_theta_restrict hL a z₀
  obtain ⟨y', hy', vy⟩ := exists_theta_restrict hL b y₀
  obtain ⟨z'', hz'', vz'⟩ := exists_theta_restrict hL b z₁
  have hx : x'.pt = overResι W ≫ x := by
    rw [hx', hx₀]
    simp only [a, overIncl_comp_assoc]
  have hy : y'.pt = overResι W ≫ y := by
    rw [hy', hy₀]
    simp only [b, overIncl_comp_assoc]
  have hz : z'.pt = overResι W ≫ z := by
    rw [hz', hz₀]
    simp only [a, overIncl_comp_assoc]
  have hz'₂ : z''.pt = overResι W ≫ z := by
    rw [hz'', hz₁]
    simp only [b, overIncl_comp_assoc]
  have hX := commIsOf_of_restrict hL a hx' hz' vx vz (h₁ x₀ z₀ hx₀ hz₀)
  have hY := commIsOf_of_restrict hL b hy' hz'' vy vz' (h₂ y₀ z₁ hy₀ hz₁)
  have hX' : CommIsOf A L k x' z' (unitRes W c) :=
    (unitRes_of_overIncl (show W ≤ U from inf_le_left) c) ▸ hX
  have hY' : CommIsOf A L k y' z' (unitRes W d) :=
    commIsOf_of_same_points hA hL rfl (hz.trans hz'₂.symm)
      ((unitRes_of_overIncl (show W ≤ V from inf_le_right) d) ▸ hY)
  obtain ⟨w, hw, h⟩ := exists_commIsOf_mul_left hL hX' hY'
  have hw' : w.pt = overResι W ≫ (x * y) := by rw [hw, hx, hy, MonObj.comp_mul]
  refine ⟨W, ⟨hpU, hpV⟩, ⟨w, z', hw', hz⟩, fun u v hu hv => ?_⟩
  have e : unitRes W (c * d) = unitRes W c * unitRes W d :=
    (Units.map W.ι.appTop.hom.toMonoidHom).map_mul c d
  exact e.symm ▸ commIsOf_of_same_points hA hL (hu.trans hw'.symm) (hv.trans hz.symm) h

end GlobalTheory.CommPairing

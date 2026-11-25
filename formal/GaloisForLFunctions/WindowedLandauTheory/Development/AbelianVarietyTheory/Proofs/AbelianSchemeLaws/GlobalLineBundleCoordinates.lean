import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionSheaf

/-! Global sections of the glued module are the compatible chart coordinates of the bundle. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {L : LB X}

private def toCoordinates (s : Γ(toMod L, ⊤)) : L.Sec where
  f i := resG X (le_inf le_top le_rfl) (coord s i)
  compat i j := by
    let W := L.U i ⊓ L.U j
    have h := coord_rel s i j (W := W)
      (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl
    rw [resG_self] at h
    change resG X inf_le_left (resG X (le_inf le_top le_rfl) (coord s i)) =
      (L.g i j : Γ(X, W)) * resG X inf_le_right (resG X (le_inf le_top le_rfl) (coord s j))
    rw [resG_resG, resG_resG]
    exact h

private def ofCoordinates (s : L.Sec) : Γ(toMod L, ⊤) :=
  mkSec (fun i => resG X inf_le_right (s.f i)) fun i j => by
    let W := (⊤ : X.Opens) ⊓ L.U i ⊓ L.U j
    let h : W ≤ L.U i ⊓ L.U j := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have e : resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s.f i) =
        (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
          resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (s.f j) := s.compat i j
    have he := congrArg (resG X h) e
    simp only [map_mul, resG_resG] at he
    change resG X inf_le_left (resG X inf_le_right (s.f i)) =
      resG X h (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
        resG X (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (resG X inf_le_right (s.f j))
    rw [resG_resG, resG_resG]
    exact he

/-- The two section descriptions differ by restricting along `⊤ ⊓ U = U` in each chart. -/
def globalCoordinates : Γ(toMod L, ⊤) ≃ L.Sec where
  toFun := toCoordinates
  invFun := ofCoordinates
  left_inv s := sec_ext fun i => by
    change resG X inf_le_right (resG X (le_inf le_top le_rfl) (coord s i)) = coord s i
    rw [resG_resG, resG_self]
  right_inv s := by
    cases s with
    | mk vals compat =>
      congr 1
      funext i
      change resG X (le_inf le_top le_rfl) (resG X inf_le_right (vals i)) = vals i
      rw [resG_resG, resG_self]

theorem globalCoordinates_apply (s : Γ(toMod L, ⊤)) (i : L.ι) :
    (globalCoordinates s).f i = resG X (le_inf le_top le_rfl) (coord s i) := rfl

theorem exists_gen_of_unit_coordinates (s : Γ(toMod L, ⊤))
    (h : ∀ i, IsUnit ((globalCoordinates s).f i)) :
    ∃ t : L.Gen, t.IsGen := by
  refine ⟨⟨fun i => (h i).unit⟩, fun i j => ?_⟩
  apply Units.ext
  simpa only [res, Units.coe_map, IsUnit.unit_spec, Units.val_mul] using (globalCoordinates s).compat i j

/-- Being a generator can be checked in one chosen bundle coordinate on each member of a cover. -/
theorem exists_gen_of_nonvanishing_coordinates (s : Γ(toMod L, ⊤)) {I : Type}
    (W : I → X.Opens) (c : I → L.ι) (hle : ∀ i, W i ≤ L.U (c i))
    (hu : ∀ y : X, ∃ i, y ∈ X.basicOpen (resG X (hle i) ((globalCoordinates s).f (c i)))) :
    ∃ t : L.Gen, t.IsGen := by
  let a := globalCoordinates s
  apply exists_gen_of_unit_coordinates s
  intro j
  change IsUnit (a.f j)
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro y hy
  obtain ⟨i, hi⟩ := hu y
  have hyi := X.basicOpen_le _ hi
  let V := W i ⊓ L.U j
  have hv : y ∈ V := ⟨hyi, hy⟩
  have h₁ : V ≤ L.U j := inf_le_right
  have h₂ : V ≤ L.U (c i) := inf_le_left.trans (hle i)
  have hcompat : resG X (inf_le_left : L.U j ⊓ L.U (c i) ≤ L.U j) (a.f j) =
      (L.g j (c i) : Γ(X, L.U j ⊓ L.U (c i))) *
        resG X (inf_le_right : L.U j ⊓ L.U (c i) ≤ L.U (c i)) (a.f (c i)) :=
    a.compat j (c i)
  have e := congrArg (resG X (le_inf h₁ h₂)) hcompat
  simp only [map_mul, resG_resG] at e
  let germ := X.presheaf.germ V y hv
  have hu₂ : IsUnit (germ (resG X h₂ (a.f (c i)))) := by
    have hh := (X.mem_basicOpen _ y hyi).1 hi
    rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : V ≤ W i)) y hv] at hh
    change IsUnit (germ (resG X (inf_le_left : V ≤ W i) (resG X (hle i) (a.f (c i))))) at hh
    rwa [resG_resG] at hh
  change IsUnit (X.presheaf.germ (L.U j) y hy (a.f j))
  rw [← X.presheaf.germ_res_apply (homOfLE h₁) y hv]
  change IsUnit (germ (resG X h₁ (a.f j)))
  rw [e, map_mul]
  exact (((L.g j (c i)).isUnit.map (resG X (le_inf h₁ h₂))).map germ.hom).mul hu₂

/-- Dividing by a trivializing section glues its local quotients to a global function. -/
theorem section_proportional_to_gen (hL : L.IsLB) (s : L.Sec) (t : L.Gen) (ht : t.IsGen) :
    ∃ a : Γ(X, ⊤), ∀ i, s.f i = resG X le_top a * (t.s i).val := by
  let q (i : L.ι) := s.f i * ((t.s i)⁻¹).val
  obtain ⟨a, ha⟩ := exists_fun_of_cover L.U (fun _ => le_top) hL.cover.ge q (by
    intro i j
    have h := congrArg (fun u => u⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at h
    have hi : resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) ((t.s i)⁻¹).val =
        ((L.g i j)⁻¹).val * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) ((t.s j)⁻¹).val :=
      congrArg Units.val h
    have hs : resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s.f i) =
        (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X inf_le_right (s.f j) := s.compat i j
    dsimp only [q]
    rw [map_mul, map_mul, hs, hi, mul_mul_mul_comm, Units.mul_inv, one_mul])
  refine ⟨a, fun i => ?_⟩
  rw [ha i, q, Units.inv_mul_cancel_right]

theorem globalSection_ext_on_coordinates (s t : L.Sec) {I : Type}
    (W : I → X.Opens) (c : I → L.ι) (hle : ∀ i, W i ≤ L.U (c i)) (hc : ⨆ i, W i = ⊤)
    (h : ∀ i, resG X (hle i) (s.f (c i)) = resG X (hle i) (t.f (c i))) : s = t := by
  have he : s.f = t.f := funext fun j => by
    refine fun_ext_of_cover (fun i => L.U j ⊓ W i) (fun _ => inf_le_left)
      (by rw [← inf_iSup_eq, hc, inf_top_eq]) fun i => ?_
    have e₁ := congrArg (resG X (inf_le_inf_left (L.U j) (hle i))) (s.compat j (c i))
    have e₂ := congrArg (resG X (inf_le_inf_left (L.U j) (hle i))) (t.compat j (c i))
    have e₃ := congrArg (resG X (inf_le_right : L.U j ⊓ W i ≤ W i)) (h i)
    change resG X _ (resG X inf_le_left (s.f j)) = resG X _
      ((L.g j (c i) : Γ(X, L.U j ⊓ L.U (c i))) * resG X inf_le_right (s.f (c i))) at e₁
    change resG X _ (resG X inf_le_left (t.f j)) = resG X _
      ((L.g j (c i) : Γ(X, L.U j ⊓ L.U (c i))) * resG X inf_le_right (t.f (c i))) at e₂
    simp only [map_mul, resG_resG] at e₁ e₂ e₃
    rw [e₁, e₂, e₃]
  cases s
  cases t
  cases he
  rfl

end GlobalTheory.LineBundleSections

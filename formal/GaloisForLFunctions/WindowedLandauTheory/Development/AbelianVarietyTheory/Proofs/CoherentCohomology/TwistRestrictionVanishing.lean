import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwistPowers
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalLineBundleCoordinates

/-! A twisted section vanishing on a nonvanishing open is killed by a power of its defining section. -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {L : LB X}

/-- A compact scheme admits a finite affine cover refining any line-bundle cover. -/
theorem exists_finite_affine_refinement [CompactSpace X] (hL : L.IsLB) :
    ∃ (ι : Type) (_ : Fintype ι) (W : ι → X.Opens) (p : ι → L.ι),
      (∀ i, IsAffineOpen (W i)) ∧ (∀ i, W i ≤ L.U (p i)) ∧ ⨆ i, W i = ⊤ := by
  classical
  have h (x : X) : ∃ (W : X.Opens) (p : L.ι), IsAffineOpen W ∧ x ∈ W ∧ W ≤ L.U p := by
    obtain ⟨p, hp⟩ := Opens.mem_iSup.1 (hL.cover.ge (show x ∈ (⊤ : X.Opens) from trivial))
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hp (L.U p).isOpen
    exact ⟨W, p, hW, hx, hle⟩
  choose W p hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun i => W i, fun i => p i,
    fun i => hW i, fun i => hle i, top_unique fun x _ => ?_⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, hxi⟩

theorem globalSection_eq_zero_of_refinement {ι : Type} (W : ι → X.Opens) (p : ι → L.ι)
    (hle : ∀ i, W i ≤ L.U (p i)) (hc : ⨆ i, W i = ⊤) (s : Γ(toMod L, ⊤))
    (hs : ∀ i, resG X (le_inf le_top (hle i)) (coord s (p i)) = 0) : s = 0 := by
  apply globalCoordinates.injective
  apply globalSection_ext_on_coordinates _ _ W p hle hc
  intro i
  simpa only [globalCoordinates_apply, resG_resG, coord_zero, map_zero] using hs i

variable {M H : LB X} {t d : ℤ}

theorem exists_pow_mulTwistPower_eq_zero [CompactSpace X]
    (hM : M.IsLB) (hH : H.IsLB) (s : (transitionPower H d).Sec)
    (a : Γ(toMod (twist M H t), ⊤))
    (ha : (toMod (twist M H t)).presheaf.map (homOfLE (le_top : nonzeroLocus s ≤ ⊤)).op a = 0) :
    ∃ k, mulTwistPower M s k t ⊤ a = 0 := by
  obtain ⟨ι, hι, W, p, hW, hp, hcov⟩ := exists_finite_affine_refinement (twist_isLB hM hH t)
  letI := hι
  let V := nonzeroLocus s
  let h (i : ι) : W i ≤ ⊤ ⊓ (M.U (p i).1 ⊓ H.U (p i).2) := le_inf le_top (hp i)
  let u (i : ι) : Γ(X, W i) := resG X ((hp i).trans inf_le_right) (powerCoord s (p i).2)
  let x (i : ι) : Γ(X, W i) := resG X (h i) (twistCoord a (p i))
  have kill (i : ι) : ∃ n : ℕ, u i ^ n * x i = 0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (hW i) (x i) (u i) ?_
    have hb := basicOpen_coord_restrict s (p i).2 ((hp i).trans inf_le_right)
    have hV : X.basicOpen (u i) ≤ V := hb.le.trans inf_le_left
    let L := twist M H t
    let T := X.basicOpen (u i)
    let hT : T ≤ W i := X.basicOpen_le (u i)
    let hw : T ≤ V ⊓ L.U (p i) := le_inf hV (hT.trans (hp i))
    let ψ (z : Γ(toMod L, V)) : Γ(X, T) := resG X hw (coord z (p i))
    have hψ : ψ ((toMod L).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a) =
        resG X hT (x i) := by
      change resG X hw (coord ((toMod L).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a) (p i)) =
        resG X hT (resG X (h i) (coord a (p i)))
      rw [coord_map, resG_resG, resG_resG]
      rfl
    have hzero : ψ 0 = 0 := by
      change resG X hw (coord (0 : Γ(toMod L, V)) (p i)) = 0
      rw [coord_zero, map_zero]
    exact hψ.symm.trans ((congrArg ψ ha).trans hzero)
  choose n hn using kill
  let k := Finset.univ.sup n
  refine ⟨k, globalSection_eq_zero_of_refinement (L := twist M H (t + k * d))
    W p hp hcov _ fun i => ?_⟩
  change resG X (h i) (twistCoord (mulTwistPower M s k t ⊤ a) (p i)) = 0
  rw [twistCoord_mulTwistPower, map_mul, map_pow, resG_resG]
  change u i ^ k * x i = 0
  have leN : n i ≤ k := Finset.le_sup (Finset.mem_univ i)
  rw [← Nat.sub_add_cancel leN, pow_add, mul_assoc, hn, mul_zero]

end GlobalTheory.LineBundleSections

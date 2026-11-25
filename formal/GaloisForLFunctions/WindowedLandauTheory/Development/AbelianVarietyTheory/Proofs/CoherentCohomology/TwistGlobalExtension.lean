import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistAffineExtension
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistRestrictionVanishing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleQuasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Local lifts of a twisted section glue globally after a uniform additional power. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M H : LB X}

private abbrev restrictSec (L : LB X) {U V : X.Opens} (h : V ≤ U) :
    Γ(toMod L, U) →+ Γ(toMod L, V) :=
  secRes L h

private theorem restrictSec_comp (L : LB X) {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V)
    (a : Γ(toMod L, U)) :
    restrictSec L k (restrictSec L h a) = restrictSec L (k.trans h) a := by
  apply sec_ext
  intro p
  change resG X (inf_le_inf_right _ k) (resG X (inf_le_inf_right _ h) (coord a p)) =
    resG X (inf_le_inf_right _ (k.trans h)) (coord a p)
  exact resG_resG _ _ _

private theorem restrictSec_mulTwistPower {d : ℤ} (s : (transitionPower H d).Sec) (k : ℕ) (t : ℤ)
    {V W : X.Opens} (h : W ≤ V) (a : Γ(toMod (twist M H t), V)) :
    restrictSec (twist M H (t + k * d)) h (mulTwistPower M s k t V a) =
      mulTwistPower M s k t W (restrictSec (twist M H t) h a) :=
  (mulTwistPower_restrict s k t h a).symm

private def twistDegreeCongr {t u : ℤ} (h : t = u) (V : X.Opens) :
    Γ(toMod (twist M H t), V) ≃ₗ[Γ(X, V)] Γ(toMod (twist M H u), V) := by
  subst u
  exact LinearEquiv.refl _ _

private theorem twistDegreeCongr_restrict {t u : ℤ} (e : t = u) {V W : X.Opens} (h : W ≤ V)
    (a : Γ(toMod (twist M H t), V)) :
    restrictSec (twist M H u) h (twistDegreeCongr e V a) =
      twistDegreeCongr e W (restrictSec (twist M H t) h a) := by
  subst u
  rfl

private theorem twistCoord_twistDegreeCongr {t u : ℤ} (e : t = u) {V : X.Opens}
    (a : Γ(toMod (twist M H t), V)) (p : M.ι × H.ι) :
    twistCoord (twistDegreeCongr e V a) p = twistCoord a p := by
  subst u
  rfl

private theorem mulTwistPower_comp {d : ℤ} (s : (transitionPower H d).Sec) (t : ℤ)
    (n k : ℕ) {V : X.Opens} (a : Γ(toMod (twist M H t), V))
    (e : t + (n : ℤ) * d + k * d = t + ((n + k : ℕ) : ℤ) * d) :
    twistDegreeCongr e V (mulTwistPower M s k _ V (mulTwistPower M s n t V a)) =
      mulTwistPower M s (n + k) t V a := by
  apply sec_ext
  intro p
  change twistCoord (twistDegreeCongr e V
    (mulTwistPower M s k (t + n * d) V (mulTwistPower M s n t V a))) p =
      twistCoord (mulTwistPower M s (n + k) t V a) p
  simp only [twistCoord_twistDegreeCongr, twistCoord_mulTwistPower, pow_add]
  ring

private theorem exists_pow_smul_eq_zero_of_twist_restrict {L : LB X} (hL : L.IsLB)
    {W V : X.Opens} (hW : IsAffineOpen W) (u : Γ(X, W)) (h : V ≤ W) (e : X.basicOpen u = V)
    (a : Γ(toMod L, W)) (ha : restrictSec L h a = 0) :
    ∃ k : ℕ, u ^ k • a = 0 := by
  subst V
  letI : (toMod L).IsQuasicoherent := isQuasicoherent_toMod hL
  exact (hasBasicOpenLocalization_of_isQuasicoherent (toMod L) hW u).2 a ha

/-- A section on the nonvanishing open extends after multiplication by a power
of the defining section, with the twist increased accordingly. -/
theorem exists_global_lift_mulTwistPower [CompactSpace X] [X.IsSeparated] {t d : ℤ}
    (hM : M.IsLB) (hH : H.IsLB) (s : (transitionPower H d).Sec)
    (a : Γ(toMod (twist M H t), nonzeroLocus s)) :
    ∃ (k : ℕ) (b : Γ(toMod (twist M H (t + k * d)), ⊤)),
      (toMod (twist M H (t + k * d))).presheaf.map (homOfLE le_top).op b =
        mulTwistPower M s k t (nonzeroLocus s) a := by
  obtain ⟨ι, hι, W, p, hW, hp, hcov⟩ := exists_finite_affine_refinement (twist_isLB hM hH t)
  letI := hι
  let V := nonzeroLocus s
  let A := twist M H t
  let aV (i : ι) : Γ(toMod A, V ⊓ W i) := restrictSec A inf_le_left a
  choose n lift hlift using fun i => exists_affine_lift_mulTwistPower hM hH s (hW i) (p i) (hp i) (aV i)
  let N := Finset.univ.sup n
  let L := twist M H (t + N * d)
  let b (i : ι) : Γ(toMod L, W i) := lift i N (Finset.le_sup (Finset.mem_univ i))
  have hb (i : ι) : restrictSec L (inf_le_right : V ⊓ W i ≤ W i) (b i) =
      mulTwistPower M s N t (V ⊓ W i) (aV i) := hlift i N (Finset.le_sup (Finset.mem_univ i))
  let O (i j : ι) := W i ⊓ W j
  let diff (i j : ι) : Γ(toMod L, O i j) :=
    restrictSec L inf_le_left (b i) - restrictSec L inf_le_right (b j)
  let u (i j : ι) : Γ(X, O i j) :=
    resG X ((inf_le_left.trans (hp i)).trans inf_le_right) (powerCoord s (p i).2)
  have kill (i j : ι) : ∃ k : ℕ, u i j ^ k • diff i j = 0 := by
    refine exists_pow_smul_eq_zero_of_twist_restrict (twist_isLB hM hH _) ((hW i).inf (hW j))
      (u i j) (inf_le_right : V ⊓ O i j ≤ O i j) (basicOpen_coord_restrict s _ _) (diff i j) ?_
    let hi : V ⊓ O i j ≤ V ⊓ W i := inf_le_inf_left _ inf_le_left
    let hj : V ⊓ O i j ≤ V ⊓ W j := inf_le_inf_left _ inf_le_right
    have ei := congrArg (restrictSec L hi) (hb i)
    have ej := congrArg (restrictSec L hj) (hb j)
    rw [restrictSec_comp, restrictSec_mulTwistPower, show aV i = restrictSec A inf_le_left a from rfl,
      restrictSec_comp] at ei
    rw [restrictSec_comp, restrictSec_mulTwistPower, show aV j = restrictSec A inf_le_left a from rfl,
      restrictSec_comp] at ej
    change restrictSec L inf_le_right (diff i j) = 0
    rw [show diff i j = restrictSec L inf_le_left (b i) - restrictSec L inf_le_right (b j) from rfl,
      map_sub, restrictSec_comp, restrictSec_comp, ei, ej, sub_self]
  choose k hk using fun q : ι × ι => kill q.1 q.2
  let K := Finset.univ.sup k
  have hK (i j : ι) : u i j ^ K • diff i j = 0 := by
    have hle : k (i, j) ≤ K := Finset.le_sup (Finset.mem_univ (i, j))
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hk (i, j), smul_zero]
  have hdeg : t + (N : ℤ) * d + K * d = t + ((N + K : ℕ) : ℤ) * d := by push_cast; ring
  let L' := twist M H (t + ((N + K : ℕ) : ℤ) * d)
  let c (i : ι) : Γ(toMod L', W i) :=
    twistDegreeCongr hdeg (W i) (mulTwistPower M s K _ (W i) (b i))
  have hc (i j : ι) : restrictSec L' (inf_le_left : O i j ≤ W i) (c i) =
      restrictSec L' (inf_le_right : O i j ≤ W j) (c j) := by
    have hz : mulTwistPower M s K _ (O i j) (diff i j) = 0 := by
      let hO : O i j ≤ M.U (p i).1 ⊓ H.U (p i).2 := inf_le_left.trans (hp i)
      let e := chartEquiv (twist_isLB hM hH (t + N * d)) (p i) hO
      apply (chartEquiv (twist_isLB hM hH (t + N * d + K * d)) (p i) hO).injective
      rw [chartEquiv_mulTwistPower hM hH s K (t + N * d) (p i) hO, map_zero]
      have hh := congrArg e (hK i j)
      rw [map_smul, map_zero] at hh
      exact hh
    dsimp only [c]
    rw [twistDegreeCongr_restrict, twistDegreeCongr_restrict, restrictSec_mulTwistPower,
      restrictSec_mulTwistPower]
    apply congrArg (twistDegreeCongr hdeg (O i j))
    apply sub_eq_zero.1
    rw [← map_sub]
    exact hz
  let F : TopCat.Sheaf AddCommGrpCat X.carrier := (SheafOfModules.toSheaf X.ringCatSheaf).obj (toMod L')
  obtain ⟨z, hz⟩ := (TopCat.Sheaf.existsUnique_gluing' F W ⊤
    (fun _ => homOfLE le_top) hcov.ge c hc).exists
  refine ⟨N + K, z, ?_⟩
  have hcovV : V ≤ ⨆ i, V ⊓ W i := by rw [← inf_iSup_eq, hcov, inf_top_eq]
  refine TopCat.Sheaf.eq_of_locally_eq' F (fun i => V ⊓ W i) V
    (fun _ => homOfLE inf_le_left) hcovV _ _ fun i => ?_
  change restrictSec L' inf_le_left (restrictSec L' le_top z) =
    restrictSec L' inf_le_left (mulTwistPower M s (N + K) t V a)
  have hzi : restrictSec L' (le_top : W i ≤ ⊤) z = c i := hz i
  have e := congrArg (restrictSec L' (inf_le_right : V ⊓ W i ≤ W i)) hzi
  rw [restrictSec_comp] at e
  rw [restrictSec_comp, e, restrictSec_mulTwistPower]
  dsimp only [c]
  rw [twistDegreeCongr_restrict, restrictSec_mulTwistPower, hb, mulTwistPower_comp]

end GlobalTheory.LineBundleSections

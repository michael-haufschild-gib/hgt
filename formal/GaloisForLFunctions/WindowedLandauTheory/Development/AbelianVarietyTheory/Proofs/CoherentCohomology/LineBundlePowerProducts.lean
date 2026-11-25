import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwists
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveSectionRatios

/-! Products of bundle sections cut out intersections of their nonvanishing opens. -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {H : LB X}

theorem basicOpen_coord_restrict (s : H.Sec) (i : H.ι) {W : X.Opens} (h : W ≤ H.U i) :
    X.basicOpen (resG X h (s.f i)) = nonzeroLocus s ⊓ W := by
  calc
    _ = W ⊓ X.basicOpen (s.f i) := X.basicOpen_res _ (homOfLE h).op
    _ = W ⊓ (nonzeroLocus s ⊓ H.U i) := by rw [GlobalTheory.nonzeroLocus_inf_bundleChart]
    _ = _ := by rw [inf_left_comm, inf_eq_left.mpr h]

theorem powerSec_rel {d : ℤ} (s : (transitionPower H d).Sec) (i j : H.ι)
    {W : X.Opens} (hi : W ≤ H.U i) (hj : W ≤ H.U j) :
    resG X hi (s.f i) = (res (le_inf hi hj) (H.g i j) ^ d).val * resG X hj (s.f j) := by
  let U := H.U i ⊓ H.U j
  have h₀ : resG X (inf_le_left : U ≤ H.U i) (s.f i) =
      (H.g i j ^ d).val * resG X (inf_le_right : U ≤ H.U j) (s.f j) := s.compat i j
  have h := congrArg (resG X (le_inf hi hj : W ≤ U)) h₀
  have e : resG X hi (s.f i) =
      resG X (le_inf hi hj) ((H.g i j ^ d).val) * resG X hj (s.f j) := by
    simpa only [map_mul, resG_resG] using h
  exact e.trans (congrArg (fun u : Γ(X, W)ˣ => u.val * resG X hj (s.f j))
    (map_zpow (res (le_inf hi hj)) (H.g i j) d))

def sectionProduct {ι : Type} (s : ι → H.Sec) (I : Finset ι) :
    (transitionPower H (I.card : ℤ)).Sec where
  f i := ∏ k ∈ I, (s k).f i
  compat i j := by
    let U := H.U i ⊓ H.U j
    change resG X (inf_le_left : U ≤ H.U i) (∏ k ∈ I, (s k).f i) =
      ((H.g i j) ^ (I.card : ℤ)).val * resG X (inf_le_right : U ≤ H.U j) (∏ k ∈ I, (s k).f j)
    rw [map_prod, map_prod, zpow_natCast, Units.val_pow_eq_pow_val, ← Finset.prod_const,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => (s k).compat i j

private theorem mem_basicOpen_prod {ι : Type} {U : X.Opens} (p : ι → Γ(X, U)) (I : Finset ι)
    {x : X} (hx : x ∈ U) :
    x ∈ X.basicOpen (∏ i ∈ I, p i) ↔ ∀ i ∈ I, x ∈ X.basicOpen (p i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hx
  | insert a I ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, Finset.forall_mem_insert, ← ih]
    rfl

private theorem mem_finset_inf {ι : Type} (U : ι → X.Opens) (I : Finset ι) {x : X} :
    x ∈ (⨅ i ∈ I, U i) ↔ ∀ i ∈ I, x ∈ U i := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    rw [Finset.iInf_insert, Finset.forall_mem_insert, ← ih]
    rfl

theorem nonzeroLocus_sectionProduct (hH : H.IsLB) {ι : Type} (s : ι → H.Sec) (I : Finset ι) :
    nonzeroLocus (sectionProduct s I) = ⨅ i ∈ I, nonzeroLocus (s i) := by
  apply Opens.ext
  ext x
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hH.cover.ge (show x ∈ (⊤ : X.Opens) from trivial))
  have mem_chart {L : LB X} (u : L.Sec) (k : L.ι) (hk : x ∈ L.U k) :
      x ∈ nonzeroLocus u ↔ x ∈ X.basicOpen (u.f k) := by
    rw [← GlobalTheory.nonzeroLocus_inf_bundleChart]
    exact ⟨fun h => ⟨h, hk⟩, fun h => h.1⟩
  exact (mem_chart (sectionProduct s I) j hj).trans
    ((mem_basicOpen_prod (fun i => (s i).f j) I hj).trans
      ((forall₂_congr fun i _ => (mem_chart (s i) j hj).symm).trans
        (mem_finset_inf (fun i => nonzeroLocus (s i)) I).symm))

end GlobalTheory.LineBundleSections

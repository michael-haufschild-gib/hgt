import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionSheaf
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundlePullback

/-! Section spaces on opens contained in a line-bundle chart are free of rank one. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}}
variable {L : LB X}

private theorem resG_g_self (hL : L.IsLB) (i : L.ι) {W : X.Opens} (h : W ≤ L.U i ⊓ L.U i) :
    resG X h (L.g i i : Γ(X, L.U i ⊓ L.U i)) = 1 := by
  have e := congrArg (res (h.trans inf_le_left)) (hL.g_self i)
  rw [map_one, res_res] at e
  exact congrArg Units.val e

private theorem resG_cocycle (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    resG X h₁ (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X h₂ (L.g j k : Γ(X, L.U j ⊓ L.U k)) =
      resG X h₃ (L.g i k : Γ(X, L.U i ⊓ L.U k)) := by
  have e := congrArg (res (le_inf h₁ (h₂.trans inf_le_right))) (hL.cocycle i j k)
  simp only [map_mul, res_res] at e
  exact congrArg Units.val e

def chartSec (hL : L.IsLB) (i : L.ι) : Γ(toMod L, L.U i) :=
  mkSec (fun j => resG X (le_inf inf_le_right inf_le_left) (L.g j i : Γ(X, L.U j ⊓ L.U i)))
    fun j k => by
      rw [resG_resG, resG_resG]
      exact (resG_cocycle hL j k i _ _ _).symm

@[simp] theorem coord_chartSec (hL : L.IsLB) (i j : L.ι) :
    coord (chartSec hL i) j =
      resG X (le_inf inf_le_right inf_le_left) (L.g j i : Γ(X, L.U j ⊓ L.U i)) := rfl

/-- On an open inside one chart, its coordinate identifies sections with regular functions. -/
def chartEquiv (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) :
    Γ(toMod L, V) ≃ₗ[Γ(X, V)] Γ(X, V) where
  toFun s := resG X (le_inf le_rfl h) (coord s i)
  invFun a := a • (toMod L).presheaf.map (homOfLE h).op (chartSec hL i)
  map_add' s t := map_add _ _ _
  map_smul' a s := by
    simp only [coord_smul, map_mul, resG_resG, resG_self, RingHom.id_apply, smul_eq_mul]
  left_inv s := sec_ext fun j => by
    simp only [coord_smul, coord_map, coord_chartSec, resG_resG]
    rw [mul_comm, ← coord_rel s j i le_rfl, resG_self]
  right_inv a := by
    simp only [coord_smul, coord_map, coord_chartSec, resG_resG, resG_self,
      resG_g_self hL, map_one, mul_one]

theorem chartEquiv_apply (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i)
    (s : Γ(toMod L, V)) : chartEquiv hL i h s = resG X (le_inf le_rfl h) (coord s i) := rfl

theorem chartEquiv_symm_apply (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i)
    (a : Γ(X, V)) : (chartEquiv hL i h).symm a =
      a • (toMod L).presheaf.map (homOfLE h).op (chartSec hL i) := rfl

theorem chartEquiv_map (hL : L.IsLB) (i : L.ι) {V W : X.Opens} (h : V ≤ L.U i) (h' : W ≤ V)
    (s : Γ(toMod L, V)) :
    chartEquiv hL i (h'.trans h) ((toMod L).presheaf.map (homOfLE h').op s) =
      resG X h' (chartEquiv hL i h s) := by
  simp only [chartEquiv_apply, coord_map, resG_resG]

theorem chartEquiv_change (hL : L.IsLB) (i j : L.ι) {V : X.Opens} (hi : V ≤ L.U i)
    (hj : V ≤ L.U j) (s : Γ(toMod L, V)) :
    chartEquiv hL i hi s =
      resG X (le_inf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) * chartEquiv hL j hj s :=
  coord_rel s i j _ _ _

end GlobalTheory.LineBundleSections

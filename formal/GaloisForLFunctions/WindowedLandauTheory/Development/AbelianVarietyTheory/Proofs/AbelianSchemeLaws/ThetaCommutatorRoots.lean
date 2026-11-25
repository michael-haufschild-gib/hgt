import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ThetaCommutatorMultiplication
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilPairingFromThetaLifts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELWeilUniqueness

/-! Torsion points with global theta lifts have root-of-unity Weil pairings. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
  {L : LB A.left} {T : Over S} {k : ℤ}

private theorem scalar_eq_one_of_pt_eq_one (hA : IsAbelianScheme A) (hL : L.IsLB)
    {x y : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (hx : x.pt = 1)
    (h : CommIsOf A L k x y c) : c = 1 := by
  obtain ⟨v, hv, hc⟩ := exists_commIsOf_mul_left hL h h
  have hpt : v.pt = x.pt := by rw [hv, hx, _root_.mul_one]
  have hc' := commIsOf_of_same_points hA hL hpt.symm rfl hc
  exact mul_eq_left.mp (commIsOf_scalar_unique hL hc' h)

theorem commIsOf_pow_eq_one (hA : IsAbelianScheme A) (hL : L.IsLB)
    {x y : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (h : CommIsOf A L k x y c)
    {n : ℕ} (hx : x.pt ^ n = 1) : c ^ n = 1 := by
  have lifts (m : ℕ) : ∃ v : ThetaGrp A L k T, v.pt = x.pt ^ (m + 1) ∧ CommIsOf A L k v y (c ^ (m + 1)) := by
    induction m with
    | zero => exact ⟨x, (pow_one _).symm, by simpa only [Nat.zero_add, pow_one] using h⟩
    | succ m ih =>
      obtain ⟨u, hu, hc⟩ := ih
      obtain ⟨v, hv, hd⟩ := exists_commIsOf_mul_left hL hc h
      exact ⟨v, hv.trans ((congrArg (· * x.pt) hu).trans (pow_succ _ (m + 1)).symm),
        by rwa [pow_succ]⟩
  rcases n with _ | m
  · exact pow_zero _
  · obtain ⟨v, hv, hc⟩ := lifts m
    exact scalar_eq_one_of_pt_eq_one hA hL (hv.trans hx) hc

theorem exists_weilIs_root_of_lifts (hA : IsAbelianScheme A) (hL : L.IsLB)
    (x y : ThetaGrp A L k T) {n : ℕ} (hx : x.pt ^ n = 1) :
    ∃ c : Γ(T.left, ⊤)ˣ, c ^ n = 1 ∧ WeilIs A L k x.pt y.pt c := by
  obtain ⟨c, h⟩ := exists_commIsOf hA hL x y
  exact ⟨c, commIsOf_pow_eq_one hA hL h hx, weilIs_of_commIsOf hA hL h⟩

end GlobalTheory.CommPairing

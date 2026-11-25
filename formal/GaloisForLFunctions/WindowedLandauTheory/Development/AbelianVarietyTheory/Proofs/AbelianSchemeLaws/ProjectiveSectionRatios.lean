import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionSheaf
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELPolarizations

/-! Ratios of line-bundle sections have the normalization and overlap laws of projective coordinates. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.LineBundleSections

namespace GlobalTheory

variable {X : Scheme.{0}} {L : LB X}

/-- In each bundle chart, the nonvanishing locus is the basic open of the local coordinate. -/
theorem nonzeroLocus_inf_bundleChart (s : L.Sec) (i : L.ι) :
    nonzeroLocus s ⊓ L.U i = X.basicOpen (s.f i) := by
  refine le_antisymm (fun x hx => ?_) (le_inf (le_iSup (fun j => X.basicOpen (s.f j)) i)
    (X.basicOpen_le (s.f i)))
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx.1
  let W := L.U i ⊓ L.U j
  have hxW : x ∈ W := ⟨hx.2, X.basicOpen_le (s.f j) hj⟩
  have hi : X.basicOpen (resG X (inf_le_left : W ≤ L.U i) (s.f i)) =
      W ⊓ X.basicOpen (s.f i) := X.basicOpen_res (s.f i) (homOfLE inf_le_left).op
  have hj' : X.basicOpen (resG X (inf_le_right : W ≤ L.U j) (s.f j)) =
      W ⊓ X.basicOpen (s.f j) := X.basicOpen_res (s.f j) (homOfLE inf_le_right).op
  have hmem : x ∈ X.basicOpen (resG X (inf_le_left : W ≤ L.U i) (s.f i)) := by
    have e : resG X (inf_le_left : W ≤ L.U i) (s.f i) =
        (L.g i j : Γ(X, W)) * resG X (inf_le_right : W ≤ L.U j) (s.f j) := s.compat i j
    rw [e, Scheme.basicOpen_mul, X.basicOpen_of_isUnit (L.g i j).isUnit, hj']
    exact ⟨hxW, hxW, hj⟩
  exact (hi.le hmem).2

theorem isUnit_section_on_nonzeroLocus (s : L.Sec) (i : L.ι) {W : X.Opens}
    (hW : W ≤ nonzeroLocus s) (hi : W ≤ L.U i) : IsUnit (resG X hi (s.f i)) := by
  have h : W ≤ X.basicOpen (s.f i) := (le_inf hW hi).trans (nonzeroLocus_inf_bundleChart s i).le
  have e := (X.toRingedSpace.isUnit_res_basicOpen (s.f i)).map (resG X h)
  change IsUnit (resG X h (resG X (X.basicOpen_le (s.f i)) (s.f i))) at e
  rwa [resG_resG] at e

variable {ι : Type} (s : ι → L.Sec)
  (r : ∀ i j : ι, Γ(X, nonzeroLocus (s i)))
  (hr : ∀ i j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
    resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))

include hr in
theorem sectionRatio_on (i j : ι) (k : L.ι) {W : X.Opens} (hi : W ≤ nonzeroLocus (s i))
    (hk : W ≤ L.U k) :
    resG X hk ((s j).f k) = resG X hi (r i j) * resG X hk ((s i).f k) := by
  have e := congrArg (resG X (le_inf hi hk)) (hr i j k)
  simpa only [map_mul, resG_resG] using e

include hr in
theorem sectionRatio_self (hL : L.IsLB) (i : ι) : r i i = 1 := by
  let U := nonzeroLocus (s i)
  refine fun_ext_of_cover (fun k => U ⊓ L.U k) (fun _ => inf_le_left)
    (by rw [← inf_iSup_eq, hL.cover, inf_top_eq]) fun k => ?_
  rw [map_one]
  apply (isUnit_section_on_nonzeroLocus (s i) k inf_le_left inf_le_right).mul_right_cancel
  simpa only [one_mul] using (sectionRatio_on s r hr i i k inf_le_left inf_le_right).symm

include hr in
theorem sectionRatio_mul (hL : L.IsLB) (i j k : ι) {W : X.Opens}
    (hi : W ≤ nonzeroLocus (s i)) (hj : W ≤ nonzeroLocus (s j)) :
    resG X hi (r i j) * resG X hj (r j k) = resG X hi (r i k) := by
  refine fun_ext_of_cover (fun l => W ⊓ L.U l) (fun _ => inf_le_left)
    (by rw [← inf_iSup_eq, hL.cover, inf_top_eq]) fun l => ?_
  simp only [map_mul, resG_resG]
  let hi' : W ⊓ L.U l ≤ nonzeroLocus (s i) := inf_le_left.trans hi
  let hj' : W ⊓ L.U l ≤ nonzeroLocus (s j) := inf_le_left.trans hj
  apply (isUnit_section_on_nonzeroLocus (s i) l hi' inf_le_right).mul_right_cancel
  rw [mul_comm (resG X hi' (r i j)) (resG X hj' (r j k)), mul_assoc,
    ← sectionRatio_on s r hr i j l hi' inf_le_right,
    ← sectionRatio_on s r hr j k l hj' inf_le_right, sectionRatio_on s r hr i k l hi' inf_le_right]

include hr in
theorem basicOpen_sectionRatio (hL : L.IsLB) (i j : ι) :
    X.basicOpen (r i j) = nonzeroLocus (s i) ⊓ nonzeroLocus (s j) := by
  have key (x : X) (hx : x ∈ nonzeroLocus (s i)) :
      x ∈ X.basicOpen (r i j) ↔ x ∈ nonzeroLocus (s j) := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ k, L.U k by rw [hL.cover]; trivial)
    let W := nonzeroLocus (s i) ⊓ L.U k
    let a := resG X (inf_le_left : W ≤ nonzeroLocus (s i)) (r i j)
    let b := resG X (inf_le_right : W ≤ L.U k) ((s j).f k)
    let c := resG X (inf_le_right : W ≤ L.U k) ((s i).f k)
    have e : b = a * c := sectionRatio_on s r hr i j k inf_le_left inf_le_right
    have hc := isUnit_section_on_nonzeroLocus (s i) k (W := W) inf_le_left inf_le_right
    have hD : X.basicOpen b = X.basicOpen a := by
      rw [e, Scheme.basicOpen_mul, X.basicOpen_of_isUnit hc,
        inf_eq_left.mpr (X.basicOpen_le a)]
    have ha : X.basicOpen a = W ⊓ X.basicOpen (r i j) :=
      X.basicOpen_res (r i j) (homOfLE inf_le_left).op
    have hb : X.basicOpen b = W ⊓ X.basicOpen ((s j).f k) :=
      X.basicOpen_res ((s j).f k) (homOfLE inf_le_right).op
    rw [ha, hb] at hD
    have hxW : x ∈ W := ⟨hx, hk⟩
    rw [← nonzeroLocus_inf_bundleChart (s j) k] at hD
    exact ⟨fun h => (hD.ge ⟨hxW, h⟩).2.1, fun h => (hD.le ⟨hxW, h, hk⟩).2⟩
  refine le_antisymm (fun x hx => ?_) (fun x hx => (key x hx.1).mpr hx.2)
  have hi := X.basicOpen_le (r i j) hx
  exact ⟨hi, (key x hi).mp hx⟩

end GlobalTheory

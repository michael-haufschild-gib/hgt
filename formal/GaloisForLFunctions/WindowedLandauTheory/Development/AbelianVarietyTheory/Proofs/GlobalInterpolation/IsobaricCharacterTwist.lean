import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.DataN

/-! Local character twists commute with the sums and real twists that
define Speh and isobaric parameters. -/

noncomputable section

open WindowedLandauTheory.BasicNotions
open WindowedLandauTheory.MainNotions.N

namespace WindowedLandauTheory.NormalizedTypes

variable {R : Ranks} {H : Host R} {rows : Rows.Data R}
variable (N : NData R H rows) (A : NAut N)

theorem spehLoc_eq_foldr (p : Part A.CG) (w : PlE H) :
    spehLoc N A p w = (List.range p.d).foldr
      (fun (k : ℕ) acc => A.lpSum (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - (k : ℝ))) acc)
      (A.lpZero w) := by
  change ((List.range p.d).flatMap (pure ∘ fun k : ℕ => (k : ℝ))).foldr _ _ = _
  simp only [List.flatMap_pure_eq_map, List.foldr_map]

variable {w : PlE H} (χ : A.CG 1)

private theorem spehLoc_character_twist
    (hSum : ∀ a b : A.LP w,
      A.lpChar (A.lpSum a b) (A.locG χ w) =
        A.lpSum (A.lpChar a (A.locG χ w)) (A.lpChar b (A.locG χ w)))
    (hZero : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w)
    (hTw : ∀ (a : A.LP w) (s : ℝ),
      A.lpChar (A.lpTw a s) (A.locG χ w) = A.lpTw (A.lpChar a (A.locG χ w)) s)
    (p : Part A.CG) :
    A.lpChar (spehLoc N A p w) (A.locG χ w) =
      spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w := by
  simp only [spehLoc_eq_foldr, A.locG_tw]
  induction List.range p.d with
  | nil => exact hZero
  | cons j L ih =>
    rw [List.foldr_cons, List.foldr_cons, hSum, hTw, ih]

/-- Twisting an isobaric parameter by a character twists every Speh block
by that character. -/
theorem isoLoc_character_twist
    (hSum : ∀ a b : A.LP w,
      A.lpChar (A.lpSum a b) (A.locG χ w) =
        A.lpSum (A.lpChar a (A.locG χ w)) (A.lpChar b (A.locG χ w)))
    (hZero : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w)
    (hTw : ∀ (a : A.LP w) (s : ℝ),
      A.lpChar (A.lpTw a s) (A.locG χ w) = A.lpTw (A.lpChar a (A.locG χ w)) s)
    (P : List (Part A.CG)) :
    A.lpChar (isoLoc N A P w) (A.locG χ w) = isoLoc N A (twistIso N A P χ) w := by
  induction P with
  | nil => exact hZero
  | cons p P ih =>
    change A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A P w)) (A.locG χ w) =
      A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A P χ) w)
    rw [hSum, spehLoc_character_twist N A χ hSum hZero hTw, ih]

end WindowedLandauTheory.NormalizedTypes

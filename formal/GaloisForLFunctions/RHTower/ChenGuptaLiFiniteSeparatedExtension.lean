/-
# Chen--Gupta--Li finite separated ordinate extension

A finite zero packet is naturally specified by its actual ordinates and a
pairwise separation certificate; its input order need not be increasing.
This module sorts those ordinates internally, assigns each original row its
sorted rank, and extends the finite ordered sequence past its final row at the
same certified spacing.  The result instantiates the existing CGL fibrewise
packet interface without reordering the visible finite rows.

No RH, GRH, zero-density, large-value, or analytic premise is supplied by a
caller.  Separation is certified data in the finite packet itself.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketFibreSeparation

open Complex

noncomputable section

namespace RHTower

/-- Finite real ordinates with a closed pairwise spacing certificate. -/
structure CGLFiniteSeparatedOrdinates (R : ℕ) where
  ordinate : Fin R → ℝ
  spacing : ℝ
  spacing_pos : 0 < spacing
  separated : ∀ r s : Fin R, r ≠ s → spacing ≤ |ordinate r - ordinate s|

/-- The finite set of actual ordinates in a separated packet. -/
noncomputable def cglFiniteSeparatedOrdinatesImage {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) : Finset ℝ :=
  Finset.univ.image P.ordinate

/-- Pairwise positive separation makes the finite ordinate map injective. -/
theorem cglFiniteSeparatedOrdinates_ordinate_injective {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) : Function.Injective P.ordinate := by
  intro r s hrs
  by_contra hne
  have hsep := P.separated r s hne
  rw [hrs] at hsep
  simp only [sub_self, abs_zero] at hsep
  linarith [P.spacing_pos]

/-- A separated packet has exactly as many distinct ordinates as finite rows. -/
theorem cglFiniteSeparatedOrdinatesImage_card {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) :
    (cglFiniteSeparatedOrdinatesImage P).card = R := by
  unfold cglFiniteSeparatedOrdinatesImage
  have hinj : Set.InjOn P.ordinate (↑(Finset.univ : Finset (Fin R))) := by
    intro x hx y hy hxy
    exact cglFiniteSeparatedOrdinates_ordinate_injective P hxy
  exact (Finset.card_image_iff.mpr hinj).trans (by simp)

/-- Increasing finite enumeration of the packet's actual ordinates. -/
noncomputable def cglFiniteSeparatedOrdinatesOrdered {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) : Fin R → ℝ :=
  (cglFiniteSeparatedOrdinatesImage P).orderEmbOfFin
    (cglFiniteSeparatedOrdinatesImage_card P)

/-- Sorted rank of an original finite row. -/
noncomputable def cglFiniteSeparatedOrdinatesRank {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) (r : Fin R) : Fin R :=
  ((cglFiniteSeparatedOrdinatesImage P).orderIsoOfFin
    (cglFiniteSeparatedOrdinatesImage_card P)).symm
    ⟨P.ordinate r, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩⟩

/-- Evaluating the sorted enumeration at a row's sorted rank recovers its
literal original ordinate. -/
theorem cglFiniteSeparatedOrdinates_ordered_rank {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) (r : Fin R) :
    cglFiniteSeparatedOrdinatesOrdered P (cglFiniteSeparatedOrdinatesRank P r) =
      P.ordinate r := by
  unfold cglFiniteSeparatedOrdinatesOrdered cglFiniteSeparatedOrdinatesRank
  rw [← Finset.coe_orderIsoOfFin_apply]
  exact congrArg Subtype.val
    (((cglFiniteSeparatedOrdinatesImage P).orderIsoOfFin
      (cglFiniteSeparatedOrdinatesImage_card P)).apply_symm_apply
      ⟨P.ordinate r, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩⟩)

/-- Sorted ranks retain the injectivity of the original finite rows. -/
theorem cglFiniteSeparatedOrdinates_rank_injective {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) :
    Function.Injective (cglFiniteSeparatedOrdinatesRank P) := by
  intro r s hrs
  apply cglFiniteSeparatedOrdinates_ordinate_injective P
  rw [← cglFiniteSeparatedOrdinates_ordered_rank P r,
    ← cglFiniteSeparatedOrdinates_ordered_rank P s, hrs]

/-- Consecutive sorted ordinates retain the original packet spacing. -/
theorem cglFiniteSeparatedOrdinates_ordered_step {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) (i : ℕ) (hi : i + 1 < R) :
    cglFiniteSeparatedOrdinatesOrdered P ⟨i, by omega⟩ + P.spacing ≤
      cglFiniteSeparatedOrdinatesOrdered P ⟨i + 1, hi⟩ := by
  have hmemI := Finset.orderEmbOfFin_mem (cglFiniteSeparatedOrdinatesImage P)
    (cglFiniteSeparatedOrdinatesImage_card P) ⟨i, by omega⟩
  have hmemJ := Finset.orderEmbOfFin_mem (cglFiniteSeparatedOrdinatesImage P)
    (cglFiniteSeparatedOrdinatesImage_card P) ⟨i + 1, hi⟩
  rcases Finset.mem_image.mp hmemI with ⟨r, -, hr⟩
  rcases Finset.mem_image.mp hmemJ with ⟨s, -, hs⟩
  have hlt : cglFiniteSeparatedOrdinatesOrdered P ⟨i, by omega⟩ <
      cglFiniteSeparatedOrdinatesOrdered P ⟨i + 1, hi⟩ :=
    ((cglFiniteSeparatedOrdinatesImage P).orderEmbOfFin
      (cglFiniteSeparatedOrdinatesImage_card P)).strictMono (by simp)
  have hrs : r ≠ s := by
    intro heq
    subst s
    have heq' : cglFiniteSeparatedOrdinatesOrdered P ⟨i, by omega⟩ =
        cglFiniteSeparatedOrdinatesOrdered P ⟨i + 1, hi⟩ := hr.symm.trans hs
    exact (ne_of_lt hlt) heq'
  have hsep := P.separated r s hrs
  have hlt' :
      ((cglFiniteSeparatedOrdinatesImage P).orderEmbOfFin
        (cglFiniteSeparatedOrdinatesImage_card P)) ⟨i, by omega⟩ <
      ((cglFiniteSeparatedOrdinatesImage P).orderEmbOfFin
        (cglFiniteSeparatedOrdinatesImage_card P)) ⟨i + 1, hi⟩ := by
    exact hlt
  rw [hr, hs, abs_of_nonpos (by linarith [hlt'])] at hsep
  change cglFiniteSeparatedOrdinatesOrdered P ⟨i, by omega⟩ + P.spacing ≤
    cglFiniteSeparatedOrdinatesOrdered P ⟨i + 1, hi⟩
  dsimp [cglFiniteSeparatedOrdinatesOrdered]
  linarith [hsep]

/-- Infinite increasing extension of a finite sorted packet.  In the empty
case it is the spacing arithmetic progression; otherwise it continues from
the last finite ordinate. -/
noncomputable def cglFiniteSeparatedOrdinatesTimeline {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) (m : ℕ) : ℝ :=
  if hR : R = 0 then (m : ℝ) * P.spacing else
    if hm : m < R then cglFiniteSeparatedOrdinatesOrdered P ⟨m, hm⟩ else
      cglFiniteSeparatedOrdinatesOrdered P
        ⟨R - 1, Nat.sub_lt (Nat.pos_of_ne_zero hR) (Nat.succ_pos 0)⟩ +
        ((m - (R - 1) : ℕ) : ℝ) * P.spacing

/-- The infinite extension has the certified spacing at every consecutive
pair of natural indices. -/
theorem cglFiniteSeparatedOrdinatesTimeline_step {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) (m : ℕ) :
    cglFiniteSeparatedOrdinatesTimeline P m + P.spacing ≤
      cglFiniteSeparatedOrdinatesTimeline P (m + 1) := by
  by_cases hR : R = 0
  · simp [cglFiniteSeparatedOrdinatesTimeline, hR]
    nlinarith [P.spacing_pos]
  · have hRpos : 0 < R := Nat.pos_of_ne_zero hR
    by_cases hm : m < R
    · by_cases hm' : m + 1 < R
      · simp [cglFiniteSeparatedOrdinatesTimeline, hR, hm, hm']
        exact cglFiniteSeparatedOrdinates_ordered_step P m hm'
      · have hlast : (⟨m, hm⟩ : Fin R) =
          ⟨R - 1, Nat.sub_lt hRpos (Nat.succ_pos 0)⟩ := by
          have hm_eq : m = R - 1 := by omega
          subst m
          rfl
        have htail : m + 1 - (R - 1) = 1 := by omega
        simp [cglFiniteSeparatedOrdinatesTimeline, hR, hm, hm', hlast, htail]
    · have hm' : ¬ m + 1 < R := by omega
      have htail : m + 1 - (R - 1) = m - (R - 1) + 1 := by omega
      simp [cglFiniteSeparatedOrdinatesTimeline, hR, hm, hm', htail]
      nlinarith

/-- The extension recovers every original ordinate at its internal sorted
rank. -/
theorem cglFiniteSeparatedOrdinatesTimeline_rank {R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) (r : Fin R) :
    cglFiniteSeparatedOrdinatesTimeline P (cglFiniteSeparatedOrdinatesRank P r) =
      P.ordinate r := by
  have hR : R ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt r.isLt)
  rw [cglFiniteSeparatedOrdinatesTimeline, dif_neg hR,
    dif_pos (cglFiniteSeparatedOrdinatesRank P r).isLt]
  exact cglFiniteSeparatedOrdinates_ordered_rank P r

/-- Converts finite certified same-character ordinates to CGL's existing
fibrewise separated-packet interface.  Original finite row labels remain
visible; only `fibreRank` uses the internal increasing enumeration. -/
noncomputable def CGLFiniteSeparatedOrdinates.toCGLFibreSeparatedPacket
    {q R : ℕ} (P : CGLFiniteSeparatedOrdinates R)
    (χ : DirichletCharacter ℂ (q + 1)) : CGLFibreSeparatedPacket q R where
  ordinate := P.ordinate
  character := fun _ => χ
  spacing := P.spacing
  spacing_pos := P.spacing_pos
  fibreRank := fun r => (cglFiniteSeparatedOrdinatesRank P r).1
  fibreRank_lt := fun r => (cglFiniteSeparatedOrdinatesRank P r).isLt
  fibreTime := fun _ => cglFiniteSeparatedOrdinatesTimeline P
  fibreTime_step := fun _ m => cglFiniteSeparatedOrdinatesTimeline_step P m
  ordinate_eq_fibreTime := fun r => (cglFiniteSeparatedOrdinatesTimeline_rank P r).symm
  fibreRank_injective := by
    intro r s _ hrs
    exact cglFiniteSeparatedOrdinates_rank_injective P (Fin.ext hrs)

/-- The converted CGL packet retains each literal input ordinate. -/
theorem cglFiniteSeparatedOrdinates_toCGLFibreSeparatedPacket_ordinate {q R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) (χ : DirichletCharacter ℂ (q + 1))
    (r : Fin R) :
    (P.toCGLFibreSeparatedPacket χ).ordinate r = P.ordinate r := by
  simp [CGLFiniteSeparatedOrdinates.toCGLFibreSeparatedPacket]

/-- The converted CGL packet carries the one literal input character at every
row. -/
theorem cglFiniteSeparatedOrdinates_toCGLFibreSeparatedPacket_character {q R : ℕ}
    (P : CGLFiniteSeparatedOrdinates R) (χ : DirichletCharacter ℂ (q + 1))
    (r : Fin R) :
    (P.toCGLFibreSeparatedPacket χ).character r = χ := by
  simp [CGLFiniteSeparatedOrdinates.toCGLFibreSeparatedPacket]

end RHTower

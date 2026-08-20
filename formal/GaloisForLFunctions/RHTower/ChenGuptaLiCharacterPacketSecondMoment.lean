/-
# Chen--Gupta--Li finite character-packet second moment

This module completes the finite second-moment layer used in Chen--Gupta--Li
Lemma 9.1.  Character orthogonality gives an exact interval identity.  Its
diagonal is explicit, and the source-correct fibrewise separation machinery
bounds the remaining off-diagonal correction by a finite harmonic budget.

No RH, GRH, smoothness, large-value, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketFibreAggregate

open Complex MeasureTheory

noncomputable section

namespace RHTower

/-- The literal CGL rows carried by a fibrewise separated packet. -/
def cglFibreSeparatedPacketRows {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) : Fin R → CGLCharacterDyadicRowData (q + 1) :=
  fun r => { time := P.ordinate r, character := P.character r }

/-- The compact log-ordinate interval moment of a fibrewise CGL packet. -/
noncomputable def cglFibreSeparatedPacketIntervalMoment {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) : ℂ :=
  ∫ τ in A..B, cglCharacterPacketHermitianMass q R (cglFibreSeparatedPacketRows P) τ

/-- The off-diagonal correction to the CGL compact interval moment. -/
noncomputable def cglFibreSeparatedPacketIntervalOffDiagonal {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) : ℂ :=
  ∑ r : Fin R, ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
    (if P.character r = P.character s then ((q + 1).totient : ℂ) else 0) *
      cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)

/-- Exact diagonal/off-diagonal decomposition of the finite CGL interval
moment.  The diagonal is the number of unit residue classes times the number
of rows times the log-interval length. -/
theorem cglFibreSeparatedPacket_intervalMoment_eq_diagonal_add_offDiagonal {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) :
    cglFibreSeparatedPacketIntervalMoment P A B =
      ((q + 1).totient : ℂ) * (R : ℂ) * ((B - A : ℝ) : ℂ) +
        cglFibreSeparatedPacketIntervalOffDiagonal P A B := by
  unfold cglFibreSeparatedPacketIntervalMoment
  rw [intervalIntegral_cglCharacterPacketHermitianMass_expand q R
    (cglFibreSeparatedPacketRows P) A B]
  let F : Fin R → Fin R → ℂ := fun r s =>
    (if P.character r = P.character s then ((q + 1).totient : ℂ) else 0) *
      cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)
  change (∑ r, ∑ s, F r s) = _
  calc
    ∑ r, ∑ s, F r s = ∑ r, (F r r + ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r, F r s) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (Finset.add_sum_erase (Finset.univ : Finset (Fin R)) (F r) (Finset.mem_univ r)).symm
    _ = (∑ r, F r r) + cglFibreSeparatedPacketIntervalOffDiagonal P A B := by
      rw [Finset.sum_add_distrib]
      rfl
    _ = _ := by
      have hdiag : ∀ r : Fin R, F r r = ((q + 1).totient : ℂ) * ((B - A : ℝ) : ℂ) := by
        intro r
        dsimp [F]
        rw [if_pos rfl, cglCharacterPacketIntervalKernel_self]
      have hsumdiag : (∑ r, F r r) = ∑ _ : Fin R,
          ((q + 1).totient : ℂ) * ((B - A : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hdiag r
      rw [hsumdiag]
      simp
      ring

/-- The complex off-diagonal correction is bounded by its total absolute
same-character kernel mass. -/
theorem norm_cglFibreSeparatedPacketIntervalOffDiagonal_le {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) :
    ‖cglFibreSeparatedPacketIntervalOffDiagonal P A B‖ ≤
      ((q + 1).totient : ℝ) * cglFibreSeparatedPacketSameCharacterKernelTotal P A B := by
  unfold cglFibreSeparatedPacketIntervalOffDiagonal
  calc
    ‖∑ r : Fin R, ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
        (if P.character r = P.character s then ((q + 1).totient : ℂ) else 0) *
          cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖
      ≤ ∑ r : Fin R, ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
          ‖(if P.character r = P.character s then ((q + 1).totient : ℂ) else 0) *
            cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖ := by
        calc
          ‖∑ r : Fin R, ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
              (if P.character r = P.character s then ((q + 1).totient : ℂ) else 0) *
                cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖
            ≤ ∑ r : Fin R, ‖∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
                (if P.character r = P.character s then ((q + 1).totient : ℂ) else 0) *
                  cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ r : Fin R, ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
              ‖(if P.character r = P.character s then ((q + 1).totient : ℂ) else 0) *
                cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖ := by
              apply Finset.sum_le_sum
              intro r hr
              exact norm_sum_le _ _
    _ = ((q + 1).totient : ℝ) * cglFibreSeparatedPacketSameCharacterKernelTotal P A B := by
      have hterm : ∀ r s : Fin R,
          ‖(if P.character r = P.character s then ((q + 1).totient : ℂ) else 0) *
              cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖ =
            ((q + 1).totient : ℝ) *
              (if P.character r = P.character s then
                ‖cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖ else 0) := by
        intro r s
        by_cases hchar : P.character r = P.character s
        · simp only [hchar, ↓reduceIte]
          rw [norm_mul, norm_natCast]
        · simp [hchar]
      rw [show (∑ r : Fin R, ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
          ‖(if P.character r = P.character s then ((q + 1).totient : ℂ) else 0) *
              cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖) =
          ∑ r : Fin R, ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
            ((q + 1).totient : ℝ) *
              (if P.character r = P.character s then
                ‖cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖ else 0) by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        exact hterm r s]
      have hfactor : (∑ r : Fin R, ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
          ((q + 1).totient : ℝ) *
            (if P.character r = P.character s then
              ‖cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖ else 0)) =
          ∑ r : Fin R, ((q + 1).totient : ℝ) *
            (∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
              if P.character r = P.character s then
                ‖cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖ else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
      rw [hfactor, ← Finset.mul_sum]
      rfl

/-- The interval moment differs from its explicit diagonal main term by at
most the total same-character off-diagonal kernel mass. -/
theorem norm_cglFibreSeparatedPacketIntervalMoment_sub_diagonal_le {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) :
    ‖cglFibreSeparatedPacketIntervalMoment P A B -
        ((q + 1).totient : ℂ) * (R : ℂ) * ((B - A : ℝ) : ℂ)‖ ≤
      ((q + 1).totient : ℝ) * cglFibreSeparatedPacketSameCharacterKernelTotal P A B := by
  rw [cglFibreSeparatedPacket_intervalMoment_eq_diagonal_add_offDiagonal P A B]
  convert norm_cglFibreSeparatedPacketIntervalOffDiagonal_le P A B using 1
  ring_nf

/-- Closed finite CGL second-moment estimate: its exact diagonal main term has
a source-correct fibrewise harmonic error budget. -/
theorem norm_cglFibreSeparatedPacketIntervalMoment_sub_diagonal_le_harmonic {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) :
    ‖cglFibreSeparatedPacketIntervalMoment P A B -
        ((q + 1).totient : ℂ) * (R : ℂ) * ((B - A : ℝ) : ℂ)‖ ≤
      ((q + 1).totient : ℝ) *
        ((R : ℝ) * ((4 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1))) := by
  calc
    ‖cglFibreSeparatedPacketIntervalMoment P A B -
        ((q + 1).totient : ℂ) * (R : ℂ) * ((B - A : ℝ) : ℂ)‖ ≤
      ((q + 1).totient : ℝ) * cglFibreSeparatedPacketSameCharacterKernelTotal P A B :=
        norm_cglFibreSeparatedPacketIntervalMoment_sub_diagonal_le P A B
    _ ≤ ((q + 1).totient : ℝ) *
        ((R : ℝ) * ((4 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1))) := by
      exact mul_le_mul_of_nonneg_left
        (cglFibreSeparatedPacket_sameCharacterKernelTotal_le P A B) (by positivity)

end RHTower

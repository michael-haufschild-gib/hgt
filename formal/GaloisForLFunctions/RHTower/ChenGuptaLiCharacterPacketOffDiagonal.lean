/-
# Chen--Gupta--Li same-character off-diagonal packet kernel

This module combines three closed ingredients for CGL Lemma 9.1:

* exact character orthogonality removes different character labels;
* the interval kernel has size at most `2 / |t-u|` off the diagonal;
* a certified separated packet has a harmonic reciprocal-gap row bound.

It proves the finite same-character off-diagonal row is bounded by the
literal reciprocal row.  The next layer sums these rows and combines them
with the diagonal interval mass.

No RH, GRH, smoothness, large-value, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketSeparation

noncomputable section

namespace RHTower

/-- Different finite labels in an ordered separated packet have different
ordinates. -/
theorem cglGloballySeparatedPacket_ordinate_ne {q R : ℕ}
    (P : CGLGloballySeparatedPacket q R) (r s : Fin R) (hrs : r ≠ s) :
    P.ordinate r.1 ≠ P.ordinate s.1 := by
  have hval : r.1 ≠ s.1 := fun h => hrs (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact ne_of_lt (RHTower.Sieve.lt_of_gap P.spacing_pos P.spacing_step hlt)
  · exact ne_of_gt (RHTower.Sieve.lt_of_gap P.spacing_pos P.spacing_step hgt)

/-- The same-character off-diagonal interval-kernel row at the label `r`. -/
def cglGloballySeparatedPacketSameCharacterKernelRow {q R : ℕ}
    (P : CGLGloballySeparatedPacket q R) (A B : ℝ) (r : Fin R) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
    if P.character r = P.character s then
      ‖cglCharacterPacketIntervalKernel A B (P.ordinate r.1) (P.ordinate s.1)‖ else 0

/-- The CGL same-character off-diagonal row is bounded by the certified
reciprocal-gap row.  Character inequality makes a summand zero; character
equality leaves an off-diagonal pair with a certified nonzero ordinate gap. -/
theorem cglGloballySeparatedPacket_sameCharacterKernelRow_le {q R : ℕ}
    (P : CGLGloballySeparatedPacket q R) (A B : ℝ) (r : Fin R) :
    cglGloballySeparatedPacketSameCharacterKernelRow P A B r ≤
      cglGloballySeparatedPacketReciprocalRow P r := by
  rw [cglGloballySeparatedPacketReciprocalRow_eq_fin]
  unfold cglGloballySeparatedPacketSameCharacterKernelRow
  apply Finset.sum_le_sum
  intro s hs
  have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
  have htime : P.ordinate r.1 ≠ P.ordinate s.1 :=
    cglGloballySeparatedPacket_ordinate_ne P r s (Ne.symm hsr)
  by_cases hchar : P.character r = P.character s
  · rw [if_pos hchar]
    let p : CGLDistinctOrdinatePair := ⟨(P.ordinate r.1, P.ordinate s.1), htime⟩
    simpa only [p, abs_sub_comm] using norm_cglCharacterPacketIntervalKernel_le A B p
  · rw [if_neg hchar]
    positivity

end RHTower

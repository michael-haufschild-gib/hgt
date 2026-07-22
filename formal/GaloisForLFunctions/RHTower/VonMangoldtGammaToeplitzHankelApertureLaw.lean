import GaloisForLFunctions.RHTower.VonMangoldtGammaStrictHankelLaw
import GaloisForLFunctions.HTGeometry.ToeplitzHankelPolarization

open scoped BigOperators

namespace RHTower

noncomputable section

/-!
# Von Mangoldt--Gamma Toeplitz--Hankel aperture law

The finite von Mangoldt--Gamma moment row belongs to the Toeplitz--Hankel intersection exactly
when its source aperture is empty.  Thus no nonempty source can be represented by a purely
shift-invariant phase orbit: strict Hausdorff Hankel positivity forces a radial polarization.
-/

/-- **Toeplitz--Hankel aperture law.**  A finite von Mangoldt--Gamma moment row is diagonally
shift invariant exactly for the empty source aperture. -/
theorem finiteVonMangoldtGammaBivariateMoment_hankelShiftInvariant_iff
    (M : ℕ) (x : ℝ) (a : ℕ) :
    HTGeometry.HankelShiftInvariant
      (fun b ↦ finiteVonMangoldtGammaBivariateMoment M x a b) ↔ M = 0 := by
  constructor
  · intro hshift
    by_contra hM
    have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have hdetpos := det_finiteVonMangoldtGammaBivariateMoment_hankel_pos
      hMpos x a 3
    have hperiodic :=
      (HTGeometry.hankelShiftInvariant_iff_twoPeriodic
        (fun b ↦ finiteVonMangoldtGammaBivariateMoment M x a b)).mp hshift
    rw [HTGeometry.det_momentHankelMatrix_add_three_eq_zero
      (fun b ↦ finiteVonMangoldtGammaBivariateMoment M x a b) hperiodic 0] at hdetpos
    exact (lt_irrefl 0) hdetpos
  · intro hM
    subst M
    intro i j
    simp [finiteVonMangoldtGammaBivariateMoment,
      finiteExponentialGammaBivariateMoment]

/-- A shift-invariant real Gram orbit realizes a finite von Mangoldt--Gamma moment row exactly
for the empty source aperture. -/
theorem finiteVonMangoldtGammaBivariateMoment_shiftInvariantGram_iff
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : ℕ) (x : ℝ) (a : ℕ) :
    (∃ v : ℕ → E,
        (∀ i j, inner ℝ (v i) (v j) =
          finiteVonMangoldtGammaBivariateMoment M x a (i + j)) ∧
        (∀ i j, inner ℝ (v (i + 1)) (v (j + 1)) =
          inner ℝ (v i) (v j))) ↔ M = 0 := by
  constructor
  · rintro ⟨v, hgram, hshift⟩
    exact (finiteVonMangoldtGammaBivariateMoment_hankelShiftInvariant_iff M x a).mp
      (HTGeometry.hankelShiftInvariant_of_shiftInvariantGram
        (fun b ↦ finiteVonMangoldtGammaBivariateMoment M x a b) v hgram hshift)
  · intro hM
    subst M
    refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · intro i j
      simp [finiteVonMangoldtGammaBivariateMoment,
        finiteExponentialGammaBivariateMoment]
    · intro i j
      simp

end

end RHTower

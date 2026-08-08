import GaloisForLFunctions.RHTower.SquaredXiRadialJetSourceCompletion

/-!
# Exact reverse-Bessel source representation of shifted Xi moments

The completed source polynomial and the shifted reciprocal-square moment tower were previously
connected only through an intermediate radial derivative.  Eliminating that derivative exposes
the exact positive normalization needed for far-right asymptotics and Hankel recession.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The completed reverse-Bessel source jet is exactly a positive monomial multiple of the real
shifted Xi moment. -/
theorem completedSourceJet_eq_xiShiftedReciprocalMoment
    (n : ℕ) {w : ℝ} (hw : 0 < w) :
    completedSourceJet n w =
      (2 : ℝ) ^ n * (n.factorial : ℝ) * w ^ (2 * n + 1) *
        (xiShiftedReciprocalMoment (w ^ 2) n).re := by
  rw [completedSourceJet_eq n hw,
    iteratedDeriv_squaredXiRadialField n (by positivity : (0 : ℝ) < w ^ 2)]
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [show
      (-1 : ℝ) ^ n * 2 ^ (n + 1) * w ^ (2 * n + 1) *
          ((-1 : ℝ) ^ n * (n.factorial : ℝ) / 2 *
            (xiShiftedReciprocalMoment (w ^ 2) n).re) =
        ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
          (2 ^ (n + 1) / 2) * (n.factorial : ℝ) * w ^ (2 * n + 1) *
            (xiShiftedReciprocalMoment (w ^ 2) n).re by ring,
    hsign, one_mul, pow_succ]
  ring

end

end RHTower

import GaloisForLFunctions.RHTower.SEMTruncatedJetWeylCharge

/-!
# The SEM dyadic Weyl degeneracy law

The boundary-completed truncated jet has two, and only two, ways to satisfy the depth-`k`
dyadic Weyl relation.  Either its wrap holonomy vanishes, leaving the canonical singular
one-sided shift, or its dimension is divisible by `2^k`.

For an actual completed SEM hole packet, the second alternative is exactly vanishing of the
completed contour charge.  Thus the full matrix Weyl equation detects the source obstruction
only after excluding the singular zero-wrap branch:

`boundary Weyl law  <->  zero wrap or zero completed-SEM contour charge`.
-/

open Complex Matrix

noncomputable section

namespace RHTower

/-- **Universal dyadic boundary classification.**  A boundary-completed truncated jet obeys the
depth-`k` Weyl equation exactly when its wrap is zero or its dimension is divisible by `2^k`. -/
theorem dyadicBoundaryCompletedJetWeyl_iff_zero_or_dvd
    (n k : ℕ) (holonomy : ℂ) :
    (truncatedJetClock n (Bottcher.dyadicRoot k) *
          boundaryCompletedJetShift n holonomy =
        Bottcher.dyadicRoot k •
          (boundaryCompletedJetShift n holonomy *
            truncatedJetClock n (Bottcher.dyadicRoot k))) ↔
      holonomy = 0 ∨ 2 ^ k ∣ n + 1 := by
  constructor
  · intro hweyl
    by_cases hholonomy : holonomy = 0
    · exact Or.inl hholonomy
    · exact Or.inr
        (pow_dvd_card_of_dyadic_boundaryCompletedJetWeyl
          n k holonomy hholonomy hweyl)
  · rintro (rfl | hdvd)
    · exact truncatedJetClock_oneSidedShift_weyl n (Bottcher.dyadicRoot k)
    · apply boundaryCompletedJetWeyl_of_phase_pow_card
      exact ((dyadicWeylPhase_isPrimitiveRoot k).pow_eq_one_iff_dvd (n + 1)).mpr hdvd

/-- **SEM dyadic Weyl degeneracy law.**  Once `n+1` is the actual SEM hole count, the full
boundary Weyl equation holds exactly through one of two mutually meaningful mechanisms: the
singular zero-wrap branch, or vanishing of the source-defined completed contour charge. -/
theorem boundaryCompletedJetWeyl_iff_zero_or_completedSEMContourCharge_zero
    {rho : ℂ} {r0 R : ℝ} {N n : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (hsplit : SEMSplitData rho r0 R N zs u) (hlen : zs.length = n + 1)
    (k : ℕ) (holonomy : ℂ) :
    (truncatedJetClock n (Bottcher.dyadicRoot k) *
          boundaryCompletedJetShift n holonomy =
        Bottcher.dyadicRoot k •
          (boundaryCompletedJetShift n holonomy *
            truncatedJetClock n (Bottcher.dyadicRoot k))) ↔
      holonomy = 0 ∨
        integralJetCharge 1 (2 ^ k) (by omega)
          (completedSEMContourBoundaryZ rho r0 R N 1) = 0 := by
  rw [dyadicBoundaryCompletedJetWeyl_iff_zero_or_dvd]
  congr 1
  rw [completedSEMContourCharge_zero_iff_dyadicPhase_pow_holeCount hsplit k]
  rw [hlen]
  exact (dyadicWeylPhase_isPrimitiveRoot k).pow_eq_one_iff_dvd (n + 1) |>.symm

end RHTower

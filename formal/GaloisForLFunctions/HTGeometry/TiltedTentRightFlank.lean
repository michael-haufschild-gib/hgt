import GaloisForLFunctions.HTGeometry.TiltedTentGeometricBracketMinimax

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-!
# Subcritical right-flank law for exponentially tilted tents

The normalized right flank of an exponentially tilted tent is
`exp (beta * d) * (1 - d / L)`.  When `beta * L < 1`, the linear loss dominates the
exponential tilt throughout the support, so the profile is strictly decreasing.
-/

/-- Normalized right flank of a tent of width `L` with exponential tilt `beta`. -/
def tiltedTentRightProfile (beta L d : ℝ) : ℝ :=
  Real.exp (beta * d) * (1 - d / L)

lemma hasDerivAt_tiltedTentRightProfile (beta d : ℝ) {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt (tiltedTentRightProfile beta L)
      (Real.exp (beta * d) / L * (beta * (L - d) - 1)) d := by
  change HasDerivAt (fun x : ℝ => Real.exp (beta * x) * (1 - x / L)) _ d
  convert! ((((hasDerivAt_id d).const_mul beta).exp).mul
    ((hasDerivAt_const d 1).sub ((hasDerivAt_id d).div_const L))) using 1
  · simp only [Pi.sub_apply, id_eq]
    field_simp [hL]
    ring

/-- Below the critical tilt-width product, the right tent flank is strictly decreasing. -/
theorem tiltedTentRightProfile_strictAntiOn
    {beta L : ℝ} (hbeta : 0 ≤ beta) (hL : 0 < L) (hsub : beta * L < 1) :
    StrictAntiOn (tiltedTentRightProfile beta L) (Set.Icc 0 L) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) L)
  · exact (((continuous_const.mul continuous_id).rexp).mul
      (continuous_const.sub (continuous_id.div_const L))).continuousOn
  · intro d hd
    rw [(hasDerivAt_tiltedTentRightProfile beta d hL.ne').deriv]
    rw [interior_Icc] at hd
    have hcore : beta * (L - d) < 1 := by
      have hd0 : 0 < d := hd.1
      have hLd : L - d ≤ L := by linarith
      exact (mul_le_mul_of_nonneg_left hLd hbeta).trans_lt hsub
    exact mul_neg_of_pos_of_neg (div_pos (Real.exp_pos _) hL) (sub_neg.mpr hcore)

/-- Sharp tail-envelope law: the left endpoint is the exact least upper bound on every
subcritical right-flank tail. -/
theorem tiltedTentRightProfile_tail_bound_iff
    {beta L r C : ℝ} (hbeta : 0 ≤ beta) (hL : 0 < L) (hsub : beta * L < 1)
    (hr0 : 0 ≤ r) (hrL : r ≤ L) :
    (∀ d ∈ Set.Icc r L, tiltedTentRightProfile beta L d ≤ C) ↔
      tiltedTentRightProfile beta L r ≤ C := by
  constructor
  · intro h
    exact h r ⟨le_rfl, hrL⟩
  · intro hr d hd
    by_cases hrd : r = d
    · simpa [hrd] using hr
    · have hrdlt : r < d := lt_of_le_of_ne hd.1 hrd
      have hrMem : r ∈ Set.Icc (0 : ℝ) L := ⟨hr0, hrL⟩
      have hdMem : d ∈ Set.Icc (0 : ℝ) L := ⟨hr0.trans hd.1, hd.2⟩
      exact ((tiltedTentRightProfile_strictAntiOn hbeta hL hsub)
        hrMem hdMem hrdlt).le.trans hr

/-- Every positive displacement contracts a subcritically tilted right tent below its apex. -/
theorem tiltedTentRightProfile_lt_one
    {beta L d : ℝ} (hbeta : 0 ≤ beta) (hL : 0 < L) (hsub : beta * L < 1)
    (hd0 : 0 < d) (hdL : d ≤ L) :
    tiltedTentRightProfile beta L d < 1 := by
  have hanti := tiltedTentRightProfile_strictAntiOn hbeta hL hsub
  have hlt := hanti (show 0 ∈ Set.Icc (0 : ℝ) L by simp [hL.le])
    (show d ∈ Set.Icc (0 : ℝ) L by exact ⟨hd0.le, hdL⟩) hd0
  simpa [tiltedTentRightProfile] using hlt

end GaloisForLFunctions.HTGeometry

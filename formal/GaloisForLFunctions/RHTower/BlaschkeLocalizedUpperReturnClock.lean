import GaloisForLFunctions.RHTower.BlaschkeLocalizedEarlyReturnClock
import GaloisForLFunctions.RHTower.SummableWeightedHeadFixedWaterCeiling

/-!
# Constructive upper return clock for the infinite Blaschke packet

Every coordinate in the active Blaschke head lies above the common water
line. This evaluates its normalized projective water mass exactly. The
fixed-water countable ceiling then yields a return whose logarithmic
deadline is the exact Blaschke depth entropy plus a linear active-head
rounding cost.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Every coordinate in the active Blaschke head lies above the water line
`exp (-L)`. -/
theorem exp_neg_le_blaschkeLocalizedWeight_activeHead
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {L : ℝ}
    (hLtail : blaschkeSpectralOffset a ≤ L)
    (hLzero : blaschkeSpectralSlope a ≤ L)
    (i : Fin (blaschkeActiveTailRadius a L + 2)) :
    Real.exp (-L) ≤ blaschkeLocalizedWeight a i := by
  let R := blaschkeActiveTailRadius a L
  refine Fin.cases ?_ (fun j => ?_) i
  · change Real.exp (-L) ≤ blaschkeLocalizedWeight a 0
    rw [blaschkeLocalizedWeight_zero]
    have ha2pos : 0 < a ^ 2 := sq_pos_of_pos ha0
    rw [← Real.exp_log ha2pos]
    apply Real.exp_le_exp.mpr
    rw [blaschkeSpectralSlope] at hLzero
    linarith
  · change Real.exp (-L) ≤
      blaschkeLocalizedWeight a ((j : ℕ) + 1)
    have hpositive :
        0 < blaschkeLocalizedWeight a (j + 1) :=
      blaschkeLocalizedWeight_succ_pos a ha0 ha1 j
    rw [← Real.exp_log hpositive]
    apply Real.exp_le_exp.mpr
    have hactive : (j : ℕ) ≤ blaschkeActiveTailRadius a L := by
      simpa only [R] using j.is_le
    have hdepth :
        blaschkeSpectralDepth a j ≤ L :=
      (blaschkeSpectralDepth_le_iff_le_activeTailRadius
        a ha0 ha1 hLtail j).2 hactive
    rw [blaschkeSpectralDepth] at hdepth
    linarith

/-- Projective clipped water mass is at most one for every finite
probability packet and every level. -/
theorem projectiveWaterMass_le_one
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (lam : ℝ) :
    projectiveWaterMass w k lam ≤ 1 := by
  rw [projectiveWaterMass]
  calc
    (∑ j, if j = k then 0 else min (w j) lam⁻¹) ≤
        ∑ j, w j := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hjk : j = k
      · subst j
        simp only [ite_true]
        exact hw k
      · simp only [hjk, ↓reduceIte]
        exact min_le_left _ _
    _ = 1 := hmass

/-- The normalized active Blaschke head has an exact constant-per-nonpivot
water mass. -/
theorem
    projectiveWaterMass_normalizedBlaschkeActiveHead_eq
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {L : ℝ}
    (hLtail : blaschkeSpectralOffset a ≤ L)
    (hLzero : blaschkeSpectralSlope a ≤ L)
    (pivot : Fin (blaschkeActiveTailRadius a L + 2)) :
    projectiveWaterMass
        (normalizedWeightedHeadWeight
          (blaschkeLocalizedWeight a)
          (blaschkeActiveTailRadius a L + 2))
        pivot
        (summableWeightedHeadMass
            (blaschkeLocalizedWeight a)
            (blaschkeActiveTailRadius a L + 2) *
          Real.exp L) =
      ((blaschkeActiveTailRadius a L + 1 : ℕ) : ℝ) *
        Real.exp (-L) /
        summableWeightedHeadMass
          (blaschkeLocalizedWeight a)
          (blaschkeActiveTailRadius a L + 2) := by
  let M := blaschkeActiveTailRadius a L + 2
  let m := summableWeightedHeadMass (blaschkeLocalizedWeight a) M
  have hM : 1 ≤ M := by
    dsimp only [M]
    omega
  have hmass : 0 < m := by
    dsimp only [m]
    exact summableWeightedHeadMass_blaschkeLocalizedWeight_pos
      a ha0 ha1 M hM
  have hlevelInv :
      (m * Real.exp L)⁻¹ = Real.exp (-L) / m := by
    rw [Real.exp_neg]
    field_simp [hmass.ne', Real.exp_ne_zero L]
  have hterm : ∀ j : Fin M,
      min (normalizedWeightedHeadWeight
          (blaschkeLocalizedWeight a) M j)
        ((m * Real.exp L)⁻¹) =
      Real.exp (-L) / m := by
    intro j
    rw [hlevelInv]
    apply min_eq_right
    rw [normalizedWeightedHeadWeight]
    apply (div_le_div_iff_of_pos_right hmass).2
    exact exp_neg_le_blaschkeLocalizedWeight_activeHead
      a ha0 ha1 hLtail hLzero j
  rw [projectiveWaterMass]
  change
    (∑ j : Fin M,
      if j = pivot then 0 else
        min (normalizedWeightedHeadWeight
          (blaschkeLocalizedWeight a) M j)
          ((m * Real.exp L)⁻¹)) =
      ((blaschkeActiveTailRadius a L + 1 : ℕ) : ℝ) *
        Real.exp (-L) / m
  simp_rw [hterm]
  have hsum :
      (∑ j : Fin M,
        if j = pivot then 0 else Real.exp (-L) / m) =
      ((M - 1 : ℕ) : ℝ) * (Real.exp (-L) / m) := by
    calc
      (∑ j : Fin M,
          if j = pivot then 0 else Real.exp (-L) / m) =
          ∑ j : Fin M,
            (Real.exp (-L) / m -
              if j = pivot then Real.exp (-L) / m else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjp : j = pivot <;> simp [hjp]
      _ = (M : ℝ) * (Real.exp (-L) / m) -
          Real.exp (-L) / m := by
        rw [Finset.sum_sub_distrib]
        simp
      _ = ((M - 1 : ℕ) : ℝ) * (Real.exp (-L) / m) := by
        have hMone : 1 ≤ M := hM
        rw [Nat.cast_sub hMone]
        push_cast
        ring
  rw [hsum]
  dsimp only [M, m]
  rw [show blaschkeActiveTailRadius a L + 2 - 1 =
      blaschkeActiveTailRadius a L + 1 by omega]
  ring

/-- Exact amplitude defect delivered by the active Blaschke water head. -/
def blaschkeActiveWaterReturnDefect (a L : ℝ) : ℝ :=
  ((blaschkeActiveTailRadius a L + 1 : ℕ) : ℝ) *
      Real.exp (-L) +
    2 * ((1 - a ^ 2) *
      (a ^ 2) ^ (blaschkeActiveTailRadius a L + 1))

/--
Exact constructive upper clock at Blaschke water level `L`.
-/
theorem exists_blaschkeLocalizedCoherenceDeadline_activeWater
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {L : ℝ}
    (hLtail : blaschkeSpectralOffset a ≤ L)
    (hLzero : blaschkeSpectralSlope a ≤ L) :
    ∃ T : ℕ,
      (∀ omega : ℕ → ℝ, ∃ n : ℕ,
        0 < n ∧ n ≤ T ∧
        1 - blaschkeActiveWaterReturnDefect a L ≤
          ‖summableWeightedPhaseAmplitude
            (blaschkeLocalizedWeight a) (fun k =>
              Complex.exp
                (Complex.I * ((((n : ℝ) * omega k : ℝ) : ℂ))))‖) ∧
      Real.log (T : ℝ) ≤
        blaschkeDepthWaterEntropy a L +
          (blaschkeActiveTailRadius a L + 1 : ℕ) *
            Real.log projectivePhaseResolutionConstant := by
  let M := blaschkeActiveTailRadius a L + 2
  let m := summableWeightedHeadMass (blaschkeLocalizedWeight a) M
  let eta : ℝ :=
    ((blaschkeActiveTailRadius a L + 1 : ℕ) : ℝ) *
      Real.exp (-L) / m
  let pivot : Fin M := ⟨0, by dsimp only [M]; omega⟩
  have hM : 2 ≤ M := by
    dsimp only [M]
    omega
  have hmass : 0 < m := by
    dsimp only [m]
    exact summableWeightedHeadMass_blaschkeLocalizedWeight_pos
      a ha0 ha1 M (by omega)
  have hetaEq :
      projectiveWaterMass
          (normalizedWeightedHeadWeight
            (blaschkeLocalizedWeight a) M)
          pivot (m * Real.exp L) = eta := by
    simpa only [M, m, eta] using
      projectiveWaterMass_normalizedBlaschkeActiveHead_eq
        a ha0 ha1 hLtail hLzero pivot
  have heta0 : 0 < eta := by
    dsimp only [eta]
    positivity
  have heta1 : eta ≤ 1 := by
    rw [← hetaEq]
    apply projectiveWaterMass_le_one
    · exact normalizedWeightedHeadWeight_nonneg
        (blaschkeLocalizedWeight a)
        (fun k => sq_nonneg (blaschkeLocalizedKernel a k))
        M hmass
    · exact sum_normalizedWeightedHeadWeight
        (blaschkeLocalizedWeight a) M hmass
  obtain ⟨T, hreturn, hlog⟩ :=
    exists_countableWeightedCoherenceDeadline_headFixedWaterCeiling
      (blaschkeLocalizedWeight a)
      (fun k => sq_nonneg (blaschkeLocalizedKernel a k))
      (blaschkeLocalizedKernel_sq_summable a ha0 ha1)
      (blaschkeLocalizedWeight_tsum a ha0 ha1)
      M hM hmass pivot heta0 heta1 (Real.exp_pos L)
      (by simpa only [m] using hetaEq.le)
  refine ⟨T, ?_, ?_⟩
  · intro omega
    obtain ⟨n, hn0, hnT, hnreturn⟩ := hreturn omega
    refine ⟨n, hn0, hnT, ?_⟩
    have htail :
        (∑' j : ℕ,
          blaschkeLocalizedWeight a (M + j)) =
        (1 - a ^ 2) *
          (a ^ 2) ^ (blaschkeActiveTailRadius a L + 1) := by
      have htailBase :=
        summablePurePointSurvivalTail_blaschkeLocalizedWeight
          a ha0 ha1 M (by omega)
      rw [show M - 1 = blaschkeActiveTailRadius a L + 1 by
        dsimp only [M]
        omega] at htailBase
      simpa only [summablePurePointSurvivalTail] using htailBase
    have hdefect :
        m * eta +
            2 * ∑' j : ℕ,
              blaschkeLocalizedWeight a (M + j) =
          blaschkeActiveWaterReturnDefect a L := by
      rw [htail]
      dsimp only [eta, blaschkeActiveWaterReturnDefect]
      field_simp [hmass.ne']
    rwa [hdefect] at hnreturn
  · have hentropy :=
      blaschkeActiveHeadWaterEntropy_eq
        a ha0 ha1 hLtail hLzero
    simpa only [M, hentropy,
      show blaschkeActiveTailRadius a L + 2 - 1 =
        blaschkeActiveTailRadius a L + 1 by omega] using hlog

end RHTower

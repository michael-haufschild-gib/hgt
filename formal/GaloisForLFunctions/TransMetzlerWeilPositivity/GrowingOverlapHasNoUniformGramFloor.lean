import GaloisForLFunctions.TransMetzlerWeilPositivity.ExplicitPlateauParameters
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ExactSuccessorShellWindows
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanCrossTermsVanishOnPeriodicProfiles

/-!
# Growing overlap has no uniform coefficient-mass lower bound

The difference of the last two atoms has coefficient squared mass two.
After division by twice one atom's mass, its actual squared mass is
`1-Cφ(t)/Cφ(0)`, where `t` is the logarithmic gap divided by the width.
At every overlap schedule tending to infinity, `t` tends to zero.
Thus no fixed positive lower comparison of these two norms survives.
-/

noncomputable section

set_option autoImplicit false

open Finset MeasureTheory Filter Topology

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory

/-- Opposite unit coefficients at the last two centers of horizon `N+1`. -/
def adjacentDipoleWeights (N n : ℕ) : ℝ :=
  (if n = N then 1 else 0) - (if n = N + 1 then 1 else 0)

theorem atomicTest_adjacentDipole {N : ℕ} (hN : 1 ≤ N) (g : ℝ → ℝ) (u : ℝ) :
    atomicTest (N + 1) (adjacentDipoleWeights N) g u =
      g (u - Real.log N) - g (u - Real.log (N + 1 : ℕ)) := by
  have hn : N ∈ Icc 1 (N + 1) := mem_Icc.mpr ⟨hN, Nat.le_succ N⟩
  have hsucc : N + 1 ∈ Icc 1 (N + 1) := mem_Icc.mpr ⟨by omega, le_rfl⟩
  change (∑ n ∈ Icc 1 (N + 1),
    ((if n = N then 1 else 0) - (if n = N + 1 then 1 else 0)) * g (u - Real.log n)) = _
  simp_rw [sub_mul]
  rw [sum_sub_distrib]
  have hunit (a : ℕ) (ha : a ∈ Icc 1 (N + 1)) :
      (∑ n ∈ Icc 1 (N + 1), (if n = a then (1 : ℝ) else 0) * g (u - Real.log n)) =
        g (u - Real.log a) := by
    rw [sum_eq_single_of_mem a ha]
    · simp only [if_pos rfl, one_mul]
    · intro b _ hba
      rw [if_neg hba, zero_mul]
  rw [hunit N hn, hunit (N + 1) hsucc]

theorem adjacentDipole_coefficient_mass {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 (N + 1), adjacentDipoleWeights N n ^ 2 = 2 := by
  have hn : N ∈ Icc 1 (N + 1) := mem_Icc.mpr ⟨hN, Nat.le_succ N⟩
  have hsucc : N + 1 ∈ Icc 1 (N + 1) := mem_Icc.mpr ⟨by omega, le_rfl⟩
  have heq : ∀ n, adjacentDipoleWeights N n ^ 2 =
      (if n = N then (1 : ℝ) else 0) + (if n = N + 1 then 1 else 0) := by
    intro n
    unfold adjacentDipoleWeights
    split_ifs with h₁ h₂ <;> norm_num <;> omega
  simp_rw [heq]
  rw [sum_add_distrib]
  simp [hn, hsucc]

/-- Logarithmic separation of the adjacent centers in profile coordinates. -/
def adjacentProfileLag (c : ℝ) (N : ℕ) : ℝ :=
  (Real.log (N + 1 : ℕ) - Real.log N) / (c / (N + 1 : ℕ))

/-- Actual squared mass divided by the coefficient mass times one atom's mass. -/
def plateauAdjacentMassRatio (c : ℝ) (N : ℕ) : ℝ :=
  (∫ u, atomicTest (N + 1) (adjacentDipoleWeights N)
    (atomDilate transMetzlerProfile (c / (N + 1 : ℕ))) u ^ 2) /
    (2 * ∫ u, atomDilate transMetzlerProfile (c / (N + 1 : ℕ)) u ^ 2)

/-- The exact Gram ratio is the autocorrelation deficit at the rescaled adjacent gap. -/
theorem plateauAdjacentMassRatio_eq {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    plateauAdjacentMassRatio c N =
      1 - bumpCorr transMetzlerProfile (adjacentProfileLag c N) /
        (∫ u, transMetzlerProfile u ^ 2) := by
  let g := atomDilate transMetzlerProfile (c / (N + 1 : ℕ))
  let t := Real.log (N + 1 : ℕ) - Real.log N
  have hw : 0 < c / (N + 1 : ℕ) := div_pos hc (by positivity)
  have hint : (∫ u, atomicTest (N + 1) (adjacentDipoleWeights N) g u ^ 2) =
      ∫ u, (g u - g (u + t)) ^ 2 := by
    simp_rw [atomicTest_adjacentDipole hN]
    have htranslate := integral_sub_right_eq_self (μ := volume)
      (fun u => (g u - g (u + t)) ^ 2) (Real.log (N + 1 : ℕ))
    rw [← htranslate]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      rw [show u - Real.log (N + 1 : ℕ) + t = u - Real.log N by dsimp only [t]; ring]
      ring
  unfold plateauAdjacentMassRatio
  rw [hint, integral_sub_shift_atomDilate hw,
    integral_sub_shift_sq_eq contDiff_transMetzlerProfile.continuous
      hasCompactSupport_transMetzlerProfile, integral_atomDilate_sq hw]
  change (c / (N + 1 : ℕ) *
    (2 * (∫ u, transMetzlerProfile u ^ 2) -
      2 * bumpCorr transMetzlerProfile (adjacentProfileLag c N))) /
    (2 * (c / (N + 1 : ℕ) * (∫ u, transMetzlerProfile u ^ 2))) = _
  field_simp [integral_transMetzlerProfile_sq_pos.ne', hw.ne']
  ring

private theorem tendsto_succ_div_nat :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / N) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := hone.add hsmall
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := (show (0 : ℝ) < N by exact_mod_cast hN).ne'
  push_cast
  field_simp

/-- Growing overlap makes adjacent logarithmic centers indistinguishable at profile scale. -/
theorem tendsto_adjacentProfileLag {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) :
    Tendsto (fun N => adjacentProfileLag (c N) N) atTop (𝓝 0) := by
  have h := (tendsto_firstExteriorOverlap.mul tendsto_succ_div_nat).div_atTop hc
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ), hc.eventually_gt_atTop 0] with N hN hcN
  have hN0 : (N : ℝ) ≠ 0 := (show (0 : ℝ) < N by exact_mod_cast hN).ne'
  dsimp only [adjacentProfileLag, firstExteriorOverlap]
  field_simp [hN0, hcN.ne']

/-- At every overlap schedule tending to infinity, a coefficient vector of squared mass two
has vanishing atom-normalized synthesized mass. -/
theorem tendsto_plateauAdjacentMassRatio {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) :
    Tendsto (fun N => plateauAdjacentMassRatio (c N) N) atTop (𝓝 0) := by
  have hcorr := (continuous_bumpCorr contDiff_transMetzlerProfile
    hasCompactSupport_transMetzlerProfile).tendsto 0
  have hquot := (hcorr.comp (tendsto_adjacentProfileLag hc)).div_const
    (∫ u, transMetzlerProfile u ^ 2)
  rw [bumpCorr_zero, div_self integral_transMetzlerProfile_sq_pos.ne'] at hquot
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := hone.sub hquot
  rw [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ), hc.eventually_gt_atTop 0] with N hN hcN
  exact (plateauAdjacentMassRatio_eq hcN hN).symm

/-- The explicit adjacent vector violates every proposed positive uniform mass floor. -/
theorem eventually_plateau_adjacentDipole_mass_lt {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∫ u, atomicTest (N + 1) (adjacentDipoleWeights N)
        (atomDilate transMetzlerProfile (c N / (N + 1 : ℕ))) u ^ 2) <
      ε * (∫ u, atomDilate transMetzlerProfile (c N / (N + 1 : ℕ)) u ^ 2) *
        ∑ n ∈ Icc 1 (N + 1), adjacentDipoleWeights N n ^ 2 := by
  filter_upwards [(tendsto_plateauAdjacentMassRatio hc).eventually (gt_mem_nhds hε),
    hc.eventually_gt_atTop 0, eventually_ge_atTop (1 : ℕ)] with N hratio hcN hN
  have hmass : 0 < ∫ u, atomDilate transMetzlerProfile (c N / (N + 1 : ℕ)) u ^ 2 := by
    rw [integral_atomDilate_sq (div_pos hcN (by positivity))]
    exact mul_pos (div_pos hcN (by positivity)) integral_transMetzlerProfile_sq_pos
  dsimp only [plateauAdjacentMassRatio] at hratio
  have hnum := (div_lt_iff₀ (mul_pos two_pos hmass)).mp hratio
  rw [adjacentDipole_coefficient_mass hN]
  nlinarith only [hnum]

/-- No positive constant compares synthesized mass from below with coefficient mass times
one atom's mass along a growing-overlap schedule. -/
theorem no_uniform_plateau_atomic_mass_floor {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      ε * (∫ u, atomDilate transMetzlerProfile (c N / (N + 1 : ℕ)) u ^ 2) *
          (∑ n ∈ Icc 1 (N + 1), x n ^ 2) ≤
        ∫ u, atomicTest (N + 1) x
          (atomDilate transMetzlerProfile (c N / (N + 1 : ℕ))) u ^ 2 := by
  rintro ⟨ε, hε, hfloor⟩
  obtain ⟨N, hsmall, hN⟩ :=
    ((eventually_plateau_adjacentDipole_mass_lt hc hε).and hfloor).exists
  exact (not_le_of_gt hsmall) (hN (adjacentDipoleWeights N))

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.atomicTest_adjacentDipole
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.plateauAdjacentMassRatio_eq
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.tendsto_plateauAdjacentMassRatio
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.no_uniform_plateau_atomic_mass_floor

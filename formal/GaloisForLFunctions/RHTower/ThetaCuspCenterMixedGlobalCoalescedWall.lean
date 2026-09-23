import GaloisForLFunctions.RHTower.HedenmalmCenterMixedCorrelationAngle
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedLocalThreePoint

open Set

namespace RHTower

noncomputable section

/-- Global three-point positivity controls the full coalesced first-gap wall at every
nonnegative second gap. -/
theorem thetaCuspCenterMixedGlobalCoalescedWall_nonneg
    {a y : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (hy : 0 ≤ y) :
    0 ≤ (-thetaCuspCenterMixedDensitySecondJet a 0) *
          (thetaCuspCenterMixedDensity a 0 ^ (2 : ℕ) -
            thetaCuspCenterMixedDensity a y ^ (2 : ℕ)) -
        thetaCuspCenterMixedDensity a 0 *
          thetaCuspCenterMixedDensityFirstJet a y ^ (2 : ℕ) := by
  let f : ℝ → ℝ := thetaCuspCenterMixedDensity a
  let f' : ℝ → ℝ := thetaCuspCenterMixedDensityFirstJet a
  let f'' : ℝ → ℝ := thetaCuspCenterMixedDensitySecondJet a
  let D : ℝ → ℝ := HilbertMetric.threePointCorrelationDeterminantPath f y
  let D' : ℝ → ℝ :=
    HilbertMetric.threePointCorrelationDeterminantPathFirstJet f f' y
  let D'' : ℝ → ℝ :=
    HilbertMetric.threePointCorrelationDeterminantPathSecondJet f f' f'' y
  have hf : ∀ x, HasDerivAt f (f' x) x := fun x => by
    simpa only [f, f'] using hasDerivAt_thetaCuspCenterMixedDensity ha0.le ha x
  have hf' : ∀ x, HasDerivAt f' (f'' x) x := fun x => by
    simpa only [f', f''] using
      hasDerivAt_thetaCuspCenterMixedDensityFirstJet ha0.le ha x
  have hD : ∀ x, HasDerivAt D (D' x) x := fun x => by
    simpa only [D, D'] using
      HilbertMetric.hasDerivAt_threePointCorrelationDeterminantPath hf y x
  have hD' : ∀ x, HasDerivAt D' (D'' x) x := fun x => by
    simpa only [D', D''] using
      HilbertMetric.hasDerivAt_threePointCorrelationDeterminantPathFirstJet hf hf' y x
  have hD'' : Continuous D'' := by
    have hfcont : Continuous f :=
      continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
    have hf'cont : Continuous f' :=
      continuous_iff_continuousAt.mpr fun x => (hf' x).continuousAt
    have hf''cont : Continuous f'' := by
      simpa only [f''] using
        continuous_thetaCuspCenterMixedDensitySecondJet ha0.le ha
    change Continuous (fun x =>
      2 * (f'' x * f y * f (x + y) + 2 * f' x * f y * f' (x + y) +
        f x * f y * f'' (x + y)) -
      2 * f 0 * (f' x ^ (2 : ℕ) + f x * f'' x + f' (x + y) ^ (2 : ℕ) +
        f (x + y) * f'' (x + y)))
    fun_prop
  have hfirst : f' 0 = 0 := by
    simpa only [f'] using thetaCuspCenterMixedDensityFirstJet_zero a
  have hDzero : D 0 = 0 := by
    simp [D, HilbertMetric.threePointCorrelationDeterminantPath,
      HilbertMetric.threePointCorrelationDeterminant]
    ring
  have hD'zero : D' 0 = 0 := by
    simp [D', HilbertMetric.threePointCorrelationDeterminantPathFirstJet, hfirst]
    ring
  have hD''zero : D'' 0 =
      2 * ((-f'' 0) * (f 0 ^ (2 : ℕ) - f y ^ (2 : ℕ)) - f 0 * f' y ^ (2 : ℕ)) := by
    simp [D'', HilbertMetric.threePointCorrelationDeterminantPathSecondJet, hfirst]
    ring
  by_contra hnot
  have hwall :
      (-f'' 0) * (f 0 ^ (2 : ℕ) - f y ^ (2 : ℕ)) - f 0 * f' y ^ (2 : ℕ) < 0 := by
    simpa only [f, f', f''] using lt_of_not_ge hnot
  have hsecondNeg : 0 < -D'' 0 := by rw [hD''zero]; linarith
  obtain ⟨ε, hε, hright⟩ :=
    HilbertMetric.exists_pos_right_of_secondJet_pos
      (F := fun x => -D x) (F' := fun x => -D' x) (F'' := fun x => -D'' x)
      (fun x => (hD x).neg) (fun x => (hD' x).neg) hD''.neg
      (by simp [hDzero]) (by simp [hD'zero]) hsecondNeg
  let x := ε / 2
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hxε : x < ε := by dsimp [x]; linarith
  have hneg : D x < 0 := by linarith [hright x hx0 hxε]
  have hglobal :=
    thetaCuspCenterMixedThreePointDeterminant_nonneg ha0 ha hx0.le hy
  have heq : D x = thetaCuspCenterMixedThreePointDeterminant a x y := by
    rfl
  rw [← heq] at hglobal
  exact (not_lt_of_ge hglobal) hneg

/-- The normalized center-mixed correlation angle cannot move faster than its coalesced
center speed.  This is the division form of the global coalesced wall. -/
theorem thetaCuspCenterMixedCorrelationAngleSpeedSq_le_center
    {a y : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (hy : 0 < y) :
    thetaCuspCenterMixedDensityFirstJet a y ^ (2 : ℕ) /
          (thetaCuspCenterMixedDensity a 0 ^ (2 : ℕ) -
            thetaCuspCenterMixedDensity a y ^ (2 : ℕ)) ≤
      (-thetaCuspCenterMixedDensitySecondJet a 0) /
        thetaCuspCenterMixedDensity a 0 := by
  let f0 := thetaCuspCenterMixedDensity a 0
  let fy := thetaCuspCenterMixedDensity a y
  have hf0 : 0 < f0 := by
    simpa only [f0] using thetaCuspCenterMixedDensity_pos ha0 ha 0
  have hfy : 0 < fy := by
    simpa only [fy] using thetaCuspCenterMixedDensity_pos ha0 ha y
  have hlt : fy < f0 := by
    simpa only [fy, f0] using thetaCuspCenterMixedDensity_lt_zero ha0 ha hy
  have hgap : 0 < f0 ^ (2 : ℕ) - fy ^ (2 : ℕ) := by
    have hsquare : fy ^ (2 : ℕ) < f0 ^ (2 : ℕ) := (sq_lt_sq₀ hfy.le hf0.le).2 hlt
    linarith
  have hwall := thetaCuspCenterMixedGlobalCoalescedWall_nonneg ha0 ha hy.le
  apply (div_le_div_iff₀ hgap hf0).2
  dsimp only [f0, fy] at hgap ⊢
  nlinarith

end

end RHTower

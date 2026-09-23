import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFinitePositiveAtomicSeamNoGo

/-!
# Countable positive seam obstruction for Parikh--Wilczek reflection

A countable positive atomic completed seam may mix every physical energy into
infinitely many target-energy channels. If both total mass and first target
energy moment are summable, the two Mellin reflection grades still cannot hold
within a finite physical interval: positivity makes the endpoint-gap series
strictly positive, while the two grades force it negative. A nonzero
independent seam contact is explicitly retained.

Proof-chain role:
`countable positive finite-energy CTP seam + finite-energy contact -> two
Mellin reflection grades` is impossible. PW-B must therefore derive an
unbounded reciprocal tail, signed/complex transport, or a singular spectral
mechanism before it can attempt fixed-grade partner balance and Xi occurrence.
-/

namespace RHTower

noncomputable section

/-- A countable positive, energy-nonlocal candidate CTP seam. The separate
contact is retained rather than absorbed into the reverse kernel. -/
structure PWFiniteEnergyPositiveCountableFEReflectionData (X : ℝ) where
  energy : ℕ → ℝ
  energy_mem : ∀ n, 0 < energy n ∧ energy n < X
  weight : ℝ → ℕ → ℝ
  weight_nonneg : ∀ {x : ℝ}, 0 < x → x < X → ∀ n, 0 ≤ weight x n
  weight_summable : ∀ {x : ℝ}, 0 < x → x < X → Summable (weight x)
  moment_summable : ∀ {x : ℝ}, 0 < x → x < X →
    Summable (fun n => weight x n * energy n)
  mellinGradeOne : ∀ {x : ℝ}, 0 < x → x < X →
    (∑' n, weight x n) = x⁻¹
  mellinGradeTwo : ∀ {x : ℝ}, 0 < x → x < X →
    (∑' n, weight x n * energy n) = x⁻¹ ^ (2 : ℕ)
  contact : ℂ
  contact_ne_zero : contact ≠ 0

/-- **Countable-positive CTP seam no-go.** No countable positive atomic seam
with finite target-energy support, even with a separate nonzero contact, can
realize the two Mellin grades of functional-equation reflection. -/
theorem no_PWFiniteEnergyPositiveCountableFEReflectionData
    {X : ℝ} (hX : 0 < X) :
    IsEmpty (PWFiniteEnergyPositiveCountableFEReflectionData X) := by
  refine ⟨fun D => ?_⟩
  let x : ℝ := X / (X ^ (2 : ℕ) + 1)
  have hden : 0 < X ^ (2 : ℕ) + 1 := by positivity
  have hx0 : 0 < x := div_pos hX hden
  have hxX : x < X := by
    dsimp only [x]
    exact div_lt_self hX (by nlinarith [sq_pos_of_pos hX])
  have hmass := D.mellinGradeOne hx0 hxX
  have hmoment := D.mellinGradeTwo hx0 hxX
  have hweight_summable := D.weight_summable hx0 hxX
  have hmoment_summable := D.moment_summable hx0 hxX
  have hweight_nonneg (n : ℕ) : 0 ≤ D.weight x n :=
    D.weight_nonneg hx0 hxX n
  have hmass_pos : 0 < ∑' n, D.weight x n := by
    rw [hmass]
    exact inv_pos.mpr hx0
  have hweight_exists : ∃ n, 0 < D.weight x n := by
    by_contra h
    push Not at h
    have hzero : ∀ n, D.weight x n = 0 := fun n =>
      le_antisymm (h n) (hweight_nonneg n)
    have : (∑' n, D.weight x n) = 0 := by simp [hzero]
    linarith
  obtain ⟨n, hn⟩ := hweight_exists
  have hgap_summable : Summable (fun m => D.weight x m * (X - D.energy m)) := by
    rw [show (fun m => D.weight x m * (X - D.energy m)) =
      (fun m => D.weight x m * X - D.weight x m * D.energy m) by
        funext m
        ring]
    exact (hweight_summable.mul_right X).sub hmoment_summable
  have hgap_nonneg (m : ℕ) : 0 ≤ D.weight x m * (X - D.energy m) :=
    mul_nonneg (hweight_nonneg m) (sub_nonneg.mpr (D.energy_mem m).2.le)
  have hgap_term_pos : 0 < D.weight x n * (X - D.energy n) :=
    mul_pos hn (sub_pos.mpr (D.energy_mem n).2)
  have hgap_pos : 0 < ∑' m, D.weight x m * (X - D.energy m) :=
    hgap_summable.tsum_pos hgap_nonneg n hgap_term_pos
  have hgap_eq : (∑' m, D.weight x m * (X - D.energy m)) =
      (∑' m, D.weight x m) * X - ∑' m, D.weight x m * D.energy m := by
    calc
      (∑' m, D.weight x m * (X - D.energy m)) =
          ∑' m, (D.weight x m * X - D.weight x m * D.energy m) := by
            congr with m
            ring
      _ = (∑' m, D.weight x m * X) - ∑' m, D.weight x m * D.energy m :=
          (hweight_summable.mul_right X).hasSum.sub hmoment_summable.hasSum |>.tsum_eq
      _ = (∑' m, D.weight x m) * X - ∑' m, D.weight x m * D.energy m := by
          rw [tsum_mul_right]
  have hinv_gt : X < x⁻¹ := by
    have hxinv : x⁻¹ = X + X⁻¹ := by
      dsimp only [x]
      field_simp [hX.ne']
    rw [hxinv]
    exact lt_add_of_pos_right X (inv_pos.mpr hX)
  have hinv_pos : 0 < x⁻¹ := inv_pos.mpr hx0
  have hreciprocal_lt : x⁻¹ * X < x⁻¹ * x⁻¹ :=
    mul_lt_mul_of_pos_left hinv_gt hinv_pos
  rw [hgap_eq, hmass, hmoment, pow_two] at hgap_pos
  linarith

end

end RHTower

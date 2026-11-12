import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerContactCoefficientIsTheRealResidue
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerContactDirichletSeries

/-!
# The harmonically centered critical contact transform

Critical comb convergence makes the harmonic remainder bounded and
convergent. Its Mellin transform is holomorphic on the right half-plane
and has zero residue at each nonreal boundary point. Restoring the
removed harmonic symbol preserves both properties.
-/

noncomputable section

open Complex Finset Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity TransHorizonIncidenceMechanics

theorem criticalHarmonicContacts_zero : criticalHarmonicContacts 0 = 0 := by
  simp [criticalHarmonicContacts, powerContactPrefix, harm]

private theorem criticalHarmonicContacts_normalized_limit
    (hc : PowerCombTailConverges (1 / 2)) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(0 : ℝ)) * criticalHarmonicContacts N)
      atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := criticalPowerCombTailConverges_iff_harmonicContacts_converges.mp hc
  exact ⟨L, by simpa only [neg_zero, Real.rpow_zero, one_mul] using hL⟩

/-- The bounded remainder transform with the exact removed harmonic
Dirichlet symbol restored. -/
def criticalPowerContactMellin (s : ℂ) : ℂ :=
  complexMellinPairing criticalHarmonicContacts s +
    (criticalPowerContactCoefficient : ℂ) * riemannZeta (s + 1)

/-- Critical comb convergence supplies holomorphy to the right of zero. -/
theorem differentiableOn_criticalPowerContactMellin
    (hc : PowerCombTailConverges (1 / 2)) :
    DifferentiableOn ℂ criticalPowerContactMellin {s : ℂ | 0 < s.re} := by
  obtain ⟨L, hL⟩ := criticalHarmonicContacts_normalized_limit hc
  obtain ⟨C, _, hb⟩ := exists_power_bound_of_normalized_tendsto
    criticalHarmonicContacts_zero hL
  have hΦ := differentiableOn_complexMellinPairing_of_power_bound
    criticalHarmonicContacts_zero (le_refl (0 : ℝ)) hb
  refine hΦ.add ?_
  intro s hs
  have hs1 : s + 1 ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [add_re, one_re] at hr
    change 0 < s.re at hs
    linarith only [hr, hs]
  exact (((differentiableAt_riemannZeta hs1).comp s
    (differentiableAt_id.add_const 1)).const_mul _).differentiableWithinAt

/-- Restoring the harmonic symbol creates no nonreal boundary residue. -/
theorem tendsto_mul_criticalPowerContactMellin_at_nonreal_boundary
    (hc : PowerCombTailConverges (1 / 2)) {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun ε : ℝ => (ε : ℂ) *
      criticalPowerContactMellin ((ε : ℂ) + (τ : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨L, hL⟩ := criticalHarmonicContacts_normalized_limit hc
  have hΦ := tendsto_mul_complexMellinPairing_at_nonreal_boundary
    criticalHarmonicContacts_zero (le_refl (0 : ℝ)) hτ hL
  simp only [zero_add] at hΦ
  have heps : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hpath : Tendsto (fun ε : ℝ => (ε : ℂ) + (τ : ℂ) * I + 1)
      (𝓝[>] 0) (𝓝 ((τ : ℂ) * I + 1)) := by
    simpa only [zero_add] using (heps.add_const ((τ : ℂ) * I)).add_const 1
  have hne : (τ : ℂ) * I + 1 ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
      mul_one, zero_mul, add_zero, one_im] at hi
    exact hτ hi
  have hζpath := (differentiableAt_riemannZeta hne).continuousAt.tendsto.comp hpath
  have hζ := hζpath.const_mul (criticalPowerContactCoefficient : ℂ)
  have hz := heps.mul hζ
  rw [zero_mul] at hz
  have hsum := hΦ.add hz
  rw [add_zero] at hsum
  exact hsum.congr fun ε => (mul_add _ _ _).symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

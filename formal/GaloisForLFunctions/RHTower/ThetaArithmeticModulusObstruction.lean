import GaloisForLFunctions.RHTower.ThetaRealGroundPolarization

/-!
# Taking the modulus can strictly increase the complete arithmetic energy

The disjoint-bump construction survives the full arithmetic form. Its signed
and nonnegative profiles have the same pointwise modulus and the same ground
mass, but the nonnegative profile has strictly larger energy. Every scalar
mass shift retains this obstruction. This does not assert a negative Weil
energy and does not decide RH.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

open GaloisForLFunctions.RHTower

/-- An unconditional counterexample to modulus contraction for the full form.
The same two profiles work for every scalar shift of the ground mass. -/
theorem exists_compact_thetaArithmetic_modulus_increase :
    ∃ f g : 𝓢(ℝ, ℝ),
      HasCompactSupport f ∧ HasCompactSupport g ∧
      (∀ x, g x = |f x|) ∧
      thetaGroundNormSq (thetaComplexify f) = thetaGroundNormSq (thetaComplexify g) ∧
      ∀ c : ℝ,
        thetaRealArithmeticQuadratic f + c * thetaGroundNormSq (thetaComplexify f) <
          thetaRealArithmeticQuadratic g + c * thetaGroundNormSq (thetaComplexify g) := by
  obtain ⟨phi, psi, hp, hq, hd, hgap, _, hcross, hpc, hqc⟩ :=
    exists_disjoint_positive_compact_thetaGammaPolarGroundCrossPairing
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y :=
    fun x hx y hy => screwSignThreshold_pos.trans (hgap x hx y hy).1
  have hatom : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n :=
    fun x hx y hy => (hgap x hx y hy).2
  have habs (x : ℝ) : (phi + psi) x = |(phi - psi) x| := by
    simp only [add_apply, sub_apply]
    by_cases hx : phi x = 0
    · simp [hx, abs_of_nonneg (hq x)]
    · have hy : psi x = 0 := by
        by_contra hy
        exact (Set.disjoint_left.mp hd hx hy)
      simp [hy, abs_of_nonneg (hp x)]
  have hnorm : thetaGroundNormSq (thetaComplexify (phi - psi)) =
      thetaGroundNormSq (thetaComplexify (phi + psi)) := by
    unfold thetaGroundNormSq thetaGroundNormDensity
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [thetaComplexify_apply, Complex.norm_real, Real.norm_eq_abs, habs, abs_abs]
  have hdiff := thetaRealArithmeticQuadratic_disjoint_polarization phi psi hsep hatom
  refine ⟨phi - psi, phi + psi, hpc.sub hqc, hpc.add hqc, habs, hnorm, fun c => ?_⟩
  rw [hnorm]
  linarith

theorem exists_thetaArithmetic_modulus_increase :
    ∃ f g : 𝓢(ℝ, ℝ),
      (∀ x, g x = |f x|) ∧
      thetaGroundNormSq (thetaComplexify f) = thetaGroundNormSq (thetaComplexify g) ∧
      ∀ c : ℝ,
        thetaRealArithmeticQuadratic f + c * thetaGroundNormSq (thetaComplexify f) <
          thetaRealArithmeticQuadratic g + c * thetaGroundNormSq (thetaComplexify g) := by
  obtain ⟨f, g, _, _, habs, hmass, hlt⟩ := exists_compact_thetaArithmetic_modulus_increase
  exact ⟨f, g, habs, hmass, hlt⟩

/-- No scalar multiple of the ground mass repairs the modulus inequality. -/
theorem not_thetaArithmetic_modulus_contracts (c : ℝ) :
    ¬ ∀ f g : 𝓢(ℝ, ℝ), (∀ x, g x = |f x|) →
      thetaRealArithmeticQuadratic g + c * thetaGroundNormSq (thetaComplexify g) ≤
        thetaRealArithmeticQuadratic f + c * thetaGroundNormSq (thetaComplexify f) := by
  obtain ⟨f, g, habs, _, hlt⟩ := exists_thetaArithmetic_modulus_increase
  intro h
  exact (not_le_of_gt (hlt c)) (h f g habs)

end RHTower.ThetaSourceWard

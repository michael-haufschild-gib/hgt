import GaloisForLFunctions.RHTower.XiGaussianDeletedProductBound

/-!
# Removing one conjugate orbit without losing its value

The finite real products annihilate all other divisor copies. Their value
at the retained node converges to a nonzero number, by reciprocal-square
summability. No zero location or simplicity assumption is used.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Copies outside the selected squared-coordinate conjugate orbit. -/
def xiGaussianOrbitComplement (z : ℂ) : Set XiZeroCopy :=
  {q | xiSpectralPoint q ^ 2 ≠ z ∧ xiSpectralPoint q ^ 2 ≠ (starRingEnd ℂ) z}

private def orbitProductIncrement (z : ℂ) (conjugate : Bool) (q : XiZeroCopy) : ℂ := by
  classical
  exact if q ∈ xiGaussianOrbitComplement z then
    -(if conjugate then (starRingEnd ℂ) ((xiSpectralPoint q ^ 2)⁻¹)
      else (xiSpectralPoint q ^ 2)⁻¹) * z else 0

private theorem summable_norm_orbitProductIncrement (z : ℂ) (b : Bool) :
    Summable (fun q => ‖orbitProductIncrement z b q‖) := by
  apply (xiSpectralPoint_inv_sq_summable.mul_right ‖z‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun q => ?_)
  by_cases h : q ∈ xiGaussianOrbitComplement z
  · cases b <;> simp [orbitProductIncrement, h, norm_inv, norm_pow, one_div]
  · simp only [orbitProductIncrement, if_neg h, norm_zero]
    positivity

private theorem one_add_orbitProductIncrement_ne_zero (z : ℂ) (b : Bool)
    (q : XiZeroCopy) : 1 + orbitProductIncrement z b q ≠ 0 := by
  classical
  by_cases h : q ∈ xiGaussianOrbitComplement z
  · have hw : xiSpectralPoint q ^ 2 ≠ 0 := pow_ne_zero _ (xiSpectralPoint_ne_zero q)
    have hp : xiSpectralPoint q ^ 2 ≠ z ∧
        xiSpectralPoint q ^ 2 ≠ (starRingEnd ℂ) z := h
    cases b
    · simp only [orbitProductIncrement, if_pos h, Bool.false_eq_true, if_false,
        neg_mul, ← sub_eq_add_neg]
      intro he
      exact hp.1 ((inv_mul_eq_one₀ hw).mp (sub_eq_zero.mp he).symm)
    · simp only [orbitProductIncrement, if_pos h, if_true,
        neg_mul, ← sub_eq_add_neg, map_inv₀]
      intro he
      have hz := (inv_mul_eq_one₀ ((_root_.map_ne_zero (starRingEnd ℂ)).mpr hw)).mp
        (sub_eq_zero.mp he).symm
      exact hp.2 (by simpa using congrArg (starRingEnd ℂ) hz)
  · simp [orbitProductIncrement, h]

/-- The target value converges to a nonzero number even though all other
orbits are eventually annihilated. Multiplicity remains in every product. -/
theorem exists_xiGaussianOrbitProduct_nonzero_limit (z : ℂ) :
    ∃ a : ℂ, a ≠ 0 ∧ Tendsto
      (fun F : Finset XiZeroCopy =>
        evalRealPolynomial (xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) F) z)
      atTop (𝓝 a) := by
  classical
  let f := orbitProductIncrement z false
  let g := orbitProductIncrement z true
  have hf := summable_norm_orbitProductIncrement z false
  have hg := summable_norm_orbitProductIncrement z true
  let a := ∏' q, (1 + f q)
  let b := ∏' q, (1 + g q)
  have ha : a ≠ 0 := tprod_one_add_ne_zero_of_summable
    (one_add_orbitProductIncrement_ne_zero z false) hf
  have hb : b ≠ 0 := tprod_one_add_ne_zero_of_summable
    (one_add_orbitProductIncrement_ne_zero z true) hg
  refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
  have hlim := (multipliable_one_add_of_summable hf).hasProd.mul
    (multipliable_one_add_of_summable hg).hasProd
  change Tendsto (fun F : Finset XiZeroCopy =>
    ∏ q ∈ F, (1 + f q) * (1 + g q)) atTop (𝓝 (a * b)) at hlim
  apply hlim.congr
  intro F
  rw [xiGaussianSelectedAnnihilator, eval_xiGaussianAnnihilator, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro q _
  by_cases h : q ∈ xiGaussianOrbitComplement z <;>
    simp [f, g, orbitProductIncrement, h, eval_realNormalizedConjFactor, sub_eq_add_neg]

/-- A retained-complement copy is killed once its own factor is present. -/
theorem eventually_xiGaussianOrbitProduct_eval_zero (z : ℂ)
    (q : {q : XiZeroCopy // q ∈ xiGaussianOrbitComplement z}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop,
      evalRealPolynomial (xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) F)
        (xiSpectralPoint q.1 ^ 2) = 0 := by
  classical
  filter_upwards [eventually_ge_atTop ({q.1} : Finset XiZeroCopy)] with F hF
  exact xiGaussianAnnihilator_vanishes _
    ⟨q.1, Finset.mem_filter.mpr ⟨hF (Finset.mem_singleton_self q.1), q.property⟩⟩

end RHTower

import GaloisForLFunctions.RHTower.XiGaussianPolarRemoval

/-!
# Exact finite interpolation during polar removal

The polar correction vanishes on every divisor copy included in its finite
product. Consequently an arbitrary finite set of complex sample values can
be preserved exactly while the polar evaluation is removed and the full
native quadratic expressions change arbitrarily little on a heat half-line.
-/

open Complex Polynomial Filter Topology
open scoped Real
noncomputable section
namespace RHTower

theorem xiGaussianPolarAnnihilator_vanishes (F : Finset XiZeroCopy)
    (q : {q : XiZeroCopy // q ∈ F}) :
    evalRealPolynomial (xiGaussianPolarAnnihilator F) (xiSpectralPoint q.1 ^ 2) = 0 := by
  rw [xiGaussianPolarAnnihilator, evalRealPolynomial_mul,
    xiGaussianAnnihilator_vanishes F q, mul_zero]

/-- Polar removal preserves each selected complex sample, not only its norm. -/
theorem xiGaussianRemovePolar_eval_selected (P : Polynomial ℝ) (F : Finset XiZeroCopy)
    (q : {q : XiZeroCopy // q ∈ F}) :
    evalRealPolynomial (xiGaussianRemovePolar P F) (xiSpectralPoint q.1 ^ 2) =
      evalRealPolynomial P (xiSpectralPoint q.1 ^ 2) := by
  have h := xiGaussianPolarAnnihilator_vanishes F q
  simp only [xiGaussianRemovePolar, evalRealPolynomial, Polynomial.map_add,
    Polynomial.eval_add, Polynomial.map_mul, Polynomial.eval_mul]
  change evalRealPolynomial P (xiSpectralPoint q.1 ^ 2) +
    evalRealPolynomial (Polynomial.C (-(P.eval (-(1 / 4 : ℝ)))))
      (xiSpectralPoint q.1 ^ 2) *
    evalRealPolynomial (xiGaussianPolarAnnihilator F) (xiSpectralPoint q.1 ^ 2) = _
  rw [h, mul_zero, add_zero]
  rfl

theorem xiGaussianRemovePolar_heatTerm_selected (P : Polynomial ℝ)
    (F : Finset XiZeroCopy) (q : {q : XiZeroCopy // q ∈ F}) (t : ℝ) :
    xiPolynomialGaussianHeatTerm (xiGaussianRemovePolar P F) t q.1 =
      xiPolynomialGaussianHeatTerm P t q.1 := by
  rw [xiPolynomialGaussianHeatTerm, xiGaussianRemovePolar_eval_selected P F q]
  rfl

/-- Exact preservation on any finite divisor set is compatible with
arbitrarily small full mixed-term errors at every later positive heat time. -/
theorem exists_xiGaussian_poleFree_interpolating_approximation
    (P : Polynomial ℝ) (S : Finset XiZeroCopy)
    (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∃ Q : Polynomial ℝ, Q.eval (-(1 / 4 : ℝ)) = 0 ∧
      (∀ q ∈ S, evalRealPolynomial Q (xiSpectralPoint q ^ 2) =
        evalRealPolynomial P (xiSpectralPoint q ^ 2)) ∧
      ∀ s : Set.Ici (t₀ : ℝ),
        let t := xiGaussianHeatAfter t₀ s
        xiGaussianNativeEnergy (Q - P) t < (ε : ℝ) ∧
        ‖xiPolynomialGaussianHeatTrace Q t - xiPolynomialGaussianHeatTrace P t‖ < (ε : ℝ) ∧
        |xiGaussianNativeEnergy Q t - xiGaussianNativeEnergy P t| < (ε : ℝ) ∧
        |(∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t q) -
          (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q)| < (ε : ℝ) ∧
        |xiGaussianCompletedSourceResidual Q t -
          xiGaussianCompletedSourceResidual P t| < π * (ε : ℝ) := by
  obtain ⟨F, hF, hS⟩ :=
    ((eventually_xiGaussianRemovePolar_heatHalfLine_control P t₀ ε).and
      (eventually_ge_atTop S)).exists
  exact ⟨xiGaussianRemovePolar P F, xiGaussianRemovePolar_eval_pole P F,
    fun q hq => xiGaussianRemovePolar_eval_selected P F ⟨q, hS hq⟩, hF⟩

end RHTower

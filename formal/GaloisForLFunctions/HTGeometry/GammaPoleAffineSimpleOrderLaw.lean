import GaloisForLFunctions.HTGeometry.GammaPoleMovingAffineProfileHorizon
import GaloisForLFunctions.HTGeometry.GammaPoleWeightedCovariantAsymptotic

/-!
# Branchwise simple-order law for moving Gamma affine profiles

The moving-profile horizon says that an at-most-simple Gamma source is exactly affine in the
undifferentiated carrier.  The covariant top-residue theorem independently computes local
meromorphic order after factorial normalization.  Their conjunction is sharper than either
statement: at the pole indexed by `branch`, the affine packet has an exact simple pole if and only
if its Gamma coefficient does not vanish at `-branch`.

For an arbitrary at-most-simple source, the coefficient is canonical: it is the constant
coefficient of the derivative with respect to the undifferentiated Gamma variable.
-/

open Complex Filter Topology Finset MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- **Explicit affine-source simple-order law.**  Polynomial motion in both affine coefficients
cannot change the principal Gamma pole.  It cancels exactly at those branches where the Gamma
coefficient itself vanishes. -/
theorem gammaPoleAffineSource_order_eq_neg_one_iff
    (branch n : ℕ) (a b : Polynomial ℂ) :
    meromorphicOrderAt
        (fun x : ℂ => gammaPolyJetEval (n + 1)
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)
          (MvPolynomial.C a +
            MvPolynomial.C b * MvPolynomial.X (0 : Fin (n + 1)))) 0 =
        ((-1 : ℤ) : WithTop ℤ) ↔
      b.eval (-(branch : ℂ)) ≠ 0 := by
  let P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
    MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X (0 : Fin (n + 1))
  let center : ℂ := -(branch : ℂ)
  let scale : ℂ := reciprocalGammaFactorialScale branch
  have hx : Tendsto (fun x : ℂ => x) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have ha : Tendsto (fun x : ℂ => a.eval (center + scale * x))
      (𝓝[≠] 0) (𝓝 (a.eval center)) := by
    have hcont : ContinuousAt (fun x : ℂ => a.eval (center + scale * x)) 0 := by
      fun_prop
    simpa using! hcont.tendsto.mono_left inf_le_left
  have hb : Tendsto (fun x : ℂ => b.eval (center + scale * x))
      (𝓝[≠] 0) (𝓝 (b.eval center)) := by
    have hcont : ContinuousAt (fun x : ℂ => b.eval (center + scale * x)) 0 := by
      fun_prop
    simpa using! hcont.tendsto.mono_left inf_le_left
  have hgamma : Tendsto
      (fun x : ℂ => x * gammaPoleCovariantJetValue branch 0 x)
      (𝓝[≠] 0) (𝓝 (-1)) := by
    simpa using tendsto_pow_succ_mul_gammaPoleCovariantJetValue branch 0
  have hcov : Tendsto
      (fun x : ℂ => x * gammaPoleCovariantPolynomialJetEval branch n x P)
      (𝓝[≠] 0) (𝓝 (-(b.eval center))) := by
    have hsum := hx.mul ha |>.add (hb.mul hgamma)
    have hsum' : Tendsto
        (fun x : ℂ => x * a.eval (center + scale * x) +
          b.eval (center + scale * x) *
            (x * gammaPoleCovariantJetValue branch 0 x))
        (𝓝[≠] 0) (𝓝 (-(b.eval center))) := by
      simpa using hsum
    apply hsum'.congr'
    filter_upwards with x
    simp only [P, gammaPoleCovariantPolynomialJetEval, map_add, map_mul,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', center, scale,
      Polynomial.coe_evalRingHom]
    change x * a.eval (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) +
        b.eval (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) *
          (x * gammaPoleCovariantJetValue branch 0 x) =
      x * (a.eval (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) +
        b.eval (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) *
          gammaPoleCovariantJetValue branch 0 x)
    ring
  have hnative : Tendsto
      (fun x : ℂ => x ^ 1 * gammaPolyJetEval (n + 1)
        (center + scale * x) P)
      (𝓝[≠] 0) (𝓝 (-(b.eval center))) := by
    apply hcov.congr'
    filter_upwards [gammaPolyJetEval_affine_eventuallyEq_covariant branch n P]
      with x heq
    simp only [center, scale, pow_one]
    rw [heq]
  have horder := meromorphicOrderAt_eq_neg_nat_iff_limit_ne_zero 1
    (meromorphicAt_gammaPolyJetEval_affine branch n P) (by
      simpa [center, scale] using hnative)
  simpa [P, center, scale] using horder

/-- **Canonical at-most-simple Gamma order law.**  Once the moving Laurent profile has no pole
grade above one, its exact branchwise pole order is read from the source derivative coefficient. -/
theorem gammaPoleProfileAtMostSimple_order_eq_neg_one_iff
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hprofile : GammaPoleProfileAtMostSimple n P) (branch : ℕ) :
    meromorphicOrderAt
        (fun x : ℂ => gammaPolyJetEval (n + 1)
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) P) 0 =
        ((-1 : ℤ) : WithTop ℤ) ↔
      (((MvPolynomial.pderiv (0 : Fin (n + 1)) P).coeff 0).eval
        (-(branch : ℂ))) ≠ 0 := by
  rcases (gammaPoleProfileAtMostSimple_iff_affine P).mp hprofile with
    ⟨a, b, rfl⟩
  simpa using gammaPoleAffineSource_order_eq_neg_one_iff branch n a b

/-- **Affine-horizon/simple-order classification.**  An actual moving Gamma profile is
at-most-simple exactly when it has affine source form whose Gamma coefficient governs the exact
simple-pole locus at every branch. -/
theorem gammaPoleProfileAtMostSimple_iff_affine_with_simple_order_law
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    GammaPoleProfileAtMostSimple n P ↔
      ∃ a b : Polynomial ℂ,
        P = MvPolynomial.C a +
          MvPolynomial.C b * MvPolynomial.X (0 : Fin (n + 1)) ∧
        ∀ branch : ℕ,
          (meromorphicOrderAt
              (fun x : ℂ => gammaPolyJetEval (n + 1)
                (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) P) 0 =
              ((-1 : ℤ) : WithTop ℤ) ↔
            b.eval (-(branch : ℂ)) ≠ 0) := by
  constructor
  · intro hprofile
    rcases (gammaPoleProfileAtMostSimple_iff_affine P).mp hprofile with
      ⟨a, b, hP⟩
    refine ⟨a, b, hP, ?_⟩
    intro branch
    rw [hP]
    exact gammaPoleAffineSource_order_eq_neg_one_iff branch n a b
  · rintro ⟨a, b, hP, _horder⟩
    exact (gammaPoleProfileAtMostSimple_iff_affine P).mpr ⟨a, b, hP⟩

end

end GaloisForLFunctions

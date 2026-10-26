import GaloisForLFunctions.ArithmeticEffectivityTheory.TatesLimitLaw
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHorizonTorsion
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheGoldenCurveIsABeurlingSystem
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheBaseIsAFixedLoss

/-!
# The base axioms and the five currencies of effectivity

**Multiplicative axioms do not give effectivity** (`goldenDatum_multiplicative_axioms_not_effective`).
The golden datum `1 − 5X + 5X²` is a Beurling system — its point counts are
`N_k = Σ_{d ∣ k} d π(d)` with `π(d) ∈ ℕ` — with an integral zeta series and the functional equation.
These are the data a base over `Spec ℤ` would be built from if it were multiplicatively definable
(simple pole, Euler product with nonnegative integral prime counts, self-duality). Yet the golden
datum has an abundant class on a Frobenius window and its degree form `deg(m − nF)` has no naive
height. A base must contain data these axioms do not see.

**For `ζ` effectivity has five equivalent currencies** (`riemannHypothesis_effectivity_tfae`):

1. RH;
2. an effectivity function on the scaling surface with the Riemann inequality, bounded on degree
   levels (the effectivity calculus);
3. no abundant class of degree zero;
4. a naive height for the integral Rosati form of every cycle (Tate's limit law);
5. a fixed loss for the tensor powers of the spline orbit correlation (the base, ACP);
6. the log-torsion of the horizon equals the Euler characteristic of the box class up to
   `O(√N log² N)` (the horizon torsion).

Each is a theorem of a sibling module; the content here is that they are one statement — a growth
law of sections, a nonnegative function at bounded distance from a quadratic form, a loss that does
not scale, and a count of a finite group — so that progress in any currency is progress in all.
-/

noncomputable section

open Filter Asymptotics

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry

/-- **The golden datum satisfies the multiplicative base axioms and has no effectivity.** -/
theorem goldenDatum_multiplicative_axioms_not_effective (κ : SpanCycle) (χ₀ : ℝ) :
    (∃ π : ℕ → ℕ, ∀ k, 1 ≤ k → goldenDatum.pointCount k = ∑ d ∈ k.divisors, (d : ℝ) * π d) ∧
      (∃ Zℤ : PowerSeries ℤ, PowerSeries.constantCoeff Zℤ = 1 ∧
        PowerSeries.map (Int.castRingHom ℂ) Zℤ = goldenDatum.zetaSeries) ∧
      (∀ i, goldenDatum.β (goldenDatum.fePerm i) * goldenDatum.β i = 1) ∧
      (∃ W : Finset ℕ, ∃ x, Abundant (goldenDatum.windowSurface W) κ χ₀ x) ∧
      ¬ ∃ h : ℤ × ℤ → ℝ, ∃ K B : ℝ, (∀ v, -K ≤ h v) ∧ ∀ v, |h v - intEndDeg goldenDatum v| ≤ B :=
  ⟨goldenDatum_beurling_not_pure.1, goldenDatum_beurling_not_pure.2.1,
    goldenDatum_beurling_not_pure.2.2.1, goldenDatum_exists_abundant κ χ₀,
    goldenDatum_no_naiveHeight⟩

/-- **The currencies of effectivity for `ζ`.** -/
theorem riemannHypothesis_effectivity_tfae (a b χ₀ : ℝ) :
    List.TFAE [RiemannHypothesis,
      ∃ h : ScalingCycle → ℝ,
        RiemannInequality scalingSurface (a • scalingSurface.H + b • scalingSurface.V) χ₀ h ∧
          DegreeBounded scalingSurface h,
      ∀ x, ¬ Abundant scalingSurface (a • scalingSurface.H + b • scalingSurface.V) χ₀ x,
      ∀ x : ScalingCycle, ∃ h : (ℝ →₀ ℤ) → ℝ, ∃ K B : ℝ,
        (∀ ξ, -K ≤ h ξ) ∧ ∀ ξ, |h ξ - intRosatiForm zetaScalingDatum x ξ| ≤ B,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
        |ArithmeticCorrespondencePositivity.splineCorr t| ^ k ≤ C * Real.exp (L * t),
      (fun N : ℕ => logTorsion N - eulerChar scalingSurface 0 0 (boxClass scalingSurface N))
        =O[atTop] (fun N : ℕ => Real.sqrt N * Real.log N ^ 2)] := by
  tfae_have 1 ↔ 2 := riemannHypothesis_iff_exists_effectivity a b χ₀
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_no_abundant_class _ χ₀
  tfae_have 1 ↔ 4 := riemannHypothesis_iff_forall_exists_naiveHeight
  tfae_have 1 ↔ 5 := ArithmeticCorrespondencePositivity.riemannHypothesis_iff_fixed_tensor_loss
  tfae_have 1 ↔ 6 := riemannHypothesis_iff_logTorsion_sub_eulerChar scalingSurface
  tfae_finish

end GaloisForLFunctions.ArithmeticEffectivityTheory

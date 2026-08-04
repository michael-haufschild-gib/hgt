import GaloisForLFunctions.HTGeometry.ExponentialCarrierHypertranscendence
import GaloisForLFunctions.HTGeometry.LocalPolynomialGauge
import GaloisForLFunctions.HTGeometry.BohrHullContinuity
import GaloisForLFunctions.HTGeometry.FamilyPowerGauge

/-!
# The boundary functions of a perturbed outer orbit are hypertranscendental

Every point of the Bohr hull of an exponential carrier is a unimodular twist of that carrier, so no
point of the hull satisfies an algebraic differential equation.  The boundary functions of the
perturbed orbit are affine images of the hull points with a nonzero multiplier, and an affine change
with polynomial data cannot create a differential relation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- **No point of the Bohr hull satisfies an algebraic differential equation.** -/
theorem not_differentiallyAlgebraicOn_bohrHullMap {a : ι → ℂ} {omega : ι → ℝ}
    (hom : RationallyIndependentSequence omega) (h : ExpSeriesNormallySummable a omega)
    (hinf : {i : ι | a i ≠ 0}.Infinite) (lam : ι → Circle) {U : Set ℂ} (hU : IsOpen U)
    (hUne : U.Nonempty) :
    ¬ DifferentiallyAlgebraicOn (bohrHullMap a omega h lam) U :=
  not_differentiallyAlgebraicOn_cexpSeriesCarrier_twist hom h hinf
    (fun i => Circle.norm_coe (lam i)) hU hUne

/-- **The boundary functions of the perturbed outer orbit are hypertranscendental.** -/
theorem not_differentiallyAlgebraicOn_perturbedBoundaryFun {a : ι → ℂ} {omega : ι → ℝ}
    (hom : RationallyIndependentSequence omega) (h : ExpSeriesNormallySummable a omega)
    (hinf : {i : ι | a i ≠ 0}.Infinite) (lam : ι → Circle) {c eps : ℂ} (heps : eps ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ¬ DifferentiallyAlgebraicOn (fun z => c + eps * bohrHullMap a omega h lam z) U := by
  have hsum : ExpSeriesNormallySummable (fun i => a i * (lam i : ℂ)) omega := by
    intro R
    refine (h R).congr fun i => ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
  refine not_differentiallyAlgebraicOn_polynomialGauge hU (Polynomial.C eps) (Polynomial.C c)
    (fun hcon => heps (by simpa using congrArg (Polynomial.coeff · 0) hcon))
    (fun z _ => by simp) (fun z _ => ?_)
    (not_differentiallyAlgebraicOn_bohrHullMap hom h hinf lam hU hUne)
  exact (analyticAt_cexpSeriesCarrier hsum z).contDiffAt

/-- **Every power of every boundary function of the perturbed outer orbit is hypertranscendental.**
A function is algebraic over its own power, so passing to powers cannot create a differential
relation. -/
theorem not_differentiallyAlgebraicOn_perturbedBoundaryFun_pow {a : ι → ℂ} {omega : ι → ℝ}
    (hom : RationallyIndependentSequence omega) (h : ExpSeriesNormallySummable a omega)
    (hinf : {i : ι | a i ≠ 0}.Infinite) (lam : ι → Circle) {c eps : ℂ} (heps : eps ≠ 0)
    {n : ℕ} (hn : n ≠ 0) {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ¬ DifferentiallyAlgebraicOn
      (fun z => (c + eps * bohrHullMap a omega h lam z) ^ n) U := by
  have hsum : ExpSeriesNormallySummable (fun i => a i * (lam i : ℂ)) omega := by
    intro R
    refine (h R).congr fun i => ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
  refine not_differentiallyAlgebraicOn_pow hn (fun z _ => ?_)
    (not_differentiallyAlgebraicOn_perturbedBoundaryFun hom h hinf lam heps hU hUne)
  exact contDiffAt_const.add (contDiffAt_const.mul (analyticAt_cexpSeriesCarrier hsum z).contDiffAt)

end

end GaloisForLFunctions.HTGeometry

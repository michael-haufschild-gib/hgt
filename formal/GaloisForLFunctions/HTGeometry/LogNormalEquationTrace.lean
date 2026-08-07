import GaloisForLFunctions.HTGeometry.HalfLogCesaroAverage
import GaloisForLFunctions.HTGeometry.GammaTransportKernel

/-!
# The equation bounds the half-log trace

The logarithmic normal equation says the Dirichlet operator plus the transport operator equals the
source.  A bound on the source together with a bound on the transport term therefore bounds the
Dirichlet operator, and dividing by `2√L` converts that into a bound on the half-log trace offset
by the averaged trace.

This is where the equation is actually used: everything else in the chain is an estimate about one
of the two operators separately.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The equation bounds the trace from above.**  A source bounded by `T` and a transport term
bounded below by `−B` give `√X f(X) ≤ (T+B)/(2√X) + A(X)`. -/
theorem halfLog_le_of_equation {f : ℝ → ℝ} {X S T B : ℝ} (hX : 0 < X)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : S ≤ T)
    (hB : -B ≤ gammaTransport f X) :
    Real.sqrt X * f X ≤ (T + B) / (2 * Real.sqrt X) + halfLogAverage f X := by
  refine halfLog_le_of_logDirichlet_le hX ?_
  linarith [heq, hS, hB]

/-- **The equation bounds the trace from below.**  The mirror, with the transport term bounded
above. -/
theorem le_halfLog_of_equation {f : ℝ → ℝ} {X S T B : ℝ} (hX : 0 < X)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : T ≤ S)
    (hB : gammaTransport f X ≤ B) :
    (T - B) / (2 * Real.sqrt X) + halfLogAverage f X ≤ Real.sqrt X * f X := by
  refine le_halfLog_of_le_logDirichlet hX ?_
  linarith [heq, hS, hB]

/-! ## The trace bounds with every derived input chained

The two lemmas above take a bound on the transport term.  That bound is not an assumption — it is
the transport estimate at the critical point.  Chaining it leaves only the equation, the
maximizing (resp. minimizing) property of the point, and object regularity.
-/

open MeasureTheory Set in
/-- **The trace bound at a penalized maximizer, with nothing derived assumed.** -/
theorem halfLog_le_of_equation_isMaxOn {f : ℝ → ℝ} {X δ M L₀ a S T : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hf : 0 ≤ f X) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hmax : IsMaxOn (penalized (fun L => Real.sqrt L * f L) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : S ≤ T) :
    Real.sqrt X * f X
      ≤ (T + ((2 * δ / Real.sqrt X + 2 * (f X + δ * Real.sqrt X / 2) / X)
              * (∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s)
            + 4 * M * (-Real.log (1 - Real.exp (-(X / 2))))))
          / (2 * Real.sqrt X) + halfLogAverage f X :=
  halfLog_le_of_equation hX heq hS
    (neg_le_gammaTransport_of_isMaxOn hX hδ hf hFb hmeas hnear hmax ha)

open MeasureTheory Set in
/-- **The mirrored trace bound at a penalized minimizer.** -/
theorem le_halfLog_of_equation_isMaxOn_neg {f : ℝ → ℝ} {X δ M L₀ a S T : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hnum : ∀ s, 0 ≤ s → s ≤ X / 2 → 0 ≤ f X - δ * s / Real.sqrt X)
    (hmax : IsMaxOn (penalized (fun L => -(Real.sqrt L * f L)) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : T ≤ S) :
    (T - ((2 * δ / Real.sqrt X + f X / (2 * X))
            * (∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s)
          + 4 * M * (-Real.log (1 - Real.exp (-(X / 2))))))
        / (2 * Real.sqrt X) + halfLogAverage f X
      ≤ Real.sqrt X * f X :=
  le_halfLog_of_equation hX heq hS
    (gammaTransport_le_of_isMaxOn_neg hX hδ hFb hmeas hnear hnum hmax ha)

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.PolynomialRootLoopTransport
import Mathlib.Analysis.Complex.CoveringMap

open Polynomial Set Topology
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

abbrev PolynomialRegularValue {n : ℕ} (v : Parameter n) :=
  {w : ℂ // ∀ j, w ≠ valuesWithConstant v j}

abbrev PolynomialRegularSource {n : ℕ} (v : Parameter n) :=
  {z : ℂ // ∀ j, (additivePolynomial v).eval z ≠ valuesWithConstant v j}

/-- The actual polynomial map between its regular source and regular target. -/
def polynomialCoverMap {n : ℕ} (v : Parameter n)
    (z : PolynomialRegularSource v) : PolynomialRegularValue v :=
  ⟨(additivePolynomial v).eval z, z.property⟩

/-- All actual critical values are among the supplied values, including collision parameters. -/
theorem isCoveringMapOn_additivePolynomial {n : ℕ} (v : Parameter n) :
    IsCoveringMapOn (additivePolynomial v).eval {w : ℂ | ∀ j, w ≠ valuesWithConstant v j} := by
  apply (additivePolynomial v).isCoveringMapOn_eval.mono
  intro w hw
  rintro ⟨z, hz, hzw⟩
  change (additivePolynomial v).derivative.eval z = 0 at hz
  have hcrit : (polynomial v).derivative.IsRoot z := by
    simpa only [IsRoot, derivative_additivePolynomial, derivative_polynomial] using hz
  obtain ⟨j, hza⟩ := derivative_root_position v hcrit
  apply hw j
  rw [← hzw, hza]
  simp only [additivePolynomial, valuesWithConstant, eval_add, eval_C]

/-- Covering-space structure for the actual polynomial, not the critical-value parameter map. -/
theorem isCoveringMap_polynomialCoverMap {n : ℕ} (v : Parameter n) :
    IsCoveringMap (polynomialCoverMap v) :=
  (isCoveringMapOn_additivePolynomial v).isCoveringMap_restrictPreimage

/-- The covering fiber is exactly the ordinary polynomial root fiber. -/
def rootFiberCoverEquiv {n : ℕ} (v : Parameter n) (b : PolynomialRegularValue v) :
    RootFiber v (b : ℂ) ≃ (polynomialCoverMap v) ⁻¹' {b} where
  toFun z := ⟨⟨z.val, fun j h => b.property j (z.property.symm.trans h)⟩, Subtype.ext z.property⟩
  invFun z := ⟨z.val.val, congrArg Subtype.val z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual root-loop transport is the native covering monodromy with the same path orientation. -/
theorem rootLoopTransport_eq_covering_monodromy {n : ℕ} (v : Parameter n)
    {b : PolynomialRegularValue v} (γ : Path b b) (z : RootFiber v (b : ℂ)) :
    rootFiberCoverEquiv v b
        (rootLoopTransport v (γ.map continuous_subtype_val) (fun t => (γ t).property) z) =
      (isCoveringMap_polynomialCoverMap v).monodromy (.mk γ) (rootFiberCoverEquiv v b z) := by
  let cov := isCoveringMap_polynomialCoverMap v
  let w := rootFiberCoverEquiv v b z
  let Γ : C(I, PolynomialRegularSource v) :=
    cov.liftPath γ.toContinuousMap w.val (γ.source.trans w.property.symm)
  let u : C(I, ℂ) := ⟨fun t => (Γ t).val, continuous_subtype_val.comp Γ.continuous⟩
  have hu₀ : u 0 = z.val :=
    congrArg Subtype.val (cov.liftPath_zero γ.toContinuousMap w.val
      (γ.source.trans w.property.symm))
  have hu : ∀ t, (additivePolynomial v).eval (u t) = (γ.map continuous_subtype_val) t := by
    intro t
    exact congrArg Subtype.val (congrFun (cov.liftPath_lifts γ.toContinuousMap w.val
      (γ.source.trans w.property.symm)) t)
  have h := rootLoopTransport_val_eq_of_section v (γ.map continuous_subtype_val)
    (fun t => (γ t).property) z u hu₀ hu
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- Based homotopies in the regular target preserve the actual root-loop permutation. -/
theorem rootLoopTransport_eq_of_homotopic {n : ℕ} (v : Parameter n)
    {b : PolynomialRegularValue v} {γ δ : Path b b} (h : γ.Homotopic δ) :
    rootLoopTransport v (γ.map continuous_subtype_val) (fun t => (γ t).property) =
      rootLoopTransport v (δ.map continuous_subtype_val) (fun t => (δ t).property) := by
  apply Equiv.ext
  intro z
  apply (rootFiberCoverEquiv v b).injective
  rw [rootLoopTransport_eq_covering_monodromy v γ z,
    rootLoopTransport_eq_covering_monodromy v δ z]
  exact congrArg (fun q => (isCoveringMap_polynomialCoverMap v).monodromy q
    (rootFiberCoverEquiv v b z)) (Path.Homotopic.Quotient.eq.mpr h)

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap

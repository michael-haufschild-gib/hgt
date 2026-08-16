import GaloisForLFunctions.RHTower.RoutePFourthDepthGammaCyclicJuliaIntertwiner
import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthHilbertSource

/-!
# Route P joint-depth Gamma--Julia scalar-intertwiner no-go

P-G105D identifies the universal Gamma cyclic amplitude with the fourth-depth Julia defect.  That
does not make the literal Xi-landing source and reciprocal-promotion co-source the same vector.
This file tests that remaining identification on the actual joint `(prime, depth)` Hilbert carrier.

The scalar-intertwiner conjecture is false.  For every source parameter, there is no real or complex
constant taking the primitive source vector to the reciprocal-promotion co-source.  The exact
positive survivor is

```text
source(p,e) = log(p) coSource(p,e).
```

Consequently the Gamma--Julia defect transported from the literal co-source has coefficient

```text
(sqrt 63 / 8) log(p),
```

independent of depth but necessarily varying with prime.  This is a source-defined diagonal
operator-valued completion law, and it maps the particular co-source vector back into the proved
Hilbert source even though the ambient logarithmic multiplier is not asserted bounded.

Thus P-G105C's universal Kronecker completion cannot by itself be identified with the Xi-landing
co-source.  The next construction must retain this prime-log diagonal before finite Gram assembly.
-/

open Complex Set
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Exact coordinate relation between the literal primitive source and reciprocal-promotion
co-source.  Prime logarithm is retained; depth is untouched. -/
theorem routePPrimitiveJointDepth_source_eq_log_mul_coSource
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveBoundaryAmplitude u pe =
      Real.log (pe.1 : ℝ) *
        xiGammaEulerPrimitiveDescentTestAmplitude u pe := by
  have hlog : 0 < Real.log (pe.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  have hpromotion : xiGammaEulerPrimitivePromotion pe ≠ 0 := by
    rw [xiGammaEulerPrimitivePromotion]
    exact (Real.sqrt_pos.2 hlog).ne'
  rw [xiGammaEulerPrimitiveBoundaryAmplitude,
    xiGammaEulerPrimitiveDescentTestAmplitude]
  rw [xiGammaEulerPrimitivePromotion]
  have hsqrt : Real.sqrt (Real.log (pe.1 : ℝ)) ^ 2 =
      Real.log (pe.1 : ℝ) := Real.sq_sqrt hlog.le
  field_simp [hpromotion]
  rw [hsqrt]
  ring

/-- No real constant identifies the actual joint-depth source and co-source families. -/
theorem routePPrimitiveJointDepth_no_real_scalar_intertwiner (u : ℝ) :
    ¬ ∃ lambda : ℝ, ∀ pe : Nat.Primes × ℕ,
      xiGammaEulerPrimitiveDescentTestAmplitude u pe =
        lambda * xiGammaEulerPrimitiveBoundaryAmplitude u pe := by
  rintro ⟨lambda, h⟩
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  let p3 : Nat.Primes := ⟨3, by norm_num⟩
  let pe2 : Nat.Primes × ℕ := (p2, 0)
  let pe3 : Nat.Primes × ℕ := (p3, 0)
  have hcoefficient (pe : Nat.Primes × ℕ) :
      Real.log (pe.1 : ℝ) * lambda = 1 := by
    have hrel := routePPrimitiveJointDepth_source_eq_log_mul_coSource u pe
    rw [h pe] at hrel
    have hs : xiGammaEulerPrimitiveBoundaryAmplitude u pe ≠ 0 :=
      (xiGammaEulerPrimitiveBoundaryAmplitude_pos u pe).ne'
    apply mul_right_cancel₀ hs
    calc
      (Real.log (pe.1 : ℝ) * lambda) *
          xiGammaEulerPrimitiveBoundaryAmplitude u pe =
        Real.log (pe.1 : ℝ) *
          (lambda * xiGammaEulerPrimitiveBoundaryAmplitude u pe) := by ring
      _ = xiGammaEulerPrimitiveBoundaryAmplitude u pe := hrel.symm
      _ = 1 * xiGammaEulerPrimitiveBoundaryAmplitude u pe := by ring
  have hlambda2 : Real.log 2 * lambda = 1 := by
    simpa [pe2, p2] using hcoefficient pe2
  have hlambda3 : Real.log 3 * lambda = 1 := by
    simpa [pe3, p3] using hcoefficient pe3
  have hlambda : lambda ≠ 0 := by
    intro hz
    rw [hz] at hlambda2
    norm_num at hlambda2
  have hlogs : Real.log 2 = Real.log 3 := by
    apply mul_right_cancel₀ hlambda
    nlinarith
  have hlt : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Typed Hilbert no-go: even a complex scalar cannot identify the two literal Xi-landing legs.
Positive displacement is parameterized by `exp(tau)`, so the theorem has no premise. -/
theorem routePPrimitiveJointDepth_no_complex_scalar_intertwiner (tau : ℝ) :
    ¬ ∃ lambda : ℂ,
      xiGammaEulerPrimitiveDescentTestLp
          (Real.exp tau) (Real.exp_pos tau) =
        lambda • xiGammaEulerPrimitiveBoundarySourceLp
          (Real.exp tau) (Real.exp_pos tau) := by
  rintro ⟨lambda, h⟩
  apply routePPrimitiveJointDepth_no_real_scalar_intertwiner (Real.exp tau)
  refine ⟨lambda.re, ?_⟩
  intro pe
  have hc := congrArg (fun x : XiGammaEulerPrimitiveJointDepthHilbert => x pe) h
  change (xiGammaEulerPrimitiveDescentTestAmplitude (Real.exp tau) pe : ℂ) =
    lambda *
      (xiGammaEulerPrimitiveBoundaryAmplitude (Real.exp tau) pe : ℂ) at hc
  have hre := congrArg Complex.re hc
  norm_num [Complex.mul_re] at hre
  exact hre

/-- Exact operator-valued replacement coefficient forced by Gamma--Julia and primitive promotion. -/
def routePPrimitiveJointDepthGammaJuliaLogMultiplier
    (pe : Nat.Primes × ℕ) : ℝ :=
  routePPrimitiveFourthDepthGammaCyclicAmplitude *
    Real.log (pe.1 : ℝ)

/-- Gamma--Julia source channel is the prime-log diagonal transport of literal co-source. -/
theorem routePPrimitiveJointDepth_gammaSource_eq_logMultiplier_coSource
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    routePPrimitiveFourthDepthGammaCyclicAmplitude *
        xiGammaEulerPrimitiveBoundaryAmplitude u pe =
      routePPrimitiveJointDepthGammaJuliaLogMultiplier pe *
        xiGammaEulerPrimitiveDescentTestAmplitude u pe := by
  rw [routePPrimitiveJointDepthGammaJuliaLogMultiplier,
    routePPrimitiveJointDepth_source_eq_log_mul_coSource]
  ring

/-- Hilbert-valued Gamma--Julia transport of the actual primitive source. -/
def routePPrimitiveJointDepthGammaJuliaLogTransport
    (u : ℝ) (hu : 0 < u) : XiGammaEulerPrimitiveJointDepthHilbert :=
  (routePPrimitiveFourthDepthGammaCyclicAmplitude : ℂ) •
    xiGammaEulerPrimitiveBoundarySourceLp u hu

/-- Coordinatewise, the Hilbert transport is exactly the unbounded prime-log multiplier applied to
the actual reciprocal-promotion co-source; hence this specific vector lies in the multiplier domain. -/
theorem routePPrimitiveJointDepthGammaJuliaLogTransport_apply
    (u : ℝ) (hu : 0 < u) (pe : Nat.Primes × ℕ) :
    routePPrimitiveJointDepthGammaJuliaLogTransport u hu pe =
      (routePPrimitiveJointDepthGammaJuliaLogMultiplier pe : ℂ) *
        xiGammaEulerPrimitiveDescentTestLp u hu pe := by
  rw [routePPrimitiveJointDepthGammaJuliaLogTransport]
  change (routePPrimitiveFourthDepthGammaCyclicAmplitude : ℂ) *
      xiGammaEulerPrimitiveBoundarySourceLp u hu pe = _
  rw [xiGammaEulerPrimitiveBoundarySourceLp_apply,
    xiGammaEulerPrimitiveDescentTestLp_apply]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
    routePPrimitiveJointDepth_gammaSource_eq_logMultiplier_coSource]

/-- P-G105E capstone: universal scalar identification is impossible, and the exact prime-log
operator-valued survivor acts on the literal Hilbert co-source. -/
theorem routePPrimitiveJointDepth_GammaJulia_scalarNoGo_logSurvivor
    (tau : ℝ) :
    (¬ ∃ lambda : ℂ,
      xiGammaEulerPrimitiveDescentTestLp
          (Real.exp tau) (Real.exp_pos tau) =
        lambda • xiGammaEulerPrimitiveBoundarySourceLp
          (Real.exp tau) (Real.exp_pos tau)) ∧
      (∀ pe : Nat.Primes × ℕ,
        routePPrimitiveFourthDepthGammaCyclicAmplitude *
            xiGammaEulerPrimitiveBoundaryAmplitude (Real.exp tau) pe =
          routePPrimitiveJointDepthGammaJuliaLogMultiplier pe *
            xiGammaEulerPrimitiveDescentTestAmplitude (Real.exp tau) pe) ∧
      (∀ pe : Nat.Primes × ℕ,
        routePPrimitiveJointDepthGammaJuliaLogTransport
            (Real.exp tau) (Real.exp_pos tau) pe =
          (routePPrimitiveJointDepthGammaJuliaLogMultiplier pe : ℂ) *
            xiGammaEulerPrimitiveDescentTestLp
              (Real.exp tau) (Real.exp_pos tau) pe) :=
  ⟨routePPrimitiveJointDepth_no_complex_scalar_intertwiner tau,
    routePPrimitiveJointDepth_gammaSource_eq_logMultiplier_coSource
      (Real.exp tau),
    routePPrimitiveJointDepthGammaJuliaLogTransport_apply
      (Real.exp tau) (Real.exp_pos tau)⟩

end
end RHTower

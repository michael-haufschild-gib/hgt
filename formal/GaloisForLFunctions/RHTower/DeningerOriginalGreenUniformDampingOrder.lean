import GaloisForLFunctions.RHTower.DeningerOriginalGreenZeroDampingGerm
import GaloisForLFunctions.RHTower.XiHeatShellMinimum

/-!
# Uniform scalar damping orders for the original prime Green source

At a fixed Xi divisor the literal original Green continuation has a pole of
order twice the Xi multiplicity.  This module classifies exactly what a single
scalar damping power can do simultaneously at every divisor: finite coordinate
limits are equivalent to a global multiplicity bound, while nonzero coordinate
limits are equivalent to one common multiplicity.  It deliberately does not
promote coordinatewise limits to a source-space or physical-reader limit.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- A single scalar damping power gives finite coordinate limits for every literal original-prime
Green continuation. -/
def DeningerOriginalPrimeGreenUniformFiniteDampingLimit (k : ℕ) : Prop :=
  ∀ p : Nat.Primes, ∀ rho : XiDivisorSupport, ∃ c : ℂ,
    Tendsto (fun a : ℂ => a ^ k *
      deningerOriginalPrimeGreenDampingContinuation p rho a) (𝓝[≠] 0) (𝓝 c)

/-- A single scalar damping power gives nonzero coordinate limits for every literal
original-prime Green continuation. -/
def DeningerOriginalPrimeGreenUniformNonzeroDampingLimit (k : ℕ) : Prop :=
  ∀ p : Nat.Primes, ∀ rho : XiDivisorSupport, ∃ c : ℂ, c ≠ 0 ∧
    Tendsto (fun a : ℂ => a ^ k *
      deningerOriginalPrimeGreenDampingContinuation p rho a) (𝓝[≠] 0) (𝓝 c)

/-- A source-space zero-damping lift is literal when every Xi coordinate agrees eventually with
the original Green continuation before the putative Hilbert-space limit is taken. -/
def DeningerOriginalPrimeGreenLiteralCoordinatewiseHilbertZeroDampingLift
    (p : Nat.Primes) : Prop :=
  ∃ F : ℂ → XiDivisorL2, ∃ v : XiDivisorL2,
    Tendsto F (𝓝[≠] 0) (𝓝 v) ∧
      ∀ᶠ a in 𝓝[≠] (0 : ℂ), ∀ q : XiZeroCopy,
        F a q = deningerOriginalPrimeGreenDampingContinuation p q.1 a

/-- **Literal source-space zero-damping no-go.**  No Xi-Hilbert vector can be the finite
zero-damping limit of fields that eventually retain every coordinate of the literal original
prime Green continuation.  The obstruction is already visible at one actual Xi copy: continuous
coordinate evaluation would create a forbidden finite scalar limit. -/
theorem not_deningerOriginalPrimeGreenLiteralCoordinatewiseHilbertZeroDampingLift
    (p : Nat.Primes) :
    ¬ DeningerOriginalPrimeGreenLiteralCoordinatewiseHilbertZeroDampingLift p := by
  rintro ⟨F, v, hF, hcoords⟩
  let q : XiZeroCopy := Classical.choice nonempty_xiZeroCopy
  have hcoordinate : Tendsto (fun a : ℂ => F a q) (𝓝[≠] 0) (𝓝 (v q)) :=
    ((lp.evalCLM ℂ (fun _ : XiZeroCopy => ℂ) 2 q).continuous.tendsto _).comp hF
  have hmatch : (fun a : ℂ => F a q) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun a : ℂ => deningerOriginalPrimeGreenDampingContinuation p q.1 a) := by
    filter_upwards [hcoords] with a ha
    exact ha q
  have hscalar : Tendsto
      (fun a : ℂ => deningerOriginalPrimeGreenDampingContinuation p q.1 a)
      (𝓝[≠] 0) (𝓝 (v q)) :=
    hcoordinate.congr' hmatch
  exact deningerOriginalPrimeGreenDampingContinuation_no_finite_limit p q.1
    ⟨v q, hscalar⟩

/-- **Sharp finite-order classification.**  One scalar normalization has finite limits at all
literal original-Green coordinates exactly when it dominates twice every native Xi multiplicity. -/
theorem deningerOriginalPrimeGreen_uniformFiniteDampingLimit_iff (k : ℕ) :
    DeningerOriginalPrimeGreenUniformFiniteDampingLimit k ↔
      ∀ rho : XiDivisorSupport, 2 * xiSupportMultiplicity rho ≤ k := by
  constructor
  · intro h rho
    obtain ⟨c, hc⟩ := h ⟨2, by norm_num⟩ rho
    exact (deningerOriginalPrimeGreenDampingContinuation_finite_limit_iff
      ⟨2, by norm_num⟩ rho k).mp ⟨c, hc⟩
  · intro h p rho
    exact (deningerOriginalPrimeGreenDampingContinuation_finite_limit_iff p rho k).mpr (h rho)

/-- **Sharp nonzero-order classification.**  A scalar normalization that retains nonzero limits
at every literal original-Green coordinate exists exactly at twice their common Xi multiplicity. -/
theorem deningerOriginalPrimeGreen_uniformNonzeroDampingLimit_iff (k : ℕ) :
    DeningerOriginalPrimeGreenUniformNonzeroDampingLimit k ↔
      ∀ rho : XiDivisorSupport, k = 2 * xiSupportMultiplicity rho := by
  constructor
  · intro h rho
    obtain ⟨c, hc, hlimit⟩ := h ⟨2, by norm_num⟩ rho
    exact (deningerOriginalPrimeGreenDampingContinuation_nonzero_limit_iff
      ⟨2, by norm_num⟩ rho k).mp ⟨c, hc, hlimit⟩
  · intro h p rho
    exact (deningerOriginalPrimeGreenDampingContinuation_nonzero_limit_iff p rho k).mpr (h rho)

/-- A doubled scalar order has finite literal original-Green limits at every Xi coordinate exactly
when the entire Xi divisor support has multiplicity at most that order. -/
theorem deningerOriginalPrimeGreen_uniformFiniteDampingLimit_two_mul_iff (m : ℕ) :
    DeningerOriginalPrimeGreenUniformFiniteDampingLimit (2 * m) ↔
      ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho ≤ m := by
  rw [deningerOriginalPrimeGreen_uniformFiniteDampingLimit_iff]
  constructor
  · intro h rho
    have hrho := h rho
    omega
  · intro h rho
    have hrho := h rho
    omega

/-- A doubled scalar order retains nonzero literal original-Green limits at every Xi coordinate
exactly when all Xi divisor multiplicities equal that order. -/
theorem deningerOriginalPrimeGreen_uniformNonzeroDampingLimit_two_mul_iff (m : ℕ) :
    DeningerOriginalPrimeGreenUniformNonzeroDampingLimit (2 * m) ↔
      ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = m := by
  rw [deningerOriginalPrimeGreen_uniformNonzeroDampingLimit_iff]
  constructor
  · intro h rho
    have hrho := h rho
    omega
  · intro h rho
    have hrho := h rho
    omega

end

end RHTower

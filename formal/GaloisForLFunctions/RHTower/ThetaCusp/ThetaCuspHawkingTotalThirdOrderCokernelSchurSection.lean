import Mathlib

/-!
# Total third-order Teukolsky cokernel Schur section

Put the gauge-fixed bulk Einstein--Teukolsky equation, ingoing horizon condition, and outer
radiation condition into one nonlinear residual map. Let `(L,B,C)` be its first three Taylor
derivatives. The codomain below is the augmented bulk-plus-boundary residual space.

For linear branches `p,m`, complete causal response maps at the two quadratic grades give

`u₊₊ = R₊₊(B(p,p)/2)`,

`u₊₋ = R₊₋((B(p,m)+B(m,p))/2)`.

The convention for `Rγ` is `Lγ(Rγ q)+q=0`; consequently it includes the retarded bulk resolvent,
stationary horizon-charge closure, and outer boundary trace. The total resonant coefficient is the
single cubic Schur source

`B(p,u₊₋) + B(m,u₊₊) + (C(p,p,m)+C(p,m,p)+C(m,p,p))/6`.

For symmetric Fréchet derivatives this reduces to

`B(p,R₊₋ B(p,m)) + B(m,R₊₊(B(p,p)/2)) + C(p,p,m)/2`.

Pairing this vector with an augmented left QNM state defines the total `++-` cokernel section.
Changing a boundary-preserving gauge representative contributes only a vector in `range L`.
An arbitrary target-grade third-jet correction, however, can change the section to any prescribed
scalar. Thus linear and quadratic horizon-flux data do not determine the total section.
-/

open Complex

namespace RHTower

noncomputable section

variable {X Y : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- Augmented quadratic residual in the `++` grade. -/
def d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (p : X) : Y :=
  (1 / 2 : ℂ) • B p p

/-- Augmented quadratic residual in the `+-` grade, without assuming Hessian symmetry. -/
def d4GaugeFixedTeukolskyQuadraticPlusMinusResidual
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (p m : X) : Y :=
  (1 / 2 : ℂ) • (B p m + B m p)

/-- Complete causal `++` response of the augmented boundary problem. -/
def d4GaugeFixedTeukolskyRetardedPlusPlusResponse
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Rpp : Y →ₗ[ℂ] X) (p : X) : X :=
  Rpp (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)

/-- Complete causal `+-` response, including stationary horizon-charge closure. -/
def d4GaugeFixedTeukolskyRetardedPlusMinusResponse
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Rpm : Y →ₗ[ℂ] X) (p m : X) : X :=
  Rpm (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m)

/-- Direct third Taylor residual in the `++-` grade. -/
def d4GaugeFixedTeukolskyDirectPlusPlusMinusResidual
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y) (p m : X) : Y :=
  (1 / 6 : ℂ) • (C p p m + C p m p + C m p p)

/-- Total retarded cubic Schur source. No named perturbative channel is retained. -/
def d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : Y →ₗ[ℂ] X) (p m : X) : Y :=
  B p (d4GaugeFixedTeukolskyRetardedPlusMinusResponse B Rpm p m) +
    B m (d4GaugeFixedTeukolskyRetardedPlusPlusResponse B Rpp p) +
    d4GaugeFixedTeukolskyDirectPlusPlusMinusResidual C p m

/-- Total `++-` section in the augmented left cokernel. -/
def d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : Y →ₗ[ℂ] X) (p m : X) : ℂ :=
  ell (d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource B C Rpp Rpm p m)

/-- Hessian symmetry collapses the polarized `+-` residual to `B(p,m)`. -/
theorem d4GaugeFixedTeukolskyQuadraticPlusMinusResidual_eq
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (p m : X)
    (hB : B m p = B p m) :
    d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m = B p m := by
  simp [d4GaugeFixedTeukolskyQuadraticPlusMinusResidual, hB]
  module

/-- Symmetry of the third Fréchet derivative gives the coefficient `C(p,p,m)/2`. -/
theorem d4GaugeFixedTeukolskyDirectPlusPlusMinusResidual_eq
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y) (p m : X)
    (hC1 : C p m p = C p p m) (hC2 : C m p p = C p p m) :
    d4GaugeFixedTeukolskyDirectPlusPlusMinusResidual C p m =
      (1 / 2 : ℂ) • C p p m := by
  simp [d4GaugeFixedTeukolskyDirectPlusPlusMinusResidual, hC1, hC2]
  module

/-- Exact compact Schur-complement formula for the complete `++-` source. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource_eq
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : Y →ₗ[ℂ] X) (p m : X)
    (hB : B m p = B p m)
    (hC1 : C p m p = C p p m) (hC2 : C m p p = C p p m) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource B C Rpp Rpm p m =
      B p (Rpm (B p m)) +
        B m (Rpp ((1 / 2 : ℂ) • B p p)) +
        (1 / 2 : ℂ) • C p p m := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource,
    d4GaugeFixedTeukolskyRetardedPlusMinusResponse,
    d4GaugeFixedTeukolskyQuadraticPlusMinusResidual_eq B p m hB,
    d4GaugeFixedTeukolskyRetardedPlusPlusResponse,
    d4GaugeFixedTeukolskyQuadraticPlusPlusResidual,
    d4GaugeFixedTeukolskyDirectPlusPlusMinusResidual_eq C p m hC1 hC2]

/-- Exact total cokernel section after all quadratic propagation has been integrated out. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection_eq
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : Y →ₗ[ℂ] X) (p m : X)
    (hB : B m p = B p m)
    (hC1 : C p m p = C p p m) (hC2 : C m p p = C p p m) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection ell B C Rpp Rpm p m =
      ell (B p (Rpm (B p m)) +
        B m (Rpp ((1 / 2 : ℂ) • B p p)) +
        (1 / 2 : ℂ) • C p p m) := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource_eq
      B C Rpp Rpm p m hB hC1 hC2]

/-- The declared causal `++` response solves the augmented quadratic equation. -/
theorem d4GaugeFixedTeukolskyRetardedPlusPlusResponse_solves
    (Lpp : X →ₗ[ℂ] Y) (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp : Y →ₗ[ℂ] X) (p : X)
    (hRpp : ∀ q, Lpp (Rpp q) + q = 0) :
    Lpp (d4GaugeFixedTeukolskyRetardedPlusPlusResponse B Rpp p) +
      d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p = 0 := by
  exact hRpp _

/-- The declared causal `+-` response solves the augmented stationary equation. -/
theorem d4GaugeFixedTeukolskyRetardedPlusMinusResponse_solves
    (Lpm : X →ₗ[ℂ] Y) (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpm : Y →ₗ[ℂ] X) (p m : X)
    (hRpm : ∀ q, Lpm (Rpm q) + q = 0) :
    Lpm (d4GaugeFixedTeukolskyRetardedPlusMinusResponse B Rpm p m) +
      d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m = 0 := by
  exact hRpm _

/-- A boundary-preserving gauge change is invisible to the augmented left cokernel. -/
theorem d4GaugeFixedTeukolskyTotalCokernelSection_add_range
    (L : X →ₗ[ℂ] Y) (ell : Y →ₗ[ℂ] ℂ)
    (hleft : ∀ x, ell (L x) = 0) (source : Y) (gauge : X) :
    ell (source + L gauge) = ell source := by
  simp [map_add, hleft]

/-- Total section after adding a target-grade third-jet correction. -/
def d4GaugeFixedTeukolskyCokernelSectionWithThirdJetCorrection
    (ell : Y →ₗ[ℂ] ℂ) (source correction : Y) : ℂ :=
  ell (source + correction)

/-- A third-jet correction changes the section by its left projection. -/
theorem d4GaugeFixedTeukolskyCokernelSectionWithThirdJetCorrection_eq
    (ell : Y →ₗ[ℂ] ℂ) (source correction : Y) :
    d4GaugeFixedTeukolskyCokernelSectionWithThirdJetCorrection ell source correction =
      ell source + ell correction := by
  simp [d4GaugeFixedTeukolskyCokernelSectionWithThirdJetCorrection, map_add]

/-- Sharp lower-order insufficiency theorem. If the left cokernel is normalized on one target
direction, a third-jet correction realizes every prescribed total section while leaving all lower
Taylor data unchanged. -/
theorem d4GaugeFixedTeukolsky_exists_thirdJetCorrection_cokernelSection_eq
    (ell : Y →ₗ[ℂ] ℂ) (unitDirection source : Y)
    (hunit : ell unitDirection = 1) (target : ℂ) :
    ∃ correction : Y,
      d4GaugeFixedTeukolskyCokernelSectionWithThirdJetCorrection
        ell source correction = target := by
  refine ⟨(target - ell source) • unitDirection, ?_⟩
  simp [d4GaugeFixedTeukolskyCokernelSectionWithThirdJetCorrection,
    map_add, map_smul, hunit]

/-- Nonlinear QNM pole velocity determined by the total cokernel section. -/
def d4GaugeFixedTeukolskyTotalPlusPlusMinusPoleVelocity
    (coefficient normalization : ℂ) : ℂ :=
  -coefficient / normalization

/-- Fredholm solvability relation between total section and nonlinear pole velocity. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusSection_eq_neg_poleVelocity_mul
    (coefficient normalization : ℂ) (hnorm : normalization ≠ 0) :
    coefficient =
      -d4GaugeFixedTeukolskyTotalPlusPlusMinusPoleVelocity coefficient normalization *
        normalization := by
  unfold d4GaugeFixedTeukolskyTotalPlusPlusMinusPoleVelocity
  field_simp

end

end RHTower

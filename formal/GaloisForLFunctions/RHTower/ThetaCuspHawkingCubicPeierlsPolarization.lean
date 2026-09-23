import GaloisForLFunctions.RHTower.ThetaCuspHawkingTotalThirdOrderCausalCut

/-!
# Cubic Peierls polarization of the nonlinear Teukolsky causal cut

Let `P : X × Y → ℂ` pair augmented fields with complete bulk-plus-boundary residuals, let `B` be
the symmetric quadratic residual, and let `Delta : Y → X` be the global retarded-minus-advanced
propagator. If the third action variation is cyclic and the causal source pairing

`Omega(f,g) = P(Delta f,g)`

is skew, the mixed `+-` response in the phase-normalized cubic cut is a causal self-pairing and
vanishes. The complete cut is instead twice the polarized pairing of the `++` and `--` quadratic
sources. Consequently it is branch-antisymmetric, zero on the diagonal, and scales by `|A|^(4 : ℕ)`
under the physical amplitude law `p ↦ A p`, `m ↦ conj(A) m`.

This is an abstract variational identity. Applying it to Birmingham--Mokhtari modes still requires
proving that the augmented horizon/AdS response maps are blocks of one Peierls propagator and that
the unit-Wronskian left QNM functional is induced by the same action pairing.
-/

open Complex

namespace RHTower

noncomputable section

variable {X Y : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- Causal source pairing induced by an augmented field--residual pairing. -/
def d4GaugeFixedTeukolskyPeierlsSourcePairing
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (Delta : Y →ₗ[ℂ] X)
    (f g : Y) : ℂ :=
  pairing (Delta f) g

/-- Phase-normalized cubic causal cut with the Schwarz target leg included in the pairing. -/
def d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Delta : Y →ₗ[ℂ] X)
    (p m : X) : ℂ :=
  pairing m (B p (Delta
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m))) +
    pairing m (B m (Delta
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)))

/-- Exact corpus causal cut becomes the phase-normalized Peierls cut when both graded response
jumps are restrictions of one causal propagator. -/
theorem d4GaugeFixedTeukolskyCokernelCausalCut_eq_phaseNormalizedPeierls
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (hpm : RpmRet - RpmAdv = Delta)
    (hpp : RppRet - RppAdv = Delta) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        (pairing m) B C RppRet RpmRet RppAdv RpmAdv p m =
      d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta p m := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq, hpm, hpp]
  rfl

/-- Peierls skewness kills the mixed quadratic source's causal self-contraction. -/
theorem d4GaugeFixedTeukolskyPeierls_mixed_self_eq_zero
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Delta : Y →ₗ[ℂ] X)
    (p m : X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) :
    pairing m (B p (Delta
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m))) = 0 := by
  let f := d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m
  have hf : f = B p m :=
    d4GaugeFixedTeukolskyQuadraticPlusMinusResidual_eq B p m (hB m p)
  rw [hcyclic m p (Delta f), hB m p, ← hf]
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp (hskew f f))

/-- Cubic Peierls polarization: only the polarized second-harmonic source pairing survives. -/
theorem d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_eq_polarized
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Delta : Y →ₗ[ℂ] X)
    (p m : X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) :
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta p m =
      2 * d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B m) := by
  rw [d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut,
    d4GaugeFixedTeukolskyPeierls_mixed_self_eq_zero pairing B Delta p m
      hB hcyclic hskew,
    zero_add, hcyclic m m]
  simp [d4GaugeFixedTeukolskyPeierlsSourcePairing,
    d4GaugeFixedTeukolskyQuadraticPlusPlusResidual, map_smul]

/-- Exchanging the two linear branches reverses the polarized cubic causal cut. -/
theorem d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_swap
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Delta : Y →ₗ[ℂ] X)
    (p m : X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) :
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta m p =
      -d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta p m := by
  rw [d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_eq_polarized
      pairing B Delta m p hB hcyclic hskew,
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_eq_polarized
      pairing B Delta p m hB hcyclic hskew,
    hskew]
  ring

/-- Coincident branches have zero phase-normalized cubic Peierls cut. -/
theorem d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_self_eq_zero
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Delta : Y →ₗ[ℂ] X)
    (p : X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) :
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta p p = 0 := by
  have h := d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_swap
    pairing B Delta p p hB hcyclic hskew
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp h)

/-- Physical amplitude scaling is quartic and phase invariant. -/
theorem d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_smul_conj
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Delta : Y →ₗ[ℂ] X)
    (A : ℂ) (p m : X) :
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta
        (A • p) ((starRingEnd ℂ A) • m) =
      (Complex.normSq A : ℂ) ^ (2 : ℕ) *
        d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta p m := by
  simp [d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut,
    d4GaugeFixedTeukolskyQuadraticPlusMinusResidual,
    d4GaugeFixedTeukolskyQuadraticPlusPlusResidual, map_smul]
  rw [← Complex.mul_conj]
  ring

end

end RHTower

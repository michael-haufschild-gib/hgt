import GaloisForLFunctions.RHTower.ThetaCuspHawkingModularBoostEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingKMSCayleyScatteringMixingEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxTwoSupportRigidity

/-!
# Hawking modular characteristic scattering endpoint

This module derives a coherent multi-shell scattering problem from the actual
deembedded Davies--Fulling Born pair amplitude already constructed in the
Hawking route.

* `[PROVED BRIDGE]` Causal rotation of the deembedded pair amplitude is exactly
  the bilateral Laplace transform of `thetaCuspTiltSource`.  Modular aperture
  translation therefore gives the existing `tiltWindow`, not an analogy to it.
* `[PROVED BRIDGE]` On every positive physical shell, nonvanishing of that same
  causal amplitude is equivalent both to nonzero exchange in the exact unitary
  Hawking KMS two-port dilation and to repeated-scattering sector mixing.
* `[PROVED BRIDGE]` The characteristic fields `generator ± t * packet` have
  an exact signed energy balance governed by the theta-source Bezoutian.  On a
  single shell their output/input quotient is the canonical Cayley transform.
* `[PROVED SURVIVOR]` RH is equivalent to contractivity of this full coherent
  modular characteristic scattering problem on every exterior Euler packet.
  Every packet supported on at most two exterior real shells is contractive
  unconditionally.  Thus any failure must use complex shells or at least three
  real shells.

`[LOCAL-RESEARCH] [NOVELTY UNVERIFIED]` The source-specific identification of
the coherent Hawking packet with the RH-complete theta tilt flux appears new.
The Cayley transform and Bogoliubov/characteristic scattering mechanisms are
standard.  The displayed characteristic Cayley law is a canonical completion,
not a theorem that exact nonlinear mirror dynamics selects that completion.
This endpoint does **not** prove the required full contractivity.
It isolates the remaining RH-bearing producer: a source-specific multi-shell
correlation law forcing characteristic contractivity (or, equivalently,
forcing all tilted sectors to mix with the needed sign).  Particle number,
single-sector KMS positivity, and local quantum energy inequalities do not
supply that coherent cross-shell law.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-- Causal/Laplace rotation of the deembedded Hawking pair amplitude. -/
def thetaCuspHawkingCausalDeembeddedPairAmplitude (z : ℂ) : ℂ :=
  thetaCuspHawkingDeembeddedPairAmplitude (-Complex.I * z)

/-- Coherent modular packet assembled from causal Hawking pair amplitudes. -/
def thetaCuspHawkingModularPacket {d : ℕ} (c w : Fin d → ℂ)
    (a s : ℝ) : ℂ :=
  ∑ j, c j *
    thetaCuspHawkingCausalDeembeddedPairAmplitude (w j + (a : ℂ)) *
      Complex.exp (-(w j) * (s : ℂ))

theorem thetaCuspHawkingCausalDeembeddedPairAmplitude_eq_laplace (z : ℂ) :
    thetaCuspHawkingCausalDeembeddedPairAmplitude z =
      bilateralLaplace thetaCuspTiltSource z := by
  rw [thetaCuspHawkingCausalDeembeddedPairAmplitude,
    thetaCuspHawkingDeembeddedPairAmplitude,
    bilateralLaplace_thetaCuspTiltSource_eq_xiCent, xiCent_eq_XiC]

/-- The causal amplitude on a positive physical shell is the Xi factor feeding
the exact Hawking KMS two-port scattering dilation. -/
theorem thetaCuspHawkingCausalDeembeddedPairAmplitude_physicalShell
    (a omega : ℝ) :
    thetaCuspHawkingCausalDeembeddedPairAmplitude
        ((-a : ℂ) + (omega : ℂ) * Complex.I) =
      XiC ((omega : ℂ) + (a : ℂ) * Complex.I) := by
  rw [thetaCuspHawkingCausalDeembeddedPairAmplitude,
    thetaCuspHawkingDeembeddedPairAmplitude]
  congr 1
  apply Complex.ext <;> simp

/-- Nonzero exchange in the exact unitary KMS two-port is precisely a bright
causal theta/Hawking shell. -/
theorem thetaCuspHawkingKMSCayleyTransition_one_ne_zero_iff_causalAmplitude
    (a omega : ℝ) (homega : 0 < omega) :
    thetaCuspHawkingCayleyTransition 1 a omega ≠ 0 ↔
      thetaCuspHawkingCausalDeembeddedPairAmplitude
        ((-a : ℂ) + (omega : ℂ) * Complex.I) ≠ 0 := by
  rw [thetaCuspHawkingCayleyTransition_one_ne_zero_iff, ne_eq,
    thetaCuspHawkingFriedrichsShellFormFactor_eq_zero_iff homega,
    ← thetaCuspHawkingCausalDeembeddedPairAmplitude_physicalShell]

/-- Resonance-sector mixing is derived from the exact KMS scattering dilation
and is equivalent to brightness of the same causal amplitude used below. -/
theorem thetaCuspHawkingKMSCayleySectorMixes_iff_causalAmplitude
    {kappa a omega : ℝ} (homega : 0 < omega) :
    ThetaCuspHawkingKMSCayleySectorMixes kappa a omega ↔
      thetaCuspHawkingCausalDeembeddedPairAmplitude
        ((-a : ℂ) + (omega : ℂ) * Complex.I) ≠ 0 := by
  rw [thetaCuspHawkingKMSCayleySectorMixes_iff_XiC_ne_zero homega,
    thetaCuspHawkingCausalDeembeddedPairAmplitude_physicalShell]

theorem thetaCuspHawkingModularPacket_eq_tiltWindow {d : ℕ}
    (c w : Fin d → ℂ) (a s : ℝ) :
    thetaCuspHawkingModularPacket c w a s =
      tiltWindow thetaCuspTiltSource c w a s := by
  rw [thetaCuspHawkingModularPacket, tiltWindow_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [thetaCuspHawkingCausalDeembeddedPairAmplitude_eq_laplace]

/-- Half-line energy of a coherent modular Hawking packet. -/
def thetaCuspHawkingModularPacketEnergy {d : ℕ} (c w : Fin d → ℂ)
    (a : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), ‖thetaCuspHawkingModularPacket c w a s‖ ^ (2 : ℕ)

theorem thetaCuspHawkingModularPacketEnergy_eq_tiltCorrelation {d : ℕ}
    (c w : Fin d → ℂ) (a : ℝ) :
    thetaCuspHawkingModularPacketEnergy c w a =
      tiltCorrelation thetaCuspTiltSource c w a := by
  unfold thetaCuspHawkingModularPacketEnergy tiltCorrelation
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  rw [thetaCuspHawkingModularPacket_eq_tiltWindow]

theorem thetaCuspHawkingCausalDeembeddedPairAmplitude_deriv_eq_laplaceDeriv
    (z : ℂ) :
    deriv thetaCuspHawkingCausalDeembeddedPairAmplitude z =
      bilateralLaplaceDeriv thetaCuspTiltSource z := by
  have hfun : thetaCuspHawkingCausalDeembeddedPairAmplitude =
      bilateralLaplace thetaCuspTiltSource :=
    funext thetaCuspHawkingCausalDeembeddedPairAmplitude_eq_laplace
  rw [hfun, deriv_bilateralLaplace]

/-- Infinitesimal modular-translation generator of the coherent packet. -/
def thetaCuspHawkingModularPacketGenerator {d : ℕ} (c w : Fin d → ℂ)
    (s : ℝ) : ℂ :=
  ∑ j, c j * deriv thetaCuspHawkingCausalDeembeddedPairAmplitude (w j) *
    Complex.exp (-(w j) * (s : ℂ))

theorem thetaCuspHawkingModularPacketGenerator_eq_sourceMoment {d : ℕ}
    (c w : Fin d → ℂ) (s : ℝ) :
    thetaCuspHawkingModularPacketGenerator c w s =
      sourceMoment thetaCuspTiltSource c w s := by
  rw [thetaCuspHawkingModularPacketGenerator, sourceMoment]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [thetaCuspHawkingCausalDeembeddedPairAmplitude_deriv_eq_laplaceDeriv]

/-- Incoming characteristic field `generator + t * packet`. -/
def thetaCuspHawkingCharacteristicIncoming {d : ℕ} (c w : Fin d → ℂ)
    (t s : ℝ) : ℂ :=
  thetaCuspHawkingModularPacketGenerator c w s +
    (t : ℂ) * thetaCuspHawkingModularPacket c w 0 s

/-- Outgoing characteristic field `generator - t * packet`. -/
def thetaCuspHawkingCharacteristicOutgoing {d : ℕ} (c w : Fin d → ℂ)
    (t s : ℝ) : ℂ :=
  thetaCuspHawkingModularPacketGenerator c w s -
    (t : ℂ) * thetaCuspHawkingModularPacket c w 0 s

theorem thetaCuspHawkingCharacteristicIncoming_eq_contractionPlus {d : ℕ}
    (c w : Fin d → ℂ) (t s : ℝ) :
    thetaCuspHawkingCharacteristicIncoming c w t s =
      contractionPlus thetaCuspTiltSource c w t s := by
  rw [thetaCuspHawkingCharacteristicIncoming, contractionPlus,
    thetaCuspHawkingModularPacketGenerator_eq_sourceMoment,
    thetaCuspHawkingModularPacket_eq_tiltWindow, tiltWindow_zero]

theorem thetaCuspHawkingCharacteristicOutgoing_eq_contractionMinus {d : ℕ}
    (c w : Fin d → ℂ) (t s : ℝ) :
    thetaCuspHawkingCharacteristicOutgoing c w t s =
      contractionMinus thetaCuspTiltSource c w t s := by
  rw [thetaCuspHawkingCharacteristicOutgoing, contractionMinus,
    thetaCuspHawkingModularPacketGenerator_eq_sourceMoment,
    thetaCuspHawkingModularPacket_eq_tiltWindow, tiltWindow_zero]

def thetaCuspHawkingCharacteristicIncomingEnergy {d : ℕ}
    (c w : Fin d → ℂ) (t : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ),
    ‖thetaCuspHawkingCharacteristicIncoming c w t s‖ ^ (2 : ℕ)

def thetaCuspHawkingCharacteristicOutgoingEnergy {d : ℕ}
    (c w : Fin d → ℂ) (t : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ),
    ‖thetaCuspHawkingCharacteristicOutgoing c w t s‖ ^ (2 : ℕ)

/-- Exact coherent characteristic balance.  No positivity assumption enters. -/
theorem thetaCuspHawkingCharacteristicEnergy_balance {d : ℕ}
    (c w : Fin d → ℂ) (hw : ∀ j, 0 < (w j).re) (t : ℝ) :
    thetaCuspHawkingCharacteristicIncomingEnergy c w t -
        thetaCuspHawkingCharacteristicOutgoingEnergy c w t =
      2 * t *
        (∑ j, ∑ l, c j * conj (c l) *
          sourceBezoutian thetaCuspTiltSource (w j) (w l)).re := by
  have h := contraction_energy_difference thetaCuspTiltSource c w hw t
  rw [← sourceBezoutianSum_eq_pairing thetaCuspTiltSource c w hw] at h
  let F : ℂ := ∑ j, ∑ l, c j * conj (c l) *
    sourceBezoutian thetaCuspTiltSource (w j) (w l)
  change
    (((∫ s in Set.Ioi (0 : ℝ),
        ‖contractionPlus thetaCuspTiltSource c w t s‖ ^ (2 : ℕ) : ℝ) : ℂ) -
      ((∫ s in Set.Ioi (0 : ℝ),
        ‖contractionMinus thetaCuspTiltSource c w t s‖ ^ (2 : ℕ) : ℝ) : ℂ)) =
      2 * (t : ℂ) * F at h
  have hFim : F.im = 0 := by
    simpa only [F] using sourceBezoutianSum_im thetaCuspTiltSource c w
  have hre := congrArg Complex.re h
  norm_num [Complex.mul_re, hFim] at hre
  dsimp only [F] at hre
  rw [thetaCuspHawkingCharacteristicIncomingEnergy,
    thetaCuspHawkingCharacteristicOutgoingEnergy]
  simpa only [thetaCuspHawkingCharacteristicIncoming_eq_contractionPlus,
    thetaCuspHawkingCharacteristicOutgoing_eq_contractionMinus] using hre

theorem thetaCuspHawkingCharacteristicEnergy_balance_of_hasDerivAt {d : ℕ}
    (c w : Fin d → ℂ) (hw : ∀ j, 0 < (w j).re) {D : ℝ}
    (hD : HasDerivAt (thetaCuspHawkingModularPacketEnergy c w) D 0)
    (t : ℝ) :
    thetaCuspHawkingCharacteristicIncomingEnergy c w t -
        thetaCuspHawkingCharacteristicOutgoingEnergy c w t =
      2 * t * D := by
  have hcanonical := hasDerivAt_tiltCorrelation thetaCuspTiltSource c w hw
  have henergy :
      HasDerivAt (tiltCorrelation thetaCuspTiltSource c w) D 0 := by
    exact hD.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun a =>
        (thetaCuspHawkingModularPacketEnergy_eq_tiltCorrelation c w a).symm)
  have huniq := henergy.unique hcanonical
  rw [thetaCuspHawkingCharacteristicEnergy_balance c w hw t, ← huniq]

/-- Canonical nonperturbative single-shell theta-mirror characteristic Cayley
coefficient.  Dynamical selection of this completion remains open. -/
def thetaCuspHawkingCharacteristicCayley (t : ℝ) (w : ℂ) : ℂ :=
  (deriv thetaCuspHawkingCausalDeembeddedPairAmplitude w -
      (t : ℂ) * thetaCuspHawkingCausalDeembeddedPairAmplitude w) /
    (deriv thetaCuspHawkingCausalDeembeddedPairAmplitude w +
      (t : ℂ) * thetaCuspHawkingCausalDeembeddedPairAmplitude w)

theorem thetaCuspHawkingCharacteristicCayley_mul_input (t : ℝ) (w : ℂ)
    (hden : deriv thetaCuspHawkingCausalDeembeddedPairAmplitude w +
      (t : ℂ) * thetaCuspHawkingCausalDeembeddedPairAmplitude w ≠ 0) :
    thetaCuspHawkingCharacteristicCayley t w *
        (deriv thetaCuspHawkingCausalDeembeddedPairAmplitude w +
          (t : ℂ) * thetaCuspHawkingCausalDeembeddedPairAmplitude w) =
      deriv thetaCuspHawkingCausalDeembeddedPairAmplitude w -
        (t : ℂ) * thetaCuspHawkingCausalDeembeddedPairAmplitude w := by
  rw [thetaCuspHawkingCharacteristicCayley, div_mul_cancel₀ _ hden]

/-- Full coherent exterior-packet contractivity of characteristic scattering. -/
def ThetaCuspHawkingModularCharacteristicContractive : Prop :=
  ∀ (d : ℕ) (c w : Fin d → ℂ), (∀ j, 1 / 2 < (w j).re) →
    thetaCuspHawkingCharacteristicOutgoingEnergy c w 1 ≤
      thetaCuspHawkingCharacteristicIncomingEnergy c w 1

/-- The coherent Hawking characteristic-scattering completion is RH-complete. -/
theorem riemannHypothesis_iff_thetaCuspHawkingModularCharacteristicContractive :
    RiemannHypothesis ↔ ThetaCuspHawkingModularCharacteristicContractive := by
  rw [riemannHypothesis_iff_thetaCuspTiltSource_sourceBezoutian_nonneg]
  constructor
  · intro h d c w hw
    have hflux := h d c w hw
    have hbalance := thetaCuspHawkingCharacteristicEnergy_balance c w
      (fun j => lt_trans (by norm_num) (hw j)) 1
    linarith
  · intro h d c w hw
    have hcontractive := h d c w hw
    have hbalance := thetaCuspHawkingCharacteristicEnergy_balance c w
      (fun j => lt_trans (by norm_num) (hw j)) 1
    linarith

/-- At most two exterior real shells are unconditionally contractive. -/
theorem thetaCuspHawkingModularCharacteristic_twoSupport_realRay_contractive
    {n : ℕ} (c w : Fin n → ℂ) {x y : ℝ}
    (hx : 1 / 2 < x) (hxy : x < y)
    (hsupport : ∀ j, w j = (x : ℂ) ∨ w j = (y : ℂ)) :
    thetaCuspHawkingCharacteristicOutgoingEnergy c w 1 ≤
      thetaCuspHawkingCharacteristicIncomingEnergy c w 1 := by
  have hw : ∀ j, 0 < (w j).re := by
    intro j
    rcases hsupport j with hj | hj <;> rw [hj] <;> simp <;> linarith
  let D : ℝ :=
    (∑ j, ∑ l, c j * conj (c l) *
      sourceBezoutian thetaCuspTiltSource (w j) (w l)).re
  have hD : HasDerivAt (tiltCorrelation thetaCuspTiltSource c w) D 0 :=
    hasDerivAt_tiltCorrelation thetaCuspTiltSource c w hw
  have hnonneg : 0 ≤ D :=
    thetaCuspTiltSource_twoSupport_realRay_tiltFlux_nonneg
      c w hx hxy hsupport hD
  have hbalance := thetaCuspHawkingCharacteristicEnergy_balance c w hw 1
  dsimp only [D] at hnonneg
  linarith

/-- Under failure of RH, noncontractivity needs complex or at least three real shells. -/
theorem exists_noncontractive_thetaCuspHawkingModularCharacteristic_not_twoSupport_realRay
    (hRH : ¬ RiemannHypothesis) :
    ∃ (n : ℕ) (c w : Fin n → ℂ),
      (∀ j, 1 / 2 < (w j).re) ∧
      thetaCuspHawkingCharacteristicIncomingEnergy c w 1 <
        thetaCuspHawkingCharacteristicOutgoingEnergy c w 1 ∧
      ¬ ∃ x y : ℝ, 1 / 2 < x ∧ x < y ∧
        ∀ j, w j = (x : ℂ) ∨ w j = (y : ℂ) := by
  obtain ⟨n, c, w, D, hw, hD, hneg, hsupport⟩ :=
    exists_negative_thetaCuspTiltFlux_not_twoSupport_realRay hRH
  have hwpos : ∀ j, 0 < (w j).re :=
    fun j => lt_trans (by norm_num) (hw j)
  have hDenergy :
      HasDerivAt (thetaCuspHawkingModularPacketEnergy c w) D 0 := by
    exact hD.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun a =>
        thetaCuspHawkingModularPacketEnergy_eq_tiltCorrelation c w a)
  have hbalance :=
    thetaCuspHawkingCharacteristicEnergy_balance_of_hasDerivAt
      c w hwpos hDenergy 1
  exact ⟨n, c, w, hw, by linarith, hsupport⟩

end RHTower

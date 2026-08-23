import GaloisForLFunctions.RHTower.ThetaCuspHawkingMinimumPhaseEndpoint
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel

/-!
# Quantized Wigner--Smith winding of theta-cusp Hawking resonances

The theta-cusp moving-mirror Born response has a literal causal all-pass factor at every
upper-half-plane anomaly resonance.  Its physical Wigner--Smith clock is the Lorentzian

`2 Im(alpha) / (Im(alpha)^2 + (x - Re(alpha))^2)`.

This file integrates that clock over the full physical-frequency line.  Every such resonance
contributes exactly `2*pi`, hence one normalized phase-winding unit, independently of its position.
A finite hidden all-pass sector therefore has charge equal to its cardinality.  Hawking particle
number remains blind to this integer, while phase-sensitive delay sees it.

The result is a scalar Birman--Krein/Levinson-type winding law, not a claim that `XiC` has already
been realized as the Jost determinant of a self-adjoint Hamiltonian.  The theta Born--Witten
factorizations reconstruct moments but do not supply that missing realization.  Accordingly the
capstone below is an exact RH endpoint/observer, not an independent RH producer.
-/

open Complex Real MeasureTheory
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Full-line Wigner--Smith delay carried by one upper causal theta-Hawking resonance. -/
def thetaCuspHawkingAllPassDelayArea
    (r : ThetaCuspHawkingBackreactionResonantMode) : ℝ :=
  ∫ x : ℝ, thetaCuspHawkingCausalAllPassClock r x

/-- Normalized phase-winding charge of one causal theta-Hawking all-pass sector. -/
def thetaCuspHawkingAllPassWindingCharge
    (r : ThetaCuspHawkingBackreactionResonantMode) : ℝ :=
  thetaCuspHawkingAllPassDelayArea r / (2 * Real.pi)

/-- The Lorentzian Wigner--Smith clock of an upper theta-Hawking resonance is integrable. -/
theorem integrable_thetaCuspHawkingCausalAllPassClock
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    Integrable (thetaCuspHawkingCausalAllPassClock r) := by
  have hbase :=
    GaloisForLFunctions.HTGeometry.integrable_inv_shifted_sq_add_sq
      hr r.1.re
  have hscaled := hbase.const_mul (2 * r.1.im)
  refine hscaled.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [thetaCuspHawkingCausalAllPassClock_eq r hr]
  simp only [div_eq_mul_inv]

/-- **Quantized delay-area law.**  Every upper causal theta-Hawking resonance contributes exactly
one full `2*pi` turn of Wigner--Smith phase, regardless of its real frequency or growth rate. -/
theorem thetaCuspHawkingAllPassDelayArea_eq_two_pi
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    thetaCuspHawkingAllPassDelayArea r = 2 * Real.pi := by
  rw [thetaCuspHawkingAllPassDelayArea]
  have hfun : thetaCuspHawkingCausalAllPassClock r =
      fun x : ℝ =>
        2 * r.1.im * (r.1.im ^ 2 + (x - r.1.re) ^ 2)⁻¹ := by
    funext x
    rw [thetaCuspHawkingCausalAllPassClock_eq r hr]
    simp only [div_eq_mul_inv]
  rw [hfun, MeasureTheory.integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_inv_shifted_sq_add_sq hr]
  field_simp [ne_of_gt hr]

/-- One upper causal zero carries exactly one normalized winding unit. -/
theorem thetaCuspHawkingAllPassWindingCharge_eq_one
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    thetaCuspHawkingAllPassWindingCharge r = 1 := by
  rw [thetaCuspHawkingAllPassWindingCharge,
    thetaCuspHawkingAllPassDelayArea_eq_two_pi r hr]
  field_simp [Real.pi_ne_zero]

/-- Total normalized winding charge of a finite theta-Hawking all-pass sector. -/
def thetaCuspHawkingAllPassPacketWindingCharge
    (S : Finset ThetaCuspHawkingBackreactionResonantMode) : ℝ :=
  S.sum thetaCuspHawkingAllPassWindingCharge

/-- **Finite Levinson count.**  Winding charge counts upper theta-Hawking resonances in every
finite packet, including multiplicity represented by distinct packet entries. -/
theorem thetaCuspHawkingAllPassPacketWindingCharge_eq_card
    (S : Finset ThetaCuspHawkingBackreactionResonantMode)
    (hS : ∀ r ∈ S, 0 < r.1.im) :
    thetaCuspHawkingAllPassPacketWindingCharge S = S.card := by
  classical
  rw [thetaCuspHawkingAllPassPacketWindingCharge]
  calc
    S.sum thetaCuspHawkingAllPassWindingCharge = S.sum (fun _r => (1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [thetaCuspHawkingAllPassWindingCharge_eq_one r (hS r hr)]
    _ = S.card := by simp

/-- Source-normalized scattering rigidity: no upper causal theta-Hawking resonance contributes a
nonzero global Wigner--Smith phase winding. -/
def ThetaCuspHawkingAllPassWindingRigid : Prop :=
  ∀ r : ThetaCuspHawkingBackreactionResonantMode,
    0 < r.1.im → thetaCuspHawkingAllPassWindingCharge r = 0

/-- **Theta-Hawking Wigner--Smith winding endpoint.**  RH is equivalent to absence of every
positive, intensity-invisible global phase-winding sector in the literal theta-cusp Hawking Born
response. -/
theorem riemannHypothesis_iff_thetaCuspHawkingAllPassWindingRigid :
    RiemannHypothesis ↔ ThetaCuspHawkingAllPassWindingRigid := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal r hr
    have hzero := hreal r.1
      (thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero r)
    exfalso
    linarith
  · intro hrigid alpha hXi
    let r : ThetaCuspHawkingBackreactionResonantMode :=
      ⟨alpha,
        (xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance alpha).mp hXi⟩
    by_contra him
    have horient : 0 < r.1.im ∨
        0 < (thetaCuspHawkingBackreactionReflectedResonantMode r).1.im := by
      rw [thetaCuspHawkingBackreactionReflectedResonantMode_im]
      rcases lt_or_gt_of_ne him with hneg | hpos
      · exact Or.inr (neg_pos.mpr hneg)
      · exact Or.inl hpos
    rcases horient with hr | hr
    · have hone := thetaCuspHawkingAllPassWindingCharge_eq_one r hr
      have hzero := hrigid r hr
      linarith
    · let r' := thetaCuspHawkingBackreactionReflectedResonantMode r
      have hone := thetaCuspHawkingAllPassWindingCharge_eq_one r' hr
      have hzero := hrigid r' hr
      linarith

end RHTower

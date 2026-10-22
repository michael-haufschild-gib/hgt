import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTargetIndependentFullCokernelPeierlsRealization
import GaloisForLFunctions.HTGeometry.FinitePassiveResponse

/-!
# Finite-KMS passivity has the wrong polarity for the HB full-cokernel orbit

The complete target-independent HB Peierls orbit is a negative optical square.  This file shows
that the sign is not merely compatible with abstract passivity: every Xi fibre is exactly the
dissipative quadrature of an explicit two-level canonical KMS/Wightman response.

The realizing Hamiltonian has energies `0,1`, inverse temperature zero, and a Hermitian observable
supported only on the two off-diagonal transitions.  Thus no zero-frequency atom, divisorwise
division, infinite-state limit, or QNM-completeness premise is used.  At the upper-half-plane point
`i`, the response is `-i P`, where `P` is the positive HB susceptibility times optical power;
multiplication by the fixed quadrature `-i` gives the full-cokernel orbit `-P` exactly.

Consequently standard finite-KMS passivity supplies the orbit's already-known nonpositive
orientation on every fibre.  Its opposite nonnegative orientation holds exactly on the critical
wall and globally exactly under RH.  Generic KMS/passivity or ordinary optical positivity therefore
cannot be the missing HB producer.  A survivor must derive an additional phase-sensitive
Einstein--Teukolsky/source law with the opposite polarity.

`[NEW] [HB ROUTE KILL] [FINITE KMS] [PASSIVITY POLARITY] [TWO LEVEL] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

open HTGeometry

noncomputable section

/-- Nonnegative dissipative intensity of the canonical HB full-cokernel orbit. -/
def hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility n q *
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q

theorem hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity_nonneg
    (n : ℕ) (q : XiZeroCopy) :
    0 ≤ hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity n q := by
  rw [hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity,
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_wardEnergyMultiplier_mul_charge_sq]
  exact mul_nonneg
    (d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility_pos n q).le
    (mul_nonneg
      (hbXiPeierlsFESchwarzCanonicalWardEnergyMultiplier_pos n q).le
      (sq_nonneg _))

/-- Fixed two-level Hamiltonian used by the exact passive realization. -/
def hbXiPeierlsCanonicalFullCokernelTwoLevelKMSEnergy (a : Fin 2) : ℝ :=
  a.1

/-- Hermitian off-diagonal observable whose KMS intensity is the HB dissipative intensity. -/
def hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude
    (n : ℕ) (q : XiZeroCopy) (a b : Fin 2) : ℂ :=
  if a = b then 0
  else Real.sqrt
    (2 * hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity n q)

theorem hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude_hermitian
    (n : ℕ) (q : XiZeroCopy) (a b : Fin 2) :
    hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude n q b a =
      star (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude n q a b) := by
  simp only [hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude]
  by_cases h : a = b
  · subst b
    simp
  · have h' : b ≠ a := Ne.symm h
    rw [if_neg h, if_neg h']
    simp

/-- The realizing observable has no diagonal/zero-frequency transition. -/
theorem hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude_self
    (n : ℕ) (q : XiZeroCopy) (a : Fin 2) :
    hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude n q a a = 0 := by
  simp [hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude]

/-- Exact canonical KMS/Wightman intensity matrix: zero on the diagonal and the HB intensity on
both nonzero-frequency transitions. -/
theorem hbXiPeierlsCanonicalFullCokernelTwoLevelKMSIntensity_eq
    (n : ℕ) (q : XiZeroCopy) (a b : Fin 2) :
    finiteKMSWightmanTransitionIntensity 0
        hbXiPeierlsCanonicalFullCokernelTwoLevelKMSEnergy
        (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude n q) a b =
      if a = b then 0
      else hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity n q := by
  have hPself :
      Real.sqrt (hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity n q) *
          Real.sqrt (hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity n q) =
        hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity n q := by
    simpa only [pow_two] using Real.sq_sqrt
      (hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity_nonneg n q)
  fin_cases a <;> fin_cases b <;>
    simp [finiteKMSWightmanTransitionIntensity, wightmanTransitionIntensity,
      finiteKMSWightmanWeight, finiteGibbsPartition,
      hbXiPeierlsCanonicalFullCokernelTwoLevelKMSEnergy,
      hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude, hPself]

/-- Canonical finite-KMS response of the explicit two-level system. -/
def hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt
    (n : ℕ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  finiteTransitionPassiveResponse
    (finiteKMSWightmanTransitionIntensity 0
      hbXiPeierlsCanonicalFullCokernelTwoLevelKMSEnergy
      (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude n q))
    hbXiPeierlsCanonicalFullCokernelTwoLevelKMSEnergy z

/-- The two-level response is passive throughout the upper half-plane. -/
theorem hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_im_nonpos
    (n : ℕ) (q : XiZeroCopy) {z : ℂ} (hz : 0 < z.im) :
    (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q z).im ≤ 0 := by
  exact finiteKMSWightmanTransitionPassiveResponse_im_nonpos 0
    hbXiPeierlsCanonicalFullCokernelTwoLevelKMSEnergy
    (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSAmplitude n q) hz

/-- At `i`, the exact response is the negative imaginary HB dissipative intensity. -/
theorem hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_eq
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I =
      -Complex.I *
        (hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity n q : ℂ) := by
  rw [hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt,
    finiteTransitionPassiveResponse]
  simp_rw [hbXiPeierlsCanonicalFullCokernelTwoLevelKMSIntensity_eq]
  simp [hbXiPeierlsCanonicalFullCokernelTwoLevelKMSEnergy]
  have hp : (1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hm : (-1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hp' : (Complex.I + 1 : ℂ) ≠ 0 := by simpa [add_comm] using hp
  have hm' : (Complex.I - 1 : ℂ) ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hm
  field_simp [hp, hm, hp', hm']
  ring_nf
  rw [show Complex.I ^ (3 : ℕ) = -Complex.I by norm_num [pow_succ, Complex.I_sq]]
  ring

/-- Fixed dissipative quadrature of the explicit KMS response is exactly the complete
target-independent full-cokernel HB orbit. -/
theorem neg_I_mul_hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_eq_orbitCut
    (n : ℕ) (q : XiZeroCopy) :
    -Complex.I *
        hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I =
      hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q := by
  rw [hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_eq,
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_hbOpticalPower]
  unfold hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Absorptive KMS response and real HB orbit are the same signed scalar. -/
theorem hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_eq_orbitCut_re
    (n : ℕ) (q : XiZeroCopy) :
    (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I).im =
      (hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q).re := by
  rw [hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_eq,
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_hbOpticalPower]
  unfold hbXiPeierlsCanonicalFullCokernelKMSDissipativeIntensity
  simp

/-- Standard KMS passivity reproduces the nonpositive HB orbit orientation. -/
theorem hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_nonpos
    (n : ℕ) (q : XiZeroCopy) :
    (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I).im ≤ 0 := by
  exact hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_im_nonpos n q (by norm_num)

/-- The passive response is strictly dissipative at every tilted Xi fibre. -/
theorem hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_neg_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I).im < 0 := by
  rw [hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_eq_orbitCut_re]
  exact hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_re_neg_of_tilt n q htilt

/-- The sign opposite to standard passivity occurs exactly on the critical wall. -/
theorem hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_nonneg_iff
    (n : ℕ) (q : XiZeroCopy) :
    0 ≤ (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I).im ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_eq_orbitCut_re]
  exact hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_re_nonneg_iff n q

/-- Extinction of the passive response is exactly critical-line incidence. -/
theorem hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I).im = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    exact
      (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_nonneg_iff n q).mp
        (le_of_eq hzero.symm)
  · intro hline
    have hnonneg :=
      (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_nonneg_iff n q).mpr
        hline
    have hnonpos :=
      hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_nonpos n q
    linarith

/-- Universal opposite-KMS orientation of one fixed grade is exactly RH. -/
theorem forall_hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_nonneg_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      0 ≤ (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I).im) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply
      (forall_hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_re_nonneg_iff_rh n).mp
    intro q
    rw [← hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_eq_orbitCut_re]
    exact h q
  · intro hRH q
    apply
      (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_nonneg_iff n q).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

/-- Closed route class: generic finite-KMS passivity realizes the existing negative HB orbit and
its opposite sign remains exactly the critical-line/RH condition. -/
def D4HBFullCokernelFiniteKMSPassivityPolarityRouteKilled : Prop :=
  (∀ (n : ℕ) (q : XiZeroCopy),
      (∀ z : ℂ, 0 < z.im →
        (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q z).im ≤ 0) ∧
      -Complex.I *
          hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I =
        hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q ∧
      (0 ≤ (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I).im ↔
        (q.1 : ℂ).re = 1 / 2)) ∧
    ∀ n : ℕ,
      (∀ q : XiZeroCopy,
        0 ≤ (hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt n q Complex.I).im) ↔
        RiemannHypothesis

/-- Premise-free certificate killing generic KMS/passivity and ordinary optical positivity as
producers of the missing HB opposite sign. -/
theorem d4HBFullCokernelFiniteKMSPassivityPolarityRouteKilled :
    D4HBFullCokernelFiniteKMSPassivityPolarityRouteKilled := by
  constructor
  · intro n q
    exact ⟨fun z hz =>
        hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_im_nonpos n q hz,
      neg_I_mul_hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_eq_orbitCut n q,
      hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_nonneg_iff n q⟩
  · exact
      forall_hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_nonneg_iff_rh

end

end RHTower

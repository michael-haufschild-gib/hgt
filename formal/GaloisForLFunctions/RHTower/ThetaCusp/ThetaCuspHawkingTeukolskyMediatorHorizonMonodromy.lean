import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskyMediatorHorizonHolonomy
import GaloisForLFunctions.HTGeometry.ScaledGammaBorelResidue

/-!
# Hawking monodromy obstruction for the Teukolsky mediator pair

In Birmingham--Mokhtari dimensionless time the massless topological horizon has unit surface
gravity.  One positive circuit of incoming affine frequency multiplies the exponential-peeling
carrier by `exp (2*pi*omega)`.  The relative multiplier of the two virtual mediator clocks is
`exp (2*pi*I*(Re rho-1/2))`.  Critical-strip confinement removes every nonzero integer alias.
Thus a tilted relative branch cannot be closed by a single-valued meromorphic calibration; any
closing completion must carry a nontrivial compensating sheet character.
-/

open Complex Real Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Relative incoming-frequency monodromy of the two mediator Hawking carriers. -/
def d4BMXiMediatorHorizonMonodromy (n : ℕ) (q : XiZeroCopy) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) *
    (d4BMXiReflectedRealPairFrequency n q -
      d4BMFunctionalReflectionMediatorFrequency n n))

/-- The relative monodromy is the unit-circle character of Xi tilt. -/
theorem d4BMXiMediatorHorizonMonodromy_eq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiMediatorHorizonMonodromy n q =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ))) := by
  rw [d4BMXiMediatorHorizonMonodromy,
    d4BMXiReflectedRealPairFrequency_sub_functionalMediator]
  congr 1
  ring

/-- Relative horizon monodromy is trivial exactly on the critical line. -/
theorem d4BMXiMediatorHorizonMonodromy_eq_one_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiMediatorHorizonMonodromy n q = 1 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiMediatorHorizonMonodromy_eq]
  have hlattice :=
    exp_two_pi_I_real_ratio_eq_one_iff_lattice (scale := 1) (by norm_num)
      ((q.1 : ℂ).re - 1 / 2)
  have hlattice' :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ))) = 1 ↔
        ∃ k : ℤ, (q.1 : ℂ).re - 1 / 2 = (k : ℝ) := by
    simpa using hlattice
  rw [hlattice']
  constructor
  · rintro ⟨k, hk⟩
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    have hk0 : (0 : ℤ) ≤ k := by
      by_contra hneg
      have hle : k ≤ -1 := by omega
      have hleR : (k : ℝ) ≤ -1 := by exact_mod_cast hle
      linarith
    have hk1 : k ≤ 0 := by
      by_contra hpos
      have hge : 1 ≤ k := by omega
      have hgeR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hge
      linarith
    have hkzero : k = 0 := by omega
    norm_num [hkzero] at hk
    linarith
  · intro h
    refine ⟨0, ?_⟩
    norm_num [h]

theorem d4BMXiMediatorHorizonMonodromy_ne_one_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiMediatorHorizonMonodromy n q ≠ 1 ↔
      (q.1 : ℂ).re ≠ 1 / 2 :=
  not_congr (d4BMXiMediatorHorizonMonodromy_eq_one_iff n q)

/-- A nonzero tilted relative amplitude cannot itself be single-valued. -/
theorem d4BMXiMediatorHorizon_no_nonzero_singleValuedRelativeAmplitude
    (n : ℕ) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ ∃ amplitude : ℂ,
      amplitude ≠ 0 ∧
        d4BMXiMediatorHorizonMonodromy n q * amplitude = amplitude := by
  rintro ⟨amplitude, hnonzero, hfixed⟩
  have hmonodromy : d4BMXiMediatorHorizonMonodromy n q = 1 := by
    apply mul_right_cancel₀ hnonzero
    simpa using hfixed
  exact htilt
    ((d4BMXiMediatorHorizonMonodromy_eq_one_iff n q).1 hmonodromy)

/-- A tilted branch-closing calibration must have nontrivial monodromy. -/
theorem d4BMXiMediatorHorizon_closingCalibration_ne_one_of_tilt
    (n : ℕ) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2)
    {calibrationMonodromy : ℂ}
    (hclose : calibrationMonodromy *
        d4BMXiMediatorHorizonMonodromy n q = 1) :
    calibrationMonodromy ≠ 1 := by
  intro htrivial
  apply htilt
  apply (d4BMXiMediatorHorizonMonodromy_eq_one_iff n q).1
  simpa [htrivial] using hclose

/-- The compensating monodromy character is unique. -/
theorem d4BMXiMediatorHorizon_closingCalibration_unique
    (n : ℕ) (q : XiZeroCopy)
    {calibrationMonodromy₁ calibrationMonodromy₂ : ℂ}
    (hclose₁ : calibrationMonodromy₁ *
        d4BMXiMediatorHorizonMonodromy n q = 1)
    (hclose₂ : calibrationMonodromy₂ *
        d4BMXiMediatorHorizonMonodromy n q = 1) :
    calibrationMonodromy₁ = calibrationMonodromy₂ := by
  have hnonzero : d4BMXiMediatorHorizonMonodromy n q ≠ 0 := by
    unfold d4BMXiMediatorHorizonMonodromy
    exact Complex.exp_ne_zero _
  apply mul_right_cancel₀ hnonzero
  rw [hclose₁, hclose₂]

/-- Trivial relative horizon monodromy in every Xi sector. -/
def D4BMXiMediatorHorizonMonodromyTrivial (n : ℕ) : Prop :=
  ∀ q : XiZeroCopy, d4BMXiMediatorHorizonMonodromy n q = 1

/-- Global single-sheet closure of one mediator overtone is exactly RH. -/
theorem riemannHypothesis_iff_d4BMXiMediatorHorizonMonodromyTrivial
    (n : ℕ) :
    RiemannHypothesis ↔ D4BMXiMediatorHorizonMonodromyTrivial n := by
  constructor
  · intro hRH q
    exact (d4BMXiMediatorHorizonMonodromy_eq_one_iff n q).2
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)
  · intro htrivial
    exact (riemannHypothesis_iff_d4BMXiTwoChannelBackreactionIsConfluent).2
      (fun q => (d4BMXiTwoChannelHelicityTransfer_eq_zero_iff q).2
        ((d4BMXiMediatorHorizonMonodromy_eq_one_iff n q).1 (htrivial q)))

end

end RHTower

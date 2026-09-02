import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEArbitraryCausalSpectrumNoCancellation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEQNMRieszShaleRigidity

/-!
# Full BM Jost-divisor spectral no-go

The exact reciprocal-Gamma Birmingham--Mokhtari radial Jost determinant has no hidden zero
component: its full frequency divisor is exactly the union of the positive and negative QNM
branches.  On an actual Xi fibre both branches lie strictly in the lower half-plane.

This classification discharges the damping premise in the arbitrary causal-spectrum theorem.
Consequently no complex finite-variation causal spectral measure supported almost everywhere on
the full radial Jost divisor can persistently supply the nonzero counterterm `-AIME` required by
the fixed-channel third-order HB same-pole cancellation.

The killed proof chain is

`meromorphic radial-pole support -> full BM Jost divisor -> persistent -AIME -> HB extinction`.

Any survivor must use non-polar peripheral/threshold singular support, growing modes, or leave
finite variation.  The exact QNM formula is classical; the new result is the converse full-divisor
classification welded to the arbitrary-measure AIME obstruction.

`[PROVED HERE] [HB] [FULL JOST DIVISOR] [ARBITRARY SPECTRUM] [ROUTE KILL] [LEAN-PROVED]`
-/

open Complex Real Set Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-- Reciprocal Gamma vanishes exactly over the nonpositive integers. -/
theorem oneDivGamma_eq_zero_iff (z : ℂ) :
    (Complex.Gamma z)⁻¹ = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  constructor
  · intro hz
    by_contra hzeros
    have hall : ∀ n : ℕ, z ≠ -(n : ℂ) := by
      intro n hn
      exact hzeros ⟨n, hn⟩
    exact (inv_ne_zero (Complex.Gamma_ne_zero hall)) hz
  · rintro ⟨n, rfl⟩
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]

/-- The first radial hypergeometric parameter hits a Gamma pole exactly on the positive QNM
branch. -/
theorem d4BMCausalRadialA_eq_negNat_iff (omega chi : ℂ) (n : ℕ) :
    d4BMCausalRadialA omega chi = -(n : ℂ) ↔
      omega = d4BMCausalQNMPlus n chi := by
  constructor
  · intro h
    rw [d4BMCausalRadialA] at h
    rw [d4BMCausalQNMPlus, d4BMCausalDecay]
    have h' := congrArg (fun z : ℂ => 2 * Complex.I * z) h
    ring_nf at h'
    rw [Complex.I_sq] at h'
    ring_nf at h' ⊢
    linear_combination h'
  · rintro rfl
    simp [d4BMCausalRadialA, d4BMCausalQNMPlus, d4BMCausalDecay]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The second radial hypergeometric parameter hits a Gamma pole exactly on the negative QNM
branch. -/
theorem d4BMCausalRadialB_eq_negNat_iff (omega chi : ℂ) (n : ℕ) :
    d4BMCausalRadialB omega chi = -(n : ℂ) ↔
      omega = d4BMCausalQNMMinus n chi := by
  constructor
  · intro h
    rw [d4BMCausalRadialB] at h
    rw [d4BMCausalQNMMinus, d4BMCausalDecay]
    have h' := congrArg (fun z : ℂ => 2 * Complex.I * z) h
    ring_nf at h'
    rw [Complex.I_sq] at h'
    ring_nf at h' ⊢
    linear_combination h'
  · rintro rfl
    simp [d4BMCausalRadialB, d4BMCausalQNMMinus, d4BMCausalDecay]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Exact zero classification for the positive reciprocal-Gamma Jost factor. -/
theorem d4BMCausalJostPlus_eq_zero_iff (omega chi : ℂ) :
    d4BMCausalJostPlus omega chi = 0 ↔
      ∃ n : ℕ, omega = d4BMCausalQNMPlus n chi := by
  rw [d4BMCausalJostPlus, oneDivGamma_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (d4BMCausalRadialA_eq_negNat_iff omega chi n).mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (d4BMCausalRadialA_eq_negNat_iff omega chi n).mpr hn⟩

/-- Exact zero classification for the negative reciprocal-Gamma Jost factor. -/
theorem d4BMCausalJostMinus_eq_zero_iff (omega chi : ℂ) :
    d4BMCausalJostMinus omega chi = 0 ↔
      ∃ n : ℕ, omega = d4BMCausalQNMMinus n chi := by
  rw [d4BMCausalJostMinus, oneDivGamma_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (d4BMCausalRadialB_eq_negNat_iff omega chi n).mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (d4BMCausalRadialB_eq_negNat_iff omega chi n).mpr hn⟩

/-- **Full-divisor classification.** There are no additional zeros of the exact BM Jost
determinant beyond its two QNM towers. -/
theorem d4BMCausalJost_eq_zero_iff (omega chi : ℂ) :
    d4BMCausalJost omega chi = 0 ↔
      (∃ n : ℕ, omega = d4BMCausalQNMPlus n chi) ∨
        ∃ n : ℕ, omega = d4BMCausalQNMMinus n chi := by
  rw [d4BMCausalJost, mul_eq_zero, d4BMCausalJostPlus_eq_zero_iff,
    d4BMCausalJostMinus_eq_zero_iff]

/-- Positive-branch zeros of the causal Jost determinant are strictly damped on Xi fibres. -/
theorem d4BMXiCausalQNMPlus_im_lt_zero (n : ℕ) (q : XiZeroCopy) :
    (d4BMCausalQNMPlus n (d4BMXiMixedHorizonAngularMomentum q)).im < 0 := by
  simpa [d4BMXiMixedHorizonAngularMomentum, d4BMCausalQNMPlus,
    d4BMCausalDecay, thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay] using
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus_xi_im_lt_zero n q)

/-- Negative-branch zeros of the causal Jost determinant are strictly damped on Xi fibres. -/
theorem d4BMXiCausalQNMMinus_im_lt_zero (n : ℕ) (q : XiZeroCopy) :
    (d4BMCausalQNMMinus n (d4BMXiMixedHorizonAngularMomentum q)).im < 0 := by
  simpa [d4BMXiMixedHorizonAngularMomentum, d4BMCausalQNMMinus,
    d4BMCausalDecay, thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay] using
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus_xi_im_lt_zero n q)

/-- Every zero on the full Xi-fibre BM Jost divisor lies strictly below the real frequency axis. -/
theorem d4BMXiCausalJost_zero_im_lt_zero (omega : ℂ) (q : XiZeroCopy)
    (hjost : d4BMCausalJost omega (d4BMXiMixedHorizonAngularMomentum q) = 0) :
    omega.im < 0 := by
  rcases (d4BMCausalJost_eq_zero_iff omega
    (d4BMXiMixedHorizonAngularMomentum q)).mp hjost with hplus | hminus
  · obtain ⟨n, rfl⟩ := hplus
    exact d4BMXiCausalQNMPlus_im_lt_zero n q
  · obtain ⟨n, rfl⟩ := hminus
    exact d4BMXiCausalQNMMinus_im_lt_zero n q

/-- Almost-everywhere support on the physical Jost divisor automatically supplies strict causal
damping; it is not an additional spectral hypothesis. -/
theorem d4BMXiJostSupported_ae_strictlyDamped
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (frequency : Omega → ℂ) (q : XiZeroCopy)
    (hjost : ∀ᵐ x ∂mu,
      d4BMCausalJost (frequency x) (d4BMXiMixedHorizonAngularMomentum q) = 0) :
    ∀ᵐ x ∂mu, (frequency x).im < 0 := by
  filter_upwards [hjost] with x hx
  exact d4BMXiCausalJost_zero_im_lt_zero (frequency x) q hx

/-- No arbitrary complex finite-variation spectrum carried by the full radial Jost divisor can
persistently equal the exact counterterm required to erase fundamental AIME. -/
theorem not_eventually_d4BMXiJostSupportedCausalSpectrum_eq_negAIME
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega → ℂ) (q : XiZeroCopy)
    (hdensity : Integrable density mu) (hfrequency : Measurable frequency)
    (hjost : ∀ᵐ x ∂mu,
      d4BMCausalJost (frequency x) (d4BMXiMixedHorizonAngularMomentum q) = 0) :
    ¬ ∀ᶠ delay in atTop,
      d4BMCausalSpectralSourceRemainder mu density frequency delay =
        -d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) := by
  intro hpersistent
  have hcounterterm :
      -d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) ≠ 0 :=
    neg_ne_zero.mpr
      ((d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff 1 q).mpr one_ne_zero)
  have hnot := d4BMCausalSpectralPersistentCounterterm_forces_not_ae_strictlyDamped
    mu density frequency hdensity hfrequency hcounterterm hpersistent
  exact hnot (d4BMXiJostSupported_ae_strictlyDamped mu frequency q hjost)

/-- Closed route class: arbitrary complex finite-variation causal spectra supported on exact BM
radial poles cannot realize the persistent same-pole counterterm demanded by HB. -/
def D4HBFullJostDivisorFiniteVariationAIMECountertermRouteKilled : Prop :=
  ∀ (Omega : Type) [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega → ℂ) (q : XiZeroCopy),
    Integrable density mu →
    Measurable frequency →
    (∀ᵐ x ∂mu,
      d4BMCausalJost (frequency x) (d4BMXiMixedHorizonAngularMomentum q) = 0) →
    ¬ ∀ᶠ delay in atTop,
      d4BMCausalSpectralSourceRemainder mu density frequency delay =
        -d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q)

/-- Premise-free certificate killing every finite-variation meromorphic radial-pole completion of
the HB same-pole AIME remainder. -/
theorem d4HBFullJostDivisorFiniteVariationAIMECountertermRouteKilled :
    D4HBFullJostDivisorFiniteVariationAIMECountertermRouteKilled := by
  intro Omega _ mu density frequency q hdensity hfrequency hjost
  exact not_eventually_d4BMXiJostSupportedCausalSpectrum_eq_negAIME
    mu density frequency q hdensity hfrequency hjost

end

end RHTower

import GaloisForLFunctions.RHTower.CCMFirstClockPrimeEntrySlopeTomography
import GaloisForLFunctions.RHTower.CCMFirstClockHalfWaveReflection
import GaloisForLFunctions.RHTower.CCMCriticalMellinGrowingCumulative

/-!
# Complete first-clock crease current

Subtracting the explicit continuous CCM background from the literal published first sine clock
leaves exactly the hard-entered finite prime packet.  Near `L = log k` this complete arithmetic
trace is one fixed finite packet: every atom other than `k` is smooth, while `k` contributes its
source-marked one-sided slope defect.  The normalized right-minus-left derivative therefore
recovers `vonMangoldt k` for every integer `k >= 2`.

This is an unconditional finite-aperture source-tomography theorem.  It neither assumes nor proves
the Riemann hypothesis.
-/

open scoped BigOperators
open Filter Set Topology

namespace RHTower

noncomputable section

/-- Prime part of the moving first physical CCM clock. -/
def ccmFirstClockPhysicalPrimeTrace (L : ℝ) : ℝ :=
  ccmFirstClockPrimeSineMass L (2 * Real.pi / L)

/-- Literal first CCM clock after subtraction of its explicit continuous background. -/
def ccmFirstClockArithmeticTrace (L : ℝ) : ℝ :=
  Real.pi * ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) -
    ∫ h : ℝ in (0 : ℝ)..L,
      Real.sin ((2 * Real.pi / L) * h) * ccmFirstClockContinuousSourceDensity h

/-- At any larger common horizon, the physical prime trace is exactly the corresponding entered
finite packet. -/
theorem ccmFirstClockPhysicalPrimeTrace_eq_commonEnteredPacket
    {L H : ℝ} (hLH : L ≤ H) :
    ccmFirstClockPhysicalPrimeTrace L =
      ccmFirstClockEnteredPrimePacket (Finset.Icc 2 ⌊Real.exp H⌋₊) L := by
  rw [ccmFirstClockPhysicalPrimeTrace, ccmFirstClockPrimeSineMass,
    ccmFirstClockEnteredPrimePacket]
  let K : Finset ℕ := Finset.Icc 2 ⌊Real.exp H⌋₊
  let p : ℕ → Prop := fun k => Real.log k ≤ L
  have hfin : (Finset.Icc 2 ⌊Real.exp L⌋₊ : Finset ℕ) = K.filter p := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_filter, K, p]
    constructor
    · intro hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkexp : (k : ℝ) ≤ Real.exp L :=
        (Nat.le_floor_iff (Real.exp_pos L).le).mp hk.2
      have hlog : Real.log k ≤ L :=
        (Real.log_le_iff_le_exp hkpos).mpr hkexp
      have hfloor : ⌊Real.exp L⌋₊ ≤ ⌊Real.exp H⌋₊ :=
        Nat.floor_mono (Real.exp_le_exp.mpr hLH)
      exact ⟨⟨hk.1, hk.2.trans hfloor⟩, hlog⟩
    · intro hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkexp : (k : ℝ) ≤ Real.exp L :=
        (Real.log_le_iff_le_exp hkpos).mp hk.2
      exact ⟨hk.1.1, (Nat.le_floor_iff (Real.exp_pos L).le).mpr hkexp⟩
  rw [hfin, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hentry : Real.log k ≤ L
  · simp [ccmFirstClockEnteredPrimeAtom, ccmFirstClockActivePrimeAtom, hentry]
  · simp [ccmFirstClockEnteredPrimeAtom, hentry]

/-- Exact background subtraction: the arithmetic trace equals the physical prime trace at every
positive aperture. -/
theorem ccmFirstClockArithmeticTrace_eq_physicalPrimeTrace
    {L : ℝ} (hL : 0 < L) :
    ccmFirstClockArithmeticTrace L = ccmFirstClockPhysicalPrimeTrace L := by
  have hsource :=
    pi_mul_ccmPublishedSourceSineCoefficient_eq_continuous_add_prime
      (L := L) (ξ := 2 * Real.pi / L) hL
  rw [ccmFirstClockArithmeticTrace, ccmFirstClockPhysicalPrimeTrace]
  linarith

/-- Around the entry of `k`, the complete arithmetic trace is one fixed finite packet. -/
theorem ccmFirstClockArithmeticTrace_eventuallyEq_entryPacket
    {k : ℕ} (hk : 1 < k) :
    ccmFirstClockArithmeticTrace =ᶠ[𝓝 (Real.log k)]
      ccmFirstClockEnteredPrimePacket (Finset.Icc 2 (k + 1)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_trans Nat.zero_lt_one hk)
  have hlogpos : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk)
  have hsuccpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlogsucc : Real.log k < Real.log (k + 1) :=
    Real.strictMonoOn_log hkpos hsuccpos (by norm_num)
  have hfloor : ⌊Real.exp (Real.log (k + 1))⌋₊ = k + 1 := by
    rw [Real.exp_log hsuccpos,
      show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num,
      Nat.floor_natCast]
  filter_upwards [Ioi_mem_nhds hlogpos, Iio_mem_nhds hlogsucc] with L hLpos hLH
  rw [ccmFirstClockArithmeticTrace_eq_physicalPrimeTrace hLpos]
  rw [ccmFirstClockPhysicalPrimeTrace_eq_commonEnteredPacket hLH.le, hfloor]

/-- **Complete first-clock crease law.**  At every integer entry aperture, the whole literal
source trace has a smooth common drift plus the exact source-marked slope defect. -/
theorem ccmFirstClockArithmeticTrace_entry_oneSided
    {k : ℕ} (hk : 1 < k) :
    ∃ d : ℝ,
      HasDerivWithinAt ccmFirstClockArithmeticTrace
        (d + ccmFirstClockPrimeEntrySlope k)
        (Set.Ici (Real.log k)) (Real.log k) ∧
      HasDerivWithinAt ccmFirstClockArithmeticTrace d
        (Set.Iic (Real.log k)) (Real.log k) := by
  let s : Finset ℕ := Finset.Icc 2 (k + 1)
  have hks : k ∈ s := by
    simp [s]
    omega
  have hsupport : ∀ j ∈ s, 1 < j := by
    intro j hj
    simp only [s, Finset.mem_Icc] at hj
    omega
  obtain ⟨g, hg, hpacket, hentryRight, hentryLeft⟩ :=
    ccmFirstClockEnteredPrimePacket_entry_smoothDecomposition
      hks hk hsupport
  let d : ℝ := deriv g (Real.log k)
  have hgderiv : HasDerivAt g d (Real.log k) := hg.hasDerivAt
  have hpacketRight :
      HasDerivWithinAt (ccmFirstClockEnteredPrimePacket s)
        (d + ccmFirstClockPrimeEntrySlope k)
        (Set.Ici (Real.log k)) (Real.log k) := by
    rw [hpacket]
    exact hgderiv.hasDerivWithinAt.add hentryRight
  have hpacketLeft :
      HasDerivWithinAt (ccmFirstClockEnteredPrimePacket s) d
        (Set.Iic (Real.log k)) (Real.log k) := by
    rw [hpacket]
    change HasDerivWithinAt (g + ccmFirstClockEnteredPrimeAtom k) d
      (Set.Iic (Real.log k)) (Real.log k)
    simpa only [add_zero] using hgderiv.hasDerivWithinAt.add hentryLeft
  have htrace := ccmFirstClockArithmeticTrace_eventuallyEq_entryPacket hk
  have htrace' : ccmFirstClockArithmeticTrace =ᶠ[𝓝 (Real.log k)]
      ccmFirstClockEnteredPrimePacket s := by
    simpa only [s] using htrace
  refine ⟨d, ?_, ?_⟩
  · exact hpacketRight.congr_of_eventuallyEq
      (htrace'.filter_mono nhdsWithin_le_nhds) htrace'.self_of_nhds
  · exact hpacketLeft.congr_of_eventuallyEq
      (htrace'.filter_mono nhdsWithin_le_nhds) htrace'.self_of_nhds

/-- **Von Mangoldt crease tomography.**  The normalized right-minus-left derivative of the
complete source trace recovers the exact von Mangoldt atom. -/
theorem ccmFirstClockArithmeticTrace_entry_recovers_vonMangoldt
    {k : ℕ} (hk : 1 < k) :
    ∃ d : ℝ,
      HasDerivWithinAt ccmFirstClockArithmeticTrace
        (d + ccmFirstClockPrimeEntrySlope k)
        (Set.Ici (Real.log k)) (Real.log k) ∧
      HasDerivWithinAt ccmFirstClockArithmeticTrace d
        (Set.Iic (Real.log k)) (Real.log k) ∧
      (-(Real.log k) / (2 * Real.pi) *
          ((d + ccmFirstClockPrimeEntrySlope k) - d)) *
            Real.exp (Real.log k / 2) =
        ArithmeticFunction.vonMangoldt k := by
  obtain ⟨d, hright, hleft⟩ :=
    ccmFirstClockArithmeticTrace_entry_oneSided hk
  refine ⟨d, hright, hleft, ?_⟩
  rw [add_sub_cancel_left,
    ccmFirstClockPrimeEntrySlope_recovers_weight hk]
  exact criticalMellinAtomWeight_mul_exp_log_half (by omega)

end

end RHTower

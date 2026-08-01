import GaloisForLFunctions.RHTower.CCMFirstClockPrimePowerTowerCollapse

open scoped BigOperators

/-!
# CCM first-clock prime-entry slope tomography

The hard first-clock prime atom enters at the moving aperture `L = log k`. Its value is zero at
entry, but its right slope is a source-marked negative quantum. The left slope of the entered atom
is zero. Normalizing the slope recovers the exact critical-Mellin/von-Mangoldt atom weight.

For `k = p^e`, the slope is `-2π p^(-e/2) / e`; for a non-prime-power it vanishes. Thus the
one-sided derivative defects of the literal first-clock atoms retain complete prime-power source
data. This is an unconditional source-tomography theorem. It does not orient the sum of the atoms
and does not prove RH.
-/

namespace RHTower

noncomputable section

/-- Smooth first-clock contribution of `k` after it has entered the hard aperture. -/
def ccmFirstClockActivePrimeAtom (k : ℕ) (L : ℝ) : ℝ :=
  criticalMellinAtomWeight k *
    Real.sin ((2 * Real.pi / L) * Real.log k)

/-- Hard-aperture first-clock atom, absent before `L = log k`. -/
def ccmFirstClockEnteredPrimeAtom (k : ℕ) (L : ℝ) : ℝ :=
  if Real.log k ≤ L then ccmFirstClockActivePrimeAtom k L else 0

/-- Source-marked right slope inserted at the entry aperture of `k`. -/
def ccmFirstClockPrimeEntrySlope (k : ℕ) : ℝ :=
  -2 * Real.pi * criticalMellinAtomWeight k / Real.log k

/-- The active atom vanishes at its entry aperture. -/
theorem ccmFirstClockActivePrimeAtom_entry_value
    {k : ℕ} (hk : 1 < k) :
    ccmFirstClockActivePrimeAtom k (Real.log k) = 0 := by
  have hlog : Real.log k ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hk)).ne'
  rw [ccmFirstClockActivePrimeAtom]
  have harg : (2 * Real.pi / Real.log k) * Real.log k = 2 * Real.pi := by
    field_simp
  rw [harg, Real.sin_two_pi, mul_zero]

/-- Chain rule at the entry aperture: the active atom has exact source-marked slope. -/
theorem hasDerivAt_ccmFirstClockActivePrimeAtom_entry
    {k : ℕ} (hk : 1 < k) :
    HasDerivAt (ccmFirstClockActivePrimeAtom k)
      (ccmFirstClockPrimeEntrySlope k) (Real.log k) := by
  have hlog : Real.log k ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hk)).ne'
  have hinner : HasDerivAt
      (fun L : ℝ => (2 * Real.pi / L) * Real.log k)
      (-2 * Real.pi / Real.log k) (Real.log k) := by
    have hraw := (((hasDerivAt_const (x := Real.log k) (2 * Real.pi)).div
      (hasDerivAt_id (x := Real.log k)) hlog).mul_const (Real.log k))
    simp only [id_eq] at hraw
    convert hraw using 1 <;> try rfl
    field_simp [hlog]
    ring
  have hsin := hinner.sin
  have hsin' : HasDerivAt
      (fun L : ℝ => Real.sin ((2 * Real.pi / L) * Real.log k))
      (-2 * Real.pi / Real.log k) (Real.log k) := by
    have harg : (2 * Real.pi / Real.log k) * Real.log k = 2 * Real.pi := by
      field_simp
    simpa only [harg, Real.cos_two_pi, one_mul] using hsin
  rw [ccmFirstClockPrimeEntrySlope]
  convert hsin'.const_mul (criticalMellinAtomWeight k) using 1 <;> try rfl
  field_simp [hlog]

/-- The hard-entered atom has zero left slope and the exact active right slope. -/
theorem ccmFirstClockEnteredPrimeAtom_entry_oneSided
    {k : ℕ} (hk : 1 < k) :
    HasDerivWithinAt (ccmFirstClockEnteredPrimeAtom k)
        (ccmFirstClockPrimeEntrySlope k) (Set.Ici (Real.log k)) (Real.log k) ∧
      HasDerivWithinAt (ccmFirstClockEnteredPrimeAtom k)
        0 (Set.Iic (Real.log k)) (Real.log k) := by
  have hactive := hasDerivAt_ccmFirstClockActivePrimeAtom_entry hk
  have hvalue := ccmFirstClockActivePrimeAtom_entry_value hk
  constructor
  · apply hactive.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with L hL
      simp only [Set.mem_Ici] at hL
      simp [ccmFirstClockEnteredPrimeAtom, hL]
    · simp [ccmFirstClockEnteredPrimeAtom, hvalue]
  · apply (hasDerivAt_const (x := Real.log k) (c := (0 : ℝ))).hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with L hL
      simp only [Set.mem_Iic] at hL
      by_cases hentry : Real.log k ≤ L
      · have hEq : L = Real.log k := le_antisymm hL hentry
        subst L
        simp [ccmFirstClockEnteredPrimeAtom, hvalue]
      · simp [ccmFirstClockEnteredPrimeAtom, hentry]
    · simp [ccmFirstClockEnteredPrimeAtom, hvalue]

/-- The normalized entry slope recovers the exact critical-Mellin atom weight. -/
theorem ccmFirstClockPrimeEntrySlope_recovers_weight
    {k : ℕ} (hk : 1 < k) :
    -(Real.log k) / (2 * Real.pi) * ccmFirstClockPrimeEntrySlope k =
      criticalMellinAtomWeight k := by
  have hlog : Real.log k ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hk)).ne'
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [ccmFirstClockPrimeEntrySlope]
  field_simp [hlog, hpi]

/-- On a prime-power atom, the entry slope loses the logarithmic mark only through the exponent. -/
theorem ccmFirstClockPrimeEntrySlope_primePower
    {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ccmFirstClockPrimeEntrySlope (p ^ e) =
      -2 * Real.pi * criticalPrimeTowerRadius p ^ e / (e : ℝ) := by
  rw [ccmFirstClockPrimeEntrySlope,
    criticalMellinAtomWeight_prime_pow hp he.ne', Nat.cast_pow,
    Real.log_pow]
  have hlog : Real.log p ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  field_simp [hlog, heR]

/-- Every genuine prime-power entry inserts a strictly negative first-clock slope. -/
theorem ccmFirstClockPrimeEntrySlope_primePower_neg
    {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ccmFirstClockPrimeEntrySlope (p ^ e) < 0 := by
  rw [ccmFirstClockPrimeEntrySlope_primePower hp he]
  have hpow : 0 < criticalPrimeTowerRadius p ^ e :=
    pow_pos (criticalPrimeTowerRadius_pos hp.pos) e
  have hnum : -2 * Real.pi * criticalPrimeTowerRadius p ^ e < 0 :=
    mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos) hpow
  exact div_neg_of_neg_of_pos hnum (by exact_mod_cast he)

/-- Integers outside the prime-power support insert no first-clock slope. -/
theorem ccmFirstClockPrimeEntrySlope_eq_zero_of_not_primePow
    {k : ℕ} (hk : ¬IsPrimePow k) :
    ccmFirstClockPrimeEntrySlope k = 0 := by
  rw [ccmFirstClockPrimeEntrySlope, criticalMellinAtomWeight,
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hk]
  ring

/-- Prime-power specialization of the exact one-sided entry law. -/
theorem ccmFirstClockEnteredPrimePowerAtom_entry_oneSided
    {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    HasDerivWithinAt (ccmFirstClockEnteredPrimeAtom (p ^ e))
        (-2 * Real.pi * criticalPrimeTowerRadius p ^ e / (e : ℝ))
        (Set.Ici (Real.log ((p ^ e : ℕ) : ℝ)))
        (Real.log ((p ^ e : ℕ) : ℝ)) ∧
      HasDerivWithinAt (ccmFirstClockEnteredPrimeAtom (p ^ e))
        0 (Set.Iic (Real.log ((p ^ e : ℕ) : ℝ)))
        (Real.log ((p ^ e : ℕ) : ℝ)) := by
  have hk : 1 < p ^ e := one_lt_pow₀ hp.one_lt he.ne'
  simpa only [ccmFirstClockPrimeEntrySlope_primePower hp he] using
    (ccmFirstClockEnteredPrimeAtom_entry_oneSided hk)

/-- Away from `L = 0`, every active prime atom is smooth. -/
theorem differentiableAt_ccmFirstClockActivePrimeAtom
    (k : ℕ) {L : ℝ} (hL : L ≠ 0) :
    DifferentiableAt ℝ (ccmFirstClockActivePrimeAtom k) L := by
  unfold ccmFirstClockActivePrimeAtom
  fun_prop

/-- A hard-entered atom is smooth away from its unique entry aperture. -/
theorem differentiableAt_ccmFirstClockEnteredPrimeAtom_of_log_ne
    (j : ℕ) {L : ℝ} (hL : L ≠ 0) (hne : Real.log j ≠ L) :
    DifferentiableAt ℝ (ccmFirstClockEnteredPrimeAtom j) L := by
  rcases lt_or_gt_of_ne hne with hbefore | hafter
  · apply (differentiableAt_ccmFirstClockActivePrimeAtom j hL).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hbefore] with x hx
    change Real.log (j : ℝ) < x at hx
    simp [ccmFirstClockEnteredPrimeAtom, hx.le]
  · apply (differentiableAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hafter] with x hx
    change x < Real.log (j : ℝ) at hx
    simp [ccmFirstClockEnteredPrimeAtom, not_le.mpr hx]

/-- Finite packet of hard-entered first-clock atoms. -/
def ccmFirstClockEnteredPrimePacket (s : Finset ℕ) (L : ℝ) : ℝ :=
  ∑ j ∈ s, ccmFirstClockEnteredPrimeAtom j L

/-- Packet with one distinguished entry removed. -/
def ccmFirstClockEnteredPrimeBackground (s : Finset ℕ) (k : ℕ) (L : ℝ) : ℝ :=
  ∑ j ∈ s.erase k, ccmFirstClockEnteredPrimeAtom j L

/-- Exact decomposition of a packet into distinguished atom and remaining background. -/
theorem ccmFirstClockEnteredPrimePacket_eq_background_add
    {s : Finset ℕ} {k : ℕ} (hk : k ∈ s) :
    ccmFirstClockEnteredPrimePacket s =
      fun L => ccmFirstClockEnteredPrimeBackground s k L +
        ccmFirstClockEnteredPrimeAtom k L := by
  funext L
  rw [ccmFirstClockEnteredPrimePacket, ccmFirstClockEnteredPrimeBackground]
  exact (Finset.sum_erase_add _ _ hk).symm

/-- All packet atoms except `k` form a smooth background at the entry aperture of `k`. -/
theorem differentiableAt_ccmFirstClockEnteredPrimeBackground_entry
    {s : Finset ℕ} {k : ℕ} (hk : 1 < k)
    (hsupport : ∀ j ∈ s, 1 < j) :
    DifferentiableAt ℝ (ccmFirstClockEnteredPrimeBackground s k) (Real.log k) := by
  unfold ccmFirstClockEnteredPrimeBackground
  apply DifferentiableAt.fun_sum
  intro j hj
  have hjs : j ∈ s := Finset.mem_of_mem_erase hj
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  have hlogne : Real.log j ≠ Real.log k := by
    intro hlog
    have hjpos : (0 : ℝ) < j := by
      exact_mod_cast (lt_trans Nat.zero_lt_one (hsupport j hjs))
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast (lt_trans Nat.zero_lt_one hk)
    have hcast : (j : ℝ) = (k : ℝ) :=
      Real.strictMonoOn_log.injOn hjpos hkpos hlog
    exact hjk (by exact_mod_cast hcast)
  exact differentiableAt_ccmFirstClockEnteredPrimeAtom_of_log_ne j
    (Real.log_pos (by exact_mod_cast hk)).ne' hlogne

/-- **Finite-packet entry tomography.** At a distinguished entry, every older or future atom is a
smooth common background, while the unique non-smooth summand has exact source-marked one-sided
slopes. -/
theorem ccmFirstClockEnteredPrimePacket_entry_smoothDecomposition
    {s : Finset ℕ} {k : ℕ} (hks : k ∈ s) (hk : 1 < k)
    (hsupport : ∀ j ∈ s, 1 < j) :
    ∃ g : ℝ → ℝ,
      DifferentiableAt ℝ g (Real.log k) ∧
      ccmFirstClockEnteredPrimePacket s =
        (fun L => g L + ccmFirstClockEnteredPrimeAtom k L) ∧
      HasDerivWithinAt (ccmFirstClockEnteredPrimeAtom k)
        (ccmFirstClockPrimeEntrySlope k)
        (Set.Ici (Real.log k)) (Real.log k) ∧
      HasDerivWithinAt (ccmFirstClockEnteredPrimeAtom k)
        0 (Set.Iic (Real.log k)) (Real.log k) := by
  refine ⟨ccmFirstClockEnteredPrimeBackground s k,
    differentiableAt_ccmFirstClockEnteredPrimeBackground_entry hk hsupport,
    ccmFirstClockEnteredPrimePacket_eq_background_add hks, ?_⟩
  exact ccmFirstClockEnteredPrimeAtom_entry_oneSided hk

end

end RHTower

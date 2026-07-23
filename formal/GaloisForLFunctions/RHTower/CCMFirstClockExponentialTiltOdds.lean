import GaloisForLFunctions.RHTower.CCMFirstClockHalfWaveReflection

/-!
# CCM first-clock exponential-tilt odds

A positive exponential tilt of any finite source separated by one cut increases the
division-free odds of mass above the cut against mass below it.  Applied to the literal first
CCM sine clock, this proves that de-Abelization from safe Euler weights
`Λ(n) n⁻ˢ`, `s ≥ 1/2`, to critical weights `Λ(n) / √n` moves prime mass toward the
counter-phased outer half-wave.

Thus positive diagonal half-weight transport is directionally hostile to the RH-complete
first-clock inequality.  Every theorem is unconditional.  This source-specific no-go does not
exclude a Gamma-sewn non-diagonal transport and does not assert RH.
-/

open Set

namespace RHTower

noncomputable section

/-- A finite positive source tested by `q` after exponential tilt in coordinate `x`. -/
def finiteExponentialTiltMass {ι : Type*}
    (s : Finset ι) (a q x : ι → ℝ) (θ : ℝ) : ℝ :=
  ∑ i ∈ s, a i * q i * Real.exp (θ * x i)

/-- **Separated exponential-tilt odds law.**  If `aligned` is supported below one cut and
`counter` above it, increasing exponential tilt can only increase counter/aligned odds.  The
division-free cross-product statement remains valid when either chamber is empty. -/
theorem finiteExponentialTilt_separatedOdds_mono
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a aligned counter x : ι → ℝ) (c θ₁ θ₂ : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (haligned : ∀ i ∈ s, 0 ≤ aligned i)
    (hcounter : ∀ i ∈ s, 0 ≤ counter i)
    (halignedSupport : ∀ i ∈ s, 0 < aligned i → x i ≤ c)
    (hcounterSupport : ∀ i ∈ s, 0 < counter i → c ≤ x i)
    (hθ : θ₁ ≤ θ₂) :
    finiteExponentialTiltMass s a counter x θ₂ *
        finiteExponentialTiltMass s a aligned x θ₁ ≥
      finiteExponentialTiltMass s a counter x θ₁ *
        finiteExponentialTiltMass s a aligned x θ₂ := by
  unfold finiteExponentialTiltMass
  simp_rw [Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hci : counter i = 0
  · simp [hci]
  by_cases haj : aligned j = 0
  · simp [haj]
  have hciPos : 0 < counter i :=
    lt_of_le_of_ne (hcounter i hi) (Ne.symm hci)
  have hajPos : 0 < aligned j :=
    lt_of_le_of_ne (haligned j hj) (Ne.symm haj)
  have hx : x j ≤ x i :=
    (halignedSupport j hj hajPos).trans (hcounterSupport i hi hciPos)
  have hexp :
      Real.exp (θ₁ * x i) * Real.exp (θ₂ * x j) ≤
        Real.exp (θ₂ * x i) * Real.exp (θ₁ * x j) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hbase : 0 ≤ a i * counter i * (a j * aligned j) :=
    mul_nonneg (mul_nonneg (ha i hi) (hcounter i hi))
      (mul_nonneg (ha j hj) (haligned j hj))
  calc
    a i * counter i * Real.exp (θ₁ * x i) *
          (a j * aligned j * Real.exp (θ₂ * x j)) =
        (a i * counter i * (a j * aligned j)) *
          (Real.exp (θ₁ * x i) * Real.exp (θ₂ * x j)) := by ring
    _ ≤ (a i * counter i * (a j * aligned j)) *
          (Real.exp (θ₂ * x i) * Real.exp (θ₁ * x j)) :=
      mul_le_mul_of_nonneg_left hexp hbase
    _ = a i * counter i * Real.exp (θ₂ * x i) *
          (a j * aligned j * Real.exp (θ₁ * x j)) := by ring

/-- Aligned first-clock prime mass after an exponential tilt of the critical source. -/
def ccmFirstClockPrimeAlignedTiltMass (L θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    criticalMellinAtomWeight k *
      max (Real.sin ((2 * Real.pi / L) * Real.log k)) 0 *
      Real.exp (θ * Real.log k)

/-- Counter-phased first-clock prime mass after an exponential tilt of the critical source. -/
def ccmFirstClockPrimeCounterTiltMass (L θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    criticalMellinAtomWeight k *
      max (-Real.sin ((2 * Real.pi / L) * Real.log k)) 0 *
      Real.exp (θ * Real.log k)

lemma log_mem_firstClockAperture
    {L : ℝ} {k : ℕ}
    (hk : k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊) :
    Real.log k ∈ Set.Icc 0 L := by
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkfloor : k ≤ ⌊Real.exp L⌋₊ := (Finset.mem_Icc.mp hk).2
  have hkexp : (k : ℝ) ≤ Real.exp L :=
    (Nat.le_floor_iff (Real.exp_pos L).le).mp hkfloor
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  exact ⟨Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega)),
    (Real.log_le_iff_le_exp hkpos).mpr hkexp⟩

lemma firstClock_aligned_support_le_half
    {L : ℝ} (hL : 0 < L) {h : ℝ} (hh : h ∈ Set.Icc 0 L)
    (haligned : 0 < max (Real.sin ((2 * Real.pi / L) * h)) 0) :
    h ≤ L / 2 := by
  by_contra hnot
  have hhhalf : L / 2 < h := lt_of_not_ge hnot
  have hξpos : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hphasePi : Real.pi < (2 * Real.pi / L) * h := by
    calc
      Real.pi = (2 * Real.pi / L) * (L / 2) := by field_simp
      _ < (2 * Real.pi / L) * h :=
        mul_lt_mul_of_pos_left hhhalf hξpos
  have hphaseTwoPi : (2 * Real.pi / L) * h ≤ 2 * Real.pi := by
    calc
      (2 * Real.pi / L) * h ≤ (2 * Real.pi / L) * L :=
        mul_le_mul_of_nonneg_left hh.2 hξpos.le
      _ = 2 * Real.pi := by field_simp
  have hcomp :
      0 ≤ Real.sin (2 * Real.pi - (2 * Real.pi / L) * h) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · linarith
  have hsin : Real.sin ((2 * Real.pi / L) * h) ≤ 0 := by
    rw [Real.sin_two_pi_sub] at hcomp
    linarith
  have : 0 < Real.sin ((2 * Real.pi / L) * h) := by
    simpa only [lt_max_iff, lt_self_iff_false, or_false] using haligned
  linarith

lemma firstClock_counter_support_half_le
    {L : ℝ} (hL : 0 < L) {h : ℝ} (hh : h ∈ Set.Icc 0 L)
    (hcounter : 0 < max (-Real.sin ((2 * Real.pi / L) * h)) 0) :
    L / 2 ≤ h := by
  by_contra hnot
  have hhhalf : h < L / 2 := lt_of_not_ge hnot
  have hξpos : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hphase0 : 0 ≤ (2 * Real.pi / L) * h :=
    mul_nonneg hξpos.le hh.1
  have hphasePi : (2 * Real.pi / L) * h ≤ Real.pi := by
    calc
      (2 * Real.pi / L) * h ≤ (2 * Real.pi / L) * (L / 2) :=
        mul_le_mul_of_nonneg_left hhhalf.le hξpos.le
      _ = Real.pi := by field_simp
  have hsin : 0 ≤ Real.sin ((2 * Real.pi / L) * h) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hphase0 hphasePi
  have : 0 < -Real.sin ((2 * Real.pi / L) * h) := by
    simpa only [lt_max_iff, lt_self_iff_false, or_false] using hcounter
  linarith

/-- On the actual first-clock support, increasing outward exponential tilt increases the
counter/aligned prime cross-product. -/
theorem ccmFirstClockPrimeTilt_counterAligned_cross_mono
    {L θ₁ θ₂ : ℝ} (hL : 0 < L) (hθ : θ₁ ≤ θ₂) :
    ccmFirstClockPrimeCounterTiltMass L θ₂ *
        ccmFirstClockPrimeAlignedTiltMass L θ₁ ≥
      ccmFirstClockPrimeCounterTiltMass L θ₁ *
        ccmFirstClockPrimeAlignedTiltMass L θ₂ := by
  unfold ccmFirstClockPrimeCounterTiltMass
    ccmFirstClockPrimeAlignedTiltMass
  have hmono := finiteExponentialTilt_separatedOdds_mono
      (s := Finset.Icc 2 ⌊Real.exp L⌋₊)
      (a := criticalMellinAtomWeight)
      (aligned := fun i =>
        max (Real.sin ((2 * Real.pi / L) * Real.log i)) 0)
      (counter := fun i =>
        max (-Real.sin ((2 * Real.pi / L) * Real.log i)) 0)
      (x := fun i => Real.log i)
      (c := L / 2) (θ₁ := θ₁) (θ₂ := θ₂)
      (ha := fun i _hi => criticalMellinAtomWeight_nonneg i)
      (haligned := fun _i _hi => le_max_right _ _)
      (hcounter := fun _i _hi => le_max_right _ _)
      (halignedSupport := by
        intro i hi hpos
        exact firstClock_aligned_support_le_half hL
          (log_mem_firstClockAperture hi) hpos)
      (hcounterSupport := by
        intro i hi hpos
        exact firstClock_counter_support_half_le hL
          (log_mem_firstClockAperture hi) hpos)
      hθ
  simpa only [finiteExponentialTiltMass] using hmono

theorem ccmFirstClockPrimeAlignedTiltMass_zero
    (L : ℝ) :
    ccmFirstClockPrimeAlignedTiltMass L 0 =
      ccmFirstClockPrimeAlignedMass L (2 * Real.pi / L) := by
  simp [ccmFirstClockPrimeAlignedTiltMass, ccmFirstClockPrimeAlignedMass]

theorem ccmFirstClockPrimeCounterTiltMass_zero
    (L : ℝ) :
    ccmFirstClockPrimeCounterTiltMass L 0 =
      ccmFirstClockPrimeCounterMass L (2 * Real.pi / L) := by
  simp [ccmFirstClockPrimeCounterTiltMass, ccmFirstClockPrimeCounterMass]

/-- Aligned prime mass in one hard first aperture at arbitrary Mellin exponent. -/
def ccmFirstClockPrimeAlignedExponentMass (L σ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    (k : ℝ) ^ (-σ) * ArithmeticFunction.vonMangoldt k *
      max (Real.sin ((2 * Real.pi / L) * Real.log k)) 0

/-- Counter-phased prime mass in one hard first aperture at arbitrary Mellin exponent. -/
def ccmFirstClockPrimeCounterExponentMass (L σ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    (k : ℝ) ^ (-σ) * ArithmeticFunction.vonMangoldt k *
      max (-Real.sin ((2 * Real.pi / L) * Real.log k)) 0

/-- The exponential tilt from critical weight to exponent `σ` is exactly the literal Euler
weight `Λ(k) k⁻ˢ`. -/
lemma criticalMellinAtomWeight_mul_halfWeightTilt
    {k : ℕ} (hk : 0 < k) (σ : ℝ) :
    criticalMellinAtomWeight k *
        Real.exp ((1 / 2 - σ) * Real.log k) =
      (k : ℝ) ^ (-σ) * ArithmeticFunction.vonMangoldt k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hexp :
      Real.exp ((1 / 2 - σ) * Real.log k) =
        (k : ℝ) ^ (1 / 2 - σ) := by
    rw [Real.rpow_def_of_pos hkR]
    congr 1
    ring
  rw [criticalMellinAtomWeight, hexp]
  calc
    (k : ℝ) ^ (-1 / 2 : ℝ) * ArithmeticFunction.vonMangoldt k *
        (k : ℝ) ^ (1 / 2 - σ) =
      ((k : ℝ) ^ (-1 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 - σ)) *
        ArithmeticFunction.vonMangoldt k := by ring
    _ = (k : ℝ) ^ ((-1 / 2 : ℝ) + (1 / 2 - σ)) *
        ArithmeticFunction.vonMangoldt k := by rw [Real.rpow_add hkR]
    _ = (k : ℝ) ^ (-σ) * ArithmeticFunction.vonMangoldt k := by
      congr 2
      ring

theorem ccmFirstClockPrimeAlignedTiltMass_halfWeight_eq_exponentMass
    {L σ : ℝ} :
    ccmFirstClockPrimeAlignedTiltMass L (1 / 2 - σ) =
      ccmFirstClockPrimeAlignedExponentMass L σ := by
  unfold ccmFirstClockPrimeAlignedTiltMass
    ccmFirstClockPrimeAlignedExponentMass
  apply Finset.sum_congr rfl
  intro k hk
  rw [show criticalMellinAtomWeight k *
        max (Real.sin (2 * Real.pi / L * Real.log ↑k)) 0 *
          Real.exp ((1 / 2 - σ) * Real.log ↑k) =
      (criticalMellinAtomWeight k *
        Real.exp ((1 / 2 - σ) * Real.log ↑k)) *
          max (Real.sin (2 * Real.pi / L * Real.log ↑k)) 0 by ring,
    criticalMellinAtomWeight_mul_halfWeightTilt (by
      have := (Finset.mem_Icc.mp hk).1
      omega)]

theorem ccmFirstClockPrimeCounterTiltMass_halfWeight_eq_exponentMass
    {L σ : ℝ} :
    ccmFirstClockPrimeCounterTiltMass L (1 / 2 - σ) =
      ccmFirstClockPrimeCounterExponentMass L σ := by
  unfold ccmFirstClockPrimeCounterTiltMass
    ccmFirstClockPrimeCounterExponentMass
  apply Finset.sum_congr rfl
  intro k hk
  rw [show criticalMellinAtomWeight k *
        max (-Real.sin (2 * Real.pi / L * Real.log ↑k)) 0 *
          Real.exp ((1 / 2 - σ) * Real.log ↑k) =
      (criticalMellinAtomWeight k *
        Real.exp ((1 / 2 - σ) * Real.log ↑k)) *
          max (-Real.sin (2 * Real.pi / L * Real.log ↑k)) 0 by ring,
    criticalMellinAtomWeight_mul_halfWeightTilt (by
      have := (Finset.mem_Icc.mp hk).1
      omega)]

/-- Critical-vs-safe cross-product law in tilt coordinates. -/
theorem ccmFirstClockPrime_critical_vs_safe_cross
    {L σ : ℝ} (hL : 0 < L) (hσ : 1 / 2 ≤ σ) :
    ccmFirstClockPrimeCounterMass L (2 * Real.pi / L) *
        ccmFirstClockPrimeAlignedTiltMass L (1 / 2 - σ) ≥
      ccmFirstClockPrimeCounterTiltMass L (1 / 2 - σ) *
        ccmFirstClockPrimeAlignedMass L (2 * Real.pi / L) := by
  simpa [ccmFirstClockPrimeAlignedTiltMass_zero,
    ccmFirstClockPrimeCounterTiltMass_zero] using
    ccmFirstClockPrimeTilt_counterAligned_cross_mono
      (L := L) (θ₁ := 1 / 2 - σ) (θ₂ := 0) hL (by linarith)

/-- **Literal CCM half-weight no-go.**  For every `σ ≥ 1/2`, de-Abelization from the
hard-window Euler weights `Λ(n)n⁻ˢ` to the critical weights `Λ(n)/√n` can only increase
counter-phased outer odds against aligned inner odds. -/
theorem ccmFirstClockPrime_critical_counterAlignedOdds_ge_safe
    {L σ : ℝ} (hL : 0 < L) (hσ : 1 / 2 ≤ σ) :
    ccmFirstClockPrimeCounterMass L (2 * Real.pi / L) *
        ccmFirstClockPrimeAlignedExponentMass L σ ≥
      ccmFirstClockPrimeCounterExponentMass L σ *
        ccmFirstClockPrimeAlignedMass L (2 * Real.pi / L) := by
  have h := ccmFirstClockPrime_critical_vs_safe_cross hL hσ
  rw [ccmFirstClockPrimeAlignedTiltMass_halfWeight_eq_exponentMass,
    ccmFirstClockPrimeCounterTiltMass_halfWeight_eq_exponentMass] at h
  exact h

end

end RHTower

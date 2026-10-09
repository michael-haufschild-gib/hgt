import GaloisForLFunctions.RHTower.MobiusRieszNormalizedMass
import GaloisForLFunctions.RHTower.MobiusRieszPrimePacketThreshold

/-!
# Unit-mass escape of literal finite-prime Möbius packets

At the exact positivity threshold, divide the literal prime profile by the
product of its logarithmic shifts. These are nonnegative integrable functions
of total mass one. As prime cardinality grows, they converge uniformly to zero
below each fixed logarithmic cutoff, while mass above that cutoff tends to one.
Thus their fixed-scale pointwise limit cannot retain unit integral. Moving
centres and rescaled limits, and the signed cancellation required for RH, remain
outside this obstruction.
-/

noncomputable section

namespace RHTower.MobiusRieszSmoothing

open MeasureTheory Set Filter Topology

/-- Uniform lower bound for the logarithmic shifts of all primes. -/
def primeShiftFloor : ℝ := Real.log (Real.sqrt (2:ℝ))

theorem primeShiftFloor_pos : 0 < primeShiftFloor := by
  apply Real.log_pos
  have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 2)
  simpa using h

theorem primeShiftFloor_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ∀ a ∈ primeShifts P.toList, primeShiftFloor ≤ a := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  apply Real.log_le_log (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))
  apply Real.sqrt_le_sqrt
  exact_mod_cast (hP p (by simpa using hp)).two_le

private theorem primeShifts_ne_nil {P : Finset ℕ} (hne : P.Nonempty) :
    primeShifts P.toList ≠ [] := by
  have hlen : (primeShifts P.toList).length = P.card := by simp [primeShifts]
  have hcard := Finset.card_pos.mpr hne
  intro hz
  rw [hz, List.length_nil] at hlen
  omega

/-- Product-of-log-shifts normalization of the literal finite-prime threshold profile. -/
def normalizedPrimePacket (P : Finset ℕ) : ℝ → ℝ :=
  normalizedThreshold (primeShifts P.toList)

theorem normalizedPrimePacket_eq_finiteSmoothed (P : Finset ℕ) (t : ℝ) :
    normalizedPrimePacket P t =
      finiteSmoothed P (P.card-1) t / shiftMass (primeShifts P.toList) := by
  simp [normalizedPrimePacket, normalizedThreshold, finiteSmoothed, finiteProfile,
    smoothed, primeShifts]

theorem normalizedPrimePacket_nonneg {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) (t : ℝ) :
    0 ≤ normalizedPrimePacket P t :=
  normalizedThreshold_nonneg
    (primeShifts_pos (fun p hp => hP p (by simpa using hp))) (primeShifts_ne_nil hne) t

theorem integrable_normalizedPrimePacket {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) : Integrable (normalizedPrimePacket P) :=
  integrable_normalizedThreshold
    (primeShifts_pos (fun p hp => hP p (by simpa using hp))) (primeShifts_ne_nil hne)

theorem integral_normalizedPrimePacket {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) : (∫ t, normalizedPrimePacket P t) = 1 :=
  integral_normalizedThreshold
    (primeShifts_pos (fun p hp => hP p (by simpa using hp))) (primeShifts_ne_nil hne)

/-- Explicit geometric bound for the normalized literal finite-prime profile. -/
theorem normalizedPrimePacket_halfline_bound {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) {t T : ℝ} (ht : t ≤ T) :
    normalizedPrimePacket P t ≤
      ((2 / primeShiftFloor) * Real.exp ((2 / primeShiftFloor) * T)) * (1/2:ℝ)^P.card := by
  simpa [normalizedPrimePacket, primeShifts] using
    normalizedThreshold_halfline_bound primeShiftFloor_pos (primeShiftFloor_le hP)
      (primeShifts_ne_nil hne) ht

/-- No positive fixed-scale profile survives as the number of distinct primes grows. -/
theorem tendstoUniformlyOn_normalizedPrimePacket {ι : Type*} {l : Filter ι}
    {P : ι → Finset ℕ} (hP : ∀ i, ∀ p ∈ P i, p.Prime)
    (hcard : Tendsto (fun i => (P i).card) l atTop) (T : ℝ) :
    TendstoUniformlyOn (fun i => normalizedPrimePacket (P i)) (fun _ => 0) l (Iic T) := by
  apply tendstoUniformlyOn_normalizedThreshold primeShiftFloor_pos
    (fun i => primeShiftFloor_le (hP i))
  simpa [primeShifts] using hcard

theorem normalizedPrimePacket_limit_eq_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    {P : ι → Finset ℕ} (hP : ∀ i, ∀ p ∈ P i, p.Prime)
    (hcard : Tendsto (fun i => (P i).card) l atTop) {t y : ℝ}
    (hy : Tendsto (fun i => normalizedPrimePacket (P i) t) l (𝓝 y)) : y = 0 := by
  exact tendsto_nhds_unique hy
    ((tendstoUniformlyOn_normalizedPrimePacket hP hcard t).tendsto_at (Set.mem_Iic.mpr le_rfl))

theorem normalizedPrimePacket_upper_mass_bound {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) (T : ℝ) :
    1 - (1/2:ℝ)^P.card * Real.exp ((2/primeShiftFloor)*T) ≤
      (∫ t in Ioi T, normalizedPrimePacket P t) ∧
      (∫ t in Ioi T, normalizedPrimePacket P t) ≤ 1 := by
  simpa [normalizedPrimePacket, primeShifts] using
    normalizedThreshold_upper_mass_bound primeShiftFloor_pos (primeShiftFloor_le hP)
      (primeShifts_ne_nil hne) T

/-- Unit mass escapes every fixed logarithmic cutoff as prime cardinality grows. -/
theorem tendsto_normalizedPrimePacket_upper_mass {ι : Type*} {l : Filter ι}
    {P : ι → Finset ℕ} (hP : ∀ i, ∀ p ∈ P i, p.Prime)
    (hcard : Tendsto (fun i => (P i).card) l atTop) (T : ℝ) :
    Tendsto (fun i => ∫ t in Ioi T, normalizedPrimePacket (P i) t) l (𝓝 1) := by
  apply tendsto_normalizedThreshold_upper_mass primeShiftFloor_pos
    (fun i => primeShiftFloor_le (hP i))
  simpa [primeShifts] using hcard

/-- Passing to a fixed-scale pointwise limit cannot retain a probability density. -/
theorem no_unit_mass_pointwise_limit_normalizedPrimePacket {ι : Type*}
    {l : Filter ι} [l.NeBot] {P : ι → Finset ℕ}
    (hP : ∀ i, ∀ p ∈ P i, p.Prime)
    (hcard : Tendsto (fun i => (P i).card) l atTop) :
    ¬ ∃ f : ℝ → ℝ, (∫ t, f t) = 1 ∧
      ∀ t, Tendsto (fun i => normalizedPrimePacket (P i) t) l (𝓝 (f t)) := by
  rintro ⟨f, hmass, hf⟩
  have he : f = fun _ => 0 := funext (fun t =>
    normalizedPrimePacket_limit_eq_zero hP hcard (hf t))
  simp [he] at hmass

end RHTower.MobiusRieszSmoothing

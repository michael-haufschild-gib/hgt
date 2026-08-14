import GaloisForLFunctions.HTGeometry.SharedGaugeQuotientFusion

/-!
# Reflexive polarization synchronization

This module certifies the algebraic core of ULF-LGPD-2.  A finite packet of positive scalar
polarizations converts local residuals into local correction velocities.  One source can execute
only their polarization-weighted mean.  Independent local power then splits exactly into executable
power and synchronization tension.

The module also certifies:

* balance and exact zero/synchronization classification;
* homogeneous amplification of all three powers;
* bounded amplified local power iff every local correction is zero;
* the cubic transport identity for the instantaneous power rates;
* a closed quadratic two-channel family with vanishing fused power and persistent tension.
-/

namespace HTGeometry

noncomputable section

open ConstraintFrameRelativity Filter

variable {ι : Type*} [Fintype ι]

/-- Total scalar polarization. -/
def totalPolarization (h : ι → ℝ) : ℝ := capA h

/-- Polarization-weighted local-velocity moment. -/
def polarizationMoment (h v : ι → ℝ) : ℝ := capB h v

/-- One source's executable velocity: the polarization-weighted mean. -/
def sharedPolarVelocity (h v : ι → ℝ) : ℝ :=
  polarizationMoment h v / totalPolarization h

/-- Power available to independent local corrections. -/
def localPolarPower (h v : ι → ℝ) : ℝ := capC h v

/-- Power of the single correction executable by the common source. -/
def fusedPolarPower (h v : ι → ℝ) : ℝ :=
  totalPolarization h * sharedPolarVelocity h v ^ 2

/-- Power created by incompatibility of the locally optimal velocities. -/
def synchronizationTension (h v : ι → ℝ) : ℝ :=
  ∑ i, h i * (v i - sharedPolarVelocity h v) ^ 2

/-- Common scalar amplification of a local-velocity packet. -/
def amplifyPolarVelocity (r : ℝ) (v : ι → ℝ) : ι → ℝ := fun i => r * v i

theorem totalPolarization_pos [Nonempty ι] {h : ι → ℝ} (hh : ∀ i, 0 < h i) :
    0 < totalPolarization h := by
  rw [totalPolarization, capA]
  exact Finset.sum_pos (fun i _ => hh i) Finset.univ_nonempty

/-- The relative local-velocity packet is polarization-balanced. -/
theorem synchronization_balance [Nonempty ι] {h v : ι → ℝ} (hh : ∀ i, 0 < h i) :
    ∑ i, h i * (v i - sharedPolarVelocity h v) = 0 := by
  have hH := (totalPolarization_pos hh).ne'
  calc
    ∑ i, h i * (v i - sharedPolarVelocity h v) =
        polarizationMoment h v - totalPolarization h * sharedPolarVelocity h v := by
      simp only [mul_sub, Finset.sum_sub_distrib, polarizationMoment, totalPolarization,
        capA, capB]
      congr 1
      rw [Finset.sum_mul]
    _ = 0 := by
      rw [sharedPolarVelocity]
      field_simp
      ring

/-- Independent local power is executable fused power plus synchronization tension. -/
theorem localPolarPower_eq_fused_add_tension [Nonempty ι]
    {h v : ι → ℝ} (hh : ∀ i, 0 < h i) :
    localPolarPower h v = fusedPolarPower h v + synchronizationTension h v := by
  have hH := (totalPolarization_pos hh).ne'
  have hexpand := quadratic_expand h v (sharedPolarVelocity h v) 1
  simp only [one_mul] at hexpand
  have hsquare :
      (∑ i, h i * (sharedPolarVelocity h v - v i) ^ 2) = synchronizationTension h v := by
    rw [synchronizationTension]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  rw [hsquare] at hexpand
  rw [hexpand]
  simp only [localPolarPower, fusedPolarPower, sharedPolarVelocity, polarizationMoment,
    totalPolarization]
  field_simp
  ring

theorem localPolarPower_nonneg {h v : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    0 ≤ localPolarPower h v := by
  rw [localPolarPower, capC]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hh i) (sq_nonneg _)

theorem synchronizationTension_nonneg {h v : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    0 ≤ synchronizationTension h v := by
  rw [synchronizationTension]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hh i) (sq_nonneg _)

/-- Tension vanishes exactly when every local velocity is executable as one shared velocity. -/
theorem synchronizationTension_eq_zero_iff {h v : ι → ℝ} (hh : ∀ i, 0 < h i) :
    synchronizationTension h v = 0 ↔ ∀ i, v i = sharedPolarVelocity h v := by
  constructor
  · intro hz i
    have hterm : ∀ j ∈ (Finset.univ : Finset ι),
        0 ≤ h j * (v j - sharedPolarVelocity h v) ^ 2 :=
      fun j _ => mul_nonneg (hh j).le (sq_nonneg _)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hz i (Finset.mem_univ i)
    have hsquare : (v i - sharedPolarVelocity h v) ^ 2 = 0 := by
      exact (mul_eq_zero.mp hi).resolve_left (hh i).ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro hv
    rw [synchronizationTension]
    exact Finset.sum_eq_zero fun i _ => by rw [hv i, sub_self, zero_pow (by norm_num), mul_zero]

/-- Local power vanishes exactly when every local correction vanishes. -/
theorem localPolarPower_eq_zero_iff {h v : ι → ℝ} (hh : ∀ i, 0 < h i) :
    localPolarPower h v = 0 ↔ ∀ i, v i = 0 := by
  constructor
  · intro hz i
    rw [localPolarPower, capC] at hz
    have hterm : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ h j * v j ^ 2 :=
      fun j _ => mul_nonneg (hh j).le (sq_nonneg _)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hz i (Finset.mem_univ i)
    have hsquare : v i ^ 2 = 0 := (mul_eq_zero.mp hi).resolve_left (hh i).ne'
    exact sq_eq_zero_iff.mp hsquare
  · intro hv
    rw [localPolarPower, capC]
    exact Finset.sum_eq_zero fun i _ => by rw [hv i, zero_pow (by norm_num), mul_zero]

theorem sharedPolarVelocity_amplify (h v : ι → ℝ) (r : ℝ) :
    sharedPolarVelocity h (amplifyPolarVelocity r v) = r * sharedPolarVelocity h v := by
  unfold sharedPolarVelocity polarizationMoment amplifyPolarVelocity
  have hnum : capB h (fun i => r * v i) = r * capB h v := by
    rw [capB, capB, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hnum]
  ring

theorem localPolarPower_amplify (h v : ι → ℝ) (r : ℝ) :
    localPolarPower h (amplifyPolarVelocity r v) = r ^ 2 * localPolarPower h v := by
  rw [localPolarPower, localPolarPower, capC, capC, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [amplifyPolarVelocity]
  ring

theorem fusedPolarPower_amplify (h v : ι → ℝ) (r : ℝ) :
    fusedPolarPower h (amplifyPolarVelocity r v) = r ^ 2 * fusedPolarPower h v := by
  rw [fusedPolarPower, sharedPolarVelocity_amplify, fusedPolarPower]
  ring

theorem synchronizationTension_amplify (h v : ι → ℝ) (r : ℝ) :
    synchronizationTension h (amplifyPolarVelocity r v) =
      r ^ 2 * synchronizationTension h v := by
  rw [synchronizationTension, synchronizationTension, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sharedPolarVelocity_amplify]
  simp only [amplifyPolarVelocity]
  ring

/-- Uniform boundedness of independent correction power on a source-generated scale orbit. -/
def BoundedLocalPolarOrbit (d : ℝ) (h v : ι → ℝ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, localPolarPower h (amplifyPolarVelocity (d ^ n) v) ≤ B

/-- Bounded amplified complete power selects every local residual, not only their sum. -/
theorem boundedLocalPolarOrbit_iff [Nonempty ι] {d : ℝ} {h v : ι → ℝ}
    (hd : 1 < d) (hh : ∀ i, 0 < h i) :
    BoundedLocalPolarOrbit d h v ↔ ∀ i, v i = 0 := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hv
    have hPnonzero : localPolarPower h v ≠ 0 := by
      intro hzero
      exact hv ((localPolarPower_eq_zero_iff hh).mp hzero)
    have hP : 0 < localPolarPower h v :=
      lt_of_le_of_ne (localPolarPower_nonneg fun i => (hh i).le) (Ne.symm hPnonzero)
    have hd2 : 1 < d ^ 2 := by nlinarith
    have hgrow : Tendsto (fun n : ℕ => (d ^ 2) ^ n * localPolarPower h v) atTop atTop :=
      Tendsto.atTop_mul_const hP (tendsto_pow_atTop_atTop_of_one_lt hd2)
    obtain ⟨n, hn⟩ := (hgrow.eventually_gt_atTop B).exists
    have hbound := hB n
    rw [localPolarPower_amplify] at hbound
    have heq : (d ^ n) ^ 2 = (d ^ 2) ^ n := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
    rw [heq] at hbound
    linarith
  · intro hv
    refine ⟨0, fun n => ?_⟩
    rw [localPolarPower_amplify, (localPolarPower_eq_zero_iff hh).mpr hv, mul_zero]

/-! ## Cubic transport algebra -/

/-- Instantaneous derivative forced on the independent local power by the channel response laws. -/
def localPolarPowerRate (h τ v : ι → ℝ) : ℝ :=
  -2 * fusedPolarPower h v
    - ∑ i, τ i * sharedPolarVelocity h v * v i ^ 2

/-- Instantaneous derivative forced on executable fused power by total third response. -/
def fusedPolarPowerRate (h τ v : ι → ℝ) : ℝ :=
  -2 * fusedPolarPower h v
    - (∑ i, τ i) * sharedPolarVelocity h v ^ 3

/-- Cubic current that transports synchronization tension. -/
def cubicSynchronizationTransport (h τ v : ι → ℝ) : ℝ :=
  ∑ i, τ i *
    (sharedPolarVelocity h v ^ 3 - sharedPolarVelocity h v * v i ^ 2)

/-- Difference of local and fused power rates is exactly the cubic synchronization current. -/
theorem localRate_sub_fusedRate_eq_cubicTransport (h τ v : ι → ℝ) :
    localPolarPowerRate h τ v - fusedPolarPowerRate h τ v =
      cubicSynchronizationTransport h τ v := by
  unfold localPolarPowerRate fusedPolarPowerRate cubicSynchronizationTransport
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_mul]
  have hcomm :
      (∑ i, τ i * sharedPolarVelocity h v * v i ^ 2) =
        ∑ i, sharedPolarVelocity h v * τ i * v i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcomm]
  ring

/-- Quadratic channels have zero cubic transport. -/
theorem cubicSynchronizationTransport_zero (h v : ι → ℝ) :
    cubicSynchronizationTransport h (fun _ => 0) v = 0 := by
  simp [cubicSynchronizationTransport]

/-! ## Closed quadratic witness -/

/-- Two quadratic channels can have arbitrary common velocity `a`, persistent opposite local
offsets, fused power `2a²`, and constant synchronization tension `2`. -/
theorem quadratic_twoChannel_persistent_tension (a : ℝ) :
    let h : Fin 2 → ℝ := fun _ => 1
    let v : Fin 2 → ℝ := ![a + 1, a - 1]
    sharedPolarVelocity h v = a ∧
      fusedPolarPower h v = 2 * a ^ 2 ∧
      synchronizationTension h v = 2 := by
  dsimp
  constructor
  · simp [sharedPolarVelocity, polarizationMoment, totalPolarization, capA, capB,
      Fin.sum_univ_two]
  constructor
  · simp [fusedPolarPower, sharedPolarVelocity, polarizationMoment, totalPolarization, capA, capB,
      Fin.sum_univ_two]
  · simp [synchronizationTension, sharedPolarVelocity, polarizationMoment, totalPolarization,
      capA, capB, Fin.sum_univ_two]
    ring

/-- Closed capstone for conservation, synchronization, properness, cubic transport, and the
quadratic persistence witness. -/
theorem reflexivePolarizationSynchronization_capstone [Nonempty ι]
    {d : ℝ} {h v τ : ι → ℝ} (hd : 1 < d) (hh : ∀ i, 0 < h i) :
    localPolarPower h v = fusedPolarPower h v + synchronizationTension h v
      ∧ (synchronizationTension h v = 0 ↔ ∀ i, v i = sharedPolarVelocity h v)
      ∧ (BoundedLocalPolarOrbit d h v ↔ ∀ i, v i = 0)
      ∧ localPolarPowerRate h τ v - fusedPolarPowerRate h τ v =
          cubicSynchronizationTransport h τ v
      ∧ (let h₂ : Fin 2 → ℝ := fun _ => 1
         let v₂ : Fin 2 → ℝ := ![(1 : ℝ), -1]
         fusedPolarPower h₂ v₂ = 0 ∧ synchronizationTension h₂ v₂ = 2) := by
  refine ⟨localPolarPower_eq_fused_add_tension hh,
    synchronizationTension_eq_zero_iff hh,
    boundedLocalPolarOrbit_iff hd hh,
    localRate_sub_fusedRate_eq_cubicTransport h τ v, ?_⟩
  simpa using (quadratic_twoChannel_persistent_tension 0).2

end

end HTGeometry

import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureHilbertMetric
import GaloisForLFunctions.RHTower.PhysicalPrimeEndpointMeshCoercivity

/-!
# Physical prime endpoint noncancellation

Interior clipped starts and ends retain prime labels. A start--end collision has distinct ordinary
prime weights, while every active interval of raw width below the aperture has an interior
endpoint. These are the source-specific endpoint facts required by the physical radical theorem.
-/

open MeasureTheory

namespace RHTower

noncomputable section

private theorem prime_eq_of_log_eq {p q : Nat.Primes}
    (h : Real.log (p : ℝ) = Real.log (q : ℝ)) : p = q := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.prop.pos
  have hreal : (p : ℝ) = (q : ℝ) := by
    have hexp := congrArg Real.exp h
    simpa [Real.exp_log hp, Real.exp_log hq] using hexp
  apply Subtype.ext
  exact_mod_cast hreal

theorem xiPhysicalPrimeLogApertureStart_eq_raw_of_pos
    {m : ℝ} {p : Nat.Primes}
    (h : 0 < xiPhysicalPrimeLogApertureStart m p) :
    xiPhysicalPrimeLogApertureStart m p = m - Real.log (p : ℝ) := by
  have hraw : 0 < m - Real.log (p : ℝ) := by
    simpa [xiPhysicalPrimeLogApertureStart] using h
  simp [xiPhysicalPrimeLogApertureStart, hraw.le]

theorem xiPhysicalPrimeLogApertureEnd_eq_raw_of_lt
    {A k : ℝ} {p : Nat.Primes}
    (h : xiPhysicalPrimeLogApertureEnd A k p < A) :
    xiPhysicalPrimeLogApertureEnd A k p = k - Real.log (p : ℝ) := by
  have hraw : k - Real.log (p : ℝ) < A := by
    simpa [xiPhysicalPrimeLogApertureEnd] using h
  simp [xiPhysicalPrimeLogApertureEnd, hraw.le]

theorem xiPhysicalPrimeLogApertureStart_injective_at_interior
    {m : ℝ} {p q : Nat.Primes}
    (hp : 0 < xiPhysicalPrimeLogApertureStart m p)
    (h : xiPhysicalPrimeLogApertureStart m p =
      xiPhysicalPrimeLogApertureStart m q) :
    p = q := by
  have hq : 0 < xiPhysicalPrimeLogApertureStart m q := by
    rwa [← h]
  have hpraw := xiPhysicalPrimeLogApertureStart_eq_raw_of_pos hp
  have hqraw := xiPhysicalPrimeLogApertureStart_eq_raw_of_pos hq
  apply prime_eq_of_log_eq
  linarith

theorem xiPhysicalPrimeLogApertureEnd_injective_at_interior
    {A k : ℝ} {p q : Nat.Primes}
    (hp : xiPhysicalPrimeLogApertureEnd A k p < A)
    (h : xiPhysicalPrimeLogApertureEnd A k p =
      xiPhysicalPrimeLogApertureEnd A k q) :
    p = q := by
  have hq : xiPhysicalPrimeLogApertureEnd A k q < A := by
    rwa [← h]
  have hpraw := xiPhysicalPrimeLogApertureEnd_eq_raw_of_lt hp
  have hqraw := xiPhysicalPrimeLogApertureEnd_eq_raw_of_lt hq
  apply prime_eq_of_log_eq
  linarith

theorem xiPhysicalPrimeLog_start_end_collision_ne
    {A m k t : ℝ} {p q : Nat.Primes}
    (hwidth : 0 < k - m)
    (ht0 : 0 < t) (htA : t < A)
    (hstart : xiPhysicalPrimeLogApertureStart m p = t)
    (hend : xiPhysicalPrimeLogApertureEnd A k q = t) :
    p ≠ q := by
  intro hpq
  subst q
  have hspos : 0 < xiPhysicalPrimeLogApertureStart m p := hstart.symm ▸ ht0
  have helt : xiPhysicalPrimeLogApertureEnd A k p < A := hend.symm ▸ htA
  have hsraw := xiPhysicalPrimeLogApertureStart_eq_raw_of_pos hspos
  have heraw := xiPhysicalPrimeLogApertureEnd_eq_raw_of_lt helt
  linarith

theorem xiPhysicalPrimeLog_start_end_collision_weight_ne
    {A m k t : ℝ} {p q : Nat.Primes}
    (hwidth : 0 < k - m)
    (ht0 : 0 < t) (htA : t < A)
    (hstart : xiPhysicalPrimeLogApertureStart m p = t)
    (hend : xiPhysicalPrimeLogApertureEnd A k q = t) :
    physicalPrimeEndpointWeight p ≠ physicalPrimeEndpointWeight q := by
  apply physicalPrimeEndpointWeight_ne_of_distinct p.prop q.prop
  intro hpq
  exact xiPhysicalPrimeLog_start_end_collision_ne hwidth ht0 htA hstart hend
    (Subtype.ext hpq)

theorem xiPhysicalPrimeLogApertureLength_lt_of_active
    {A m k : ℝ} {p : Nat.Primes}
    (hactive : 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth : k - m < A) :
    xiPhysicalPrimeLogApertureLength A m k p < A := by
  have hdiff : 0 < xiPhysicalPrimeLogApertureEnd A k p -
      xiPhysicalPrimeLogApertureStart m p := by
    simpa [xiPhysicalPrimeLogApertureLength] using hactive
  rw [xiPhysicalPrimeLogApertureLength, max_eq_right hdiff.le]
  have hend : xiPhysicalPrimeLogApertureEnd A k p ≤
      k - Real.log (p : ℝ) := by
    exact min_le_right _ _
  have hstart : m - Real.log (p : ℝ) ≤
      xiPhysicalPrimeLogApertureStart m p := by
    exact le_max_right _ _
  linarith

theorem xiPhysicalPrimeLogAperture_active_has_interior_endpoint
    {A m k : ℝ} {p : Nat.Primes}
    (hactive : 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth : k - m < A) :
    (0 < xiPhysicalPrimeLogApertureStart m p ∧
        xiPhysicalPrimeLogApertureStart m p < A) ∨
      (0 < xiPhysicalPrimeLogApertureEnd A k p ∧
        xiPhysicalPrimeLogApertureEnd A k p < A) := by
  have hdiff : xiPhysicalPrimeLogApertureStart m p <
      xiPhysicalPrimeLogApertureEnd A k p := by
    have : 0 < xiPhysicalPrimeLogApertureEnd A k p -
        xiPhysicalPrimeLogApertureStart m p := by
      simpa [xiPhysicalPrimeLogApertureLength] using hactive
    linarith
  have hs0 := xiPhysicalPrimeLogApertureStart_nonneg m p
  have heA := xiPhysicalPrimeLogApertureEnd_le A k p
  by_cases hs : 0 < xiPhysicalPrimeLogApertureStart m p
  · left
    exact ⟨hs, hdiff.trans_le heA⟩
  · have hsEq : xiPhysicalPrimeLogApertureStart m p = 0 :=
      le_antisymm (not_lt.mp hs) hs0
    right
    refine ⟨by linarith, ?_⟩
    by_contra he
    have heEq : xiPhysicalPrimeLogApertureEnd A k p = A :=
      le_antisymm heA (not_lt.mp he)
    have hend : xiPhysicalPrimeLogApertureEnd A k p ≤
        k - Real.log (p : ℝ) := min_le_right _ _
    have hstart : m - Real.log (p : ℝ) ≤
        xiPhysicalPrimeLogApertureStart m p := le_max_right _ _
    linarith

theorem xiPhysicalPrimeLogCenteredApertureCarrier_ne_zero_of_active
    {A m k : ℝ} {p : Nat.Primes}
    (hactive : 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth : k - m < A) :
    xiPhysicalPrimeLogCenteredApertureCarrier A m k p ≠ 0 := by
  have hLA := xiPhysicalPrimeLogApertureLength_lt_of_active hactive hwidth
  have hA : 0 < A := hactive.trans hLA
  intro hzero
  have hinner := real_inner_xiPhysicalPrimeLogCenteredApertureCarrier hA m k p p
  rw [hzero, inner_zero_left,
    xiPhysicalPrimeLogApertureFusionKernel_diagonal] at hinner
  have hpos : 0 < xiPhysicalPrimeLogApertureLength A m k p -
      xiPhysicalPrimeLogApertureLength A m k p ^ 2 / A := by
    have hfactor : xiPhysicalPrimeLogApertureLength A m k p -
        xiPhysicalPrimeLogApertureLength A m k p ^ 2 / A =
      xiPhysicalPrimeLogApertureLength A m k p *
        (A - xiPhysicalPrimeLogApertureLength A m k p) / A := by
      field_simp [hA.ne']
    rw [hfactor]
    exact div_pos (mul_pos hactive (sub_pos.mpr hLA)) hA
  linarith

/-! ## Finite-packet endpoint jumps -/

/-- Total weight of packet ends landing at `t`. -/
def xiPhysicalPrimeLogEndpointEndWeight
    (P : Finset Nat.Primes) (A k t : ℝ) : ℝ :=
  ∑ p ∈ P, if xiPhysicalPrimeLogApertureEnd A k p = t then
    physicalPrimeEndpointWeight p else 0

/-- Total weight of packet starts landing at `t`. -/
def xiPhysicalPrimeLogEndpointStartWeight
    (P : Finset Nat.Primes) (m t : ℝ) : ℝ :=
  ∑ p ∈ P, if xiPhysicalPrimeLogApertureStart m p = t then
    physicalPrimeEndpointWeight p else 0

/-- Signed physical endpoint jump: ending intervals enter with positive sign and starting
intervals with negative sign, matching `(PE3)`. -/
def xiPhysicalPrimeLogEndpointJump
    (P : Finset Nat.Primes) (A m k t : ℝ) : ℝ :=
  xiPhysicalPrimeLogEndpointEndWeight P A k t -
    xiPhysicalPrimeLogEndpointStartWeight P m t

private theorem xiPhysicalPrimeLogEndpointEndWeight_eq_single
    {P : Finset Nat.Primes} {A k t : ℝ} {p : Nat.Primes}
    (hp : p ∈ P) (htA : t < A)
    (hend : xiPhysicalPrimeLogApertureEnd A k p = t) :
    xiPhysicalPrimeLogEndpointEndWeight P A k t =
      physicalPrimeEndpointWeight p := by
  classical
  rw [xiPhysicalPrimeLogEndpointEndWeight, Finset.sum_eq_single p]
  · simp [hend]
  · intro q hq hqp
    have hneq : xiPhysicalPrimeLogApertureEnd A k q ≠ t := by
      intro hqt
      apply hqp
      exact xiPhysicalPrimeLogApertureEnd_injective_at_interior
        (hqt.symm ▸ htA) (hqt.trans hend.symm)
    simp [hneq]
  · simp [hp]

private theorem xiPhysicalPrimeLogEndpointStartWeight_eq_single
    {P : Finset Nat.Primes} {m t : ℝ} {p : Nat.Primes}
    (hp : p ∈ P) (ht0 : 0 < t)
    (hstart : xiPhysicalPrimeLogApertureStart m p = t) :
    xiPhysicalPrimeLogEndpointStartWeight P m t =
      physicalPrimeEndpointWeight p := by
  classical
  rw [xiPhysicalPrimeLogEndpointStartWeight, Finset.sum_eq_single p]
  · simp [hstart]
  · intro q hq hqp
    have hneq : xiPhysicalPrimeLogApertureStart m q ≠ t := by
      intro hqt
      apply hqp
      exact xiPhysicalPrimeLogApertureStart_injective_at_interior
        (hqt.symm ▸ ht0) (hqt.trans hstart.symm)
    simp [hneq]
  · simp [hp]

private theorem xiPhysicalPrimeLogEndpointEndWeight_eq_zero
    {P : Finset Nat.Primes} {A k t : ℝ}
    (h : ¬ ∃ p ∈ P, xiPhysicalPrimeLogApertureEnd A k p = t) :
    xiPhysicalPrimeLogEndpointEndWeight P A k t = 0 := by
  classical
  rw [xiPhysicalPrimeLogEndpointEndWeight]
  apply Finset.sum_eq_zero
  intro p hp
  simp only [ite_eq_right_iff]
  intro hend
  exact (h ⟨p, hp, hend⟩).elim

private theorem xiPhysicalPrimeLogEndpointStartWeight_eq_zero
    {P : Finset Nat.Primes} {m t : ℝ}
    (h : ¬ ∃ p ∈ P, xiPhysicalPrimeLogApertureStart m p = t) :
    xiPhysicalPrimeLogEndpointStartWeight P m t = 0 := by
  classical
  rw [xiPhysicalPrimeLogEndpointStartWeight]
  apply Finset.sum_eq_zero
  intro p hp
  simp only [ite_eq_right_iff]
  intro hstart
  exact (h ⟨p, hp, hstart⟩).elim

/-- Every interior endpoint carried by a finite physical packet has nonzero signed jump. Starts
and ends are separately injective; the only possible collision is a start--end pair of distinct
primes, whose logarithmic weights differ by unique factorization. -/
theorem xiPhysicalPrimeLogEndpointJump_ne_zero
    {P : Finset Nat.Primes} {A m k t : ℝ}
    (hwidth : 0 < k - m) (ht0 : 0 < t) (htA : t < A)
    (hendpoint :
      (∃ p ∈ P, xiPhysicalPrimeLogApertureEnd A k p = t) ∨
        (∃ p ∈ P, xiPhysicalPrimeLogApertureStart m p = t)) :
    xiPhysicalPrimeLogEndpointJump P A m k t ≠ 0 := by
  rcases hendpoint with hendpoint | hstartpoint
  · rcases hendpoint with ⟨p, hp, hend⟩
    rw [xiPhysicalPrimeLogEndpointJump,
      xiPhysicalPrimeLogEndpointEndWeight_eq_single hp htA hend]
    by_cases hstart : ∃ q ∈ P, xiPhysicalPrimeLogApertureStart m q = t
    · rcases hstart with ⟨q, hq, hqstart⟩
      rw [xiPhysicalPrimeLogEndpointStartWeight_eq_single hq ht0 hqstart]
      exact sub_ne_zero.mpr
        (xiPhysicalPrimeLog_start_end_collision_weight_ne hwidth ht0 htA
          hqstart hend).symm
    · rw [xiPhysicalPrimeLogEndpointStartWeight_eq_zero hstart, sub_zero]
      exact (physicalPrimeEndpointWeight_pos p).ne'
  · rcases hstartpoint with ⟨q, hq, hqstart⟩
    rw [xiPhysicalPrimeLogEndpointJump,
      xiPhysicalPrimeLogEndpointStartWeight_eq_single hq ht0 hqstart]
    by_cases hend : ∃ p ∈ P, xiPhysicalPrimeLogApertureEnd A k p = t
    · rcases hend with ⟨p, hp, hpend⟩
      rw [xiPhysicalPrimeLogEndpointEndWeight_eq_single hp htA hpend]
      exact sub_ne_zero.mpr
        (xiPhysicalPrimeLog_start_end_collision_weight_ne hwidth ht0 htA
          hqstart hpend).symm
    · rw [xiPhysicalPrimeLogEndpointEndWeight_eq_zero hend]
      exact sub_ne_zero.mpr (physicalPrimeEndpointWeight_pos q).ne

/-- A nonempty active physical packet of raw width strictly between zero and the aperture has an
interior endpoint with nonzero signed prime jump. This is the complete arithmetic
noncancellation input to the Brownian endpoint radical. -/
theorem exists_xiPhysicalPrimeLog_interiorEndpoint_nonzero_jump
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    ∃ t, 0 < t ∧ t < A ∧
      xiPhysicalPrimeLogEndpointJump P A m k t ≠ 0 := by
  rcases hP with ⟨p, hp⟩
  rcases xiPhysicalPrimeLogAperture_active_has_interior_endpoint
      (hactive p hp) hwidthA with hstart | hend
  · refine ⟨xiPhysicalPrimeLogApertureStart m p, hstart.1, hstart.2, ?_⟩
    exact xiPhysicalPrimeLogEndpointJump_ne_zero hwidth0 hstart.1 hstart.2
      (Or.inr ⟨p, hp, rfl⟩)
  · refine ⟨xiPhysicalPrimeLogApertureEnd A k p, hend.1, hend.2, ?_⟩
    exact xiPhysicalPrimeLogEndpointJump_ne_zero hwidth0 hend.1 hend.2
      (Or.inl ⟨p, hp, rfl⟩)

end

end RHTower

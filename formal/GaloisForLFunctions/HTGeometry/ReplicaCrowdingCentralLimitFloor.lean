import GaloisForLFunctions.HTGeometry.ReplicaAmplitudeMoments
import GaloisForLFunctions.HTGeometry.FiniteLawCentralBinCrowding
import GaloisForLFunctions.HTGeometry.FiniteEntropyPlateauFutureLaw

/-!
# The replica crowding central-limit floor

Growing the replica order does not thin out near coincidences of replica energies.  The order-`r`
replica law has mean `r` times the single level mean and variance exactly `r` times the single level
variance, so Chebyshev confines three quarters of its mass to an interval of length `4σ√r`; cutting
that interval into cells of width `δ` forces one cell to carry mass at least `3/(4√N)` in square.
The mass of a common cell is charged to exact energy collisions or to strictly near, distinct
replica pairs.

Hence the near-action mass at resolution `δ` is at least `9δ / (16(δ + 4σ√r))` minus the collision
mass, uniformly in `r`.  Since the collision mass of a maximally projective uniform spectrum decays
only like `r!/d^r`, the near-action mass cannot be made to vanish by raising the replica order: the
`δ/√r` order is forced by central-limit geometry, not by weak level repulsion.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Variance of one spectral level under a probability weighting. -/
def singleLevelSpectralVariance (weight energy : I → ℝ) : ℝ :=
  ∑ i, weight i * (energy i - ∑ j, weight j * energy j) ^ 2

/-! ## Transferring the finite-law quantities to replica multiplicity vectors -/

theorem sum_replicaAmplitude_subtype {weight : I → ℝ} (hw : ∑ i, weight i = 1) (r : ℕ) :
    ∑ p : ReplicaMultiplicityIndex I r,
        fidelityReplicaMultiplicityAmplitude weight p.1 = 1 := by
  classical
  refine Eq.trans ?_ (replicaAmplitude_total_mass hw r)
  exact Finset.sum_coe_sort ((Finset.univ : Finset I).piAntidiag r)
    (fun p => fidelityReplicaMultiplicityAmplitude weight p)

theorem sum_replicaAmplitude_variance_subtype {weight : I → ℝ} (hw : ∑ i, weight i = 1)
    (energy : I → ℝ) (r : ℕ) :
    ∑ p : ReplicaMultiplicityIndex I r,
        fidelityReplicaMultiplicityAmplitude weight p.1 *
          (replicaMultiplicityEnergy energy p.1 - (r : ℝ) * ∑ i, weight i * energy i) ^ 2
      = r * singleLevelSpectralVariance weight energy := by
  classical
  have hmom := replicaAmplitudeMoment_energy_variance hw energy r
  rw [replicaAmplitudeMoment] at hmom
  rw [singleLevelSpectralVariance]
  refine Eq.trans ?_ hmom
  exact Finset.sum_coe_sort ((Finset.univ : Finset I).piAntidiag r)
    (fun p => fidelityReplicaMultiplicityAmplitude weight p *
      (replicaMultiplicityEnergy energy p - (r : ℝ) * ∑ i, weight i * energy i) ^ 2)

theorem finiteLawCollisionMass_replicaAmplitude (weight energy : I → ℝ) (r : ℕ) :
    finiteLawCollisionMass
        (fun p : ReplicaMultiplicityIndex I r =>
          fidelityReplicaMultiplicityAmplitude weight p.1)
        (fun p : ReplicaMultiplicityIndex I r => replicaMultiplicityEnergy energy p.1)
      = fidelityReplicaCollisionMass weight energy r := by
  classical
  rw [← fidelityReplicaResonantMass_eq_collisionMass]
  unfold finiteLawCollisionMass fidelityReplicaResonantMass
  symm
  calc (∑ p ∈ Finset.univ.piAntidiag r, ∑ q ∈ Finset.univ.piAntidiag r,
          if replicaMultiplicityEnergy energy p = replicaMultiplicityEnergy energy q
          then fidelityReplicaMultiplicityWeight weight p q else 0)
      = ∑ p : ReplicaMultiplicityIndex I r, ∑ q ∈ Finset.univ.piAntidiag r,
          if replicaMultiplicityEnergy energy p.1 = replicaMultiplicityEnergy energy q
          then fidelityReplicaMultiplicityWeight weight p.1 q else 0 :=
        Finset.sum_subtype (Finset.univ.piAntidiag r) (by simp) _
    _ = ∑ p : ReplicaMultiplicityIndex I r, ∑ q : ReplicaMultiplicityIndex I r,
          if replicaMultiplicityEnergy energy p.1 = replicaMultiplicityEnergy energy q.1
          then fidelityReplicaMultiplicityWeight weight p.1 q.1 else 0 :=
        Finset.sum_congr rfl fun p _ =>
          Finset.sum_subtype (Finset.univ.piAntidiag r) (by simp) _
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [fidelityReplicaMultiplicityWeight_eq_amplitude_mul]

theorem finiteLawNearMass_replicaAmplitude (weight energy : I → ℝ) (r : ℕ) (δ : ℝ) :
    finiteLawNearMass
        (fun p : ReplicaMultiplicityIndex I r =>
          fidelityReplicaMultiplicityAmplitude weight p.1)
        (fun p : ReplicaMultiplicityIndex I r => replicaMultiplicityEnergy energy p.1) δ
      = fidelityReplicaNearActionMass weight energy r δ := by
  classical
  unfold finiteLawNearMass fidelityReplicaNearActionMass
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases h : 0 < |replicaMultiplicityEnergy energy p.1 -
        replicaMultiplicityEnergy energy q.1| ∧
      |replicaMultiplicityEnergy energy p.1 - replicaMultiplicityEnergy energy q.1| < δ
  · rw [if_pos h, if_pos (show replicaNearAction energy r δ p q from h),
      fidelityReplicaMultiplicityWeight_eq_amplitude_mul]
  · rw [if_neg h, if_neg (show ¬ replicaNearAction energy r δ p q from h)]

/-! ## The crowding floor at replica order `r` -/

/-- **The replica crowding central-limit floor.**  For every finite probability weighting, every
replica order and every resolution `δ > 0`, the strictly near replica pair mass is at least
`9δ / (16(δ + 4√(rσ²)))` minus the exact collision mass. -/
theorem fidelityReplicaNearActionMass_crowding_floor
    {weight energy : I → ℝ} (hnn : ∀ i, 0 ≤ weight i) (hw : ∑ i, weight i = 1)
    (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    9 * δ / (16 * (δ + 4 * Real.sqrt (r * singleLevelSpectralVariance weight energy)))
        - fidelityReplicaCollisionMass weight energy r
      ≤ fidelityReplicaNearActionMass weight energy r δ := by
  classical
  have hbase := finiteLaw_crowding_floor_center
    (a := fun p : ReplicaMultiplicityIndex I r =>
      fidelityReplicaMultiplicityAmplitude weight p.1)
    (X := fun p : ReplicaMultiplicityIndex I r => replicaMultiplicityEnergy energy p.1)
    (fun p => fidelityReplicaMultiplicityAmplitude_nonneg hnn p.1)
    (sum_replicaAmplitude_subtype hw r)
    ((r : ℝ) * ∑ i, weight i * energy i) hδ
  rw [sum_replicaAmplitude_variance_subtype hw energy r,
    finiteLawCollisionMass_replicaAmplitude, finiteLawNearMass_replicaAmplitude] at hbase
  exact hbase

/-- The same floor written with the standard deviation: `4σ√r`. -/
theorem fidelityReplicaNearActionMass_crowding_floor_sigma_sqrt
    {weight energy : I → ℝ} (hnn : ∀ i, 0 ≤ weight i) (hw : ∑ i, weight i = 1)
    (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    9 * δ / (16 * (δ + 4 * Real.sqrt (singleLevelSpectralVariance weight energy) *
          Real.sqrt r))
        - fidelityReplicaCollisionMass weight energy r
      ≤ fidelityReplicaNearActionMass weight energy r δ := by
  have hsplit : Real.sqrt ((r : ℝ) * singleLevelSpectralVariance weight energy)
      = Real.sqrt (singleLevelSpectralVariance weight energy) * Real.sqrt r := by
    rw [Real.sqrt_mul (Nat.cast_nonneg r), mul_comm]
  have h := fidelityReplicaNearActionMass_crowding_floor hnn hw (energy := energy) r hδ
  rw [hsplit, ← mul_assoc] at h
  exact h

/-! ## The uniform spectrum: the permutation floor is the only competitor -/

omit [DecidableEq I] in
theorem multinomial_le_factorial {p : I → ℕ} {r : ℕ} (hp : ∑ i, p i = r) :
    Nat.multinomial Finset.univ p ≤ r.factorial := by
  classical
  have hspec := Nat.multinomial_spec (Finset.univ : Finset I) p
  rw [hp] at hspec
  have hprod : 1 ≤ ∏ i, (p i).factorial :=
    Finset.one_le_prod' fun i _ => Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  calc Nat.multinomial Finset.univ p
      ≤ (∏ i, (p i).factorial) * Nat.multinomial Finset.univ p :=
        Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one hprod)
    _ = r.factorial := hspec

theorem sum_multinomial_piAntidiag (J : Type*) [Fintype J] [DecidableEq J] (r : ℕ) :
    ∑ p ∈ (Finset.univ : Finset J).piAntidiag r,
        Nat.multinomial (Finset.univ : Finset J) p
      = Fintype.card J ^ r := by
  classical
  have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset J) (fun _ => (1 : ℕ)) r
  simpa using h.symm

/-- **The uniform permutation floor.**  For the uniform weighting of a finite spectrum the
permutation collision floor is at most `r! / d^r`. -/
theorem fidelityReplicaPermutationFloor_microcanonical_le [Nonempty I] (r : ℕ) :
    fidelityReplicaPermutationFloor (microcanonicalWeight I) r
      ≤ (r.factorial : ℝ) / (Fintype.card I : ℝ) ^ r := by
  classical
  have hd : (0 : ℝ) < (Fintype.card I : ℝ) := by
    have hc : 0 < Fintype.card I := Fintype.card_pos
    exact_mod_cast hc
  have hterm : ∀ p ∈ (Finset.univ : Finset I).piAntidiag r,
      fidelityReplicaMultiplicityWeight (microcanonicalWeight I) p p
        = (Nat.multinomial (Finset.univ : Finset I) p : ℝ) ^ 2 *
          (((Fintype.card I : ℝ) ^ r)⁻¹) ^ 2 := by
    intro p hp
    have hsum : ∑ i, p i = r := by
      have := (Finset.mem_piAntidiag.mp hp).1
      simpa using this
    have hprod : ∏ i, microcanonicalWeight I i ^ p i = ((Fintype.card I : ℝ) ^ r)⁻¹ := by
      simp only [microcanonicalWeight]
      rw [Finset.prod_pow_eq_pow_sum, hsum, ← inv_pow]
    rw [fidelityReplicaMultiplicityWeight_eq_amplitude_mul,
      fidelityReplicaMultiplicityAmplitude, hprod]
    ring
  have hbound : ∀ p ∈ (Finset.univ : Finset I).piAntidiag r,
      (Nat.multinomial (Finset.univ : Finset I) p : ℝ) ^ 2 *
          (((Fintype.card I : ℝ) ^ r)⁻¹) ^ 2
        ≤ (r.factorial : ℝ) * (Nat.multinomial (Finset.univ : Finset I) p : ℝ) *
            (((Fintype.card I : ℝ) ^ r)⁻¹) ^ 2 := by
    intro p hp
    have hsum : ∑ i, p i = r := by
      have := (Finset.mem_piAntidiag.mp hp).1
      simpa using this
    have hle : (Nat.multinomial Finset.univ p : ℝ) ≤ (r.factorial : ℝ) := by
      exact_mod_cast multinomial_le_factorial hsum
    have hnn : (0 : ℝ) ≤ (Nat.multinomial Finset.univ p : ℝ) := Nat.cast_nonneg _
    have hsq : (0 : ℝ) ≤ (((Fintype.card I : ℝ) ^ r)⁻¹) ^ 2 := sq_nonneg _
    have hsq2 : (Nat.multinomial (Finset.univ : Finset I) p : ℝ) ^ 2
        ≤ (r.factorial : ℝ) * (Nat.multinomial (Finset.univ : Finset I) p : ℝ) := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hle hnn
    exact mul_le_mul_of_nonneg_right hsq2 hsq
  have hcard : ∑ p ∈ (Finset.univ : Finset I).piAntidiag r,
        (Nat.multinomial (Finset.univ : Finset I) p : ℝ)
      = (Fintype.card I : ℝ) ^ r := by
    have h := sum_multinomial_piAntidiag I r
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  calc fidelityReplicaPermutationFloor (microcanonicalWeight I) r
      = ∑ p ∈ (Finset.univ : Finset I).piAntidiag r,
          (Nat.multinomial (Finset.univ : Finset I) p : ℝ) ^ 2 *
            (((Fintype.card I : ℝ) ^ r)⁻¹) ^ 2 := by
        unfold fidelityReplicaPermutationFloor
        exact Finset.sum_congr rfl hterm
    _ ≤ ∑ p ∈ (Finset.univ : Finset I).piAntidiag r,
          (r.factorial : ℝ) * (Nat.multinomial (Finset.univ : Finset I) p : ℝ) *
            (((Fintype.card I : ℝ) ^ r)⁻¹) ^ 2 := Finset.sum_le_sum hbound
    _ = (r.factorial : ℝ) * (((Fintype.card I : ℝ) ^ r)⁻¹) ^ 2 *
          ∑ p ∈ (Finset.univ : Finset I).piAntidiag r,
            (Nat.multinomial (Finset.univ : Finset I) p : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = (r.factorial : ℝ) / (Fintype.card I : ℝ) ^ r := by
        rw [hcard]
        field_simp

/-- **The uniform replica crowding floor.**  For a maximally projective spectrum carried by the
uniform weighting, the near-action mass at resolution `δ` is at least `9δ / (16(δ + 4σ√r))` minus
the multinomial permutation floor `r!/d^r`. -/
theorem fidelityReplicaNearActionMass_microcanonical_floor [Nonempty I]
    {energy : I → ℝ} (hmax : MaximallyProjectiveEnergy energy) (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    9 * δ / (16 * (δ + 4 * Real.sqrt (singleLevelSpectralVariance (microcanonicalWeight I) energy) *
          Real.sqrt r))
        - (r.factorial : ℝ) / (Fintype.card I : ℝ) ^ r
      ≤ fidelityReplicaNearActionMass (microcanonicalWeight I) energy r δ := by
  classical
  have hd : (0 : ℝ) < (Fintype.card I : ℝ) := by
    have hc : 0 < Fintype.card I := Fintype.card_pos
    exact_mod_cast hc
  have hpos : ∀ i, 0 < microcanonicalWeight I i := fun _ => by
    simp only [microcanonicalWeight]
    positivity
  have hnn : ∀ i, 0 ≤ microcanonicalWeight I i := fun i => (hpos i).le
  have hsum : ∑ i : I, microcanonicalWeight I i = 1 := by
    simp only [microcanonicalWeight]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hfloor : fidelityReplicaCollisionMass (microcanonicalWeight I) energy r
      = fidelityReplicaPermutationFloor (microcanonicalWeight I) r :=
    (all_fidelityReplicaCollisionMass_eq_floor_iff hpos energy).2 hmax r
  have hle := fidelityReplicaPermutationFloor_microcanonical_le (I := I) r
  have hmain := fidelityReplicaNearActionMass_crowding_floor_sigma_sqrt
    (weight := microcanonicalWeight I) (energy := energy) hnn hsum r hδ
  rw [hfloor] at hmain
  linarith

end GaloisForLFunctions.HTGeometry

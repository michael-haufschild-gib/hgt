import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceDilationEnergy

/-!
# Exact receiving capacity of the finite prime dilation form

The cofactor harmonic mass is the resistance of each prime coordinate.
Completing squares gives the exact minimum energy at prescribed charge
and the full excess energy above its unique minimizing coefficient vector.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- The coherent receiving charge of a finite prime-incidence packet. -/
def primeIncidenceReceivingCharge (P : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, b p * (Real.log p / p)

/-- The exact dual charge capacity of the finite dilation energy. -/
def primeIncidenceReceivingCapacity (P : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ P, (Real.log p / p) / (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))

private theorem cofactor_harmonic_pos {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    0 < ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ) := by
  apply sum_pos'
  · intro n _
    positivity
  · have hdiv : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa only [one_mul] using hpN)
    exact ⟨1, mem_Icc.mpr ⟨le_rfl, hdiv⟩, by norm_num⟩

/-- Every nonempty prime set below the horizon has strictly positive receiving capacity. -/
theorem primeIncidenceReceivingCapacity_pos {P : Finset ℕ} (hne : P.Nonempty)
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hPN : ∀ p ∈ P, p ≤ N) :
    0 < primeIncidenceReceivingCapacity P N := by
  unfold primeIncidenceReceivingCapacity
  apply sum_pos
  · intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast (hP p hp).one_lt)
    exact div_pos (div_pos hlog hpR) (cofactor_harmonic_pos (hP p hp).pos (hPN p hp))
  · exact hne

/-- The coefficient vector that realizes a prescribed receiving charge at minimum dilation energy. -/
def primeIncidenceCapacityMinimizer (P : Finset ℕ) (N : ℕ) (t : ℝ) (p : ℕ) : ℝ :=
  t / (primeIncidenceReceivingCapacity P N * (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)))

/-- Completing squares identifies the exact cost of charge and every direction of excess energy. -/
theorem primeIncidence_energy_charge_decomposition {P : Finset ℕ} (hne : P.Nonempty)
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hPN : ∀ p ∈ P, p ≤ N) (b : ℕ → ℝ) :
    jumpEnergy N (incidencePacket P b) =
      primeIncidenceReceivingCharge P b ^ 2 / primeIncidenceReceivingCapacity P N +
        jumpEnergy N (incidencePacket P (fun p => b p -
          primeIncidenceCapacityMinimizer P N (primeIncidenceReceivingCharge P b) p)) := by
  let C := primeIncidenceReceivingCapacity P N
  let q := primeIncidenceReceivingCharge P b
  have hC : C ≠ 0 := (primeIncidenceReceivingCapacity_pos hne hP hPN).ne'
  have hpoint (p : ℕ) (hp : p ∈ P) :
      b p ^ 2 * (Real.log p / p * (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) -
        (b p - primeIncidenceCapacityMinimizer P N q p) ^ 2 *
          (Real.log p / p * (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) =
      (2 * q / C) * (b p * (Real.log p / p)) -
        (q ^ 2 / C ^ 2) * ((Real.log p / p) / (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) := by
    have hH := (cofactor_harmonic_pos (hP p hp).pos (hPN p hp)).ne'
    change b p ^ 2 * (Real.log p / p * (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) -
      (b p - q / (C * (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)))) ^ 2 *
        (Real.log p / p * (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) = _
    field_simp [hC, hH]
    ring
  have hsum := sum_congr rfl hpoint
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum] at hsum
  change (∑ p ∈ P, b p ^ 2 * (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) -
    (∑ p ∈ P, (b p - primeIncidenceCapacityMinimizer P N q p) ^ 2 *
      (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) =
        (2 * q / C) * q - (q ^ 2 / C ^ 2) * C at hsum
  have hright : (2 * q / C) * q - (q ^ 2 / C ^ 2) * C = q ^ 2 / C := by
    field_simp [hC]
    ring
  rw [hright] at hsum
  rw [jumpEnergy_incidencePacket_diagonal hP, jumpEnergy_incidencePacket_diagonal hP]
  change _ = q ^ 2 / C + _
  linarith only [hsum]

/-- The capacity minimizer retains the prescribed receiving charge exactly. -/
theorem primeIncidenceCapacityMinimizer_charge {P : Finset ℕ} (hne : P.Nonempty)
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hPN : ∀ p ∈ P, p ≤ N) (t : ℝ) :
    primeIncidenceReceivingCharge P (primeIncidenceCapacityMinimizer P N t) = t := by
  have hC := (primeIncidenceReceivingCapacity_pos hne hP hPN).ne'
  calc
    _ = (t / primeIncidenceReceivingCapacity P N) * primeIncidenceReceivingCapacity P N := by
      change (∑ p ∈ P, primeIncidenceCapacityMinimizer P N t p * (Real.log p / p)) =
        (t / primeIncidenceReceivingCapacity P N) *
          ∑ p ∈ P, (Real.log p / p) / (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))
      rw [mul_sum]
      exact sum_congr rfl fun p _ => by
        unfold primeIncidenceCapacityMinimizer
        rw [div_mul_eq_div_div]
        ring
    _ = t := div_mul_cancel₀ _ hC

/-- The minimum dilation energy at charge `t` is exactly `t²/capacity`. -/
theorem primeIncidenceCapacityMinimizer_energy {P : Finset ℕ} (hne : P.Nonempty)
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hPN : ∀ p ∈ P, p ≤ N) (t : ℝ) :
    jumpEnergy N (incidencePacket P (primeIncidenceCapacityMinimizer P N t)) =
      t ^ 2 / primeIncidenceReceivingCapacity P N := by
  have hC := (primeIncidenceReceivingCapacity_pos hne hP hPN).ne'
  rw [jumpEnergy_incidencePacket_diagonal hP]
  calc
    _ = (t ^ 2 / primeIncidenceReceivingCapacity P N ^ 2) *
        primeIncidenceReceivingCapacity P N := by
      change (∑ p ∈ P, primeIncidenceCapacityMinimizer P N t p ^ 2 *
          (Real.log p / p * (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)))) =
        (t ^ 2 / primeIncidenceReceivingCapacity P N ^ 2) *
          ∑ p ∈ P, (Real.log p / p) / (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      have hH := (cofactor_harmonic_pos (hP p hp).pos (hPN p hp)).ne'
      unfold primeIncidenceCapacityMinimizer
      field_simp [hC, hH]
    _ = _ := by field_simp [hC]

/-- Charge is bounded by the exact finite capacity times dilation energy. -/
theorem primeIncidence_charge_sq_le_capacity_energy {P : Finset ℕ} (hne : P.Nonempty)
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hPN : ∀ p ∈ P, p ≤ N) (b : ℕ → ℝ) :
    primeIncidenceReceivingCharge P b ^ 2 ≤
      primeIncidenceReceivingCapacity P N * jumpEnergy N (incidencePacket P b) := by
  have hC := primeIncidenceReceivingCapacity_pos hne hP hPN
  have h := primeIncidence_energy_charge_decomposition hne hP hPN b
  have hnonneg := jumpEnergy_nonneg N (incidencePacket P (fun p => b p -
    primeIncidenceCapacityMinimizer P N (primeIncidenceReceivingCharge P b) p))
  have hcost : primeIncidenceReceivingCharge P b ^ 2 / primeIncidenceReceivingCapacity P N ≤
      jumpEnergy N (incidencePacket P b) := by linarith only [h, hnonneg]
  exact (div_le_iff₀ hC).mp hcost |>.trans_eq (mul_comm _ _)

/-- The finite prime dilation form is strictly positive in every retained prime coefficient. -/
theorem jumpEnergy_incidencePacket_eq_zero_iff {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hPN : ∀ p ∈ P, p ≤ N) (b : ℕ → ℝ) :
    jumpEnergy N (incidencePacket P b) = 0 ↔ ∀ p ∈ P, b p = 0 := by
  rw [jumpEnergy_incidencePacket_diagonal hP]
  constructor
  · intro hz p hp
    by_contra hb
    have hpos : 0 < ∑ q ∈ P,
        b q ^ 2 * (Real.log q / q * (∑ n ∈ Icc 1 (N / q), 1 / (n : ℝ))) := by
      apply sum_pos'
      · intro q hq
        have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (hP q hq).one_le)
        positivity
      · have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
        have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast (hP p hp).one_lt)
        exact ⟨p, hp, mul_pos (sq_pos_of_ne_zero hb)
          (mul_pos (div_pos hlog hpR) (cofactor_harmonic_pos (hP p hp).pos (hPN p hp)))⟩
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  · intro hb
    exact sum_eq_zero fun p hp => by rw [hb p hp, zero_pow (by omega : 2 ≠ 0), zero_mul]

/-- Equality in the receiving-capacity bound characterizes every minimizing coefficient. -/
theorem primeIncidence_energy_eq_charge_cost_iff {P : Finset ℕ} (hne : P.Nonempty)
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hPN : ∀ p ∈ P, p ≤ N) (b : ℕ → ℝ) :
    jumpEnergy N (incidencePacket P b) =
        primeIncidenceReceivingCharge P b ^ 2 / primeIncidenceReceivingCapacity P N ↔
      ∀ p ∈ P, b p = primeIncidenceCapacityMinimizer P N (primeIncidenceReceivingCharge P b) p := by
  have hd := primeIncidence_energy_charge_decomposition hne hP hPN b
  have hz := jumpEnergy_incidencePacket_eq_zero_iff hP hPN
    (fun p => b p - primeIncidenceCapacityMinimizer P N (primeIncidenceReceivingCharge P b) p)
  constructor
  · intro he
    have hzero : jumpEnergy N (incidencePacket P (fun p => b p -
        primeIncidenceCapacityMinimizer P N (primeIncidenceReceivingCharge P b) p)) = 0 := by
      linarith only [hd, he]
    intro p hp
    exact sub_eq_zero.mp ((hz.mp hzero) p hp)
  · intro he
    have hzero := hz.mpr (fun p hp => sub_eq_zero.mpr (he p hp))
    linarith only [hd, hzero]

#print axioms primeIncidence_energy_charge_decomposition
#print axioms primeIncidenceCapacityMinimizer_charge
#print axioms primeIncidenceCapacityMinimizer_energy
#print axioms primeIncidence_energy_eq_charge_cost_iff

end GaloisForLFunctions.ArithmeticCouplingTheory

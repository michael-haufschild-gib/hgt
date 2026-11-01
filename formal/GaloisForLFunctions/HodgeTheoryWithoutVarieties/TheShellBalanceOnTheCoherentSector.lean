import GaloisForLFunctions.ArithmeticCouplingTheory.TheAffineIncidenceEnergy

/-!
# The shell balance on the coherent sector

At overlap `c > 1` the complete Weil form contains the non-ratio part `½A_N − Σ_n d_n F(n)²` (ACoT):
the affine Dirichlet energy of the successor–dilation shells `(n, kn + h)` against their degree.
Joint payment of the shell degree (review Q2b) asks when the first dominates the second. On the
coherent sector of prime-incidence packets `F_b(n) = Σ_{p ∈ P} b_p([p ∣ n] − 1/p)` this is
decided exactly, shell by shell, over a complete period `L = ∏_{p ∈ P} p`.

* **Variance of the coherent sector** (`sum_range_incidencePacket_sq`): the period mean of `F_b²` is
  `Σ_p b_p² (1/p)(1 − 1/p)`, since the incidence coordinates of distinct primes are independent.
* **The shell balance law** (`shellBalance_eq`): for one shell `(k, h)`,
  `½·mean (F_b(kn + h) − F_b(n))² − mean F_b² = Σ_p b_p² (v_p/2 − (1/p)(1 − 1/p)) + ½(Σ_p b_p μ_p)²`,
  with the period variance `v_p` and mean `μ_p` of the affine event of `p`. Prime by prime:
  - a prime dividing neither `k` nor `h` contributes the **surplus** `b_p²/p²`
    (`shellBalance_of_coprime`);
  - a prime dividing `h` but not `k` contributes the **deficit** `−b_p²(1/p)(1 − 1/p)`: the shift is
    invisible modulo `p`;
  - a prime dividing `k` contributes `−½ b_p²(1/p)(1 − 1/p)` and enters the coherent square.
* **Exact balance in the mean** (`sum_shellBalance_eq_zero`): for a dilation ratio `k` coprime to
  the sector, the balance summed over a complete period of shifts `h` is **zero**. Surplus and
  deficit cancel exactly.

So joint payment of the shell degree has no margin in the bulk of the coherent sector. Its sign is
decided by the distribution of the shell shifts modulo the primes of the packet, i.e. by the shell
profile and its boundary, and by the ratios `k` that share primes with the packet. This is why the
review's Q2b is an estimate and not an identity.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

open GaloisForLFunctions.ArithmeticCouplingTheory

/-- The incidence coordinate `e_p(n) = [p ∣ n] − 1/p`. -/
def incidenceCoord (p n : ℕ) : ℝ := (if p ∣ n then 1 else 0) - 1 / p

theorem incidenceCoord_periodic (p : ℕ) : Function.Periodic (incidenceCoord p) p := fun n => by
  simp only [incidenceCoord, Nat.dvd_add_self_right]

theorem sum_range_incidenceCoord {p : ℕ} (hp : p.Prime) :
    ∑ a ∈ range p, incidenceCoord p a = 0 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [incidenceCoord, sum_sub_distrib, sum_range_dvd_self hp, sum_const, card_range,
    nsmul_eq_mul]
  field_simp
  ring

theorem sum_range_incidenceCoord_sq {p : ℕ} (hp : p.Prime) :
    ∑ a ∈ range p, incidenceCoord p a ^ 2 = 1 - 1 / p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsq : ∀ a, incidenceCoord p a ^ 2 =
      (1 - 2 / p) * (if p ∣ a then 1 else 0) + 1 / p ^ 2 := fun a => by
    simp only [incidenceCoord]
    split_ifs <;> field_simp <;> ring
  simp only [hsq, sum_add_distrib, ← mul_sum, sum_range_dvd_self hp, sum_const, card_range,
    nsmul_eq_mul]
  field_simp
  ring

/-- Independence of incidence coordinates over the period. -/
theorem sum_range_incidenceCoord_mul {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {p q : ℕ}
    (hp : p ∈ P) (hq : q ∈ P) :
    ∑ n ∈ range (incidencePeriod P), incidenceCoord p n * incidenceCoord q n =
      if p = q then (incidencePeriod P : ℝ) * ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ))) else (0 : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨m, hm⟩ := dvd_prod_of_mem (fun x => x) hp
    have hper : Function.Periodic (fun n => incidenceCoord p n * incidenceCoord p n) p :=
      fun n => by simp only [incidenceCoord_periodic p n]
    rw [if_pos rfl, incidencePeriod, hm, mul_comm p m, sum_range_mul_period hper]
    simp only [← sq]
    rw [sum_range_incidenceCoord_sq (hP p hp)]
    push_cast
    field_simp
  · have hcop : p.Coprime q := (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
    have hdvd : p * q ∣ incidencePeriod P := by
      have := prod_dvd_prod_of_subset {p, q} P (fun x => x) (by
        intro x hx; rcases mem_insert.mp hx with rfl | hx
        · exact hp
        · rw [mem_singleton.mp hx]; exact hq)
      rwa [prod_pair hpq] at this
    obtain ⟨m, hm⟩ := hdvd
    have hper : Function.Periodic (fun n => incidenceCoord p n * incidenceCoord q n) (p * q) :=
      fun n => by
        have h1 : incidenceCoord p (n + p * q) = incidenceCoord p n := by
          rw [mul_comm]; exact (incidenceCoord_periodic p).nat_mul q n
        have h2 : incidenceCoord q (n + p * q) = incidenceCoord q n :=
          (incidenceCoord_periodic q).nat_mul p n
        simp only [h1, h2]
    rw [if_neg hpq, hm, mul_comm (p * q) m, sum_range_mul_period hper,
      sum_range_mul_of_coprime hcop (incidenceCoord_periodic p) (incidenceCoord_periodic q),
      sum_range_incidenceCoord (hP p hp), zero_mul, mul_zero]

/-- **The variance of the coherent sector**: over a complete period,
`Σ_n F_b(n)² = L Σ_p b_p² (1/p)(1 − 1/p)`. -/
theorem sum_range_incidencePacket_sq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) :
    ∑ n ∈ range (incidencePeriod P), incidencePacket P b n ^ 2 =
      (incidencePeriod P : ℝ) * ∑ p ∈ P, b p ^ 2 * ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ))) := by
  have hexp : ∀ n, incidencePacket P b n ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, b p * b q * (incidenceCoord p n * incidenceCoord q n) := fun n => by
    rw [incidencePacket, sq, sum_mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by simp only [incidenceCoord]; ring
  simp only [hexp]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [sum_comm]
  rw [sum_congr rfl fun q hq => by rw [← mul_sum, sum_range_incidenceCoord_mul hP hp hq]]
  rw [sum_eq_single p (fun q _ hqp => by rw [if_neg (Ne.symm hqp), mul_zero])
    (fun h => absurd hp h), if_pos rfl]
  ring

/-- The **shell balance** of the shell `(k, h)` on the coherent sector: half the period mean of the
squared affine jump minus the period mean of `F_b²`. -/
def shellBalance (P : Finset ℕ) (b : ℕ → ℝ) (k h : ℕ) : ℝ :=
  (1 / 2) * ((∑ n ∈ range (incidencePeriod P),
      (incidencePacket P b (k * n + h) - incidencePacket P b n) ^ 2) / incidencePeriod P) -
    (∑ n ∈ range (incidencePeriod P), incidencePacket P b n ^ 2) / incidencePeriod P

/-- **The shell balance law.** -/
theorem shellBalance_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) (k h : ℕ) :
    shellBalance P b k h =
      ∑ p ∈ P, b p ^ 2 * (affineEventVariance k h p / 2 - (1 / p) * (1 - 1 / p)) +
        (1 / 2) * (∑ p ∈ P, b p * affineEventMean k h p) ^ 2 := by
  have hL : (incidencePeriod P : ℝ) ≠ 0 := by exact_mod_cast (incidencePeriod_pos hP).ne'
  rw [shellBalance, affineIncidenceEnergy_eq hP, sum_range_incidencePacket_sq hP,
    mul_div_cancel_left₀ _ hL]
  have hsplit : ∑ p ∈ P, b p ^ 2 * (affineEventVariance k h p / 2 - (1 / p) * (1 - 1 / p)) =
      (1 / 2) * ∑ p ∈ P, b p ^ 2 * affineEventVariance k h p -
        ∑ p ∈ P, b p ^ 2 * ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ))) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun p _ => by ring
  rw [hsplit]
  ring

/-- **Coprime shells pay with surplus.** If every prime of the sector divides neither `k` nor `h`,
the balance is `Σ_p b_p²/p² ≥ 0`. -/
theorem shellBalance_of_coprime {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) {k h : ℕ}
    (hkh : ∀ p ∈ P, ¬ p ∣ k ∧ ¬ p ∣ h) :
    shellBalance P b k h = ∑ p ∈ P, b p ^ 2 / (p : ℝ) ^ 2 := by
  have hμ : ∑ p ∈ P, b p * affineEventMean k h p = 0 :=
    sum_eq_zero fun p hp => by rw [affineEventMean_eq_zero (hP p hp) (hkh p hp).1, mul_zero]
  rw [shellBalance_eq hP, hμ, sq, mul_zero, mul_zero, add_zero]
  refine sum_congr rfl fun p hp => ?_
  rw [affineEventVariance_of_not_dvd (hP p hp) (hkh p hp).1 (hkh p hp).2]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  field_simp
  ring

/-- For `p ∤ k` and `p ∣ h` the shift is invisible modulo `p`: the affine event vanishes. -/
theorem affineEvent_eq_zero_of_dvd_shift {p : ℕ} (hp : p.Prime) {k h : ℕ} (hk : ¬ p ∣ k)
    (hh : p ∣ h) (n : ℕ) : affineEvent k h p n = 0 := by
  have : p ∣ k * n + h ↔ p ∣ n := by
    rw [Nat.dvd_add_left hh, hp.dvd_mul]
    exact ⟨fun h' => h'.resolve_left hk, Or.inr⟩
  simp only [affineEvent, this, sub_self]

theorem affineEventVariance_of_dvd_shift {p : ℕ} (hp : p.Prime) {k h : ℕ} (hk : ¬ p ∣ k)
    (hh : p ∣ h) : affineEventVariance k h p = 0 := by
  simp [affineEventVariance, affineEventSq, affineEventMean,
    affineEvent_eq_zero_of_dvd_shift hp hk hh]

/-- **Exact balance in the mean.** For a dilation ratio `k` coprime to the sector, the shell
balance summed over a complete period of shifts vanishes: surplus and deficit cancel. -/
theorem sum_shellBalance_eq_zero {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) {k : ℕ}
    (hk : ∀ p ∈ P, ¬ p ∣ k) :
    ∑ h ∈ range (incidencePeriod P), shellBalance P b k h = 0 := by
  have hterm : ∀ h, shellBalance P b k h = ∑ p ∈ P, b p ^ 2 *
      ((1 / (p : ℝ) ^ 2) - (if p ∣ h then 1 / (p : ℝ) else 0)) := by
    intro h
    have hμ : ∑ p ∈ P, b p * affineEventMean k h p = 0 :=
      sum_eq_zero fun p hp => by rw [affineEventMean_eq_zero (hP p hp) (hk p hp), mul_zero]
    rw [shellBalance_eq hP, hμ, sq, mul_zero, mul_zero, add_zero]
    refine sum_congr rfl fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
    by_cases hh : p ∣ h
    · rw [affineEventVariance_of_dvd_shift (hP p hp) (hk p hp) hh, if_pos hh]
      field_simp
      ring
    · rw [affineEventVariance_of_not_dvd (hP p hp) (hk p hp) hh, if_neg hh]
      field_simp
      ring
  simp only [hterm]
  rw [sum_comm]
  refine sum_eq_zero fun p hp => ?_
  rw [← mul_sum, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  obtain ⟨m, hm⟩ := dvd_prod_of_mem (fun x => x) hp
  have hper : Function.Periodic (fun h => if p ∣ h then 1 / (p : ℝ) else 0) p := fun h => by
    simp only [Nat.dvd_add_self_right]
  rw [incidencePeriod, hm, mul_comm p m, sum_range_mul_period hper]
  have hone : ∑ a ∈ range p, (if p ∣ a then 1 / (p : ℝ) else 0) = 1 / p := by
    have hfac : ∀ a, (if p ∣ a then 1 / (p : ℝ) else 0) = 1 / p * (if p ∣ a then 1 else 0) :=
      fun a => by split_ifs <;> ring
    rw [sum_congr rfl fun a _ => hfac a, ← mul_sum, sum_range_dvd_self (hP p hp), mul_one]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  rw [hone]
  push_cast
  field_simp
  ring

end GaloisForLFunctions.HodgeTheoryWithoutVarieties

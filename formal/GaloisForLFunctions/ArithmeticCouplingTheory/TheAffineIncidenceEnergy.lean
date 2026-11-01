import GaloisForLFunctions.ArithmeticCouplingTheory.TheMertensPolarization
import GaloisForLFunctions.HTGeometry.CoprimePeriodInjectionNormality

/-!
# The affine incidence energy: sum–product energy of divisibility events

At overlap `c > 1` the complete Weil matrix pairs `n` not only with its dilates `kn` but with the
affine images `kn + h` (successor shells). On the coherent prime sector the affine jump is a sum of
**affine incidence events**

  `F_b(kn + h) − F_b(n) = Σ_{p ∈ P} b_p D_p(n)`,  `D_p(n) = [p ∣ kn + h] − [p ∣ n]`
  (`incidencePacket_affine_jump`),

each periodic modulo its prime (`affineEvent_periodic`). Over a complete period `L = ∏_{p ∈ P} p`,
events of distinct primes are independent (Chinese remainder theorem;
`sum_range_affineEvent_mul`), and the mean affine energy is an exact sum of squares
(`affineIncidenceEnergy_eq`):

  `mean_{n < L} (F_b(kn + h) − F_b(n))² = Σ_p b_p² v_p + (Σ_p b_p μ_p)²`,

with `μ_p` the period mean and `v_p ≥ 0` the period variance of `D_p`. Successor and dilation
decouple divisibility: for `p ∤ k` the event has mean zero (`affineEventMean_eq_zero`), so only the
primes of `k` carry the coherent part, with `μ_p = [p ∣ h] − 1/p` (`affineEventMean_of_dvd`). Every
prime dividing neither `k` nor `h` contributes exactly `2/p` (`affineEventVariance_of_not_dvd`).
For `h = 0` and `k = q^j` this is the dilation jump `b_q²(1 − 1/q)` of the Mertens polarization.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- Sums over a multiple of a period. -/
theorem sum_range_mul_period {g : ℕ → ℝ} {P : ℕ} (hg : Function.Periodic g P) (m : ℕ) :
    ∑ n ∈ range (m * P), g n = m * ∑ n ∈ range P, g n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have h : ∑ x ∈ range P, g (m * P + x) = ∑ x ∈ range P, g x :=
      sum_congr rfl fun x _ => by rw [add_comm]; exact hg.nat_mul m x
    rw [h]; push_cast; ring

/-- **Chinese remainder for means**: periodic functions of coprime periods are independent. -/
theorem sum_range_mul_of_coprime {a b : ℕ} (hab : a.Coprime b) {f g : ℕ → ℝ}
    (hf : Function.Periodic f a) (hg : Function.Periodic g b) :
    ∑ t ∈ range (a * b), f t * g t = (∑ t ∈ range a, f t) * ∑ t ∈ range b, g t := by
  have h := HTGeometry.FirstPowerInjection.sum_range_mul_coprime hab (f := fun t => (f t : ℂ))
    (g := fun t => (g t : ℂ)) (fun n => by simp [hf n]) (fun n => by simp [hg n])
  exact_mod_cast h

/-- The affine incidence event `D_p(n) = [p ∣ kn + h] − [p ∣ n]`. -/
def affineEvent (k h p n : ℕ) : ℝ := (if p ∣ k * n + h then 1 else 0) - (if p ∣ n then 1 else 0)

theorem affineEvent_periodic (k h p : ℕ) : Function.Periodic (affineEvent k h p) p := fun n => by
  have h1 : p ∣ k * (n + p) + h ↔ p ∣ k * n + h := by
    rw [show k * (n + p) + h = k * n + h + k * p by ring]
    exact Nat.dvd_add_left (dvd_mul_left p k)
  have h2 : p ∣ n + p ↔ p ∣ n := Nat.dvd_add_self_right
  simp only [affineEvent, h1, h2]

/-- **The affine jump of an incidence packet is a sum of affine events.** -/
theorem incidencePacket_affine_jump (P : Finset ℕ) (b : ℕ → ℝ) (k h n : ℕ) :
    incidencePacket P b (k * n + h) - incidencePacket P b n = ∑ p ∈ P, b p * affineEvent k h p n := by
  rw [incidencePacket, incidencePacket, ← sum_sub_distrib]
  exact sum_congr rfl fun p _ => by simp only [affineEvent]; ring

/-- The period mean `μ_p` of an affine event. -/
def affineEventMean (k h p : ℕ) : ℝ := (∑ a ∈ range p, affineEvent k h p a) / p

/-- The period second moment of an affine event. -/
def affineEventSq (k h p : ℕ) : ℝ := (∑ a ∈ range p, affineEvent k h p a ^ 2) / p

/-- The period variance `v_p` of an affine event. -/
def affineEventVariance (k h p : ℕ) : ℝ := affineEventSq k h p - affineEventMean k h p ^ 2

theorem affineEventVariance_eq {k h p : ℕ} (hp : 0 < p) :
    affineEventVariance k h p =
      (∑ a ∈ range p, (affineEvent k h p a - affineEventMean k h p) ^ 2) / p := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsum : ∑ a ∈ range p, (affineEvent k h p a - affineEventMean k h p) ^ 2 =
      ∑ a ∈ range p, affineEvent k h p a ^ 2 -
        2 * affineEventMean k h p * ∑ a ∈ range p, affineEvent k h p a +
          p * affineEventMean k h p ^ 2 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      mul_sum]
    refine congrArg₂ _ (congrArg₂ _ rfl (sum_congr rfl fun a _ => by ring)) rfl
  rw [hsum, affineEventVariance, affineEventSq]
  have hmean : ∑ a ∈ range p, affineEvent k h p a = p * affineEventMean k h p := by
    rw [affineEventMean]; field_simp
  rw [hmean]
  field_simp
  ring

theorem affineEventVariance_nonneg {k h p : ℕ} (hp : 0 < p) : 0 ≤ affineEventVariance k h p := by
  rw [affineEventVariance_eq hp]
  exact div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

/-- One residue class modulo a prime. -/
theorem sum_range_dvd_self {p : ℕ} (hp : p.Prime) :
    ∑ a ∈ range p, (if p ∣ a then (1 : ℝ) else 0) = 1 := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have : (range p).filter (fun a => p ∣ a) = {0} := by
    ext a
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨ha, hd⟩; exact Nat.eq_zero_of_dvd_of_lt hd ha
    · rintro rfl; exact ⟨hp.pos, dvd_zero p⟩
  rw [this, card_singleton, Nat.cast_one]

/-- For `p ∤ k`, exactly one residue `a < p` solves `p ∣ ka + h`. -/
theorem sum_range_dvd_affine {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : ¬p ∣ k) (h : ℕ) :
    ∑ a ∈ range p, (if p ∣ k * a + h then (1 : ℝ) else 0) = 1 := by
  haveI := Fact.mk hp
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have hk' : (k : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  set a₀ : ℕ := (-(h : ZMod p) * (k : ZMod p)⁻¹).val
  have hiff : ∀ a < p, (p ∣ k * a + h ↔ a = a₀) := fun a ha => by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    constructor
    · intro h0
      have : (a : ZMod p) = -(h : ZMod p) * (k : ZMod p)⁻¹ := by
        field_simp; linear_combination h0
      have h1 := congrArg ZMod.val this
      rwa [ZMod.val_natCast, Nat.mod_eq_of_lt ha] at h1
    · intro hEq
      rw [hEq, ZMod.natCast_zmod_val]
      field_simp; ring
  have : (range p).filter (fun a => p ∣ k * a + h) = {a₀} := by
    ext a
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨ha, hd⟩; exact (hiff a ha).mp hd
    · rintro rfl; exact ⟨ZMod.val_lt _, (hiff _ (ZMod.val_lt _)).mpr rfl⟩
  rw [this, card_singleton, Nat.cast_one]

/-- **Successor and dilation decouple**: for `p ∤ k` the affine event has mean zero. -/
theorem affineEventMean_eq_zero {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : ¬p ∣ k) (h : ℕ) :
    affineEventMean k h p = 0 := by
  simp only [affineEventMean, affineEvent, sum_sub_distrib, sum_range_dvd_affine hp hk h,
    sum_range_dvd_self hp, sub_self, zero_div]

/-- **The coherent part**: for `p ∣ k` the event reads `[p ∣ h] − [p ∣ n]`, of mean `[p ∣ h] − 1/p`. -/
theorem affineEventMean_of_dvd {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : p ∣ k) (h : ℕ) :
    affineEventMean k h p = (if p ∣ h then 1 else 0) - 1 / p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hc : ∀ a, (p ∣ k * a + h ↔ p ∣ h) := fun a =>
    Nat.dvd_add_right (dvd_mul_of_dvd_left hk a)
  rw [affineEventMean]
  simp only [affineEvent, sum_sub_distrib, hc, sum_const, card_range, nsmul_eq_mul,
    sum_range_dvd_self hp]
  rw [sub_div, mul_div_cancel_left₀ _ hp0]

/-- **Every prime dividing neither `k` nor `h` contributes `2/p`.** -/
theorem affineEventVariance_of_not_dvd {p : ℕ} (hp : p.Prime) {k h : ℕ} (hk : ¬p ∣ k)
    (hh : ¬p ∣ h) : affineEventVariance k h p = 2 / p := by
  have hsq : ∀ a ∈ range p, affineEvent k h p a ^ 2 =
      (if p ∣ k * a + h then 1 else 0) + (if p ∣ a then 1 else 0) := fun a ha => by
    have hab : ¬(p ∣ k * a + h ∧ p ∣ a) := by
      rintro ⟨h1, h2⟩
      have ha0 : a = 0 := Nat.eq_zero_of_dvd_of_lt h2 (mem_range.mp ha)
      subst ha0
      simp at h1
      exact hh h1
    simp only [affineEvent]
    by_cases h1 : p ∣ k * a + h <;> by_cases h2 : p ∣ a
    · exact absurd ⟨h1, h2⟩ hab
    all_goals simp [h1, h2]
  rw [affineEventVariance, affineEventSq, affineEventMean_eq_zero hp hk h, sum_congr rfl hsq,
    sum_add_distrib, sum_range_dvd_affine hp hk h, sum_range_dvd_self hp]
  ring

/-- The period of the coherent sector, `L = ∏_{p ∈ P} p`. -/
def incidencePeriod (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

theorem incidencePeriod_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) : 0 < incidencePeriod P :=
  prod_pos fun p hp => (hP p hp).pos

/-- **Independence of affine events over the period.** -/
theorem sum_range_affineEvent_mul {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (k h : ℕ) {p q : ℕ}
    (hp : p ∈ P) (hq : q ∈ P) :
    ∑ n ∈ range (incidencePeriod P), affineEvent k h p n * affineEvent k h q n =
      incidencePeriod P * (if p = q then affineEventSq k h p
        else affineEventMean k h p * affineEventMean k h q) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (hP q hq).ne_zero
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨m, hm⟩ := dvd_prod_of_mem (fun x => x) hp
    have hper : Function.Periodic (fun n => affineEvent k h p n * affineEvent k h p n) p :=
      fun n => by simp only [affineEvent_periodic k h p n]
    rw [if_pos rfl, incidencePeriod, hm, mul_comm p m, sum_range_mul_period hper, affineEventSq]
    simp only [← sq]
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
    have hper : Function.Periodic (fun n => affineEvent k h p n * affineEvent k h q n) (p * q) :=
      fun n => by
        have h1 : affineEvent k h p (n + p * q) = affineEvent k h p n := by
          rw [mul_comm]; exact (affineEvent_periodic k h p).nat_mul q n
        have h2 : affineEvent k h q (n + p * q) = affineEvent k h q n :=
          (affineEvent_periodic k h q).nat_mul p n
        simp only [h1, h2]
    rw [if_neg hpq, hm, mul_comm (p * q) m, sum_range_mul_period hper,
      sum_range_mul_of_coprime hcop (affineEvent_periodic k h p) (affineEvent_periodic k h q),
      affineEventMean, affineEventMean]
    push_cast
    field_simp

/-- **The mean affine incidence energy is a sum of squares.** Over a complete period of the coherent
sector, `mean (F_b(kn + h) − F_b(n))² = Σ_p b_p² v_p + (Σ_p b_p μ_p)²`. -/
theorem affineIncidenceEnergy_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) (k h : ℕ) :
    (∑ n ∈ range (incidencePeriod P),
        (incidencePacket P b (k * n + h) - incidencePacket P b n) ^ 2) / incidencePeriod P =
      ∑ p ∈ P, b p ^ 2 * affineEventVariance k h p +
        (∑ p ∈ P, b p * affineEventMean k h p) ^ 2 := by
  set L := incidencePeriod P
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (incidencePeriod_pos hP).ne'
  set μ := affineEventMean k h
  set v := affineEventVariance k h
  have hexp : ∀ n, (incidencePacket P b (k * n + h) - incidencePacket P b n) ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, b p * b q * (affineEvent k h p n * affineEvent k h q n) := fun n => by
    rw [incidencePacket_affine_jump, sq, sum_mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring
  have h2 : ∑ n ∈ range L, ∑ p ∈ P, ∑ q ∈ P,
      b p * b q * (affineEvent k h p n * affineEvent k h q n) =
      ∑ p ∈ P, ∑ q ∈ P, b p * b q * ∑ n ∈ range L, affineEvent k h p n * affineEvent k h q n := by
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun q _ => (mul_sum _ _ _).symm
  have h3 : ∀ p ∈ P, ∀ q ∈ P,
      b p * b q * ∑ n ∈ range L, affineEvent k h p n * affineEvent k h q n =
        L * ((b p * μ p) * (b q * μ q) + if p = q then b p ^ 2 * v p else 0) :=
    fun p hp q hq => by
      rw [sum_range_affineEvent_mul hP k h hp hq]
      by_cases hpq : p = q
      · subst hpq; simp only [↓reduceIte, v, μ, affineEventVariance]; ring
      · simp only [if_neg hpq]; ring
  have e1 : ∑ p ∈ P, ∑ q ∈ P, (L : ℝ) * ((b p * μ p) * (b q * μ q)) =
      L * (∑ p ∈ P, b p * μ p) ^ 2 := by
    rw [sq, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun p _ => (mul_sum _ _ _).symm
  have e2 : ∑ p ∈ P, ∑ q ∈ P, (L : ℝ) * (if p = q then b p ^ 2 * v p else 0) =
      L * ∑ p ∈ P, b p ^ 2 * v p := by
    rw [mul_sum]
    exact sum_congr rfl fun p hp => by rw [← mul_sum, sum_ite_eq, if_pos hp]
  rw [sum_congr rfl fun n _ => hexp n, h2,
    sum_congr rfl fun p hp => sum_congr rfl fun q hq => h3 p hp q hq]
  simp only [mul_add, sum_add_distrib, e1, e2]
  field_simp
  ring

end GaloisForLFunctions.ArithmeticCouplingTheory

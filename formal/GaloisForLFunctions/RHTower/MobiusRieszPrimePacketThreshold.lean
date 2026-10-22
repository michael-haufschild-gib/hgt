import GaloisForLFunctions.RHTower.MobiusRieszSmoothingThreshold
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusRieszPrimeCellSign
import GaloisForLFunctions.RHTower.ThetaCutoffCommutatorCofinalLimit

/-!
# Sharp smoothing threshold for finite Möbius prime packets

The literal square-root Riesz packet, including its cutoff, equals a normalized
causal finite-difference profile. For a nonempty set of k primes, its r-fold
logarithmic primitive is everywhere nonnegative exactly when k - 1 ≤ r.
Every smaller order has a negative value on the positive ray, so no fixed order
makes all finite prime packets nonnegative. This does not settle the signed
cancellation estimates required for RH.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.MobiusRieszSmoothing

def primeShifts (P : List ℕ) : List ℝ :=
  P.map (fun p : ℕ => Real.log (Real.sqrt (p : ℝ)))

def rootClock (M n : ℕ) : ℝ := Real.log (Real.sqrt M) - Real.log (Real.sqrt n)

/-- Successive literal prime pairings of the original cutoff-preserving Riesz atom. -/
def literalPacket : List ℕ → ℕ → ℕ → ℝ
  | [], M, n => MobiusRieszCancellation.atom M n 1
  | p :: P, M, n => literalPacket P M n - literalPacket P M (n * p)

theorem atom_eq_normalized_hinge {M n : ℕ} (hM : 1 ≤ M) (hn : 1 ≤ n) :
    MobiusRieszCancellation.atom M n 1 = Real.sqrt M * hinge (rootClock M n) := by
  have hMs : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hns : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have he : Real.exp (-(rootClock M n)) = Real.sqrt n / Real.sqrt M := by
    rw [show -(rootClock M n) = Real.log (Real.sqrt n) - Real.log (Real.sqrt M) by
      dsimp [rootClock]; ring]
    rw [Real.exp_sub, Real.exp_log hns, Real.exp_log hMs]
  rw [MobiusRieszCancellation.atom_eq_positivePart, Nat.mul_one, hinge, he,
    mul_max_of_nonneg _ _ hMs.le, mul_zero]
  congr 1
  field_simp

theorem rootClock_mul {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) (M : ℕ) :
    rootClock M (n * p) = rootClock M n - Real.log (Real.sqrt p) := by
  have hns : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hps : Real.sqrt (p : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  rw [rootClock, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n), Real.log_mul hns hps]
  dsimp [rootClock]
  ring

/-- The logarithmic packet is exactly the normalized literal finite prime cancellation. -/
theorem literalPacket_eq_normalized (P : List ℕ) (hP : ∀ p ∈ P, 1 ≤ p)
    {M n : ℕ} (hM : 1 ≤ M) (hn : 1 ≤ n) :
    literalPacket P M n = Real.sqrt M * packet (primeShifts P) (rootClock M n) := by
  induction P generalizing n with
  | nil => exact atom_eq_normalized_hinge hM hn
  | cons p P ih =>
      have hp := hP p (by simp)
      have hrest : ∀ q ∈ P, 1 ≤ q := fun q hq => hP q (by simp [hq])
      have hnp : 1 ≤ n * p := by nlinarith
      rw [literalPacket, ih hrest hn, ih hrest hnp, rootClock_mul hn hp]
      change _ = Real.sqrt M *
        (packet (primeShifts P) (rootClock M n) -
          packet (primeShifts P) (rootClock M n - Real.log (Real.sqrt p)))
      ring

theorem primeShifts_pos {P : List ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ∀ a ∈ primeShifts P, 0 < a := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  apply Real.log_pos
  have hs := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)
    (show (1 : ℝ) < p by exact_mod_cast (hP p hp).one_lt)
  simpa using hs

/-- The smoothing cost is exactly the number of literal prime-pair operations minus one. -/
theorem prime_packet_smoothing_threshold {P : List ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hne : P ≠ []) (r : ℕ) :
    (∀ t, 0 ≤ smoothed (primeShifts P) r t) ↔ P.length - 1 ≤ r := by
  have hsne : primeShifts P ≠ [] := by
    intro hz
    cases P with
    | nil => exact hne rfl
    | cons p P => simp [primeShifts] at hz
  simpa only [primeShifts, List.length_map] using
    smoothing_threshold (primeShifts_pos hP) hsne r

/-- The two-prime instance is the existing literal Möbius divisor cell, including its cutoff. -/
theorem literalPacket_pair_eq_primeCell (M n p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    literalPacket [p, q] M n = MobiusRieszCancellation.primeCell M n p q := by
  have hcop : p.Coprime q := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))
  have hmu : ArithmeticFunction.moebius (p * q) = 1 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_prime hq]
    ring
  have hppq : p ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt]
  have hqpq : q ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt]
  have hone : 1 ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt]
  simp [MobiusRieszCancellation.primeCell, Ne.symm hp.ne_one, Ne.symm hq.ne_one,
    hpq, hppq, hqpq, hone, hmu, ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hq, literalPacket,
    MobiusRieszCancellation.atom_eq_positivePart, Nat.mul_assoc]
  ring

/-- Expanding the actual prime pairings preserves every cutoff atom. -/
theorem literalPacket_eq_powerset (P : List ℕ) (hnd : P.Nodup) (M n : ℕ) :
    literalPacket P M n =
      ∑ S ∈ P.toFinset.powerset, (-1 : ℝ) ^ S.card *
        MobiusRieszCancellation.atom M n (∏ p ∈ S, p) := by
  classical
  induction P generalizing n with
  | nil => simp [literalPacket]
  | cons p P ih =>
      have hnd' := List.nodup_cons.mp hnd
      have hp : p ∉ P.toFinset := by simpa using hnd'.1
      rw [literalPacket, ih hnd'.2, ih hnd'.2, List.toFinset_cons,
        Finset.sum_powerset_insert hp]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S hS
      have hpS : p ∉ S := fun h => hp (Finset.mem_powerset.mp hS h)
      have hcard : (insert p S).card = S.card + 1 := by simp [hpS]
      rw [hcard, Finset.prod_insert hpS, pow_succ]
      have ha : MobiusRieszCancellation.atom M (n * p) (∏ q ∈ S, q) =
          MobiusRieszCancellation.atom M n (p * ∏ q ∈ S, q) := by
        simp only [MobiusRieszCancellation.atom, Nat.mul_assoc]
      rw [← ha]
      ring

/-- The finite prime packet is the literal Möbius sum on its prime-factor support. -/
theorem literalPacket_eq_moebius (P : List ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hnd : P.Nodup) (M n : ℕ) :
    literalPacket P M n =
      ∑' d : ℕ, if d ≠ 0 ∧ d.primeFactors ⊆ P.toFinset then
        (ArithmeticFunction.moebius d : ℝ) * MobiusRieszCancellation.atom M n d else 0 := by
  rw [literalPacket_eq_powerset P hnd]
  exact sum_powerset_eq_tsum_moebius P.toFinset
    (fun p hp => hP p (List.mem_toFinset.mp hp))
    (fun d => MobiusRieszCancellation.atom M n d)

theorem normalized_packet_eq_moebius (P : List ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hnd : P.Nodup) {M n : ℕ} (hM : 1 ≤ M) (hn : 1 ≤ n) :
    Real.sqrt M * packet (primeShifts P) (rootClock M n) =
      ∑' d : ℕ, if d ≠ 0 ∧ d.primeFactors ⊆ P.toFinset then
        (ArithmeticFunction.moebius d : ℝ) * MobiusRieszCancellation.atom M n d else 0 := by
  rw [← literalPacket_eq_normalized P (fun p hp => (hP p hp).one_lt.le) hM hn]
  exact literalPacket_eq_moebius P hP hnd M n

def finiteProfile (P : Finset ℕ) : ℝ → ℝ := packet (primeShifts P.toList)

def finiteSmoothed (P : Finset ℕ) (r : ℕ) : ℝ → ℝ := primIter r (finiteProfile P)

/-- Exact arithmetic realization of the finite-prime continuous profile. -/
theorem finiteProfile_moebius (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {M n : ℕ} (hM : 1 ≤ M) (hn : 1 ≤ n) :
    Real.sqrt M * finiteProfile P (rootClock M n) =
      ∑' d : ℕ, if d ≠ 0 ∧ d.primeFactors ⊆ P then
        (ArithmeticFunction.moebius d : ℝ) * MobiusRieszCancellation.atom M n d else 0 := by
  have h := normalized_packet_eq_moebius P.toList
    (fun p hp => hP p (by simpa using hp)) (Finset.nodup_toList P) hM hn
  simpa [finiteProfile] using h

/-- Sharp positivity threshold for the literal finite Möbius prime packet. -/
theorem finitePrime_smoothing_threshold {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hne : P.Nonempty) (r : ℕ) :
    (∀ t, 0 ≤ finiteSmoothed P r t) ↔ P.card - 1 ≤ r := by
  have hlist : ∀ p ∈ P.toList, p.Prime := fun p hp => hP p (by simpa using hp)
  have hlne : P.toList ≠ [] := by
    intro hz
    obtain ⟨p, hp⟩ := hne
    have hm : p ∈ P.toList := by simpa using hp
    simp [hz] at hm
  simpa [finiteSmoothed, finiteProfile, smoothed] using
    prime_packet_smoothing_threshold hlist hlne r

/-- Fixed smoothing order cannot ensure positivity once the prime set is too large. -/
theorem finitePrime_exists_negative_of_card {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {r : ℕ} (hr : r + 1 < P.card) : ∃ t, finiteSmoothed P r t < 0 := by
  have hne : P.Nonempty := Finset.card_pos.mp (by omega)
  by_contra h
  have hnonneg : ∀ t, 0 ≤ finiteSmoothed P r t := by simpa using h
  have hle := (finitePrime_smoothing_threshold hP hne r).mp hnonneg
  omega

/-- Negative values occur at positive physical logarithmic scale. -/
theorem finitePrime_exists_negative_on_positive_ray {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {r : ℕ} (hr : r + 1 < P.card) :
    ∃ t, 0 < t ∧ finiteSmoothed P r t < 0 := by
  obtain ⟨t, ht⟩ := finitePrime_exists_negative_of_card hP hr
  have hlist : ∀ p ∈ P.toList, p.Prime := fun p hp => hP p (by simpa using hp)
  have hc : Causal (finiteSmoothed P r) :=
    causal_smoothed (A := primeShifts P.toList)
      (fun a ha => (primeShifts_pos hlist a ha).le) r
  refine ⟨t, ?_, ht⟩
  by_contra h
  have hz := hc t (le_of_not_gt h)
  rw [hz] at ht
  exact (lt_irrefl 0) ht

/-- No fixed number of logarithmic integrations makes every finite prime packet positive. -/
theorem no_fixed_prime_smoothing_order :
    ¬ ∃ r : ℕ, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.Nonempty →
      ∀ t : ℝ, 0 ≤ t → 0 ≤ finiteSmoothed P r t := by
  rintro ⟨r, hr⟩
  obtain ⟨P, hsub, hcard⟩ := Nat.infinite_setOf_prime.exists_subset_card_eq (r + 2)
  have hP : ∀ p ∈ P, p.Prime := fun p hp => hsub hp
  have hne : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨t, ht, hneg⟩ := finitePrime_exists_negative_on_positive_ray (r := r) hP (by omega)
  exact (not_le_of_gt hneg) (hr P hP hne t ht.le)

end RHTower.MobiusRieszSmoothing

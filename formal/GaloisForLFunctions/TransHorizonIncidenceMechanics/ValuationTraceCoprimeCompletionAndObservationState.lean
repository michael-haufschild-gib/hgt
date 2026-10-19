import GaloisForLFunctions.TransHorizonIncidenceMechanics.ValuationTraceDistanceAndPrimePowerPeriod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-!
# Exact valuation-trace distances under coprime completion

GCD projection gives the local lower bounds. Chinese remainder completion makes
all complementary GCD factors agree, so each maximal prime-power lower bound is
attained globally. This yields an exact phase-separation criterion for any
positive modulus. Existing finite-LCM factorization also identifies the literal
horizon observation state with its GCD model.
-/

set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section

private theorem gcd_coprime_product (x q r : ℕ) (h : q.Coprime r) :
    Nat.gcd x (q * r) = Nat.gcd x q * Nat.gcd x r := by
  have heq := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h
    (x := Nat.gcd x (q * r))).mpr (Nat.gcd_dvd_right x (q * r))
  rw [Nat.gcd_assoc, Nat.gcd_eq_right (Nat.dvd_mul_right q r),
    Nat.gcd_assoc, Nat.gcd_eq_right (Nat.dvd_mul_left r q)] at heq
  exact heq.symm

/-- Projecting a GCD trace to a divisor cannot increase its distance. -/
theorem valuationTraceDistance_le_of_dvd {q L : ℕ} (hq : q ∣ L) (W k l : ℕ) :
    valuationTraceDistance q W k l ≤ valuationTraceDistance L W k l := by
  rw [valuationTraceDistance_eq_sum, valuationTraceDistance_eq_sum]
  apply Finset.sum_le_sum
  intro t _
  by_cases h : Nat.gcd (k + t) L = Nat.gcd (l + t) L
  · have hqeq := congrArg (fun n => Nat.gcd n q) h
    simp only [Nat.gcd_assoc, Nat.gcd_eq_right hq] at hqeq
    simp [h, hqeq]
  · simp only [ne_eq, h, not_false_eq_true, ite_true]
    split <;> omega

/-- CRT lifts any local trace pair while preserving its exact disagreement count. -/
theorem valuationTraceDistance_coprime_completion {q r : ℕ}
    (hcop : q.Coprime r) (hr : 0 < r) (W k₀ l₀ : ℕ) :
    ∃ k l : ℕ, Nat.ModEq q k k₀ ∧ Nat.ModEq q l l₀ ∧
      Nat.ModEq r k 0 ∧ Nat.ModEq r l 0 ∧
      valuationTraceDistance (q * r) W k l = valuationTraceDistance q W k₀ l₀ := by
  obtain ⟨k, hkq, hkr⟩ := Nat.chineseRemainder hcop k₀ 0
  obtain ⟨l, hlq, hlr⟩ := Nat.chineseRemainder hcop l₀ 0
  refine ⟨k, l, hkq, hlq, hkr, hlr, ?_⟩
  have heq (t : ℕ) : Nat.gcd (k + t) (q * r) = Nat.gcd (l + t) (q * r) ↔
      Nat.gcd (k₀ + t) q = Nat.gcd (l₀ + t) q := by
    rw [gcd_coprime_product _ _ _ hcop, gcd_coprime_product _ _ _ hcop,
      (hkq.add_right t).gcd_eq, (hlq.add_right t).gcd_eq,
      (hkr.add_right t).gcd_eq, (hlr.add_right t).gcd_eq, Nat.zero_add]
    have hpos := Nat.gcd_pos_of_pos_right t hr
    constructor
    · intro h
      nlinarith
    · intro h
      rw [h]
  rw [valuationTraceDistance_eq_sum, valuationTraceDistance_eq_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ne_eq, heq t]

/-- Every maximal prime-power factor has a global pair attaining its local distance floor. -/
theorem valuationTraceDistance_maximal_prime_pow_attainer {L p : ℕ}
    (hL : 0 < L) (hp : p.Prime) (ha : 1 ≤ L.factorization p) (W : ℕ) :
    ∃ k l : ℕ, ¬ Nat.ModEq L k l ∧
      valuationTraceDistance L W k l =
        primePowerTraceDistanceFloor (p ^ L.factorization p) W := by
  let a := L.factorization p
  have hcop := (Nat.coprime_ordCompl hp hL.ne').pow_left a
  obtain ⟨k, l, hk, hl, _, _, hdist⟩ :=
    valuationTraceDistance_coprime_completion hcop (Nat.ordCompl_pos p hL.ne')
      W 1 (1 + p ^ (a - 1))
  rw [Nat.ordProj_mul_ordCompl_eq_self] at hdist
  refine ⟨k, l, ?_, ?_⟩
  · intro h
    have hq := Nat.ModEq.of_dvd (Nat.ordProj_dvd L p) h
    exact (gcd_prime_pow_collision_below_totient hp ha).1 (hk.symm.trans (hq.trans hl))
  · exact hdist.trans (valuationTraceDistance_prime_pow_attainer hp ha W)

/-- Exact separation criterion for every positive modulus, including the one-phase modulus. -/
theorem valuationTraceDistance_phase_separation_iff {L : ℕ} (hL : 0 < L) (W b : ℕ) :
    (∀ k l, valuationTraceDistance L W k l ≤ b → Nat.ModEq L k l) ↔
      ∀ p : ℕ, p.Prime → 1 ≤ L.factorization p →
        b < primePowerTraceDistanceFloor (p ^ L.factorization p) W := by
  constructor
  · intro h p hp ha
    obtain ⟨k, l, hne, hd⟩ := valuationTraceDistance_maximal_prime_pow_attainer hL hp ha W
    by_contra hle
    exact hne (h k l (by omega))
  · intro h k l hdist
    apply modEq_of_forall_prime_pow_dvd hL
    intro p a hp ha hpa
    have hab := (hp.pow_dvd_iff_le_factorization hL.ne').mp hpa
    have hfull : Nat.ModEq (p ^ L.factorization p) k l := by
      by_contra hne
      have hlo := valuationTraceDistance_prime_pow_lower hp hne W
      have hproj := valuationTraceDistance_le_of_dvd (Nat.ordProj_dvd L p) W k l
      have hstrict := h p hp (ha.trans hab)
      omega
    exact Nat.ModEq.of_dvd (pow_dvd_pow p hab) hfull

/-- A nontrivial prime power divides the horizon modulus exactly when it is admitted. -/
theorem prime_pow_dvd_horizonObservationModulus_iff {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (N : ℕ) :
    p ^ a ∣ horizonObservationModulus N ↔ p ^ a ≤ N := by
  constructor
  · intro hd
    have hfac := (hp.pow_dvd_iff_le_factorization
      (horizonObservationModulus_pos N).ne').mp hd
    have hnz : ∀ d ∈ Icc 1 N, (id d : ℕ) ≠ 0 := fun d hd =>
      Nat.ne_of_gt (Finset.mem_Icc.mp hd).1
    rw [horizonObservationModulus, Finset.factorization_lcm hnz p] at hfac
    have hlt : a - 1 < (Icc 1 N).sup (fun d => d.factorization p) := by
      simpa only [id_eq] using (show a - 1 < (Icc 1 N).sup
        (fun d => (id d : ℕ).factorization p) by omega)
    obtain ⟨d, hd, hda⟩ := Finset.lt_sup_iff.mp hlt
    have hpd : p ^ a ∣ d := (hp.pow_dvd_iff_le_factorization
      (show d ≠ 0 from hnz d hd)).mpr (by omega)
    exact (Nat.le_of_dvd (Finset.mem_Icc.mp hd).1 hpd).trans (Finset.mem_Icc.mp hd).2
  · intro hle
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨pow_pos hp.pos a, hle⟩)

/-- The finite multiplicative observation state is the GCD with the horizon modulus. -/
theorem horizonObservationState_eq_gcd (N k : ℕ) :
    horizonObservationState N k = Nat.gcd k (horizonObservationModulus N) := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (horizonObservationState_dvd N k)
      (horizonObservationState_dvd_modulus N k)
  · apply dvd_of_forall_prime_pow_dvd
      (Nat.gcd_pos_of_pos_right k (horizonObservationModulus_pos N))
    intro p a hp ha hd
    have hmod : p ^ a ∣ horizonObservationModulus N :=
      hd.trans (Nat.gcd_dvd_right k (horizonObservationModulus N))
    have hmem : p ^ a ∈ Icc 1 N := Finset.mem_Icc.mpr
      ⟨pow_pos hp.pos a, (prime_pow_dvd_horizonObservationModulus_iff hp ha N).mp hmod⟩
    exact (dvd_horizonObservationState_iff N k (p ^ a) hmem).mpr
      (hd.trans (Nat.gcd_dvd_left k (horizonObservationModulus N)))

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics

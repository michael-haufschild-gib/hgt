import GaloisForLFunctions.BiScaleUncertainty.ArithmeticEdgeSieveFamily
import GaloisForLFunctions.BiScaleUncertainty.SieveHalfPeriodTranslation
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Actual translations of arithmetic edge sieves

Every edge profile has the explicit odd antiperiod given by the product of its vertex blocks.
Consequently all odd translated moments vanish. Existing sixth-order valuation recovery identifies
translation equivalence with one common coordinate sign, including every zero pattern.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BezoutValuationIncidence
open AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- A represented translate preserves every complete translated moment array. -/
theorem translatedMoment_of_signal_translate (N : ℕ) (c e : ℕ → ℝ) (t : ℕ)
    (he : ∀ k, sieveSeq N e k = sieveSeq N c (k+t))
    {m : ℕ} (h : Fin m → ℕ) : translatedMoment N e h = translatedMoment N c h := by
  have hp := (HalfPeriod.shift_representable_iff N t c).mp ⟨e,he⟩
  have hs (k : ℕ) : sieveSeq N (HalfPeriod.reflection N t c) k = sieveSeq N e k :=
    (HalfPeriod.sieveSeq_reflection N t k c hp).trans (he k).symm
  have hm := HalfPeriod.translatedMoment_reflection N t c hp h
  simpa only [translatedMoment,hs] using hm

namespace ArithmeticEdges.Blocks
variable {V : Type*} [Fintype V] (D : Blocks V)

theorem profile_neg (a : ℕ → ℝ) (q : ℕ) :
    D.profile (fun i => -a i) q = -D.profile a q := by
  classical
  unfold profile
  split_ifs <;> simp

theorem weights_neg (n : ℕ) (a : ℕ → ℝ) (d : ℕ) :
    D.weights n (fun i => -a i) d = -D.weights n a d := by
  simp only [weights,RHTower.pmRamanujanResidueCoeff,D.profile_neg,mul_neg,
    Finset.sum_neg_distrib]

theorem signal_neg (n : ℕ) (a : ℕ → ℝ) (k : ℕ) :
    sieveSeq (D.cutoff n) (D.weights n (fun i => -a i)) k =
      -sieveSeq (D.cutoff n) (D.weights n a) k := by
  simp only [sieveSeq,D.weights_neg,Finset.sum_neg_distrib]

/-- The product of odd vertex blocks is an explicit sign-reversing shift. -/
def halfPeriod : ℕ := ∏ v, D.value v

theorem halfPeriod_odd : Odd D.halfPeriod := by
  unfold halfPeriod
  exact Finset.prod_induction D.value Odd (fun _ _ ha hb => ha.mul hb)
    ⟨0,rfl⟩ (fun v _ => D.odd v)

theorem order_dvd_twice_halfPeriod {u v : V} (huv : u ≠ v) :
    D.order u v ∣ 2*D.halfPeriod := by
  have hu : D.value u ∣ D.halfPeriod :=
    Finset.dvd_prod_of_mem D.value (Finset.mem_univ u)
  have hv : D.value v ∣ D.halfPeriod :=
    Finset.dvd_prod_of_mem D.value (Finset.mem_univ v)
  obtain ⟨m,hm⟩ := (D.coprime u v huv).mul_dvd_of_dvd_of_dvd hu hv
  refine ⟨m,?_⟩
  unfold order
  rw [hm]
  ring

omit [Fintype V] in
theorem two_dvd_order (u v : V) : 2 ∣ D.order u v :=
  ⟨D.value u*D.value v,by unfold order; ring⟩

theorem signal_periodic (n : ℕ) (a : ℕ → ℝ) :
    Function.Periodic (sieveSeq (D.cutoff n) (D.weights n a)) (2*D.halfPeriod) := by
  apply (sieveSeq_periodic_iff_active_divisors _ _ _).mpr
  intro d _ hd
  by_contra hdiv
  apply hd
  have hz (m : ℕ) : D.profile a (d*m) = 0 := by
    apply D.profile_zero
    rintro ⟨u,v,huv,he⟩
    exact hdiv ((show d ∣ D.order u v from ⟨m,he.symm⟩).trans
      (D.order_dvd_twice_halfPeriod huv))
  simp only [weights,RHTower.pmRamanujanResidueCoeff,hz,mul_zero,Finset.sum_const_zero]

private theorem signal_eq_on (N : ℕ) (c e : ℕ → ℝ)
    (he : ∀ d ∈ Finset.Icc 1 N, c d = e d) (k : ℕ) :
    sieveSeq N c k = sieveSeq N e k := by
  unfold sieveSeq
  apply Finset.sum_congr rfl
  intro d hd
  exact he d (Finset.mem_filter.mp hd).1

private theorem reflection_weights (n : ℕ) (a : ℕ → ℝ) :
    ∀ d ∈ Finset.Icc 1 (D.cutoff n),
      HalfPeriod.reflection (D.cutoff n) D.halfPeriod (D.weights n a) d =
        D.weights n (fun i => -a i) d := by
  apply (sieve_active_coefficients_eq_iff _ _ _).mpr
  intro q _
  rw [HalfPeriod.coordinate_reflection,D.coordinate_weights,D.coordinate_weights,D.profile_neg]
  by_cases hq : q ∣ D.halfPeriod
  · rw [if_pos hq]
    have hz : D.profile a q = 0 := by
      apply D.profile_zero
      rintro ⟨u,v,_,he⟩
      have htwo : 2 ∣ D.halfPeriod := (D.two_dvd_order u v).trans (he ▸ hq)
      obtain ⟨j,hj⟩ := htwo
      obtain ⟨k,hk⟩ := D.halfPeriod_odd
      omega
    rw [hz,neg_zero]
  · rw [if_neg hq]

/-- Common sign reversal is a literal shift of the actual finite sieve sequence. -/
theorem signal_antiperiod (n : ℕ) (a : ℕ → ℝ) (k : ℕ) :
    sieveSeq (D.cutoff n) (D.weights n a) (k+D.halfPeriod) =
      -sieveSeq (D.cutoff n) (D.weights n a) k := by
  rw [← HalfPeriod.sieveSeq_reflection _ _ _ _ (D.signal_periodic n a),
    signal_eq_on _ _ _ (D.reflection_weights n a),D.signal_neg]

theorem moment_neg (n : ℕ) (a : ℕ → ℝ) {m : ℕ} (h : Fin m → ℕ) :
    translatedMoment (D.cutoff n) (D.weights n (fun i => -a i)) h =
      translatedMoment (D.cutoff n) (D.weights n a) h := by
  have he := HalfPeriod.translatedMoment_reflection _ _ _ (D.signal_periodic n a) h
  unfold translatedMoment at he ⊢
  simpa only [signal_eq_on _ _ _ (D.reflection_weights n a)] using he

theorem odd_moment_zero (n : ℕ) (a : ℕ → ℝ) (m : ℕ) (h : Fin (2*m+1) → ℕ) :
    translatedMoment (D.cutoff n) (D.weights n a) h = 0 := by
  apply Complex.ofReal_injective
  rw [translatedMoment_complex_eq,Complex.ofReal_zero]
  apply translationMoment_of_antiperiodic _ (D.halfPeriod : ZMod (D.cutoff n).factorial)
  intro x
  have hx : x+(D.halfPeriod : ZMod (D.cutoff n).factorial) =
      ((x.val+D.halfPeriod : ℕ) : ZMod (D.cutoff n).factorial) := by simp
  rw [hx,residueSignal_sieveSeq,D.signal_antiperiod]
  have he := residueSignal_sieveSeq (D.cutoff n) (D.weights n a) x.val
  rw [ZMod.natCast_zmod_val] at he
  rw [he]
  simp

/-- One sign on all actual arithmetic coordinates; invisible coefficient tails are ignored. -/
def CommonSign (a b : ℕ → ℝ) : Prop :=
  (∀ q, D.profile a q = D.profile b q) ∨ (∀ q, D.profile a q = -D.profile b q)

private theorem weights_of_common (n : ℕ) (a b : ℕ → ℝ) (h : D.CommonSign a b) :
    D.weights n a = D.weights n b ∨ D.weights n a = D.weights n (fun q => -b q) := by
  rcases h with he | he
  · left
    exact congrArg (fun f => RHTower.pmRamanujanResidueCoeff f (D.cutoff n)) (funext he)
  · right
    have hp : D.profile a = D.profile (fun q => -b q) := by
      funext q
      rw [D.profile_neg]
      exact he q
    exact congrArg (fun f => RHTower.pmRamanujanResidueCoeff f (D.cutoff n)) hp

/-- Sixth-order data resolve every sign ambiguity except the actual common translation. -/
theorem sixth_iff_common (n : ℕ) (a b : ℕ → ℝ) :
    (∀ h : Fin 6 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) h =
      translatedMoment (D.cutoff n) (D.weights n b) h) ↔ D.CommonSign a b := by
  constructor
  · intro h
    rcases sixth_moments_recover_valuation_block (D.cutoff n) 1
      (D.weights n a) (D.weights n b) h with he | he
    · left
      intro q
      by_cases hq : ∃ u v, u ≠ v ∧ q = D.order u v
      · obtain ⟨u,v,_,rfl⟩ := hq
        have hm : 2^1*(D.value u*D.value v) ∈ Finset.Icc 1 (D.cutoff n) := by
          simpa only [pow_one,mul_assoc,order] using D.order_mem_cutoff n u v
        have hh := he (D.value u*D.value v) ((D.odd u).mul (D.odd v)) hm
        simpa only [pow_one,← mul_assoc,D.coordinate_weights,order] using hh
      · rw [D.profile_zero a q hq,D.profile_zero b q hq]
    · right
      intro q
      by_cases hq : ∃ u v, u ≠ v ∧ q = D.order u v
      · obtain ⟨u,v,_,rfl⟩ := hq
        have hm : 2^1*(D.value u*D.value v) ∈ Finset.Icc 1 (D.cutoff n) := by
          simpa only [pow_one,mul_assoc,order] using D.order_mem_cutoff n u v
        have hh := he (D.value u*D.value v) ((D.odd u).mul (D.odd v)) hm
        simpa only [pow_one,← mul_assoc,D.coordinate_weights,order] using hh
      · rw [D.profile_zero a q hq,D.profile_zero b q hq,neg_zero]
  · intro h v
    rcases D.weights_of_common n a b h with he | he
    · rw [he]
    · rw [he,D.moment_neg]

/-- Translation equivalence is exactly one common sign, for every zero pattern. -/
theorem translation_iff_common (n : ℕ) (a b : ℕ → ℝ) :
    (∃ t : ℕ, ∀ k, sieveSeq (D.cutoff n) (D.weights n b) k =
      sieveSeq (D.cutoff n) (D.weights n a) (k+t)) ↔ D.CommonSign a b := by
  constructor
  · rintro ⟨t,ht⟩
    apply (D.sixth_iff_common n a b).mp
    intro h
    exact (translatedMoment_of_signal_translate _ _ _ t ht h).symm
  · intro h
    rcases D.weights_of_common n a b h with he | he
    · refine ⟨0,?_⟩
      intro k
      rw [Nat.add_zero,he]
    · refine ⟨D.halfPeriod,?_⟩
      intro k
      rw [D.signal_antiperiod,he,D.signal_neg,neg_neg]

end ArithmeticEdges.Blocks
end GaloisForLFunctions.BiScaleUncertainty.SieveMoments

import GaloisForLFunctions.RHTower.DeningerGibbsCyclicDiagonalRecovery
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Prime incidence and summable Green repairs

The prime-incidence kernel has uniformly bounded columns exactly at positive
exponent, and carries every summable complex diagonal to a summable prime field.
Its exact identification with the fixed ordinary-integer Gibbs trace excludes
every summable diagonal repair making all prime Wold pairs cyclic.

The endpoint failure of column control is sharp. No critical singular reader or
cyclic-to-fixed-physical source comparison is constructed, and RH remains open.
-/

open Finset
namespace RHTower
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem primeIncidence_cofactor_lower
    (S : Finset Nat.Primes) (k : PNat)
    (hd : ∀ p ∈ S, (p : ℕ) ∣ (k : ℕ)) (p : Nat.Primes) (hp : p ∈ S) :
    (2 : ℕ) ^ (S.card - 1) * (p : ℕ) ≤ (k : ℕ) := by
  have hprod : (∏ q ∈ S, (q : ℕ)) ∣ (k : ℕ) := by
    apply Finset.prod_dvd_of_isRelPrime ?_ hd
    intro q _ r _ hqr
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes q.property r.property).2 (fun heq => hqr (Subtype.ext heq)))
  have hlow : (2 : ℕ) ^ (S.card - 1) ≤ ∏ q ∈ S.erase p, (q : ℕ) := by
    rw [← Finset.card_erase_of_mem hp, ← Finset.prod_const]
    exact Finset.prod_le_prod' (fun q _ => q.property.two_le)
  calc (2 : ℕ) ^ (S.card - 1) * (p : ℕ)
    _ ≤ (∏ q ∈ S.erase p, (q : ℕ)) * (p : ℕ) := Nat.mul_le_mul_right _ hlow
    _ = ∏ q ∈ S, (q : ℕ) := by rw [mul_comm, Finset.mul_prod_erase S _ hp]
    _ ≤ (k : ℕ) := Nat.le_of_dvd k.pos hprod

def primeIncidenceColumnBudget (a : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) * ((2 : ℝ) ^ (-a)) ^ n

theorem primeIncidenceColumnBudget_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * ((2 : ℝ) ^ (-a)) ^ n) := by
  have hq : ‖(2 : ℝ) ^ (-a)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ha)
  have hs := (summable_pow_mul_geometric_of_norm_lt_one 1 hq).add
    (summable_geometric_of_norm_lt_one hq)
  simpa only [pow_one, add_mul, one_mul] using hs

theorem primeIncidenceColumnBudget_nonneg (a : ℝ) : 0 ≤ primeIncidenceColumnBudget a := by
  apply tsum_nonneg
  intro n
  positivity

theorem primeIncidence_finite_column_le
    {a : ℝ} (ha : 0 < a) (S : Finset Nat.Primes) (k : PNat)
    (hd : ∀ p ∈ S, (p : ℕ) ∣ (k : ℕ)) :
    (∑ p ∈ S, (((k : ℕ) : ℝ) / ((p : ℕ) : ℝ)) ^ (-a)) ≤
      primeIncidenceColumnBudget a := by
  by_cases hS : S.Nonempty
  · have hr : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (Finset.card_pos.mpr hS)
    have hterm (p : Nat.Primes) (hp : p ∈ S) :
        (((k : ℕ) : ℝ) / ((p : ℕ) : ℝ)) ^ (-a) ≤
          ((2 : ℝ) ^ (-a)) ^ (S.card - 1) := by
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.pos
      have hbase : (2 : ℝ) ^ (S.card - 1) ≤ ((k : ℕ) : ℝ) / ((p : ℕ) : ℝ) := by
        apply (le_div_iff₀ hp0).2
        exact_mod_cast primeIncidence_cofactor_lower S k hd p hp
      have heq : ((2 : ℝ) ^ (S.card - 1)) ^ (-a) = ((2 : ℝ) ^ (-a)) ^ (S.card - 1) := by
        rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
          Real.rpow_mul (by norm_num), Real.rpow_natCast]
      rw [← heq]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (neg_nonpos.mpr ha.le)
    calc (∑ p ∈ S, (((k : ℕ) : ℝ) / ((p : ℕ) : ℝ)) ^ (-a))
      _ ≤ ∑ _p ∈ S, ((2 : ℝ) ^ (-a)) ^ (S.card - 1) := Finset.sum_le_sum hterm
      _ = (((S.card - 1 : ℕ) : ℝ) + 1) * ((2 : ℝ) ^ (-a)) ^ (S.card - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        exact_mod_cast hr.symm
      _ ≤ primeIncidenceColumnBudget a :=
        (primeIncidenceColumnBudget_summable ha).le_tsum _ (fun n _ => by positivity)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty]
    exact primeIncidenceColumnBudget_nonneg a

/-- The actual prime-multiples incidence kernel on positive integers. -/
def primeIncidenceKernel (a : ℝ) (p : Nat.Primes) (k : PNat) : ℝ :=
  if (p : ℕ) ∣ (k : ℕ) then (((k : ℕ) : ℝ) / ((p : ℕ) : ℝ)) ^ (-a) else 0

theorem primeIncidenceKernel_nonneg (a : ℝ) (p : Nat.Primes) (k : PNat) :
    0 ≤ primeIncidenceKernel a p k := by
  unfold primeIncidenceKernel
  split_ifs <;> positivity

theorem primeIncidenceKernel_column_sum_le
    {a : ℝ} (ha : 0 < a) (P : Finset Nat.Primes) (k : PNat) :
    (∑ p ∈ P, primeIncidenceKernel a p k) ≤ primeIncidenceColumnBudget a := by
  have h := primeIncidence_finite_column_le ha
    (P.filter (fun p => (p : ℕ) ∣ (k : ℕ))) k
    (fun p hp => (Finset.mem_filter.mp hp).2)
  simpa only [Finset.sum_filter, primeIncidenceKernel] using h

theorem primeIncidenceKernel_column_summable
    {a : ℝ} (ha : 0 < a) (k : PNat) : Summable (fun p => primeIncidenceKernel a p k) :=
  summable_of_sum_le (fun p => primeIncidenceKernel_nonneg a p k)
    (fun P => primeIncidenceKernel_column_sum_le ha P k)

/-- Every summable nonnegative source has a summable full prime-incidence majorant. -/
theorem primeIncidence_summable_majorant
    {a : ℝ} (ha : 0 < a) (r : PNat → ℝ) (hr : ∀ k, 0 ≤ r k) (hs : Summable r) :
    (∀ p : Nat.Primes, Summable (fun k => primeIncidenceKernel a p k * r k)) ∧
      Summable (fun p : Nat.Primes => ∑' k : PNat, primeIncidenceKernel a p k * r k) := by
  have hc (k : PNat) : (∑' p : Nat.Primes, primeIncidenceKernel a p k) ≤
      primeIncidenceColumnBudget a :=
    (primeIncidenceKernel_column_summable ha k).tsum_le_of_sum_le
      (fun P => primeIncidenceKernel_column_sum_le ha P k)
  have hp : Summable (fun kp : PNat × Nat.Primes => primeIncidenceKernel a kp.2 kp.1 * r kp.1) := by
    apply (summable_prod_of_nonneg
      (fun kp => mul_nonneg (primeIncidenceKernel_nonneg a kp.2 kp.1) (hr kp.1))).2
    refine ⟨fun k => (primeIncidenceKernel_column_summable ha k).mul_right (r k), ?_⟩
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg
      (fun p => mul_nonneg (primeIncidenceKernel_nonneg a p k) (hr k))) ?_
        (hs.mul_left (primeIncidenceColumnBudget a))
    intro k
    change (∑' p : Nat.Primes, primeIncidenceKernel a p k * r k) ≤ primeIncidenceColumnBudget a * r k
    rw [(primeIncidenceKernel_column_summable ha k).tsum_mul_right (r k)]
    exact mul_le_mul_of_nonneg_right (hc k) (hr k)
  exact (summable_prod_of_nonneg
    (fun pk => mul_nonneg (primeIncidenceKernel_nonneg a pk.1 pk.2) (hr pk.2))).1 hp.prod_symm

/-- Absolute summability survives the full prime-incidence reader. -/
theorem primeIncidence_summable_readout
    {a : ℝ} (ha : 0 < a) (r : PNat → ℂ) (hr : Summable r) :
    Summable (fun p : Nat.Primes =>
      ∑' k : PNat, (primeIncidenceKernel a p k : ℂ) * r k) := by
  have hm := primeIncidence_summable_majorant ha (fun k => ‖r k‖)
    (fun k => norm_nonneg _) hr.norm
  refine Summable.of_norm_bounded hm.2 (fun p => ?_)
  have hnorm : Summable (fun k : PNat => ‖(primeIncidenceKernel a p k : ℂ) * r k‖) := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primeIncidenceKernel_nonneg a p _)] using hm.1 p
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primeIncidenceKernel_nonneg a p _)] using norm_tsum_le_tsum_norm hnorm

/-- A nonzero reciprocal-prime field cannot be the incidence readout of a summable source. -/
theorem primeIncidence_no_reciprocal_readout
    {a : ℝ} (ha : 0 < a) (c : ℂ) (hc : c ≠ 0) :
    ¬ ∃ r : PNat → ℂ, Summable r ∧ ∀ p : Nat.Primes,
      (∑' k : PNat, (primeIncidenceKernel a p k : ℂ) * r k) = c / ((p : ℕ) : ℂ) := by
  rintro ⟨r, hr, heq⟩
  have hs : Summable (fun p : Nat.Primes => c / ((p : ℕ) : ℂ)) :=
    (primeIncidence_summable_readout ha r hr).congr heq
  have hs' : Summable (fun p : Nat.Primes => (((p : ℕ) : ℂ))⁻¹) := by
    refine (hs.mul_left c⁻¹).congr (fun p => ?_)
    field_simp
  have hsReal : Summable (fun p : Nat.Primes => (1 / ((p : ℕ) : ℝ))) := by
    apply Complex.summable_ofReal.mp
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast, one_div, Complex.ofReal_inv] using hs'
  exact Nat.Primes.not_summable_one_div hsReal

/-- The prime-incidence kernel is the weighted physical diagonal, with its prime factor retained. -/
theorem primeIncidenceKernel_eq_gibbsWeight
    (sigma : ℝ) (p : Nat.Primes) (k : PNat) :
    primeIncidenceKernel (2 * sigma - 1) p k =
      if (p : ℕ) ∣ (k : ℕ) then
        (((p : ℕ) : ℝ) ^ (2 * sigma - 1)) *
          (deningerOrdinaryIntegerGibbsMass sigma k * ((k : ℕ) : ℝ)) else 0 := by
  unfold primeIncidenceKernel
  split_ifs
  · have hk : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast k.pos
    have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.pos
    have hw : deningerOrdinaryIntegerGibbsMass sigma k * ((k : ℕ) : ℝ) =
        (((k : ℕ) : ℝ)) ^ (-(2 * sigma - 1)) := by
      unfold deningerOrdinaryIntegerGibbsMass
      conv_lhs => rhs; rw [← Real.rpow_one (((k : ℕ) : ℝ))]
      rw [← Real.rpow_add hk]
      congr 1
      ring
    rw [hw, Real.div_rpow hk.le hp.le, Real.rpow_neg hp.le, div_inv_eq_mul, mul_comm]
  · rfl

/-- Exact identification of the incidence output with the fixed physical weighted trace. -/
theorem primeIncidence_readout_eq_gibbsTrace
    (sigma : ℝ) (p : Nat.Primes) (T : deningerOrdinaryIntegerGibbsDomain sigma) :
    (∑' k : PNat, (primeIncidenceKernel (2 * sigma - 1) p k : ℂ) *
      deningerOrdinaryIntegerDiagonalCoefficient k T.val) =
      ((((p : ℕ) : ℝ) ^ (2 * sigma - 1) : ℝ) : ℂ) *
        deningerOrdinaryIntegerGibbsTrace sigma
          ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection ⟨p, p.property.pos⟩,
            deningerOrdinaryIntegerGibbsDomain_rightProjection T ⟨p, p.property.pos⟩⟩ := by
  rw [deningerOrdinaryIntegerGibbsTrace_projection_eq_multiples, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [primeIncidenceKernel_eq_gibbsWeight]
  simp only [PNat.dvd_iff]
  change (↑(if (p : ℕ) ∣ (k : ℕ) then
    (((p : ℕ) : ℝ) ^ (2 * sigma - 1)) *
      (deningerOrdinaryIntegerGibbsMass sigma k * ((k : ℕ) : ℝ)) else 0) : ℂ) *
      deningerOrdinaryIntegerDiagonalCoefficient k T.val =
    ((((p : ℕ) : ℝ) ^ (2 * sigma - 1) : ℝ) : ℂ) *
      (if (p : ℕ) ∣ (k : ℕ) then deningerOrdinaryIntegerGibbsDiagonal sigma k T.val else 0)
  by_cases hd : (p : ℕ) ∣ (k : ℕ)
  · simp only [hd, if_true, Complex.ofReal_mul, Complex.ofReal_natCast,
      deningerOrdinaryIntegerGibbsDiagonal, LinearMap.smul_apply, smul_eq_mul]
    ring
  · simp [hd]

def DeningerOrdinaryIntegerGibbsPrimePairCyclic
    (sigma : ℝ) (h : 1 / 2 < sigma) (T : deningerOrdinaryIntegerGibbsDomain sigma) : Prop :=
  ∀ n : PNat, Nat.Prime (n : ℕ) →
    deningerOrdinaryIntegerGibbsReader sigma h
      ⟨deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n),
        deningerOrdinaryIntegerGibbsDomain_compression T n⟩ =
      deningerOrdinaryIntegerGibbsReader sigma h
        ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
          deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩

theorem deningerOrdinaryIntegerGibbsPrimePairCyclic_projection_trace_zero
    {sigma : ℝ} (h : 1 / 2 < sigma) (T : deningerOrdinaryIntegerGibbsDomain sigma)
    (hc : DeningerOrdinaryIntegerGibbsPrimePairCyclic sigma h T)
    (n : PNat) (hn : Nat.Prime (n : ℕ)) :
    deningerOrdinaryIntegerGibbsTrace sigma
      ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ = 0 := by
  have hne : n ≠ 1 := fun heq => hn.ne_one (congrArg PNat.val heq)
  have hx := (deningerOrdinaryIntegerGibbsReader_physicalExchange (sigma : ℂ) h T n).symm.trans
    (hc n hn)
  have hz : ((deningerHalfDensityMateGain n (sigma : ℂ) : ℂ) - 1) *
      deningerOrdinaryIntegerGibbsReader sigma h
        ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
          deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ = 0 := by
    linear_combination hx
  have hr := (mul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr (deningerOrdinaryIntegerGibbsGain_ne_one h n hne))
  rw [deningerOrdinaryIntegerGibbsTrace_projection_eq_multiples]
  exact (deningerOrdinaryIntegerGibbsReader_projection_zero_iff h T n).1 hr

theorem deningerOrdinaryIntegerGibbsTrace_rightProjection_sub
    {sigma : ℝ} (T U : deningerOrdinaryIntegerGibbsDomain sigma) (n : PNat) :
    deningerOrdinaryIntegerGibbsTrace sigma
      ⟨(T-U).val * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection (T-U) n⟩ =
      deningerOrdinaryIntegerGibbsTrace sigma
        ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
          deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ -
      deningerOrdinaryIntegerGibbsTrace sigma
        ⟨U.val * deningerOrdinaryIntegerDivisibilityProjection n,
          deningerOrdinaryIntegerGibbsDomain_rightProjection U n⟩ := by
  have heq :
      (⟨(T-U).val * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection (T-U) n⟩ : deningerOrdinaryIntegerGibbsDomain sigma) =
      ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ -
      ⟨U.val * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection U n⟩ := by
    apply Subtype.ext
    exact sub_mul T.val U.val _
  rw [heq]
  exact (deningerOrdinaryIntegerGibbsTrace sigma).map_sub
    (⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
      deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ : deningerOrdinaryIntegerGibbsDomain sigma)
    (⟨U.val * deningerOrdinaryIntegerDivisibilityProjection n,
      deningerOrdinaryIntegerGibbsDomain_rightProjection U n⟩ : deningerOrdinaryIntegerGibbsDomain sigma)

theorem deningerOrdinaryIntegerGibbsTrace_rightProjection_green
    {sigma : ℝ} (h : 1 / 2 < sigma) (n : PNat) :
    deningerOrdinaryIntegerGibbsTrace sigma
      ⟨deningerOrdinaryIntegerReciprocalGreen * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection
          ⟨deningerOrdinaryIntegerReciprocalGreen,
            (deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff sigma).2 h⟩ n⟩ =
      (deningerOrdinaryIntegerGibbsMass sigma n : ℂ) *
        (deningerOrdinaryIntegerGibbsPartition sigma : ℂ) := by
  have heq :
      (⟨deningerOrdinaryIntegerReciprocalGreen * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection
          ⟨deningerOrdinaryIntegerReciprocalGreen,
            (deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff sigma).2 h⟩ n⟩ : deningerOrdinaryIntegerGibbsDomain sigma) =
      ⟨deningerOrdinaryIntegerDivisibilityProjection n * deningerOrdinaryIntegerReciprocalGreen,
        deningerOrdinaryIntegerProjectionGreen_mem_gibbsDomain h n⟩ := by
    apply Subtype.ext
    exact (deningerOrdinaryIntegerDivisibilityProjection_commutes_reciprocalGreen n).symm
  rw [heq, deningerOrdinaryIntegerGibbsTrace_projectionGreen h n]

/-- Prime tests alone forbid every summable diagonal correction to the actual Green source. -/
theorem deningerOrdinaryIntegerGibbs_no_summable_prime_cyclic_green_repair
    (sigma : ℝ) (h : 1 / 2 < sigma) :
    ¬ ∃ T : deningerOrdinaryIntegerGibbsDomain sigma,
      Summable (fun k => deningerOrdinaryIntegerDiagonalCoefficient k
        (T.val - deningerOrdinaryIntegerReciprocalGreen)) ∧
      DeningerOrdinaryIntegerGibbsPrimePairCyclic sigma h T := by
  rintro ⟨T, hR, hc⟩
  have ha : 0 < 2 * sigma - 1 := by linarith
  have hZ : -(deningerOrdinaryIntegerGibbsPartition sigma : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (deningerOrdinaryIntegerGibbsPartition_pos h).ne')
  apply primeIncidence_no_reciprocal_readout ha
    (-(deningerOrdinaryIntegerGibbsPartition sigma : ℂ)) hZ
  let Q : deningerOrdinaryIntegerGibbsDomain sigma :=
    ⟨deningerOrdinaryIntegerReciprocalGreen,
      (deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff sigma).2 h⟩
  refine ⟨fun k => deningerOrdinaryIntegerDiagonalCoefficient k (T-Q).val, hR, ?_⟩
  intro p
  rw [primeIncidence_readout_eq_gibbsTrace,
    deningerOrdinaryIntegerGibbsTrace_rightProjection_sub,
    deningerOrdinaryIntegerGibbsPrimePairCyclic_projection_trace_zero h T hc ⟨p, p.property.pos⟩ p.property]
  change ((((p : ℕ) : ℝ) ^ (2 * sigma - 1) : ℝ) : ℂ) *
    (0 - deningerOrdinaryIntegerGibbsTrace sigma
      ⟨deningerOrdinaryIntegerReciprocalGreen * deningerOrdinaryIntegerDivisibilityProjection ⟨p, p.property.pos⟩,
        deningerOrdinaryIntegerGibbsDomain_rightProjection Q ⟨p, p.property.pos⟩⟩) = _
  rw [deningerOrdinaryIntegerGibbsTrace_rightProjection_green h, zero_sub, mul_neg, ← mul_assoc]
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.pos
  have hw : (((p : ℕ) : ℝ) ^ (2 * sigma - 1)) *
      deningerOrdinaryIntegerGibbsMass sigma ⟨p, p.property.pos⟩ = (((p : ℕ) : ℝ))⁻¹ := by
    change (((p : ℕ) : ℝ) ^ (2 * sigma - 1)) *
      (((p : ℕ) : ℝ) ^ (-(2 * sigma))) = (((p : ℕ) : ℝ))⁻¹
    rw [← Real.rpow_add hp]
    have he : 2 * sigma - 1 + -(2 * sigma) = (-1 : ℝ) := by ring
    rw [he, Real.rpow_neg_one]
  rw [← Complex.ofReal_mul, hw, Complex.ofReal_inv]
  push_cast
  ring

/-- At or below the neutral exponent, finite prime incidence columns are unbounded. -/
theorem primeIncidenceKernel_unbounded_of_nonpos
    {a : ℝ} (ha : a ≤ 0) (C : ℝ) :
    ∃ P : Finset Nat.Primes, ∃ k : PNat,
      C < ∑ p ∈ P, primeIncidenceKernel a p k := by
  obtain ⟨N, hN⟩ := exists_nat_gt C
  obtain ⟨P, _hP, hcard⟩ := (Set.infinite_univ : (Set.univ : Set Nat.Primes).Infinite).exists_subset_card_eq N
  have hk : 0 < ∏ p ∈ P, (p : ℕ) := Finset.prod_pos (fun p _ => p.property.pos)
  let k : PNat := ⟨∏ p ∈ P, (p : ℕ), hk⟩
  refine ⟨P, k, hN.trans_le ?_⟩
  have ht (p : Nat.Primes) (hp : p ∈ P) : 1 ≤ primeIncidenceKernel a p k := by
    have hd : (p : ℕ) ∣ (k : ℕ) := Finset.dvd_prod_of_mem (fun q : Nat.Primes => (q : ℕ)) hp
    rw [primeIncidenceKernel, if_pos hd]
    apply Real.one_le_rpow ?_ (neg_nonneg.mpr ha)
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.pos
    apply (le_div_iff₀ hp0).2
    simpa only [one_mul] using (show ((p : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) by
      exact_mod_cast Nat.le_of_dvd k.pos hd)
  calc (N : ℝ)
    _ = ∑ _p ∈ P, (1 : ℝ) := by simp [hcard]
    _ ≤ ∑ p ∈ P, primeIncidenceKernel a p k := Finset.sum_le_sum ht

/-- The column-control threshold is exactly the open Gibbs convergence side. -/
theorem primeIncidenceKernel_uniformBound_iff (a : ℝ) :
    (∃ C : ℝ, ∀ P : Finset Nat.Primes, ∀ k : PNat,
      (∑ p ∈ P, primeIncidenceKernel a p k) ≤ C) ↔ 0 < a := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra h
    obtain ⟨P, k, hPk⟩ := primeIncidenceKernel_unbounded_of_nonpos (le_of_not_gt h) C
    exact (not_lt_of_ge (hC P k)) hPk
  · intro ha
    exact ⟨primeIncidenceColumnBudget a, primeIncidenceKernel_column_sum_le ha⟩

end
end RHTower

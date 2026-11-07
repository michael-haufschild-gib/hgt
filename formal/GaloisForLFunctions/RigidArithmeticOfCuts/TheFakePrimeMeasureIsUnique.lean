import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheDualOfTheRateIsAFakePrimeMeasure
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheStencilRateReachesVinogradovKorobov
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHeckeActionOnProducers
import GaloisForLFunctions.RigidArithmeticOfCuts.ACutVectorWithAMonotoneTailVanishes

/-!
# The fake prime measure is unique

A fake prime measure of level `K` is a nonnegative `u` on the positive integers with
`Σ_r u(r) (r mod k) = log k` for `k ≤ K`. The pronic measure `1/(r (r + 1))` is one at every level.

**At infinite level it is the only one.** Three steps.

* Hecke dilates of producers bound the mass of `[j, jB)` by `A (1 − 1/B)/j`, so the geometric sum gives
  the tail bound `T(j) ≤ A/j`. Producers of rate tending to `0` exist, so `T(j) ≤ 1/j`.
* `W(r) = 1/r − T(r)` is a nonnegative kernel vector of the cut system, with monotone `W − 1/r`.
* Such a vector vanishes, because there is no uniform measure on the integers.

So the system of all Chebyshev moments, with positivity, determines the scaling limit of the primes.
The moments alone at bounded level determine nothing below the rate: translating an atom by
`lcm(1, …, K)` keeps every moment and empties any window.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

variable {u : ℕ → ℝ}

/-- A fake prime measure computes the slope of every balanced stencil on its alphabet. -/
theorem hasSum_slope_of_balanced {K : ℕ} (hu : IsFakePrimeMeasure K u) {c : ℕ →₀ ℤ} (hc0 : c 0 = 0)
    (hbal : IsBalanced c) (hK : AlphabetLE c K) :
    HasSum (fun j => u j * (stepWeight c (j + 1) : ℝ)) (stencilSlope c) := by
  have hsub : ∀ k ∈ c.support, k ∈ Icc 1 K := fun k hk => by
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero hk0, hK k hk⟩
  have hfun : (fun j => u j * (stepWeight c (j + 1) : ℝ)) = fun j =>
      ∑ k ∈ c.support, (-(c k : ℝ) / k) * (u j * (((j + 1) % k : ℕ) : ℝ)) := by
    funext j
    rw [stepWeight_eq_sum_mod hc0 hbal, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [hfun, stencilSlope]
  refine hasSum_sum fun k hk => ?_
  have h := (hu.moment k (hsub k hk)).mul_left (-(c k : ℝ) / k)
  have hval : -(c k : ℝ) / k * Real.log k = -(c k : ℝ) * Real.log k / k := by ring
  rwa [hval] at h

/-- The dilate of a stencil has its alphabet dilated. -/
theorem alphabetLE_dilate {c : ℕ →₀ ℤ} {K j : ℕ} (hK : AlphabetLE c K) :
    AlphabetLE (dilate j c) (j * K) := by
  classical
  intro k hk
  have hsub := Finsupp.mapDomain_support (f := fun x => j * x) (s := c) hk
  obtain ⟨k', hk', rfl⟩ := mem_image.mp hsub
  exact Nat.mul_le_mul_left j (hK k' hk')

/-- **The Hecke window bound.** A dilated producer bounds the mass of `[j, jB)`. -/
theorem mul_sum_Ico_le (hu : ∀ K, IsFakePrimeMeasure K u) {c : ℕ →₀ ℤ} {m B K : ℕ}
    (hP : IsProducer c m B) (hK : AlphabetLE c K) {j : ℕ} (hj : 1 ≤ j) :
    (m : ℝ) * ∑ i ∈ Ico (j - 1) (j * B - 1), u i ≤ stencilSlope c / j := by
  have hsum := hasSum_slope_of_balanced (hu (j * K)) (dilate_zero hj hP.zero)
    (isBalanced_dilate hj hP.balanced) (alphabetLE_dilate hK)
  rw [stencilSlope_dilate hj hP.zero hP.balanced] at hsum
  have hterm : ∀ i, 0 ≤ u i * (stepWeight (dilate j c) (i + 1) : ℝ) := fun i => by
    rw [stepWeight_dilate]
    exact mul_nonneg ((hu 0).nonneg i) (by exact_mod_cast hP.nonneg _)
  refine le_trans ?_ (sum_le_hasSum (Ico (j - 1) (j * B - 1)) (fun i _ => hterm i) hsum)
  rw [mul_sum]
  refine sum_le_sum fun i hi => ?_
  obtain ⟨h1, h2⟩ := mem_Ico.mp hi
  have hj0 : 0 < j := hj
  have hmem : (i + 1) / j ∈ Ico 1 B := by
    refine mem_Ico.mpr ⟨(Nat.one_le_div_iff hj0).mpr (by omega), (Nat.div_lt_iff_lt_mul hj0).mpr ?_⟩
    rw [mul_comm]
    omega
  have hw : (m : ℝ) ≤ stepWeight (dilate j c) (i + 1) := by
    rw [stepWeight_dilate]
    exact_mod_cast hP.window _ hmem
  calc (m : ℝ) * u i = u i * m := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hw ((hu 0).nonneg i)

/-- The Hecke window bound in terms of the normalized slope. -/
theorem sum_Ico_le_normSlope (hu : ∀ K, IsFakePrimeMeasure K u) {c : ℕ →₀ ℤ} {m B K : ℕ}
    (hP : IsProducer c m B) (hK : AlphabetLE c K) {j : ℕ} (hj : 1 ≤ j) :
    ∑ i ∈ Ico (j - 1) (j * B - 1), u i ≤ normSlope c m B * (1 - 1 / (B : ℝ)) / j := by
  have hm := hP.m_pos
  have hone := hP.one_sub_pos
  have hbound := mul_sum_Ico_le hu hP hK hj
  have hslope : stencilSlope c = normSlope c m B * ((m : ℝ) * (1 - 1 / (B : ℝ))) := by
    rw [normSlope]
    field_simp
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  rw [hslope] at hbound
  have hrew : normSlope c m B * ((m : ℝ) * (1 - 1 / (B : ℝ))) / j =
      (m : ℝ) * (normSlope c m B * (1 - 1 / (B : ℝ)) / j) := by ring
  rw [hrew] at hbound
  exact le_of_mul_le_mul_left hbound hm

/-- The geometric sum of the Hecke windows. -/
theorem sum_Ico_pow_le (hu : ∀ K, IsFakePrimeMeasure K u) {c : ℕ →₀ ℤ} {m B K : ℕ}
    (hP : IsProducer c m B) (hK : AlphabetLE c K) {j : ℕ} (hj : 1 ≤ j) (l : ℕ) :
    ∑ i ∈ Ico (j - 1) (j * B ^ l - 1), u i ≤
      normSlope c m B / j * (1 - (1 / (B : ℝ)) ^ l) := by
  have hB : 2 ≤ B := hP.two_le_B
  have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  induction l with
  | zero => simp
  | succ l ih =>
    have hj' : 1 ≤ j * B ^ l := Nat.mul_pos hj (pow_pos (by omega) l)
    have hle1 : j - 1 ≤ j * B ^ l - 1 := by
      have : j ≤ j * B ^ l := Nat.le_mul_of_pos_right j (pow_pos (by omega) l)
      omega
    have hmul : j * B ^ l * B = j * B ^ (l + 1) := by rw [pow_succ, mul_assoc]
    have hle2 : j * B ^ l - 1 ≤ j * B ^ (l + 1) - 1 := by
      have : j * B ^ l ≤ j * B ^ (l + 1) := by
        rw [← hmul]; exact Nat.le_mul_of_pos_right _ (by omega)
      omega
    rw [← sum_Ico_consecutive _ hle1 hle2]
    have hw := sum_Ico_le_normSlope hu hP hK hj'
    rw [hmul] at hw
    have hval : normSlope c m B * (1 - 1 / (B : ℝ)) / ((j * B ^ l : ℕ) : ℝ) =
        normSlope c m B / j * ((1 / (B : ℝ)) ^ l - (1 / (B : ℝ)) ^ (l + 1)) := by
      push_cast
      rw [pow_succ, one_div, inv_pow]
      field_simp
    rw [hval] at hw
    calc _ ≤ normSlope c m B / j * (1 - (1 / (B : ℝ)) ^ l) +
          normSlope c m B / j * ((1 / (B : ℝ)) ^ l - (1 / (B : ℝ)) ^ (l + 1)) := add_le_add ih hw
      _ = _ := by ring

/-- The window bound for all truncations of the tail from `j`. -/
theorem sum_Ico_le_of_le (hu : ∀ K, IsFakePrimeMeasure K u) {c : ℕ →₀ ℤ} {m B K : ℕ}
    (hP : IsProducer c m B) (hK : AlphabetLE c K) {j : ℕ} (hj : 1 ≤ j) (N : ℕ) :
    ∑ i ∈ Ico (j - 1) N, u i ≤ normSlope c m B / j := by
  have hB : 2 ≤ B := hP.two_le_B
  have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hA : 0 ≤ normSlope c m B := by
    have := hP.rate_pos
    rw [rate] at this
    linarith
  have hlt : N < j * B ^ N := by
    have h1 : N < 2 ^ N := Nat.lt_two_pow_self
    have h2 : 2 ^ N ≤ B ^ N := Nat.pow_le_pow_left hB N
    have h3 : B ^ N ≤ j * B ^ N := Nat.le_mul_of_pos_left _ hj
    omega
  have hsub : Ico (j - 1) N ⊆ Ico (j - 1) (j * B ^ N - 1) := by
    intro x hx
    obtain ⟨h1, h2⟩ := mem_Ico.mp hx
    exact mem_Ico.mpr ⟨h1, by omega⟩
  have h1 := sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (hu 0).nonneg i)
  refine h1.trans ((sum_Ico_pow_le hu hP hK hj N).trans ?_)
  have hpow : 0 ≤ (1 / (B : ℝ)) ^ N := by positivity
  have hcoef : 0 ≤ normSlope c m B / j := by positivity
  nlinarith

/-- Producers of arbitrarily small rate exist. -/
theorem exists_producer_rate_le {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ →₀ ℤ) (m B K : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧ rate c m B ≤ ε := by
  have h := hasRate_vk (α := 1 / 2) (by norm_num) (by norm_num)
  have ht : Tendsto (fun K : ℕ => Real.exp (-(Real.log (K : ℝ) ^ (1 / 2 : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      ((tendsto_rpow_atTop (by norm_num)).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)))
  obtain ⟨K, ⟨c, m, B, hP, hK, hr⟩, hsmall⟩ :=
    (h.and (ht.eventually (ge_mem_nhds hε))).exists
  exact ⟨c, m, B, K, hP, hK, hr.trans hsmall⟩

/-- **A fake prime measure of every level is summable.** -/
theorem summable_of_forall_isFakePrimeMeasure (hu : ∀ K, IsFakePrimeMeasure K u) : Summable u := by
  obtain ⟨c, m, B, K, hP, hK, -⟩ := exists_producer_rate_le (ε := 1) one_pos
  refine summable_of_sum_range_le (c := normSlope c m B / (1 : ℕ)) (hu 0).nonneg fun n => ?_
  rw [range_eq_Ico]
  exact sum_Ico_le_of_le hu hP hK (j := 1) le_rfl n

/-- The tail `T(r) = Σ_{j ≥ r} u(j)` of a measure on the positive integers. -/
def cutTail (u : ℕ → ℝ) (r : ℕ) : ℝ := if r = 0 then 0 else ∑' i, u (i + (r - 1))

/-- The tail drops by the mass at `r`. -/
theorem cutTail_sub_succ (hs : Summable u) {r : ℕ} (hr : 1 ≤ r) :
    cutTail u r - cutTail u (r + 1) = u (r - 1) := by
  have hr0 : r ≠ 0 := by omega
  have hf : Summable fun i => u (i + (r - 1)) := (summable_nat_add_iff (r - 1)).mpr hs
  have h := hf.tsum_eq_zero_add
  simp only [cutTail, if_neg hr0, if_neg (Nat.succ_ne_zero r), Nat.add_sub_cancel]
  have hfun : (fun i => u (i + 1 + (r - 1))) = fun i => u (i + r) := by
    funext i
    congr 1
    omega
  rw [hfun] at h
  simp only [zero_add] at h
  linarith

/-- **The tail bound.** At infinite level `T(j) ≤ 1/j`. -/
theorem cutTail_le_inv (hu : ∀ K, IsFakePrimeMeasure K u) {j : ℕ} (hj : 1 ≤ j) :
    cutTail u j ≤ 1 / (j : ℝ) := by
  have hj0 : j ≠ 0 := by omega
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨c, m, B, K, hP, hK, hr⟩ := exists_producer_rate_le hε
  have hA : normSlope c m B ≤ 1 + ε := by
    rw [rate] at hr
    linarith
  simp only [cutTail, if_neg hj0]
  refine Real.tsum_le_of_sum_range_le (fun i => (hu 0).nonneg _) fun n => ?_
  have hsum : ∑ i ∈ range n, u (i + (j - 1)) = ∑ i ∈ Ico (j - 1) (n + (j - 1)), u i := by
    rw [sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact sum_congr rfl fun i _ => by rw [add_comm]
  rw [hsum]
  refine (sum_Ico_le_of_le hu hP hK hj _).trans ?_
  have h1 : normSlope c m B / j ≤ (1 + ε) / j := by gcongr
  have h2 : (1 + ε) / (j : ℝ) = 1 / j + ε / j := add_div _ _ _
  have h3 : ε / (j : ℝ) ≤ ε := div_le_self hε.le hjR
  linarith

/-- The moments read through the tail: the cut identity at a multiple of `k`. -/
theorem tendsto_cutDefect_tail (hs : Summable u) {k : ℕ} (hk : 1 ≤ k)
    (hmom : HasSum (fun j => u j * (((j + 1) % k : ℕ) : ℝ)) (Real.log k)) :
    Tendsto (cutDefect (cutTail u) k) atTop (𝓝 (Real.log k)) := by
  have hk0 : 0 < k := hk
  have hN : Tendsto (fun J : ℕ => k * J) atTop atTop := tendsto_id.const_mul_atTop' hk0
  refine (hmom.tendsto_sum_nat.comp hN).congr fun J => ?_
  simp only [Function.comp, cutDefect]
  rw [← sum_Icc_mul_mod_mul (cutTail u) hk J, sum_Icc_one_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  rw [cutTail_sub_succ hs (by omega : 1 ≤ j + 1), Nat.add_sub_cancel]

/-- The pronic tail `1/r` has the same cut values. -/
theorem tendsto_cutDefect_inv {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (cutDefect (fun r : ℕ => 1 / (r : ℝ)) k) atTop (𝓝 (Real.log k)) := by
  have hk0 : 0 < k := hk
  have hmom := (isFakePrimeMeasure_pronic k).moment k (mem_Icc.mpr ⟨hk, le_rfl⟩)
  have hN : Tendsto (fun J : ℕ => k * J) atTop atTop := tendsto_id.const_mul_atTop' hk0
  refine (hmom.tendsto_sum_nat.comp hN).congr fun J => ?_
  simp only [Function.comp, cutDefect]
  rw [← sum_Icc_mul_mod_mul (fun r : ℕ => 1 / (r : ℝ)) hk J, sum_Icc_one_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  have h1 : ((j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : ((j + 1 + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  congr 1
  push_cast at h1 h2 ⊢
  field_simp
  ring

/-- `W = 1/r − T(r)`, the deviation of a fake from the pronic measure. -/
def cutDeviation (u : ℕ → ℝ) (r : ℕ) : ℝ := 1 / (r : ℝ) - cutTail u r

/-- **The deviation is a kernel vector.** -/
theorem isCutKernel_cutDeviation (hu : ∀ K, IsFakePrimeMeasure K u) :
    IsCutKernel (cutDeviation u) := by
  intro k hk
  have hs := summable_of_forall_isFakePrimeMeasure hu
  have h := (tendsto_cutDefect_inv hk).sub
    (tendsto_cutDefect_tail hs hk ((hu k).moment k (mem_Icc.mpr ⟨hk, le_rfl⟩)))
  rw [sub_self] at h
  refine h.congr fun J => ?_
  simp only [cutDefect, cutDeviation, sum_sub_distrib]
  ring

/-- **The tail law.** At infinite level, `T(r) = 1/r`. -/
theorem cutTail_eq_inv (hu : ∀ K, IsFakePrimeMeasure K u) {r : ℕ} (hr : 1 ≤ r) :
    cutTail u r = 1 / (r : ℝ) := by
  have hs := summable_of_forall_isFakePrimeMeasure hu
  have h0 : cutDeviation u 0 = 0 := by simp [cutDeviation, cutTail]
  have hmono : ∀ r, 1 ≤ r → cutDeviation u r - 1 / (r : ℝ) ≤
      cutDeviation u (r + 1) - 1 / ((r + 1 : ℕ) : ℝ) := by
    intro r hr
    have h1 := cutTail_sub_succ hs hr
    have h2 := (hu 0).nonneg (r - 1)
    simp only [cutDeviation]
    linarith
  have hW1 : ∀ r, 1 ≤ r → cutDeviation u r ≤ 1 / (r : ℝ) := by
    intro r hr
    have hr0 : r ≠ 0 := by omega
    have h1 : 0 ≤ cutTail u r := by
      simp only [cutTail, if_neg hr0]
      exact tsum_nonneg fun i => (hu 0).nonneg _
    simp only [cutDeviation]
    linarith
  have hnn : ∀ r, 1 ≤ r → 0 ≤ cutDeviation u r := by
    intro r hr
    have := cutTail_le_inv hu hr
    simp only [cutDeviation]
    linarith
  have h := eq_zero_of_cut_kernel h0 hnn hW1 hmono (isCutKernel_cutDeviation hu) hr
  simp only [cutDeviation] at h
  linarith

/-- **The fake prime measure is unique.** A nonnegative solution of all the Chebyshev moment equations
is the pronic measure. -/
theorem eq_pronic_of_forall_isFakePrimeMeasure (hu : ∀ K, IsFakePrimeMeasure K u) (j : ℕ) :
    u j = 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  have hs := summable_of_forall_isFakePrimeMeasure hu
  have h := cutTail_sub_succ hs (r := j + 1) (by omega)
  rw [cutTail_eq_inv hu (by omega), cutTail_eq_inv hu (by omega), Nat.add_sub_cancel] at h
  rw [← h]
  push_cast
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (j : ℝ) + 1 + 1 ≠ 0 := by positivity
  have h3 : (j : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **The set of fakes of every level is a single point.** -/
theorem forall_isFakePrimeMeasure_iff :
    (∀ K, IsFakePrimeMeasure K u) ↔ u = fun j : ℕ => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) :=
  ⟨fun hu => funext (eq_pronic_of_forall_isFakePrimeMeasure hu),
    fun hu K => hu ▸ isFakePrimeMeasure_pronic K⟩

/-- **Bounded level determines no window from below.** Translating a measure by a common period of the
alphabet keeps every moment. So at level `K` the pronic measure has translates with no mass below any
prescribed point: only the upper radius of the fake set is a theorem at finite level. -/
theorem isFakePrimeMeasure_translate {K L : ℕ} (hL : ∀ k ∈ Icc 1 K, k ∣ L)
    (hu : IsFakePrimeMeasure K u) :
    IsFakePrimeMeasure K fun j => if j < L then 0 else u (j - L) := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · split_ifs
    · exact le_rfl
    · exact hu.nonneg _
  · have h := hu.moment k hk
    have hd := hL k hk
    have hinj : Function.Injective fun j : ℕ => j + L := add_left_injective L
    have hf : ∀ x ∉ Set.range (fun j : ℕ => j + L),
        (if x < L then (0 : ℝ) else u (x - L)) * (((x + 1) % k : ℕ) : ℝ) = 0 := by
      intro x hx
      have hxL : x < L := by
        by_contra hge
        exact hx ⟨x - L, by simp only; omega⟩
      simp [hxL]
    refine (hinj.hasSum_iff hf).mp ?_
    have hfun : ((fun x : ℕ => (if x < L then (0 : ℝ) else u (x - L)) * (((x + 1) % k : ℕ) : ℝ)) ∘
        fun j : ℕ => j + L) = fun j => u j * (((j + 1) % k : ℕ) : ℝ) := by
      funext j
      obtain ⟨t, ht⟩ := hd
      have hmod : (j + L + 1) % k = (j + 1) % k := by
        rw [show j + L + 1 = j + 1 + k * t by omega, Nat.add_mul_mod_self_left]
      simp only [Function.comp]
      rw [if_neg (by omega), Nat.add_sub_cancel, hmod]
    rw [hfun]
    exact h

end GaloisForLFunctions.RigidArithmeticOfCuts

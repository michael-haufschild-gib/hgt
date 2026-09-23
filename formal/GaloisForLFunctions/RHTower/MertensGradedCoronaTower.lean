import GaloisForLFunctions.RHTower.MertensCoronaShiftConormal
import GaloisForLFunctions.RHTower.PrimeHigherMertens

/-!
# The Mertens conormal extends through a graded logarithmic differential corona

The degree-zero Mertens conormal cannot carry multiplication by `log p` on a single Marcinkiewicz
space.  Its exact positive replacement is the graded family

```text
‖b‖_{M,k} = sup_X (log X)^{-(k+1)} ∑_{p ≤ X} (log p)/p · |b_p| ,   u_k(p) = (log p)^k ,
```

for which the higher Mertens theorem `∑_{p ≤ X}(log p)^{k+1}/p = (log X)^{k+1}/(k+1) + C_k + o(1)`
is the exact normalization.  This file proves, unconditionally:

* equations (1)--(3): the graded spaces, and their agreement with the corpus `M_log`, `M_0`
  at `k = 0`;
* equation (4)/(7): `q_k`-normalization of the grade source, and `u_k ∉ M_{k,0}`;
* equations (9)--(10): the graded conormal `q_k` with norm at most `k+1`;
* equations (12)--(15): the logarithmic clock is a contraction `M_k → M_{k+1}`, sends `u_k` to
  `u_{k+1}`, and satisfies `q_{k+1} ∘ L = q_k`;
* equations (17)--(20): every positive Euler translation `S_h` is absolutely summable on `M_k`,
  hence lands in `M_{k,0}`, and stays there after any number of clock derivatives;
* equation (21): the graded source module is cyclic, `L^[k] u_0 = u_k`;
* equation (31): `q_k ∘ (I − S_h) = q_k` in every grade.

The higher Mertens input is the corpus theorem `RHTower.tendsto_primeLogPowSum_sub`.
-/

open Finset Filter Topology

namespace RHTower

noncomputable section

/-! ## The graded prime-tail spaces, equations (1)--(3) -/

/-- The graded logarithmic Marcinkiewicz quotient at grade `k`, equation (1). -/
def gradedMarcinkiewiczQuotient (k : ℕ) (b : ℕ → ℝ) (X : ℕ) : ℝ :=
  primeLogMass_weightedEulerCoefficientSpaces b X / (Real.log X) ^ (k + 1)

/-- Membership in the graded Marcinkiewicz layer `M_k`. -/
def MemGradedMarcinkiewiczLayer (k : ℕ) (b : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → gradedMarcinkiewiczQuotient k b X ≤ C

/-- Membership in the graded vanishing-tail layer `M_{k,0}`, equation (2). -/
def MemGradedVanishingTailLayer (k : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ P : ℕ,
    ∀ X : ℕ, 2 ≤ X → gradedMarcinkiewiczQuotient k (primeCoefficientTail b P) X ≤ ε

/-- The grade-`k` source class `u_k(p) = (log p)^k`, equation (3). -/
def gradeSource (k : ℕ) : ℕ → ℝ := fun p => (Real.log p) ^ k

/-- The logarithmic clock `(L b)_p = (log p) b_p`, equation (11). -/
def logClock (b : ℕ → ℝ) : ℕ → ℝ := fun p => Real.log p * b p

theorem gradedMarcinkiewiczQuotient_zero (b : ℕ → ℝ) (X : ℕ) :
    gradedMarcinkiewiczQuotient 0 b X = marcinkiewiczLogQuotient b X := by
  rw [gradedMarcinkiewiczQuotient, marcinkiewiczLogQuotient, pow_one]

theorem memGradedMarcinkiewiczLayer_zero (b : ℕ → ℝ) :
    MemGradedMarcinkiewiczLayer 0 b ↔ MemMarcinkiewiczLogLayer b := by
  constructor <;> rintro ⟨C, hC⟩ <;> exact ⟨C, fun X hX => by
    simpa [gradedMarcinkiewiczQuotient_zero] using hC X hX⟩

theorem memGradedVanishingTailLayer_zero (b : ℕ → ℝ) :
    MemGradedVanishingTailLayer 0 b ↔ MemVanishingTailLayer b := by
  constructor <;> intro h ε hε <;> obtain ⟨P, hP⟩ := h ε hε <;> exact ⟨P, fun X hX => by
    simpa [gradedMarcinkiewiczQuotient_zero] using hP X hX⟩

theorem gradedMarcinkiewiczQuotient_nonneg (k : ℕ) (b : ℕ → ℝ) {X : ℕ} (hX : 2 ≤ X) :
    0 ≤ gradedMarcinkiewiczQuotient k b X := by
  have hlog : 0 < Real.log X := log_cutoff_pos hX
  exact div_nonneg (primeLogMass_nonneg_weightedEulerCoefficientSpaces b X) (by positivity)

/-! ## Equation (14): the logarithmic clock raises degree -/

theorem logClock_gradeSource (k : ℕ) : logClock (gradeSource k) = gradeSource (k + 1) := by
  funext p
  rw [logClock, gradeSource, gradeSource, pow_succ]
  ring

/-- **Equations (12)--(13).**  The logarithmic clock is a contraction from grade `k` to
grade `k+1`. -/
theorem gradedMarcinkiewiczQuotient_logClock_le (k : ℕ) (b : ℕ → ℝ) {X : ℕ} (hX : 2 ≤ X) :
    gradedMarcinkiewiczQuotient (k + 1) (logClock b) X ≤ gradedMarcinkiewiczQuotient k b X := by
  have hlog : 0 < Real.log X := log_cutoff_pos hX
  have hmass : primeLogMass_weightedEulerCoefficientSpaces (logClock b) X ≤ Real.log X * primeLogMass_weightedEulerCoefficientSpaces b X := by
    rw [primeLogMass_weightedEulerCoefficientSpaces, primeLogMass_weightedEulerCoefficientSpaces, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hmem, hp⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hmem
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hle : Real.log n ≤ Real.log X := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast h2
    have hbase : (0 : ℝ) ≤ Real.log n / n * |b n| := primeLog_term_nonneg b n
    have habs : |logClock b n| = Real.log n * |b n| := by
      rw [logClock, abs_mul, abs_of_nonneg hlogn]
    rw [habs]
    calc Real.log n / n * (Real.log n * |b n|)
        = Real.log n * (Real.log n / n * |b n|) := by ring
      _ ≤ Real.log X * (Real.log n / n * |b n|) := mul_le_mul_of_nonneg_right hle hbase
  rw [gradedMarcinkiewiczQuotient, gradedMarcinkiewiczQuotient]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hpow : (Real.log X) ^ (k + 1 + 1) = Real.log X * (Real.log X) ^ (k + 1) := by ring
  rw [hpow]
  have hmassnn : 0 ≤ primeLogMass_weightedEulerCoefficientSpaces b X := primeLogMass_nonneg_weightedEulerCoefficientSpaces b X
  have hpk : (0 : ℝ) < (Real.log X) ^ (k + 1) := by positivity
  nlinarith [hmass, hmassnn, hpk, hlog]

/-- **Equation (13).**  The logarithmic clock maps grade `k` into grade `k+1`. -/
theorem memGradedMarcinkiewiczLayer_logClock {k : ℕ} {b : ℕ → ℝ}
    (hb : MemGradedMarcinkiewiczLayer k b) :
    MemGradedMarcinkiewiczLayer (k + 1) (logClock b) := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨C, fun X hX =>
    le_trans (gradedMarcinkiewiczQuotient_logClock_le k b hX) (hC X hX)⟩

theorem primeCoefficientTail_logClock (b : ℕ → ℝ) (P : ℕ) :
    primeCoefficientTail (logClock b) P = logClock (primeCoefficientTail b P) := by
  funext n
  rw [primeCoefficientTail, logClock, logClock, primeCoefficientTail]
  by_cases h : P < n <;> simp [h]

/-- The logarithmic clock maps the grade-`k` vanishing-tail layer into grade `k+1`. -/
theorem memGradedVanishingTailLayer_logClock {k : ℕ} {b : ℕ → ℝ}
    (hb : MemGradedVanishingTailLayer k b) :
    MemGradedVanishingTailLayer (k + 1) (logClock b) := by
  intro ε hε
  obtain ⟨P, hP⟩ := hb ε hε
  refine ⟨P, fun X hX => ?_⟩
  rw [primeCoefficientTail_logClock]
  exact le_trans (gradedMarcinkiewiczQuotient_logClock_le k _ hX) (hP X hX)


/-! ## Equations (4) and (7): the higher Mertens normalization of the grade source -/

theorem primeLogMass_gradeSource (k X : ℕ) :
    primeLogMass_weightedEulerCoefficientSpaces (gradeSource k) X = primeLogPowSum (k + 1) (X : ℝ) := by
  rw [primeLogPowSum, Nat.floor_natCast, primeLogMass_weightedEulerCoefficientSpaces, Finset.sum_filter]
  rw [show Finset.Icc 0 X = insert 0 (Finset.Icc 1 X) by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega]
  rw [Finset.sum_insert (by simp)]
  have hzero : primeLogPowWeight (k + 1) 0 = 0 := by
    rw [primeLogPowWeight, if_neg (by decide : ¬ Nat.Prime 0)]
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  by_cases hp : n.Prime
  · rw [if_pos hp, primeLogPowWeight, if_pos hp, gradeSource]
    have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    rw [abs_of_nonneg (pow_nonneg hlogn k)]
    rw [pow_succ]
    ring
  · rw [if_neg hp, primeLogPowWeight, if_neg hp]

theorem tendsto_logPow_atTop (k : ℕ) :
    Tendsto (fun X : ℕ => (Real.log X) ^ (k + 1)) atTop atTop :=
  (tendsto_pow_atTop (n := k + 1) (by omega)).comp tendsto_log_nat_atTop

/-- **Equations (4) and (7).**  After the higher Mertens normalization the grade source has
graded quotient tending to `1/(k+1)`. -/
theorem tendsto_gradedMarcinkiewiczQuotient_gradeSource (k : ℕ) :
    Tendsto (fun X : ℕ => gradedMarcinkiewiczQuotient k (gradeSource k) X) atTop
      (nhds (1 / ((k : ℝ) + 1))) := by
  have hmertens : Tendsto
      (fun X : ℕ => primeLogPowSum (k + 1) (X : ℝ) - (Real.log X) ^ (k + 1) / ((k : ℝ) + 1))
      atTop (nhds (mertensLogPowConstantFull k)) :=
    (tendsto_primeLogPowSum_sub k).comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun X : ℕ =>
      (primeLogPowSum (k + 1) (X : ℝ) - (Real.log X) ^ (k + 1) / ((k : ℝ) + 1))
        / (Real.log X) ^ (k + 1)) atTop (nhds 0) :=
    hmertens.div_atTop (tendsto_logPow_atTop k)
  have hsum := hdiv.add (tendsto_const_nhds (x := 1 / ((k : ℝ) + 1)))
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with X hX
  have hlog : 0 < Real.log X := log_cutoff_pos hX
  have hpow : (0 : ℝ) < (Real.log X) ^ (k + 1) := by positivity
  rw [gradedMarcinkiewiczQuotient, primeLogMass_gradeSource]
  field_simp
  ring

theorem memGradedMarcinkiewiczLayer_gradeSource (k : ℕ) :
    MemGradedMarcinkiewiczLayer k (gradeSource k) := by
  obtain ⟨C, hC⟩ := (tendsto_gradedMarcinkiewiczQuotient_gradeSource k).bddAbove_range
  refine ⟨C, fun X hX => ?_⟩
  exact hC ⟨X, rfl⟩

/-- The head mass of the grade source is bounded uniformly in the cutoff. -/
theorem tendsto_gradedMarcinkiewiczQuotient_gradeSource_tail (k : ℕ) (P : ℕ) :
    Tendsto (fun X : ℕ =>
      gradedMarcinkiewiczQuotient k (primeCoefficientTail (gradeSource k) P) X) atTop
      (nhds (1 / ((k : ℝ) + 1))) := by
  have hhead : Tendsto (fun X : ℕ =>
      primeLogMass_weightedEulerCoefficientSpaces (primeCoefficientHead (gradeSource k) P) X / (Real.log X) ^ (k + 1))
      atTop (nhds 0) := by
    have hbdd : ∀ X : ℕ, primeLogMass_weightedEulerCoefficientSpaces (primeCoefficientHead (gradeSource k) P) X
        ≤ primeLogMass_weightedEulerCoefficientSpaces (gradeSource k) P := primeLogMass_head_le (gradeSource k) P
    have hden : ∀ X : ℕ, (0 : ℝ) ≤ (Real.log X) ^ (k + 1) :=
      fun X => pow_nonneg (Real.log_natCast_nonneg X) _
    refine squeeze_zero (fun X => div_nonneg (primeLogMass_nonneg_weightedEulerCoefficientSpaces _ X) (hden X))
      (fun X => div_le_div_of_nonneg_right (hbdd X) (hden X))
      (tendsto_const_nhds.div_atTop (tendsto_logPow_atTop k) :
        Tendsto (fun X : ℕ => primeLogMass_weightedEulerCoefficientSpaces (gradeSource k) P / (Real.log X) ^ (k + 1))
          atTop (nhds 0))
  have hsub := (tendsto_gradedMarcinkiewiczQuotient_gradeSource k).sub hhead
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with X hX
  have hsplit := primeLogMass_head_add_tail (gradeSource k) P X
  rw [gradedMarcinkiewiczQuotient, gradedMarcinkiewiczQuotient, ← sub_div]
  congr 1
  linarith [hsplit]

/-- **Equation (7).**  The grade source lies outside the grade-`k` vanishing-tail layer. -/
theorem not_memGradedVanishingTailLayer_gradeSource (k : ℕ) :
    ¬ MemGradedVanishingTailLayer k (gradeSource k) := by
  intro h
  have hpos : (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := by positivity
  obtain ⟨P, hP⟩ := h _ hpos
  have hlim := tendsto_gradedMarcinkiewiczQuotient_gradeSource_tail k P
  have hle : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / (2 * ((k : ℝ) + 1)) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with X hX
    exact hP X hX
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ hk (by positivity)] at hle
  linarith


/-! ## Equations (9)--(10): the graded conormal -/

/-- The graded Mertens mean `q_k`, the reader of the grade-`k` source coefficient. -/
def gradedPrimeMean (k : ℕ) (b : ℕ → ℝ) (X : ℕ) : ℝ :=
  ((k : ℝ) + 1) * (∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * b n)
    / (Real.log X) ^ (k + 1)

theorem gradedPrimeMean_zero (b : ℕ → ℝ) (X : ℕ) :
    gradedPrimeMean 0 b X = mertensPrimeMean b X := by
  rw [gradedPrimeMean, mertensPrimeMean, pow_one]
  push_cast
  ring

/-- **Equation (10).**  The graded conormal has norm at most `k+1`. -/
theorem abs_gradedPrimeMean_le (k : ℕ) (b : ℕ → ℝ) {X : ℕ} (hX : 2 ≤ X) :
    |gradedPrimeMean k b X| ≤ ((k : ℝ) + 1) * gradedMarcinkiewiczQuotient k b X := by
  have hlog : 0 < Real.log X := log_cutoff_pos hX
  have hpow : (0 : ℝ) < (Real.log X) ^ (k + 1) := by positivity
  have hnum : |∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * b n| ≤ primeLogMass_weightedEulerCoefficientSpaces b X := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_of_eq (Finset.sum_congr rfl fun n hn => ?_)
    have hnp : n.Prime := (Finset.mem_filter.mp hn).2
    have hlogn : 0 ≤ Real.log n / n := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnp.two_le
      have : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
      positivity
    rw [abs_mul, abs_of_nonneg hlogn]
  rw [gradedPrimeMean, gradedMarcinkiewiczQuotient, abs_div, abs_of_pos hpow, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1))]
  rw [div_le_iff₀ hpow]
  have hq : ((k : ℝ) + 1) * (primeLogMass_weightedEulerCoefficientSpaces b X / (Real.log X) ^ (k + 1)) * (Real.log X) ^ (k + 1)
      = ((k : ℝ) + 1) * primeLogMass_weightedEulerCoefficientSpaces b X := by
    field_simp
  rw [hq]
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  exact mul_le_mul_of_nonneg_left hnum hk

theorem gradedPrimeMean_add (k : ℕ) (b₁ b₂ : ℕ → ℝ) (X : ℕ) :
    gradedPrimeMean k (fun n => b₁ n + b₂ n) X
      = gradedPrimeMean k b₁ X + gradedPrimeMean k b₂ X := by
  rw [gradedPrimeMean, gradedPrimeMean, gradedPrimeMean, ← add_div, ← mul_add]
  congr 2
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem gradedPrimeMean_sub (k : ℕ) (b₁ b₂ : ℕ → ℝ) (X : ℕ) :
    gradedPrimeMean k (fun n => b₁ n - b₂ n) X
      = gradedPrimeMean k b₁ X - gradedPrimeMean k b₂ X := by
  rw [gradedPrimeMean, gradedPrimeMean, gradedPrimeMean, ← sub_div, ← mul_sub]
  congr 2
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem gradedPrimeMean_head_add_tail (k : ℕ) (b : ℕ → ℝ) (P X : ℕ) :
    gradedPrimeMean k b X
      = gradedPrimeMean k (primeCoefficientHead b P) X
        + gradedPrimeMean k (primeCoefficientTail b P) X := by
  rw [← gradedPrimeMean_add]
  congr 1
  funext n
  rw [primeCoefficientHead, primeCoefficientTail]
  by_cases h : P < n <;> simp [h]

/-- The grade-`k` vanishing-tail layer is annihilated by the graded conormal. -/
theorem tendsto_gradedPrimeMean_zero_of_gradedVanishingTail {k : ℕ} {b : ℕ → ℝ}
    (hb : MemGradedVanishingTailLayer k b) :
    Tendsto (gradedPrimeMean k b) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  obtain ⟨P, hP⟩ := hb (ε / (4 * ((k : ℝ) + 1))) (by positivity)
  have hhead : Tendsto (fun X : ℕ => ((k : ℝ) + 1)
      * (primeLogMass_weightedEulerCoefficientSpaces b P / (Real.log X) ^ (k + 1))) atTop (nhds 0) := by
    have := (tendsto_const_nhds.div_atTop (tendsto_logPow_atTop k) :
      Tendsto (fun X : ℕ => primeLogMass_weightedEulerCoefficientSpaces b P / (Real.log X) ^ (k + 1)) atTop (nhds 0))
    have h2 := this.const_mul ((k : ℝ) + 1)
    rwa [mul_zero] at h2
  rw [NormedAddGroup.tendsto_nhds_zero] at hhead
  filter_upwards [hhead (ε / 4) (by positivity), Filter.eventually_ge_atTop 2] with X hX1 hX2
  have hsplit := gradedPrimeMean_head_add_tail k b P X
  have hheadbd : |gradedPrimeMean k (primeCoefficientHead b P) X| ≤ ε / 4 := by
    refine le_trans (abs_gradedPrimeMean_le k _ hX2) ?_
    have hden : (0 : ℝ) < (Real.log X) ^ (k + 1) := by
      have := log_cutoff_pos hX2
      positivity
    have hmass := primeLogMass_head_le b P X
    have hbound : ((k : ℝ) + 1) * gradedMarcinkiewiczQuotient k (primeCoefficientHead b P) X
        ≤ ((k : ℝ) + 1) * (primeLogMass_weightedEulerCoefficientSpaces b P / (Real.log X) ^ (k + 1)) := by
      rw [gradedMarcinkiewiczQuotient]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmass hden.le) hk.le
    refine le_trans hbound ?_
    have hnorm : |((k : ℝ) + 1) * (primeLogMass_weightedEulerCoefficientSpaces b P / (Real.log X) ^ (k + 1))| < ε / 4 := by
      rw [← Real.norm_eq_abs]
      exact hX1
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hnorm)
  have htailbd : |gradedPrimeMean k (primeCoefficientTail b P) X| ≤ ε / 4 := by
    refine le_trans (abs_gradedPrimeMean_le k _ hX2) ?_
    have hq := hP X hX2
    calc ((k : ℝ) + 1) * gradedMarcinkiewiczQuotient k (primeCoefficientTail b P) X
        ≤ ((k : ℝ) + 1) * (ε / (4 * ((k : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hq hk.le
      _ = ε / 4 := by field_simp
  rw [Real.norm_eq_abs, hsplit]
  have hfinal : |gradedPrimeMean k (primeCoefficientHead b P) X
        + gradedPrimeMean k (primeCoefficientTail b P) X| ≤ ε / 4 + ε / 4 :=
    le_trans (abs_add_le _ _) (add_le_add hheadbd htailbd)
  linarith
  
/-- The graded conormal reads the grade source as one. -/
theorem tendsto_gradedPrimeMean_gradeSource (k : ℕ) :
    Tendsto (gradedPrimeMean k (gradeSource k)) atTop (nhds 1) := by
  have hlim := (tendsto_gradedMarcinkiewiczQuotient_gradeSource k).const_mul ((k : ℝ) + 1)
  have hval : ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) = 1 := by
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with X hX
  rw [gradedMarcinkiewiczQuotient, gradedPrimeMean, primeLogMass_weightedEulerCoefficientSpaces]
  have hsum : (∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * |gradeSource k n|)
      = ∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * gradeSource k n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    rw [gradeSource, abs_of_nonneg (pow_nonneg hlogn k)]
  rw [hsum]
  ring

/-- **Equations (8)--(9).**  The graded conormal reads the grade-`k` coefficient. -/
theorem tendsto_gradedPrimeMean_of_gradedVanishingTail {k : ℕ} {b : ℕ → ℝ} {c : ℝ}
    (hb : MemGradedVanishingTailLayer k fun n => b n - c * gradeSource k n) :
    Tendsto (gradedPrimeMean k b) atTop (nhds c) := by
  have hzero := tendsto_gradedPrimeMean_zero_of_gradedVanishingTail hb
  have hsrc := (tendsto_gradedPrimeMean_gradeSource k).const_mul c
  rw [mul_one] at hsrc
  have hsum := hzero.add hsrc
  rw [zero_add] at hsum
  refine hsum.congr fun X => ?_
  have hsmul : gradedPrimeMean k (fun n => c * gradeSource k n) X
      = c * gradedPrimeMean k (gradeSource k) X := by
    rw [gradedPrimeMean, gradedPrimeMean]
    have hsum : (∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * (c * gradeSource k n))
        = c * ∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * gradeSource k n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hsum]
    ring
  rw [← hsmul, ← gradedPrimeMean_add]
  congr 1
  funext n
  ring


/-! ## Equations (19)--(20) and (31): every positive translation dies in every grade -/

theorem gradedMarcinkiewiczQuotient_le_marcinkiewicz (k : ℕ) (b : ℕ → ℝ) {X : ℕ} (hX : 2 ≤ X) :
    gradedMarcinkiewiczQuotient k b X ≤ marcinkiewiczLogQuotient b X / (Real.log 2) ^ k := by
  have hlog : 0 < Real.log X := log_cutoff_pos hX
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log 2 ≤ Real.log X := log_two_le_log_cutoff hX
  have hpow : (Real.log 2) ^ k ≤ (Real.log X) ^ k := pow_le_pow_left₀ hlog2.le hle k
  have hq : gradedMarcinkiewiczQuotient k b X
      = marcinkiewiczLogQuotient b X / (Real.log X) ^ k := by
    rw [gradedMarcinkiewiczQuotient, marcinkiewiczLogQuotient, pow_succ]
    field_simp
  rw [hq]
  have hnn : 0 ≤ marcinkiewiczLogQuotient b X :=
    div_nonneg (primeLogMass_nonneg_weightedEulerCoefficientSpaces b X) hlog.le
  refine div_le_div_of_nonneg_left hnn (by positivity) hpow
    
theorem memGradedVanishingTailLayer_of_memVanishingTailLayer (k : ℕ) {b : ℕ → ℝ}
    (hb : MemVanishingTailLayer b) : MemGradedVanishingTailLayer k b := by
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨P, hP⟩ := hb (ε * (Real.log 2) ^ k) (by positivity)
  refine ⟨P, fun X hX => ?_⟩
  refine le_trans (gradedMarcinkiewiczQuotient_le_marcinkiewicz k _ hX) ?_
  have h := hP X hX
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h, pow_pos hlog2 k]

theorem memGradedVanishingTailLayer_of_memCriticalSummableLayer (k : ℕ) {b : ℕ → ℝ}
    (hb : MemCriticalSummableLayer b) : MemGradedVanishingTailLayer k b :=
  memGradedVanishingTailLayer_of_memVanishingTailLayer k
    (memVanishingTailLayer_of_memCriticalSummableLayer hb)

theorem summable_gradedDyadicWeight {h : ℝ} (hh : 0 < h) (k : ℕ) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (k + 1) * ((2 : ℝ) ^ (-h)) ^ j) := by
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ (-h) := Real.rpow_pos_of_pos (by norm_num) _
  have hrlt : ‖((2 : ℝ) ^ (-h))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrpos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbase : Summable (fun m : ℕ => (m : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (-h)) ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one (k + 1) hrlt
  have hshift : Summable
      (fun j : ℕ => (((j + 1 : ℕ)) : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (-h)) ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hbase
  have hmul := hshift.mul_right ((2 : ℝ) ^ (-h))⁻¹
  refine hmul.congr fun j => ?_
  push_cast
  field_simp
  ring

/-- The graded dyadic constant. -/
def gradedDyadicConstant (h : ℝ) (k : ℕ) : ℝ :=
  ∑' j : ℕ, ((j : ℝ) + 1) ^ (k + 1) * ((2 : ℝ) ^ (-h)) ^ j

theorem sum_primeUnitTranslation_graded_block_le {b : ℕ → ℝ} {C h : ℝ} {k : ℕ} (hh : 0 < h)
    (hC : ∀ X : ℕ, 2 ≤ X → gradedMarcinkiewiczQuotient k b X ≤ C) (j N : ℕ) :
    ∑ p ∈ {p ∈ Nat.primesBelow N | Nat.log 2 p = j},
        Real.log p / p * |primeUnitTranslation h b p|
      ≤ C * (Real.log 2) ^ (k + 1) * (((j : ℝ) + 1) ^ (k + 1) * ((2 : ℝ) ^ (-h)) ^ j) := by
  classical
  set B := {p ∈ Nat.primesBelow N | Nat.log 2 p = j} with hB
  have hmem : ∀ p ∈ B, 2 ^ j ≤ p ∧ p < 2 ^ (j + 1) ∧ p.Prime := by
    intro p hp
    obtain ⟨hpmem, hlog⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hpp⟩ := Nat.mem_primesBelow.mp hpmem
    refine ⟨?_, ?_, hpp⟩
    · rw [← hlog]
      exact Nat.pow_log_le_self 2 hpp.pos.ne'
    · rw [← hlog]
      exact Nat.lt_pow_succ_log_self one_lt_two p
  have hterm : ∀ p ∈ B, Real.log p / p * |primeUnitTranslation h b p|
      ≤ ((2 : ℝ) ^ (-h)) ^ j * (Real.log p / p * |b p|) := by
    intro p hp
    obtain ⟨hlow, -, hpp⟩ := hmem p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hcast : ((2 : ℝ) ^ j) ≤ (p : ℝ) := by exact_mod_cast hlow
    have hpow : (p : ℝ) ^ (-h) ≤ ((2 : ℝ) ^ j) ^ (-h) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_neg h2j.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos h2j _) (Real.rpow_le_rpow h2j.le hcast hh.le)
    have hrw : ((2 : ℝ) ^ j) ^ (-h) = ((2 : ℝ) ^ (-h)) ^ j := by
      rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast ((2 : ℝ) ^ (-h)) j, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [hrw] at hpow
    have hmass : (0 : ℝ) ≤ Real.log p / p * |b p| := primeLog_term_nonneg b p
    have habs : |primeUnitTranslation h b p| = (p : ℝ) ^ (-h) * |b p| := by
      rw [primeUnitTranslation, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp0 _)]
    rw [habs]
    calc Real.log p / p * ((p : ℝ) ^ (-h) * |b p|)
        = (p : ℝ) ^ (-h) * (Real.log p / p * |b p|) := by ring
      _ ≤ ((2 : ℝ) ^ (-h)) ^ j * (Real.log p / p * |b p|) :=
          mul_le_mul_of_nonneg_right hpow hmass
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : B ⊆ (Finset.Icc 1 (2 ^ (j + 1))).filter Nat.Prime := by
    intro p hp
    obtain ⟨-, hup, hpp⟩ := hmem p hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpp.one_lt.le.trans' (by norm_num), by omega⟩, hpp⟩
  have hmassle : ∑ p ∈ B, (Real.log p / p * |b p|) ≤ primeLogMass_weightedEulerCoefficientSpaces b (2 ^ (j + 1)) := by
    rw [primeLogMass_weightedEulerCoefficientSpaces]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => primeLog_term_nonneg b p
  have hbound : primeLogMass_weightedEulerCoefficientSpaces b (2 ^ (j + 1))
      ≤ C * (((j : ℝ) + 1) * Real.log 2) ^ (k + 1) := by
    have h2 : 2 ≤ 2 ^ (j + 1) := Nat.le_self_pow (by omega) 2
    have hq := hC (2 ^ (j + 1)) h2
    have hlogpow : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 1) * Real.log 2 := by
      push_cast
      rw [Real.log_pow]
      push_cast
      ring
    rw [gradedMarcinkiewiczQuotient, hlogpow, div_le_iff₀ (by positivity)] at hq
    exact hq
  have hgeo : (0 : ℝ) ≤ ((2 : ℝ) ^ (-h)) ^ j := by positivity
  have hexp : C * (((j : ℝ) + 1) * Real.log 2) ^ (k + 1)
      = C * (Real.log 2) ^ (k + 1) * ((j : ℝ) + 1) ^ (k + 1) := by
    rw [mul_pow]
    ring
  rw [hexp] at hbound
  nlinarith [hmassle, hbound, hgeo]

/-- **Equations (19)--(20).**  Every positive Euler translation of a grade-`k` Marcinkiewicz
field is absolutely summable, hence lands in the grade-`k` vanishing-tail layer. -/
theorem memCriticalSummableLayer_primeUnitTranslation_graded {b : ℕ → ℝ} {h : ℝ} {k : ℕ}
    (hh : 0 < h) (hb : MemGradedMarcinkiewiczLayer k b) :
    MemCriticalSummableLayer (primeUnitTranslation h b) := by
  classical
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := by
    have h2 := hC 2 le_rfl
    have hq : 0 ≤ gradedMarcinkiewiczQuotient k b 2 :=
      gradedMarcinkiewiczQuotient_nonneg k b (le_refl 2)
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsummable := summable_gradedDyadicWeight hh k
  refine summable_of_sum_range_le
    (c := C * (Real.log 2) ^ (k + 1) * gradedDyadicConstant h k) ?_ ?_
  · intro n
    by_cases hp : n.Prime
    · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp)]
      exact primeLog_term_nonneg _ n
    · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp)]
  · intro n
    have hfilter : ∑ i ∈ Finset.range n,
        ({p : ℕ | p.Prime}.indicator fun m => Real.log m / m * |primeUnitTranslation h b m|) i
        = ∑ p ∈ Nat.primesBelow n, Real.log p / p * |primeUnitTranslation h b p| := by
      rw [show Nat.primesBelow n = (Finset.range n).filter Nat.Prime from rfl,
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hp : i.Prime
      · rw [Set.indicator_of_mem (show i ∈ {p : ℕ | p.Prime} from hp), if_pos hp]
      · rw [Set.indicator_of_notMem (show i ∉ {p : ℕ | p.Prime} from hp), if_neg hp]
    rw [hfilter]
    have hmaps : ∀ p ∈ Nat.primesBelow n, Nat.log 2 p ∈ Finset.range (Nat.log 2 n + 1) := by
      intro p hp
      obtain ⟨hpn, -⟩ := Nat.mem_primesBelow.mp hp
      rw [Finset.mem_range]
      have : Nat.log 2 p ≤ Nat.log 2 n := Nat.log_mono_right hpn.le
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun p => Real.log p / p * |primeUnitTranslation h b p|)]
    refine le_trans (Finset.sum_le_sum (fun j _ =>
      sum_primeUnitTranslation_graded_block_le hh hC j n)) ?_
    rw [← Finset.mul_sum]
    have hpart : ∑ j ∈ Finset.range (Nat.log 2 n + 1),
        ((j : ℝ) + 1) ^ (k + 1) * ((2 : ℝ) ^ (-h)) ^ j ≤ gradedDyadicConstant h k :=
      hsummable.sum_le_tsum _ (fun j _ => by positivity)
    have hCl : (0 : ℝ) ≤ C * (Real.log 2) ^ (k + 1) := by positivity
    exact mul_le_mul_of_nonneg_left hpart hCl

theorem memGradedVanishingTailLayer_primeUnitTranslation {b : ℕ → ℝ} {h : ℝ} {k r : ℕ}
    (hh : 0 < h) (hb : MemGradedMarcinkiewiczLayer k b) :
    MemGradedVanishingTailLayer r (primeUnitTranslation h b) :=
  memGradedVanishingTailLayer_of_memCriticalSummableLayer r
    (memCriticalSummableLayer_primeUnitTranslation_graded hh hb)

/-- **Equation (19).**  The graded conormal annihilates every positive translation. -/
theorem tendsto_gradedPrimeMean_primeUnitTranslation_zero {b : ℕ → ℝ} {h : ℝ} {k : ℕ}
    (hh : 0 < h) (hb : MemGradedMarcinkiewiczLayer k b) :
    Tendsto (gradedPrimeMean k (primeUnitTranslation h b)) atTop (nhds 0) :=
  tendsto_gradedPrimeMean_zero_of_gradedVanishingTail
    (memGradedVanishingTailLayer_primeUnitTranslation hh hb)


/-! ## The graded layers form a subspace -/

theorem gradedMarcinkiewiczQuotient_add_le (k : ℕ) (b b' : ℕ → ℝ) {X : ℕ} (hX : 2 ≤ X) :
    gradedMarcinkiewiczQuotient k (fun n => b n + b' n) X
      ≤ gradedMarcinkiewiczQuotient k b X + gradedMarcinkiewiczQuotient k b' X := by
  have hlog : 0 < Real.log X := log_cutoff_pos hX
  have hpow : (0 : ℝ) < (Real.log X) ^ (k + 1) := by positivity
  rw [gradedMarcinkiewiczQuotient, gradedMarcinkiewiczQuotient, gradedMarcinkiewiczQuotient,
    ← add_div]
  exact div_le_div_of_nonneg_right (primeLogMass_add_le b b' X) hpow.le

theorem gradedMarcinkiewiczQuotient_smul (k : ℕ) (r : ℝ) (b : ℕ → ℝ) (X : ℕ) :
    gradedMarcinkiewiczQuotient k (fun n => r * b n) X
      = |r| * gradedMarcinkiewiczQuotient k b X := by
  rw [gradedMarcinkiewiczQuotient, gradedMarcinkiewiczQuotient, primeLogMass_smul]
  ring

theorem memGradedMarcinkiewiczLayer_add {k : ℕ} {b b' : ℕ → ℝ}
    (hb : MemGradedMarcinkiewiczLayer k b) (hb' : MemGradedMarcinkiewiczLayer k b') :
    MemGradedMarcinkiewiczLayer k (fun n => b n + b' n) := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨C', hC'⟩ := hb'
  exact ⟨C + C', fun X hX => le_trans (gradedMarcinkiewiczQuotient_add_le k b b' hX)
    (add_le_add (hC X hX) (hC' X hX))⟩

theorem memGradedMarcinkiewiczLayer_smul {k : ℕ} {b : ℕ → ℝ} (r : ℝ)
    (hb : MemGradedMarcinkiewiczLayer k b) :
    MemGradedMarcinkiewiczLayer k (fun n => r * b n) := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨|r| * max C 0, fun X hX => ?_⟩
  rw [gradedMarcinkiewiczQuotient_smul]
  exact mul_le_mul_of_nonneg_left (le_trans (hC X hX) (le_max_left C 0)) (abs_nonneg r)

theorem memGradedMarcinkiewiczLayer_of_memGradedVanishingTailLayer {k : ℕ} {b : ℕ → ℝ}
    (hb : MemGradedVanishingTailLayer k b) : MemGradedMarcinkiewiczLayer k b := by
  obtain ⟨P, hP⟩ := hb 1 (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨primeLogMass_weightedEulerCoefficientSpaces b P / (Real.log 2) ^ (k + 1) + 1, fun X hX => ?_⟩
  have hlog : 0 < Real.log X := log_cutoff_pos hX
  have hpow : (0 : ℝ) < (Real.log X) ^ (k + 1) := by positivity
  have hpow2 : (Real.log 2) ^ (k + 1) ≤ (Real.log X) ^ (k + 1) :=
    pow_le_pow_left₀ hlog2.le (log_two_le_log_cutoff hX) _
  have hsplit := primeLogMass_head_add_tail b P X
  have hhead : primeLogMass_weightedEulerCoefficientSpaces (primeCoefficientHead b P) X / (Real.log X) ^ (k + 1)
      ≤ primeLogMass_weightedEulerCoefficientSpaces b P / (Real.log 2) ^ (k + 1) := by
    refine le_trans (div_le_div_of_nonneg_right (primeLogMass_head_le b P X) hpow.le) ?_
    exact div_le_div_of_nonneg_left (primeLogMass_nonneg_weightedEulerCoefficientSpaces b P) (by positivity) hpow2
  have htail := hP X hX
  rw [gradedMarcinkiewiczQuotient] at htail ⊢
  rw [hsplit, add_div]
  linarith

/-! ## Equations (15), (21) and (31) -/

/-- **Equation (15).**  The logarithmic clock raises the conormal degree: `q_{k+1} ∘ L = q_k`. -/
theorem tendsto_gradedPrimeMean_logClock {k : ℕ} {b : ℕ → ℝ} {c : ℝ}
    (hb : MemGradedVanishingTailLayer k fun n => b n - c * gradeSource k n) :
    Tendsto (gradedPrimeMean (k + 1) (logClock b)) atTop (nhds c) := by
  refine tendsto_gradedPrimeMean_of_gradedVanishingTail ?_
  have h := memGradedVanishingTailLayer_logClock hb
  have hfun : logClock (fun n => b n - c * gradeSource k n)
      = fun n => logClock b n - c * gradeSource (k + 1) n := by
    funext n
    rw [logClock, logClock, gradeSource, gradeSource, pow_succ]
    ring
  rwa [hfun] at h

/-- **Equation (21).**  The graded source module is cyclic over the logarithmic clock. -/
theorem logClock_iterate_gradeSource (k : ℕ) :
    logClock^[k] (gradeSource 0) = gradeSource k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, logClock_gradeSource]

/-- **Equation (31).**  The complete source defect `I − S_h` is detected by the graded conormal
with eigenvalue one in every grade. -/
theorem tendsto_gradedPrimeMean_gradedSourceDefect {k : ℕ} {b : ℕ → ℝ} {c h : ℝ} (hh : 0 < h)
    (hb : MemGradedVanishingTailLayer k fun n => b n - c * gradeSource k n) :
    Tendsto (gradedPrimeMean k fun n => b n - primeUnitTranslation h b n) atTop (nhds c) := by
  have hbM : MemGradedMarcinkiewiczLayer k b := by
    have h1 : MemGradedMarcinkiewiczLayer k (fun n => b n - c * gradeSource k n) :=
      memGradedMarcinkiewiczLayer_of_memGradedVanishingTailLayer hb
    have h2 : MemGradedMarcinkiewiczLayer k (fun n => c * gradeSource k n) :=
      memGradedMarcinkiewiczLayer_smul c (memGradedMarcinkiewiczLayer_gradeSource k)
    have h3 := memGradedMarcinkiewiczLayer_add h1 h2
    have hfun : (fun n => (b n - c * gradeSource k n) + c * gradeSource k n) = b := by
      funext n
      ring
    rwa [hfun] at h3
  have h1 := tendsto_gradedPrimeMean_of_gradedVanishingTail hb
  have h2 := tendsto_gradedPrimeMean_primeUnitTranslation_zero hh hbM
  have hsub := h1.sub h2
  rw [sub_zero] at hsub
  exact hsub.congr fun X => (gradedPrimeMean_sub k b (primeUnitTranslation h b) X).symm

/-- **The graded logarithmic corona tower.**  In every grade the conormal reads the grade source,
annihilates every positive translation, detects the complete defect with eigenvalue one, and is
raised one degree by the logarithmic clock. -/
theorem mertensGradedCoronaTower {k : ℕ} {b : ℕ → ℝ} {c h : ℝ} (hh : 0 < h)
    (hb : MemGradedVanishingTailLayer k fun n => b n - c * gradeSource k n) :
    Tendsto (gradedPrimeMean k b) atTop (nhds c)
      ∧ Tendsto (gradedPrimeMean k (primeUnitTranslation h b)) atTop (nhds 0)
      ∧ Tendsto (gradedPrimeMean k fun n => b n - primeUnitTranslation h b n) atTop (nhds c)
      ∧ Tendsto (gradedPrimeMean (k + 1) (logClock b)) atTop (nhds c) := by
  have hbM : MemGradedMarcinkiewiczLayer k b := by
    have h1 : MemGradedMarcinkiewiczLayer k (fun n => b n - c * gradeSource k n) :=
      memGradedMarcinkiewiczLayer_of_memGradedVanishingTailLayer hb
    have h2 : MemGradedMarcinkiewiczLayer k (fun n => c * gradeSource k n) :=
      memGradedMarcinkiewiczLayer_smul c (memGradedMarcinkiewiczLayer_gradeSource k)
    have h3 := memGradedMarcinkiewiczLayer_add h1 h2
    have hfun : (fun n => (b n - c * gradeSource k n) + c * gradeSource k n) = b := by
      funext n
      ring
    rwa [hfun] at h3
  exact ⟨tendsto_gradedPrimeMean_of_gradedVanishingTail hb,
    tendsto_gradedPrimeMean_primeUnitTranslation_zero hh hbM,
    tendsto_gradedPrimeMean_gradedSourceDefect hh hb,
    tendsto_gradedPrimeMean_logClock hb⟩


/-- **Equation (20).**  No finite number of clock derivatives can promote a positively shifted
source into a nonzero corona class. -/
theorem memGradedVanishingTailLayer_logClock_iterate {k r : ℕ} {b : ℕ → ℝ}
    (hb : MemGradedVanishingTailLayer k b) :
    MemGradedVanishingTailLayer (k + r) (logClock^[r] b) := by
  induction r with
  | zero => simpa using hb
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      have hstep := memGradedVanishingTailLayer_logClock ih
      have hk : k + (r + 1) = (k + r) + 1 := by omega
      rw [hk]
      exact hstep

/-- **Equation (20).**  `q_{k+r} ∘ L^r ∘ S_h = 0` for every `h > 0` and every `r`. -/
theorem tendsto_gradedPrimeMean_logClock_iterate_primeUnitTranslation {b : ℕ → ℝ} {h : ℝ}
    {k r : ℕ} (hh : 0 < h) (hb : MemGradedMarcinkiewiczLayer k b) :
    Tendsto (gradedPrimeMean (k + r) (logClock^[r] (primeUnitTranslation h b))) atTop
      (nhds 0) :=
  tendsto_gradedPrimeMean_zero_of_gradedVanishingTail
    (memGradedVanishingTailLayer_logClock_iterate
      (memGradedVanishingTailLayer_primeUnitTranslation hh hb))

end

end RHTower

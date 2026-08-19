import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.RHTower.CausalLaplacePlancherel
import GaloisForLFunctions.RHTower.MobiusCenteredSchurBoundary

/-!
# The weighted Mertens boundary vector

`mobius-schur-centered-boundary-limit-law.md`, equations `(13)` and `(16)`:

```text
m_omega(t) = c_omega ( sum_{n <= e^t} mu(n) n^{-1-2 omega} - 1/zeta(1+2 omega) ) ,
m_0(t)     = sum_{n <= e^t} mu(n)/n .
```

The centered prelimit vector is exactly minus `c_omega` times the Möbius Dirichlet tail beyond
`e^t`, hence decays like `e^{-omega t}` and lies in `L¹ ∩ L²(0,∞)`.
-/

open Complex MeasureTheory Set Filter ArithmeticFunction LSeries
open scoped BigOperators Topology LSeries.notation Moebius

noncomputable section
namespace RHTower

/-! ### The Möbius Dirichlet weight at a real abscissa -/

/-- The Möbius Dirichlet weight `mu(n) n^{-a}`, with the harmless zero coefficient. -/
def mobiusRealWeight (a : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (((n : ℝ) ^ (-a) : ℝ) : ℂ)

theorem mobiusRealWeight_eq_term (a : ℝ) (n : ℕ) :
    mobiusRealWeight a n = LSeries.term (↗μ) ((a : ℝ) : ℂ) n := by
  by_cases hn : n = 0
  · subst n
    simp [mobiusRealWeight]
  · rw [mobiusRealWeight, if_neg hn, LSeries.term_of_ne_zero hn]
    have hcast : ((n : ℂ)) ^ ((a : ℝ) : ℂ) = (((n : ℝ) ^ a : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    rw [hcast]
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Real.rpow_neg hnpos.le]
    push_cast
    field_simp

theorem norm_mobiusRealWeight_le (a : ℝ) (n : ℕ) :
    ‖mobiusRealWeight a n‖ ≤ (n : ℝ) ^ (-a) := by
  by_cases hn : n = 0
  · subst n
    simp [mobiusRealWeight]
    positivity
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [mobiusRealWeight, if_neg hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hnpos.le _)]
    have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      have := ArithmeticFunction.abs_moebius_le_one (n := n)
      exact_mod_cast this
    nlinarith [Real.rpow_nonneg hnpos.le (-a)]

theorem summable_mobiusRealWeight {a : ℝ} (ha : 1 < a) : Summable (mobiusRealWeight a) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_mobiusRealWeight_le a)
    (Real.summable_nat_rpow.mpr (by linarith))

theorem tsum_mobiusRealWeight {a : ℝ} (ha : 1 < a) :
    (∑' n : ℕ, mobiusRealWeight a n) = (riemannZeta ((a : ℝ) : ℂ))⁻¹ := by
  have hre : 1 < (((a : ℝ) : ℂ)).re := by simpa using ha
  rw [show (∑' n : ℕ, mobiusRealWeight a n) = ∑' n : ℕ, LSeries.term (↗μ) ((a : ℝ) : ℂ) n from
    tsum_congr (mobiusRealWeight_eq_term a)]
  exact LSeries_moebius_eq_inv_riemannZeta hre

/-! ### Partial sums and tails at the exponential cutoff -/

/-- The Möbius partial sum up to `e^t`. -/
def mobiusWeightedPartial (a t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊Real.exp t⌋₊ + 1), mobiusRealWeight a n

/-- The Möbius Dirichlet tail beyond `e^t`. -/
def mobiusWeightedTail (a t : ℝ) : ℂ :=
  ∑' n : ℕ, if Real.exp t < (n : ℝ) then mobiusRealWeight a n else 0

theorem mobiusWeightedTail_eq_shift (a t : ℝ) :
    (fun n : ℕ => if Real.exp t < (n : ℝ) then mobiusRealWeight a n else 0)
      = fun n : ℕ => if ⌊Real.exp t⌋₊ + 1 ≤ n then mobiusRealWeight a n else 0 := by
  funext n
  have hexp : (0 : ℝ) ≤ Real.exp t := (Real.exp_pos t).le
  by_cases h : Real.exp t < (n : ℝ)
  · rw [if_pos h, if_pos (by
      have := (Nat.floor_lt hexp).mpr h
      omega)]
  · rw [if_neg h, if_neg (by
      intro hc
      apply h
      have : ⌊Real.exp t⌋₊ < n := by omega
      exact (Nat.floor_lt hexp).mp this)]

theorem summable_mobiusWeightedTailTerm {a : ℝ} (ha : 1 < a) (t : ℝ) :
    Summable (fun n : ℕ => if Real.exp t < (n : ℝ) then mobiusRealWeight a n else 0) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_nat_rpow.mpr (by linarith : (-a : ℝ) < -1))
  by_cases h : Real.exp t < (n : ℝ)
  · rw [if_pos h]
    exact norm_mobiusRealWeight_le a n
  · rw [if_neg h, norm_zero]
    positivity

/-- **The exact centering identity.**  Partial sum plus tail is the reciprocal zeta value. -/
theorem mobiusWeightedTail_eq_tsum_shift {a : ℝ} (ha : 1 < a) (t : ℝ) :
    mobiusWeightedTail a t = ∑' i : ℕ, mobiusRealWeight a (i + (⌊Real.exp t⌋₊ + 1)) := by
  have hsum0 := summable_mobiusWeightedTailTerm ha t
  rw [mobiusWeightedTail, mobiusWeightedTail_eq_shift]
  rw [mobiusWeightedTail_eq_shift] at hsum0
  have hsplit := hsum0.sum_add_tsum_nat_add (⌊Real.exp t⌋₊ + 1)
  have hlow : (∑ i ∈ Finset.range (⌊Real.exp t⌋₊ + 1),
      (if ⌊Real.exp t⌋₊ + 1 ≤ i then mobiusRealWeight a i else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg (by
      have : i < ⌊Real.exp t⌋₊ + 1 := Finset.mem_range.mp hi
      omega)]
  have hhigh : (fun i : ℕ =>
      if ⌊Real.exp t⌋₊ + 1 ≤ i + (⌊Real.exp t⌋₊ + 1) then
        mobiusRealWeight a (i + (⌊Real.exp t⌋₊ + 1)) else 0)
      = fun i : ℕ => mobiusRealWeight a (i + (⌊Real.exp t⌋₊ + 1)) := by
    funext i
    rw [if_pos (by omega)]
  rw [hlow, zero_add, hhigh] at hsplit
  exact hsplit.symm

theorem mobiusWeightedPartial_add_tail {a : ℝ} (ha : 1 < a) (t : ℝ) :
    mobiusWeightedPartial a t + mobiusWeightedTail a t = (riemannZeta ((a : ℝ) : ℂ))⁻¹ := by
  rw [mobiusWeightedTail_eq_tsum_shift ha t, mobiusWeightedPartial]
  have h := (summable_mobiusRealWeight ha).sum_add_tsum_nat_add (⌊Real.exp t⌋₊ + 1)
  rw [h, tsum_mobiusRealWeight ha]

/-! ### Exponential decay of the tail -/

theorem norm_mobiusWeightedTail_le {ω : ℝ} (hω : 0 < ω) (t : ℝ) :
    ‖mobiusWeightedTail (1 + 2 * ω) t‖
      ≤ Real.exp (-(ω * t)) * ∑' n : ℕ, (n : ℝ) ^ (-(1 + ω)) := by
  have hsum := summable_mobiusWeightedTailTerm (a := 1 + 2 * ω) (by linarith) t
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + ω))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hterm : ∀ n : ℕ,
      ‖(if Real.exp t < (n : ℝ) then mobiusRealWeight (1 + 2 * ω) n else 0)‖
        ≤ Real.exp (-(ω * t)) * (n : ℝ) ^ (-(1 + ω)) := by
    intro n
    by_cases h : Real.exp t < (n : ℝ)
    · rw [if_pos h]
      have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (Real.exp_pos t) h
      have hbound := norm_mobiusRealWeight_le (1 + 2 * ω) n
      have hsplit : (n : ℝ) ^ (-(1 + 2 * ω)) = (n : ℝ) ^ (-(1 + ω)) * (n : ℝ) ^ (-ω) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
      have hmono : (n : ℝ) ^ (-ω) ≤ Real.exp t ^ (-ω) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos t) (le_of_lt h) (by linarith)
      have hexp : Real.exp t ^ (-ω) = Real.exp (-(ω * t)) := by
        rw [← Real.exp_mul]
        congr 1
        ring
      rw [hsplit] at hbound
      have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + ω)) := Real.rpow_nonneg hnpos.le _
      calc ‖mobiusRealWeight (1 + 2 * ω) n‖
          ≤ (n : ℝ) ^ (-(1 + ω)) * (n : ℝ) ^ (-ω) := hbound
        _ ≤ (n : ℝ) ^ (-(1 + ω)) * Real.exp (-(ω * t)) := by
            rw [← hexp]
            exact mul_le_mul_of_nonneg_left hmono hpos
        _ = Real.exp (-(ω * t)) * (n : ℝ) ^ (-(1 + ω)) := by ring
    · rw [if_neg h, norm_zero]
      have : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + ω)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      positivity
  calc ‖mobiusWeightedTail (1 + 2 * ω) t‖
      ≤ ∑' n : ℕ, ‖(if Real.exp t < (n : ℝ) then mobiusRealWeight (1 + 2 * ω) n else 0)‖ :=
        norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, Real.exp (-(ω * t)) * (n : ℝ) ^ (-(1 + ω)) :=
        Summable.tsum_le_tsum hterm hsum.norm (hbase.mul_left _)
    _ = Real.exp (-(ω * t)) * ∑' n : ℕ, (n : ℝ) ^ (-(1 + ω)) := tsum_mul_left


/-! ### The centered and critical Mertens vectors -/

/-- Card `(16)`: the centered prelimit weighted-Mertens vector, extended causally by zero. -/
def centeredMertensVector (ω : ℝ) (t : ℝ) : ℂ :=
  Set.indicator (Set.Ioi (0 : ℝ))
    (fun s => (1 / ((1 : ℂ) + (ω : ℂ))) *
      (mobiusWeightedPartial (1 + 2 * ω) s - (riemannZeta (((1 + 2 * ω : ℝ)) : ℂ))⁻¹)) t

/-- Card `(13)`: the critical weighted-Mertens vector `sum_{n <= e^t} mu(n)/n`. -/
def criticalMertensVector (t : ℝ) : ℂ :=
  Set.indicator (Set.Ioi (0 : ℝ)) (fun s => mobiusWeightedPartial 1 s) t

/-- The exponential decay constant of the centered vector. -/
def mertensDecayConstant (ω : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(1 + ω))

theorem mertensDecayConstant_nonneg (ω : ℝ) : 0 ≤ mertensDecayConstant ω :=
  tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem centeredMertensVector_eq_tail {ω : ℝ} (hω : 0 < ω) {t : ℝ} (ht : 0 < t) :
    centeredMertensVector ω t =
      -((1 / ((1 : ℂ) + (ω : ℂ))) * mobiusWeightedTail (1 + 2 * ω) t) := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  have hid := mobiusWeightedPartial_add_tail ha t
  rw [centeredMertensVector, Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
  have hrw : mobiusWeightedPartial (1 + 2 * ω) t - (riemannZeta (((1 + 2 * ω : ℝ)) : ℂ))⁻¹
      = -mobiusWeightedTail (1 + 2 * ω) t := by
    rw [← hid]
    ring
  rw [hrw]
  ring

theorem centeredMertensVector_of_nonpos (ω : ℝ) {t : ℝ} (ht : t ≤ 0) :
    centeredMertensVector ω t = 0 :=
  Set.indicator_of_notMem (by simpa using ht) _

theorem norm_inv_one_add_ofReal_le' {ω : ℝ} (hω : 0 < ω) :
    ‖(1 : ℂ) / ((1 : ℂ) + (ω : ℂ))‖ ≤ 1 := by
  rw [norm_div, norm_one]
  have hre : ((1 : ℂ) + (ω : ℂ)).re = 1 + ω := by simp
  have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) + (ω : ℂ)‖ := by
    have := Complex.re_le_norm ((1 : ℂ) + (ω : ℂ))
    rw [hre] at this
    linarith
  rw [div_le_one (by linarith)]
  linarith

/-- The centered vector decays exponentially on the causal ray. -/
theorem norm_centeredMertensVector_le {ω : ℝ} (hω : 0 < ω) (t : ℝ) :
    ‖centeredMertensVector ω t‖
      ≤ Set.indicator (Set.Ioi (0 : ℝ))
          (fun s => Real.exp (-ω * s) * mertensDecayConstant ω) t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [centeredMertensVector_of_nonpos ω ht, norm_zero,
      Set.indicator_of_notMem (by simpa using ht)]
  · rw [centeredMertensVector_eq_tail hω ht,
      Set.indicator_of_mem (Set.mem_Ioi.mpr ht), norm_neg, norm_mul]
    have hb := norm_mobiusWeightedTail_le hω t
    have hc := norm_inv_one_add_ofReal_le' hω
    have hexp : Real.exp (-(ω * t)) = Real.exp (-ω * t) := by
      congr 1
      ring
    rw [hexp] at hb
    have hnn : (0 : ℝ) ≤ Real.exp (-ω * t) * mertensDecayConstant ω := by
      have := mertensDecayConstant_nonneg ω
      positivity
    calc ‖(1 : ℂ) / ((1 : ℂ) + (ω : ℂ))‖ * ‖mobiusWeightedTail (1 + 2 * ω) t‖
        ≤ 1 * (Real.exp (-ω * t) * mertensDecayConstant ω) :=
          mul_le_mul hc hb (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _

theorem measurable_mobiusWeightedPartial (a : ℝ) : Measurable (mobiusWeightedPartial a) := by
  have hfloor : Measurable (fun t : ℝ => ⌊Real.exp t⌋₊) :=
    Nat.measurable_floor.comp Real.measurable_exp
  have hg : Measurable (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), mobiusRealWeight a n) :=
    Measurable.of_discrete
  exact hg.comp hfloor

theorem measurable_centeredMertensVector (ω : ℝ) : Measurable (centeredMertensVector ω) := by
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact ((measurable_mobiusWeightedPartial (1 + 2 * ω)).sub_const _).const_mul _

theorem measurable_criticalMertensVector : Measurable criticalMertensVector :=
  (measurable_mobiusWeightedPartial 1).indicator measurableSet_Ioi

theorem integrable_centeredMertensVector {ω : ℝ} (hω : 0 < ω) :
    Integrable (centeredMertensVector ω) := by
  have hmaj : Integrable
      (Set.indicator (Set.Ioi (0 : ℝ))
        (fun s : ℝ => Real.exp (-ω * s) * mertensDecayConstant ω)) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact (exp_neg_integrableOn_Ioi 0 hω).mul_const _
  refine Integrable.mono' hmaj (measurable_centeredMertensVector ω).aestronglyMeasurable ?_
  filter_upwards [] with t
  exact norm_centeredMertensVector_le hω t

theorem memLp_centeredMertensVector {ω : ℝ} (hω : 0 < ω) :
    MemLp (centeredMertensVector ω) 2 volume := by
  have hC0 : (0 : ℝ) ≤ mertensDecayConstant ω := mertensDecayConstant_nonneg ω
  have hsq : Integrable (fun t : ℝ => ‖centeredMertensVector ω t‖ ^ 2) := by
    have hmaj : Integrable
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun s : ℝ => Real.exp (-(2 * ω) * s) * mertensDecayConstant ω ^ 2)) := by
      rw [integrable_indicator_iff measurableSet_Ioi]
      exact (exp_neg_integrableOn_Ioi 0 (by linarith)).mul_const _
    refine Integrable.mono' hmaj
      (((measurable_centeredMertensVector ω).norm.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [] with t
    have hb := norm_centeredMertensVector_le hω t
    have h0 : (0 : ℝ) ≤ ‖centeredMertensVector ω t‖ := norm_nonneg _
    rcases le_or_gt t 0 with ht | ht
    · rw [Set.indicator_of_notMem (s := Set.Ioi (0 : ℝ)) (by simpa using ht)] at hb
      rw [Set.indicator_of_notMem (s := Set.Ioi (0 : ℝ)) (by simpa using ht)]
      have hzero : ‖centeredMertensVector ω t‖ = 0 := le_antisymm hb h0
      rw [hzero]
      norm_num
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht)] at hb
      rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
      have hsplit : Real.exp (-(2 * ω) * t) * mertensDecayConstant ω ^ 2
          = (Real.exp (-ω * t) * mertensDecayConstant ω) ^ 2 := by
        have hexp : Real.exp (-(2 * ω) * t)
            = Real.exp (-ω * t) * Real.exp (-ω * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        ring
      rw [hsplit, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ h0 hb 2
  exact (memLp_two_iff_integrable_sq_norm
    (measurable_centeredMertensVector ω).aestronglyMeasurable).mpr hsq


/-! ### The boundary Laplace transform of the centered vector -/

/-- The `n`-th causal atom of the centered vector's Laplace integrand. -/
def mertensAtom (ω y : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  Set.indicator (Set.Ioo (0 : ℝ) (Real.log n))
    (fun v : ℝ => -((1 / ((1 : ℂ) + (ω : ℂ))) * mobiusRealWeight (1 + 2 * ω) n) *
      Complex.exp (-((y : ℂ) * Complex.I) * (v : ℂ))) u

theorem mertensAtom_zero (ω y : ℝ) (u : ℝ) : mertensAtom ω y 0 u = 0 := by
  rw [mertensAtom]
  by_cases h : u ∈ Set.Ioo (0 : ℝ) (Real.log (0 : ℕ))
  · rw [Set.indicator_of_mem h]
    simp [mobiusRealWeight]
  · rw [Set.indicator_of_notMem h]

theorem norm_exp_neg_mul_I (y v : ℝ) :
    ‖Complex.exp (-((y : ℂ) * Complex.I) * (v : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (-((y : ℂ) * Complex.I) * (v : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

/-- Pointwise atomic decomposition of the Laplace integrand. -/
theorem tsum_mertensAtom {ω : ℝ} (hω : 0 < ω) (y : ℝ) (u : ℝ) :
    (∑' n : ℕ, mertensAtom ω y n u)
      = Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ)) * centeredMertensVector ω u := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  rcases le_or_gt u 0 with hu | hu
  · have hzero : ∀ n : ℕ, mertensAtom ω y n u = 0 := by
      intro n
      rw [mertensAtom, Set.indicator_of_notMem (by
        simp only [Set.mem_Ioo, not_and, not_lt]
        intro hc
        exact absurd hc (by linarith))]
    simp only [hzero, tsum_zero]
    rw [centeredMertensVector_of_nonpos ω hu, mul_zero]
  · have hcongr : ∀ n : ℕ, mertensAtom ω y n u
        = Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ)) *
          (-((1 / ((1 : ℂ) + (ω : ℂ))) *
            (if Real.exp u < (n : ℝ) then mobiusRealWeight (1 + 2 * ω) n else 0))) := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [mertensAtom_zero]
        have hlt : ¬ (Real.exp u < ((0 : ℕ) : ℝ)) := by
          simp only [Nat.cast_zero, not_lt]
          exact (Real.exp_pos u).le
        rw [if_neg hlt]
        simp
      · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hiff : u ∈ Set.Ioo (0 : ℝ) (Real.log n) ↔ Real.exp u < (n : ℝ) := by
          constructor
          · rintro ⟨-, h2⟩
            exact (Real.lt_log_iff_exp_lt hnpos).mp h2
          · intro h
            exact ⟨hu, (Real.lt_log_iff_exp_lt hnpos).mpr h⟩
        by_cases hmem : u ∈ Set.Ioo (0 : ℝ) (Real.log n)
        · rw [mertensAtom, Set.indicator_of_mem hmem, if_pos (hiff.mp hmem)]
          ring
        · rw [mertensAtom, Set.indicator_of_notMem hmem,
            if_neg (fun hc => hmem (hiff.mpr hc))]
          simp
    rw [tsum_congr hcongr, tsum_mul_left, tsum_neg, tsum_mul_left,
      centeredMertensVector_eq_tail hω hu, mobiusWeightedTail]

theorem integral_mertensAtom {ω y : ℝ} (hy : y ≠ 0) (n : ℕ) :
    (∫ u : ℝ, mertensAtom ω y n u)
      = -((1 / ((1 : ℂ) + (ω : ℂ))) * mobiusRealWeight (1 + 2 * ω) n) *
        ((1 - ((n : ℂ)) ^ (-((y : ℂ) * Complex.I))) / ((y : ℂ) * Complex.I)) := by
  have hc : -((y : ℂ) * Complex.I) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, Complex.I_ne_zero, or_false,
      Complex.ofReal_eq_zero]
    exact hy
  have hyI : (y : ℂ) * Complex.I ≠ 0 := by
    simpa using hc
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [mertensAtom_zero, integral_zero]
    simp [mobiusRealWeight]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    simp only [mertensAtom]
    rw [integral_indicator measurableSet_Ioo, integral_const_mul,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hlog, integral_exp_mul_complex hc]
    have hpow : Complex.exp (-((y : ℂ) * Complex.I) * ((Real.log n : ℝ) : ℂ))
        = ((n : ℂ)) ^ (-((y : ℂ) * Complex.I)) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne' : (n : ℂ) ≠ 0)]
      congr 1
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (le_of_lt hnpos)]
      ring
    rw [hpow]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
    ring


/-! ### The Fubini interchange and the exact transfer identity -/

theorem integrable_mertensAtom (ω y : ℝ) (n : ℕ) : Integrable (mertensAtom ω y n) := by
  refine (integrable_indicator_iff measurableSet_Ioo).mpr ?_
  have hbdd : IntegrableOn
      (fun _ : ℝ => ‖(1 / ((1 : ℂ) + (ω : ℂ))) * mobiusRealWeight (1 + 2 * ω) n‖)
      (Set.Ioo (0 : ℝ) (Real.log n)) volume :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  refine Integrable.mono' hbdd ?_ ?_
  · have hcont : Continuous fun v : ℝ =>
        -((1 / ((1 : ℂ) + (ω : ℂ)) * mobiusRealWeight (1 + 2 * ω) n)) *
          Complex.exp (-((y : ℂ) * Complex.I) * (v : ℂ)) := by fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with v
    rw [norm_mul, norm_neg, norm_exp_neg_mul_I, mul_one]

theorem integral_norm_mertensAtom_le {ω : ℝ} (hω : 0 < ω) (y : ℝ) (n : ℕ) :
    (∫ u : ℝ, ‖mertensAtom ω y n u‖) ≤ (n : ℝ) ^ (-(1 + ω)) / ω := by
  have hnorm : ∀ u : ℝ, ‖mertensAtom ω y n u‖
      = Set.indicator (Set.Ioo (0 : ℝ) (Real.log n))
        (fun _ : ℝ => ‖(1 / ((1 : ℂ) + (ω : ℂ))) * mobiusRealWeight (1 + 2 * ω) n‖) u := by
    intro u
    rw [mertensAtom]
    by_cases hmem : u ∈ Set.Ioo (0 : ℝ) (Real.log n)
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, norm_mul,
        norm_exp_neg_mul_I, mul_one, norm_neg]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, norm_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall hnorm),
    integral_indicator measurableSet_Ioo, setIntegral_const]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [mobiusRealWeight]
    positivity
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hcoef : ‖(1 / ((1 : ℂ) + (ω : ℂ))) * mobiusRealWeight (1 + 2 * ω) n‖
        ≤ (n : ℝ) ^ (-(1 + 2 * ω)) := by
      rw [norm_mul]
      have h1 := norm_inv_one_add_ofReal_le' hω
      have h2 := norm_mobiusRealWeight_le (1 + 2 * ω) n
      have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + 2 * ω)) := Real.rpow_nonneg hnpos.le _
      nlinarith [norm_nonneg (mobiusRealWeight (1 + 2 * ω) n)]
    have hlogb : Real.log n ≤ (n : ℝ) ^ ω / ω := Real.log_le_rpow_div hnpos.le hω
    have hvol : (volume : Measure ℝ).real (Set.Ioo (0 : ℝ) (Real.log n)) = Real.log n := by
      rw [measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hlog]
    rw [hvol, smul_eq_mul]
    have hsplit : (n : ℝ) ^ (-(1 + 2 * ω)) * ((n : ℝ) ^ ω / ω)
        = (n : ℝ) ^ (-(1 + ω)) / ω := by
      rw [div_eq_mul_inv, ← mul_assoc, ← Real.rpow_add hnpos, div_eq_mul_inv]
      congr 2
      ring
    calc Real.log n * ‖(1 / ((1 : ℂ) + (ω : ℂ))) * mobiusRealWeight (1 + 2 * ω) n‖
        ≤ ((n : ℝ) ^ ω / ω) * ((n : ℝ) ^ (-(1 + 2 * ω))) := by
          refine mul_le_mul hlogb hcoef (norm_nonneg _) (by positivity)
      _ = (n : ℝ) ^ (-(1 + ω)) / ω := by rw [← hsplit]; ring

theorem summable_integral_norm_mertensAtom {ω : ℝ} (hω : 0 < ω) (y : ℝ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖mertensAtom ω y n u‖) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + ω)) / ω) :=
    (Real.summable_nat_rpow.mpr (by linarith)).div_const ω
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _)
    (integral_norm_mertensAtom_le hω y) hbase

/-- **Card `(16)` transfer identity.**  The boundary Laplace transform of the centered
weighted-Mertens vector is the centered Schur difference quotient. -/
theorem laplaceBoundary_centeredMertensVector {ω : ℝ} (hω : 0 < ω) {y : ℝ} (hy : y ≠ 0) :
    laplaceBoundary (centeredMertensVector ω) y
      = centeredSchurQuotient ω ((y : ℂ) * Complex.I) := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  have hyI : (y : ℂ) * Complex.I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hy
  have hswap : (∑' n : ℕ, ∫ u : ℝ, mertensAtom ω y n u)
      = ∫ u : ℝ, (∑' n : ℕ, mertensAtom ω y n u) :=
    integral_tsum_of_summable_integral_norm (integrable_mertensAtom ω y)
      (summable_integral_norm_mertensAtom hω y)
  have hpt : (∫ u : ℝ, (∑' n : ℕ, mertensAtom ω y n u))
      = laplaceBoundary (centeredMertensVector ω) y := by
    rw [laplaceBoundary]
    exact integral_congr_ae (Filter.Eventually.of_forall (tsum_mertensAtom hω y))
  rw [← hpt, ← hswap]
  rw [show (∑' n : ℕ, ∫ u : ℝ, mertensAtom ω y n u)
      = ∑' n : ℕ, -((1 / ((1 : ℂ) + (ω : ℂ))) * mobiusRealWeight (1 + 2 * ω) n) *
        ((1 - ((n : ℂ)) ^ (-((y : ℂ) * Complex.I))) / ((y : ℂ) * Complex.I)) from
    tsum_congr (integral_mertensAtom hy)]
  -- split the two Dirichlet series
  have hshift : ∀ n : ℕ,
      mobiusRealWeight (1 + 2 * ω) n * ((n : ℂ)) ^ (-((y : ℂ) * Complex.I))
        = LSeries.term (↗μ) (((1 + 2 * ω : ℝ) : ℂ) + (y : ℂ) * Complex.I) n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [mobiusRealWeight]
    · have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      rw [mobiusRealWeight_eq_term, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
        Complex.cpow_add _ _ hne, Complex.cpow_neg]
      field_simp
  have hsum1 : Summable (mobiusRealWeight (1 + 2 * ω)) := summable_mobiusRealWeight ha
  have hre2 : 1 < ((((1 + 2 * ω : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  have hsum2 : Summable (fun n : ℕ =>
      mobiusRealWeight (1 + 2 * ω) n * ((n : ℂ)) ^ (-((y : ℂ) * Complex.I))) := by
    refine Summable.congr (LSeriesSummable_moebius_iff.mpr hre2) fun n => (hshift n).symm
  have hsplit : (∑' n : ℕ, -((1 / ((1 : ℂ) + (ω : ℂ))) * mobiusRealWeight (1 + 2 * ω) n) *
        ((1 - ((n : ℂ)) ^ (-((y : ℂ) * Complex.I))) / ((y : ℂ) * Complex.I)))
      = -((1 / ((1 : ℂ) + (ω : ℂ))) / ((y : ℂ) * Complex.I)) *
        ((∑' n : ℕ, mobiusRealWeight (1 + 2 * ω) n) -
          ∑' n : ℕ, mobiusRealWeight (1 + 2 * ω) n * ((n : ℂ)) ^ (-((y : ℂ) * Complex.I))) := by
    rw [← hsum1.tsum_sub hsum2, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    field_simp
  rw [hsplit, tsum_mobiusRealWeight ha]
  rw [show (∑' n : ℕ, mobiusRealWeight (1 + 2 * ω) n * ((n : ℂ)) ^ (-((y : ℂ) * Complex.I)))
      = (riemannZeta ((((1 + 2 * ω : ℝ) : ℂ) + (y : ℂ) * Complex.I)))⁻¹ from by
    rw [tsum_congr hshift]
    exact LSeries_moebius_eq_inv_riemannZeta hre2]
  rw [centeredSchurQuotient]
  have hcast : ((1 + 2 * ω : ℝ) : ℂ) = 1 + 2 * (ω : ℂ) := by push_cast; ring
  rw [hcast]
  field_simp
  ring


/-! ### The pointwise critical limit of the centered vector -/

theorem tendsto_mobiusRealWeight_one (n : ℕ) :
    Tendsto (fun ω : ℝ => mobiusRealWeight (1 + 2 * ω) n)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (mobiusRealWeight 1 n)) := by
  by_cases hn : n = 0
  · subst n
    simp only [mobiusRealWeight]
    exact tendsto_const_nhds
  · have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hcont : ContinuousAt (fun a : ℝ =>
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (((n : ℝ) ^ (-a) : ℝ) : ℂ)) 1 := by
      have h1 : ContinuousAt (fun a : ℝ => ((n : ℝ) ^ (-a) : ℝ)) 1 := by
        have hbase : Continuous fun a : ℝ => ((n : ℝ) ^ a : ℝ) :=
          Real.continuous_const_rpow (ne_of_gt hnpos)
        exact (hbase.continuousAt).comp continuousAt_neg
      exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp h1)
    have harg : Tendsto (fun ω : ℝ => 1 + 2 * ω)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
      have hc : Continuous fun ω : ℝ => 1 + 2 * ω := by fun_prop
      have h := hc.tendsto (0 : ℝ)
      simpa using h.mono_left nhdsWithin_le_nhds
    have hlim := hcont.tendsto.comp harg
    simp only [mobiusRealWeight, if_neg hn]
    exact hlim

theorem tendsto_mobiusWeightedPartial_one (t : ℝ) :
    Tendsto (fun ω : ℝ => mobiusWeightedPartial (1 + 2 * ω) t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (mobiusWeightedPartial 1 t)) := by
  simp only [mobiusWeightedPartial]
  exact tendsto_finsetSum _ fun n _ => tendsto_mobiusRealWeight_one n

/-- **Card `(17)` pointwise.**  The centered prelimit vector converges pointwise to the critical
weighted-Mertens vector. -/
theorem tendsto_centeredMertensVector_pointwise (t : ℝ) :
    Tendsto (fun ω : ℝ => centeredMertensVector ω t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (criticalMertensVector t)) := by
  rcases le_or_gt t 0 with ht | ht
  · have hzero : ∀ ω : ℝ, centeredMertensVector ω t = 0 := fun ω =>
      centeredMertensVector_of_nonpos ω ht
    simp only [hzero]
    rw [criticalMertensVector, Set.indicator_of_notMem (by simpa using ht)]
    exact tendsto_const_nhds
  · have hc : Tendsto (fun ω : ℝ => (1 : ℂ) / ((1 : ℂ) + (ω : ℂ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
      have hcont : Continuous fun ω : ℝ => (1 : ℂ) + (ω : ℂ) := by fun_prop
      have h0 : (1 : ℂ) + ((0 : ℝ) : ℂ) = 1 := by push_cast; ring
      have h := hcont.tendsto (0 : ℝ)
      rw [h0] at h
      have hmono : Tendsto (fun ω : ℝ => (1 : ℂ) + (ω : ℂ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := h.mono_left nhdsWithin_le_nhds
      have hinv : Tendsto (fun ω : ℝ => ((1 : ℂ) + (ω : ℂ))⁻¹)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((1 : ℂ))⁻¹) := hmono.inv₀ one_ne_zero
      simpa [one_div] using hinv
    have hzeta : Tendsto (fun ω : ℝ => (riemannZeta (((1 + 2 * ω : ℝ)) : ℂ))⁻¹)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hbase := tendsto_inv_riemannZeta_one_add_two_mul
      refine hbase.congr' ?_
      filter_upwards [] with ω
      congr 2
      push_cast
      ring
    have hmain := hc.mul ((tendsto_mobiusWeightedPartial_one t).sub hzeta)
    rw [sub_zero, one_mul] at hmain
    rw [criticalMertensVector, Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
    refine hmain.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ω hω
    rw [centeredMertensVector, Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]

end RHTower


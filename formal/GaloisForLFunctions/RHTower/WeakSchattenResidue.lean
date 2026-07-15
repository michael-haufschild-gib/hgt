import GaloisForLFunctions.RHTower.SchattenApproximation
import Mathlib.Analysis.PSeries

/-!
# Weak Schatten classes and logarithmic critical residues

This file supplies the missing endpoint layer between approximation-number decay and exact
Schatten depth.  A positive logarithmic residue excludes the ordinary endpoint class, while a
weak endpoint bound places the operator in every strictly larger Schatten class.
-/

namespace RHTower

open ContinuousLinearMap Filter Finset
open scoped Topology

noncomputable section

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Weak Schatten `S_{p,∞}` membership, expressed by the critical approximation-number power
bound `a_n(T)^p = O(1/(n+1))`. -/
def MemWeakSchattenClass (p : ℝ) (T : H →L[ℂ] H) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    approxNumber T n ^ p ≤ C / ((n : ℝ) + 1)

/-- Partial `p`-energy of the approximation numbers. -/
def schattenPowerPartialSum (p : ℝ) (T : H →L[ℂ] H) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, approxNumber T n ^ p

/-- Ordinary logarithmic critical residue of the `p`-energy.  Existence of this honest limit is
the Connes measurability condition needed by the Gauss-channel card. -/
def HasSchattenLogResidue (p : ℝ) (T : H →L[ℂ] H) (R : ℝ) : Prop :=
  Tendsto (fun N : ℕ => schattenPowerPartialSum p T N / Real.log (N + 1))
    atTop (nhds R)

/-- Weak endpoint membership implies ordinary membership at every strictly larger exponent. -/
theorem MemWeakSchattenClass.memSchattenClass_of_lt
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) {T : H →L[ℂ] H}
    (hT : MemWeakSchattenClass p T) : MemSchattenClass q T := by
  obtain ⟨C, hC, hbound⟩ := hT
  have hr : 1 < q / p := (one_lt_div hp).2 hpq
  have hseries : Summable (fun n : ℕ => C ^ (q / p) / |(n : ℝ) + 1| ^ (q / p)) := by
    have hbase := (Real.summable_one_div_nat_add_rpow 1 (q / p)).2 hr
    simpa [div_eq_mul_inv] using hbase.mul_left (C ^ (q / p))
  apply hseries.of_nonneg_of_le
  · intro n
    exact Real.rpow_nonneg (approxNumber_nonneg T n) q
  · intro n
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hpow :
        approxNumber T n ^ q = (approxNumber T n ^ p) ^ (q / p) := by
      rw [← Real.rpow_mul (approxNumber_nonneg T n)]
      congr 1
      field_simp
    rw [hpow]
    calc
      (approxNumber T n ^ p) ^ (q / p)
          ≤ (C / ((n : ℝ) + 1)) ^ (q / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (approxNumber_nonneg T n) p) (hbound n)
          (le_of_lt (zero_lt_one.trans hr))
      _ = C ^ (q / p) / |(n : ℝ) + 1| ^ (q / p) := by
        rw [abs_of_pos hn, Real.div_rpow hC hn.le]

/-- A positive logarithmic residue rules out ordinary Schatten membership at the endpoint. -/
theorem HasSchattenLogResidue.not_memSchattenClass
    {p R : ℝ} (hR : 0 < R) {T : H →L[ℂ] H}
    (hres : HasSchattenLogResidue p T R) : ¬ MemSchattenClass p T := by
  intro hsum
  have hpartial : Tendsto (schattenPowerPartialSum p T) atTop
      (nhds (∑' n : ℕ, approxNumber T n ^ p)) := by
    simpa [schattenPowerPartialSum] using hsum.hasSum.tendsto_sum_nat
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hzero : Tendsto
      (fun N : ℕ => schattenPowerPartialSum p T N / Real.log (N + 1))
      atTop (nhds 0) := hpartial.div_atTop hlog
  have : R = 0 := tendsto_nhds_unique hres hzero
  exact hR.ne' this

/-- Weak endpoint membership plus a positive logarithmic residue gives exact critical Schatten
depth: no class at or below `p`, every class strictly above `p`. -/
theorem exact_schattenDepth_of_weak_of_positive_logResidue
    {p R : ℝ} (hp : 0 < p) (hR : 0 < R) {T : H →L[ℂ] H}
    (hweak : MemWeakSchattenClass p T)
    (hres : HasSchattenLogResidue p T R) :
    (∀ q : ℝ, 0 < q → q ≤ p → ¬ MemSchattenClass q T) ∧
      (∀ q : ℝ, p < q → MemSchattenClass q T) := by
  have hendpoint : ¬ MemSchattenClass p T := hres.not_memSchattenClass hR
  constructor
  · intro q hq hqp hqmem
    exact hendpoint (hqmem.mono hq hqp)
  · intro q hpq
    exact hweak.memSchattenClass_of_lt hp hpq

end

end

end RHTower

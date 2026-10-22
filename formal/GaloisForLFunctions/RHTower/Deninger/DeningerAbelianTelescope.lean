import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The telescoping weight of the Abelian theorem

Abel summation applied to a Dirichlet series replaces the coefficients by the partial sums and the
exponent by the increments `n^{-σ} - (n+1)^{-σ}`.  For every positive `σ` those increments are
nonnegative and sum to exactly one, so they are a probability weight on the partial sums — which is
the whole reason the Abelian limit reproduces the ordinary sum.

* `deningerAbelWeight` : the increment `n^{-σ} - (n+1)^{-σ}`.
* `deningerAbelWeight_nonneg` : it is nonnegative.
* `deningerAbelWeight_hasSum_one` : **the increments sum to one.**
-/

namespace RHTower

open Filter Topology

noncomputable section

/-- The Abel increment weight at index `n`, for exponent `σ`. -/
def deningerAbelWeight (σ : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (-σ) - ((n : ℝ) + 2) ^ (-σ)

theorem deningerAbelWeight_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (n : ℕ) :
    0 ≤ deningerAbelWeight σ n := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) := by linarith
  have h2pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hpow : ((n : ℝ) + 1) ^ σ ≤ ((n : ℝ) + 2) ^ σ := Real.rpow_le_rpow h1.le h2 hσ
  have hppos : (0 : ℝ) < ((n : ℝ) + 1) ^ σ := Real.rpow_pos_of_pos h1 σ
  have hinv : (((n : ℝ) + 2) ^ σ)⁻¹ ≤ (((n : ℝ) + 1) ^ σ)⁻¹ :=
    one_div_le_one_div_of_le hppos hpow |>.trans_eq (by rw [one_div]) |>.trans_eq' (by rw [one_div])
  have hmono : ((n : ℝ) + 2) ^ (-σ) ≤ ((n : ℝ) + 1) ^ (-σ) := by
    rw [Real.rpow_neg h2pos.le, Real.rpow_neg h1.le]
    exact hinv
  rw [deningerAbelWeight]
  linarith

/-- The partial sums of the increments telescope. -/
theorem deningerAbelWeight_sum_range (σ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, deningerAbelWeight σ n)
      = 1 - ((N : ℝ) + 1) ^ (-σ) := by
  have hstep := Finset.sum_range_sub' (fun i : ℕ => ((i : ℝ) + 1) ^ (-σ)) N
  have hcongr : ∀ n ∈ Finset.range N,
      deningerAbelWeight σ n
        = ((n : ℝ) + 1) ^ (-σ) - (((n + 1 : ℕ) : ℝ) + 1) ^ (-σ) := by
    intro n _
    rw [deningerAbelWeight]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hcongr, hstep]
  norm_num

/-- **The Abel increments sum to one.**  So for every positive exponent they form a probability
weight on the partial sums. -/
theorem deningerAbelWeight_hasSum_one {σ : ℝ} (hσ : 0 < σ) :
    HasSum (deningerAbelWeight σ) 1 := by
  have htail : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-σ)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (tendsto_rpow_neg_atTop hσ).comp hbase
  have hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, deningerAbelWeight σ n)
      atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub htail
    rw [sub_zero] at this
    exact this.congr fun N => (deningerAbelWeight_sum_range σ N).symm
  exact (hasSum_iff_tendsto_nat_of_nonneg (deningerAbelWeight_nonneg hσ.le) 1).mpr hpartial

end

end RHTower

/-! ## The weight vanishes pointwise as the exponent goes to zero -/

namespace RHTower

noncomputable section

open Filter Topology

/-- **Each Abel increment vanishes as the exponent goes to zero.**  Both powers tend to one, so
their difference tends to zero.  Together with `deningerAbelWeight_hasSum_one` this is the whole
mechanism of the Abelian theorem: the weight is a probability weight whose finite head disappears
in the limit, so only the tail — where the partial sums are already near their limit — survives. -/
theorem deningerAbelWeight_tendsto_zero (n : ℕ) :
    Tendsto (fun σ : ℝ => deningerAbelWeight σ n) (𝓝 0) (𝓝 0) := by
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hneg : Tendsto (fun σ : ℝ => -σ) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ))
  have hA : Tendsto (fun σ : ℝ => ((n : ℝ) + 1) ^ (-σ)) (𝓝 0) (𝓝 1) := by
    have := (Real.continuousAt_const_rpow (a := (n : ℝ) + 1) (b := 0) h1).tendsto.comp hneg
    rwa [Real.rpow_zero] at this
  have hB : Tendsto (fun σ : ℝ => ((n : ℝ) + 2) ^ (-σ)) (𝓝 0) (𝓝 1) := by
    have := (Real.continuousAt_const_rpow (a := (n : ℝ) + 2) (b := 0) h2).tendsto.comp hneg
    rwa [Real.rpow_zero] at this
  have hsub := hA.sub hB
  rw [sub_self] at hsub
  exact hsub

/-- The same, along the exponents that are strictly positive. -/
theorem deningerAbelWeight_tendsto_zero_within (n : ℕ) :
    Tendsto (fun σ : ℝ => deningerAbelWeight σ n) (𝓝[>] 0) (𝓝 0) :=
  (deningerAbelWeight_tendsto_zero n).mono_left nhdsWithin_le_nhds

end

end RHTower

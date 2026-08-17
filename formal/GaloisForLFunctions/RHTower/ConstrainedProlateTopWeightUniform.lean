import GaloisForLFunctions.RHTower.ConstrainedProlateHermiteContrast
import GaloisForLFunctions.RHTower.RadialGramOffDiagonalDecay
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Depth-uniform bounds for the constrained-prolate top weight

The limiting secular root `θ_k = Q_k / Q_{k+1}`, with `Q_k = ∑_{j ≤ k} C(4j,2j)/16^j`, is already
known to lie in `(0,1)`.  For a constrained-prolate statement at a depth that grows with the
aperture, `θ_k > 0` is not enough: what is needed is a bound **independent of the depth**, because
the leakage of the `k`-th contrast is `θ_k d_{k+1}` and a decaying `θ_k` would degrade every
downstream constant.

This module supplies that.  Two facts:

* `θ_k ≥ 8/11` for **every** `k`, so the top weight never falls below its value at depth zero;
* `θ_k → 1`, because `Q_k` diverges — the weights `C(4j,2j)/16^j` are at least `1/(4j)`, which is
  exactly the size that makes the partial sums harmonic-divergent.

The second fact reverses the naive expectation.  The individual weights `C(4j,2j)/16^j` *decay*
like `j^{-1/2}`, so one might expect the top coefficient of a normalized contrast to decay too.
It does not: the weight is a ratio of partial sums, and partial sums of a nonsummable sequence
grow, so the ratio tends to one.

The lower bound `C(4j,2j)/16^j ≥ 1/(4j)` comes from `Nat.four_pow_le_two_mul_self_mul_centralBinom`
at argument `2j`; no asymptotic expansion of the central binomial coefficient is used.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## Monotonicity of the weight sums -/

theorem constrainedProlateHermiteWeightSum_mono {m k : ℕ} (h : m ≤ k) :
    constrainedProlateHermiteWeightSum m ≤ constrainedProlateHermiteWeightSum k := by
  unfold constrainedProlateHermiteWeightSum
  have hsub : Finset.range (m + 1) ⊆ Finset.range (k + 1) := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) (by omega))
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro j _ _
  exact (constrainedProlateHermiteWeight_pos j).le

theorem constrainedProlateHermiteWeightSum_ge_eleven_div_eight {k : ℕ} (hk : 1 ≤ k) :
    (11 : ℝ) / 8 ≤ constrainedProlateHermiteWeightSum k := by
  have h1 : constrainedProlateHermiteWeightSum 1 = 11 / 8 :=
    constrainedProlateHermiteWeightSum_one
  rw [← h1]
  exact constrainedProlateHermiteWeightSum_mono hk

/-! ## The depth-uniform floor -/

/-- **Depth-uniform floor.**  The limiting top weight never drops below its depth-zero value.
This is the statement a growing-depth constrained-prolate argument needs; `0 < θ_k` alone is not
enough, since a decaying `θ_k` would degrade every downstream constant. -/
theorem constrainedProlateHermiteTheta_ge_eight_div_eleven (k : ℕ) :
    (8 : ℝ) / 11 ≤ constrainedProlateHermiteTheta k := by
  match k with
  | 0 => rw [constrainedProlateHermiteTheta_zero]
  | (m + 1) =>
      have hQ : (11 : ℝ) / 8 ≤ constrainedProlateHermiteWeightSum (m + 1) :=
        constrainedProlateHermiteWeightSum_ge_eleven_div_eight (by omega)
      have hq : constrainedProlateHermiteWeight (m + 2) ≤ 1 / 2 :=
        constrainedProlateHermiteWeight_le_half_of_pos (by omega)
      have hqpos : 0 < constrainedProlateHermiteWeight (m + 2) :=
        constrainedProlateHermiteWeight_pos (m + 2)
      have hsucc : constrainedProlateHermiteWeightSum (m + 2)
          = constrainedProlateHermiteWeightSum (m + 1) + constrainedProlateHermiteWeight (m + 2) :=
        constrainedProlateHermiteWeightSum_succ (m + 1)
      have hden : (0 : ℝ) < constrainedProlateHermiteWeightSum (m + 2) := by
        rw [hsucc]; linarith
      rw [constrainedProlateHermiteTheta, le_div_iff₀ hden, hsucc]
      nlinarith [hQ, hq, hqpos]

/-! ## Divergence of the weight sums -/

/-- Each positive-index weight is at least `1/(4j)`.  This is
`Nat.four_pow_le_two_mul_self_mul_centralBinom` at argument `2j`, with no asymptotics. -/
theorem constrainedProlateHermiteWeight_ge_inv {j : ℕ} (hj : 1 ≤ j) :
    1 / (4 * (j : ℝ)) ≤ constrainedProlateHermiteWeight j := by
  have hcb : Nat.centralBinom (2 * j) = Nat.choose (4 * j) (2 * j) := by
    rw [Nat.centralBinom]
    congr 1
    omega
  have hnat := Nat.four_pow_le_two_mul_self_mul_centralBinom (2 * j) (by omega)
  rw [hcb] at hnat
  have hpow : (4 : ℕ) ^ (2 * j) = 16 ^ j := by
    rw [pow_mul]
    norm_num
  rw [hpow] at hnat
  have hreal : (16 : ℝ) ^ j ≤ 4 * (j : ℝ) * (Nat.choose (4 * j) (2 * j) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this
    linarith
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have h16 : (0 : ℝ) < (16 : ℝ) ^ j := by positivity
  rw [constrainedProlateHermiteWeight, div_le_div_iff₀ (by positivity) h16]
  nlinarith [hreal, hjpos, h16]

/-- The weight sums dominate a quarter of the harmonic sum, hence diverge. -/
theorem constrainedProlateHermiteWeightSum_ge_harmonic (k : ℕ) :
    radialHarmonicSum k / 4 ≤ constrainedProlateHermiteWeightSum k := by
  have hstep : ∀ i ∈ Finset.range k,
      1 / ((i : ℝ) + 1) / 4 ≤ constrainedProlateHermiteWeight (i + 1) := by
    intro i _
    have h := constrainedProlateHermiteWeight_ge_inv (j := i + 1) (by omega)
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    calc
      1 / ((i : ℝ) + 1) / 4 = 1 / (4 * ((i : ℝ) + 1)) := by
        field_simp
      _ ≤ constrainedProlateHermiteWeight (i + 1) := h
  have hsum : radialHarmonicSum k / 4 = ∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 1) / 4 := by
    unfold radialHarmonicSum
    rw [div_eq_mul_inv, mul_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  calc
    ∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 1) / 4
        ≤ ∑ i ∈ Finset.range k, constrainedProlateHermiteWeight (i + 1) :=
          Finset.sum_le_sum hstep
    _ ≤ constrainedProlateHermiteWeightSum k := by
          unfold constrainedProlateHermiteWeightSum
          rw [Finset.sum_range_succ']
          have h0 : 0 ≤ constrainedProlateHermiteWeight 0 :=
            (constrainedProlateHermiteWeight_pos 0).le
          linarith

theorem tendsto_constrainedProlateHermiteWeightSum_atTop :
    Tendsto constrainedProlateHermiteWeightSum atTop atTop := by
  have hharm : Tendsto (fun k : ℕ => radialHarmonicSum k / 4) atTop atTop := by
    have := Real.tendsto_sum_range_one_div_nat_succ_atTop
    have heq : ∀ k : ℕ, radialHarmonicSum k = ∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 1) := fun _ => rfl
    exact (this.congr fun k => (heq k).symm).atTop_div_const (by norm_num)
  exact tendsto_atTop_mono constrainedProlateHermiteWeightSum_ge_harmonic hharm

/-! ## The limit of the top weight -/

/-- **The top weight tends to one.**  The individual weights decay, but the top weight is a ratio
of their partial sums, and those diverge. -/
theorem tendsto_constrainedProlateHermiteTheta_one :
    Tendsto constrainedProlateHermiteTheta atTop (𝓝 1) := by
  have hgap : ∀ k : ℕ,
      |constrainedProlateHermiteTheta k - 1|
        ≤ 1 / constrainedProlateHermiteWeightSum (k + 1) := by
    intro k
    have hden : (0 : ℝ) < constrainedProlateHermiteWeightSum (k + 1) :=
      constrainedProlateHermiteWeightSum_pos (k + 1)
    have hsucc : constrainedProlateHermiteWeightSum (k + 1)
        = constrainedProlateHermiteWeightSum k + constrainedProlateHermiteWeight (k + 1) :=
      constrainedProlateHermiteWeightSum_succ k
    have hval : constrainedProlateHermiteTheta k - 1
        = -(constrainedProlateHermiteWeight (k + 1)
            / constrainedProlateHermiteWeightSum (k + 1)) := by
      rw [constrainedProlateHermiteTheta, div_sub_one hden.ne', ← neg_div]
      congr 1
      linarith [hsucc]
    have hnn : 0 ≤ constrainedProlateHermiteWeight (k + 1)
        / constrainedProlateHermiteWeightSum (k + 1) :=
      div_nonneg (constrainedProlateHermiteWeight_pos (k + 1)).le hden.le
    rw [hval, abs_neg, abs_of_nonneg hnn]
    have hq : constrainedProlateHermiteWeight (k + 1) ≤ 1 :=
      constrainedProlateHermiteWeight_le_one (k + 1)
    gcongr
  have hzero : Tendsto (fun k : ℕ => 1 / constrainedProlateHermiteWeightSum (k + 1)) atTop (𝓝 0) := by
    have hshift : Tendsto (fun k : ℕ => constrainedProlateHermiteWeightSum (k + 1)) atTop atTop :=
      tendsto_constrainedProlateHermiteWeightSum_atTop.comp (tendsto_add_atTop_nat 1)
    have hinv := hshift.inv_tendsto_atTop
    have hfun :
        (fun k : ℕ => constrainedProlateHermiteWeightSum (k + 1))⁻¹ =
          fun k : ℕ => 1 / constrainedProlateHermiteWeightSum (k + 1) := by
      funext k
      rw [Pi.inv_apply, one_div]
    rw [hfun] at hinv
    exact hinv
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hzero
  simpa [Real.dist_eq] using hgap k

end

end RHTower

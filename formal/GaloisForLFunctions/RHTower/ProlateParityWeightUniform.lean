import GaloisForLFunctions.RHTower.ConstrainedProlateTopWeightUniform

/-!
# Depth-uniform top weights in both compressed-Fourier parity sectors

The constrained-prolate constraint coordinates converge to Hermite values at the origin, and
`h_{2m}(0)^2` is proportional to the central binomial weight `C(2m,m)/4^m`.  The positive
compressed-Fourier sector runs over prolate indices `4j`, i.e. `m = 2j`; the negative sector runs
over `4j + 2`, i.e. `m = 2j + 1`.  Both sectors are therefore governed by the **same** sequence

`w m = C(2m,m) / 4^m`,

read on the even and odd subsequences of `m`.  This module proves the three facts that sequence
needs — positivity, the bound `w m ≤ 1/2` for `m ≥ 1`, and the lower bound `w m ≥ 1/(2m)` — and
uses them to give the negative sector the same depth-uniform statements the positive sector already
has: a floor at its depth-zero value `8/13`, and convergence of the top weight to `1`.

The lower bound is `Nat.four_pow_le_two_mul_self_mul_centralBinom`; no asymptotic expansion of the
central binomial coefficient is used anywhere.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## The common central-binomial weight -/

/-- `w m = C(2m,m)/4^m`, the sequence underlying both parity sectors. -/
def centralBinomWeight (m : ℕ) : ℝ := (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m

theorem centralBinomWeight_pos (m : ℕ) : 0 < centralBinomWeight m := by
  unfold centralBinomWeight
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos m) (by positivity)

@[simp] theorem centralBinomWeight_zero : centralBinomWeight 0 = 1 := by
  simp [centralBinomWeight, Nat.centralBinom_zero]

theorem centralBinomWeight_one : centralBinomWeight 1 = 1 / 2 := by
  unfold centralBinomWeight
  norm_num [Nat.centralBinom, Nat.choose]

/-- Every positive-index central-binomial weight is at most one half. -/
theorem centralBinomWeight_le_half {m : ℕ} (hm : 1 ≤ m) : centralBinomWeight m ≤ 1 / 2 := by
  have hchoose := Nat.choose_succ_le_two_pow (2 * m - 1) m
  have h2m : 2 * m = (2 * m - 1) + 1 := by omega
  rw [← h2m] at hchoose
  have hcb : Nat.centralBinom m = Nat.choose (2 * m) m := Nat.centralBinom_eq_two_mul_choose m
  have hreal : (Nat.centralBinom m : ℝ) ≤ (2 : ℝ) ^ (2 * m - 1) := by
    rw [hcb]
    exact_mod_cast hchoose
  have hden : (4 : ℝ) ^ m = 2 * (2 : ℝ) ^ (2 * m - 1) := by
    calc
      (4 : ℝ) ^ m = ((2 : ℝ) ^ 2) ^ m := by norm_num
      _ = (2 : ℝ) ^ (2 * m) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ ((2 * m - 1) + 1) := by rw [← h2m]
      _ = 2 * (2 : ℝ) ^ (2 * m - 1) := by rw [pow_succ]; ring
  rw [centralBinomWeight, hden, div_le_iff₀ (by positivity)]
  nlinarith [hreal, (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * m - 1))]

/-- Central-binomial weights are at least `1/(2m)`: the size that makes their partial sums
harmonic-divergent. -/
theorem centralBinomWeight_ge_inv {m : ℕ} (hm : 1 ≤ m) :
    1 / (2 * (m : ℝ)) ≤ centralBinomWeight m := by
  have hnat := Nat.four_pow_le_two_mul_self_mul_centralBinom m (by omega)
  have hreal : (4 : ℝ) ^ m ≤ 2 * (m : ℝ) * (Nat.centralBinom m : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this
    linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h4 : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
  rw [centralBinomWeight, div_le_div_iff₀ (by positivity) h4]
  nlinarith [hreal, hmpos, h4]

/-- The positive sector's weight is the even subsequence. -/
theorem constrainedProlateHermiteWeight_eq_centralBinomWeight (j : ℕ) :
    constrainedProlateHermiteWeight j = centralBinomWeight (2 * j) := by
  unfold constrainedProlateHermiteWeight centralBinomWeight
  have hcb : Nat.centralBinom (2 * j) = Nat.choose (4 * j) (2 * j) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    congr 1
    omega
  rw [hcb]
  congr 1
  rw [show (4 : ℝ) ^ (2 * j) = ((4 : ℝ) ^ 2) ^ j by rw [← pow_mul, mul_comm]]
  norm_num

/-! ## The negative compressed-Fourier sector -/

/-- The negative-sector weight: prolate indices `4j + 2`, i.e. `m = 2j + 1`. -/
def negativeProlateHermiteWeight (j : ℕ) : ℝ := centralBinomWeight (2 * j + 1)

theorem negativeProlateHermiteWeight_pos (j : ℕ) : 0 < negativeProlateHermiteWeight j :=
  centralBinomWeight_pos _

theorem negativeProlateHermiteWeight_le_half (j : ℕ) :
    negativeProlateHermiteWeight j ≤ 1 / 2 :=
  centralBinomWeight_le_half (by omega)

@[simp] theorem negativeProlateHermiteWeight_zero :
    negativeProlateHermiteWeight 0 = 1 / 2 := by
  unfold negativeProlateHermiteWeight
  simpa using centralBinomWeight_one

theorem negativeProlateHermiteWeight_one :
    negativeProlateHermiteWeight 1 = 5 / 16 := by
  unfold negativeProlateHermiteWeight centralBinomWeight
  norm_num [Nat.centralBinom, Nat.choose]

/-- `R_k = ∑_{j ≤ k} w(2j+1)`. -/
def negativeProlateHermiteWeightSum (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), negativeProlateHermiteWeight j

theorem negativeProlateHermiteWeightSum_pos (k : ℕ) :
    0 < negativeProlateHermiteWeightSum k := by
  unfold negativeProlateHermiteWeightSum
  exact Finset.sum_pos' (fun j _ => (negativeProlateHermiteWeight_pos j).le)
    ⟨0, by simp, negativeProlateHermiteWeight_pos 0⟩

theorem negativeProlateHermiteWeightSum_succ (k : ℕ) :
    negativeProlateHermiteWeightSum (k + 1) =
      negativeProlateHermiteWeightSum k + negativeProlateHermiteWeight (k + 1) := by
  unfold negativeProlateHermiteWeightSum
  rw [show k + 1 + 1 = (k + 1) + 1 by omega, Finset.sum_range_succ]

theorem negativeProlateHermiteWeightSum_mono {m k : ℕ} (h : m ≤ k) :
    negativeProlateHermiteWeightSum m ≤ negativeProlateHermiteWeightSum k := by
  unfold negativeProlateHermiteWeightSum
  have hsub : Finset.range (m + 1) ⊆ Finset.range (k + 1) := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) (by omega))
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro j _ _
  exact (negativeProlateHermiteWeight_pos j).le

@[simp] theorem negativeProlateHermiteWeightSum_zero :
    negativeProlateHermiteWeightSum 0 = 1 / 2 := by
  unfold negativeProlateHermiteWeightSum
  simp

theorem negativeProlateHermiteWeightSum_one :
    negativeProlateHermiteWeightSum 1 = 13 / 16 := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, negativeProlateHermiteWeightSum_succ,
    negativeProlateHermiteWeightSum_zero, negativeProlateHermiteWeight_one]
  norm_num

/-- The negative-sector limiting secular root `θ⁻_k = R_k / R_{k+1}`. -/
def negativeProlateHermiteTheta (k : ℕ) : ℝ :=
  negativeProlateHermiteWeightSum k / negativeProlateHermiteWeightSum (k + 1)

/-- Depth zero reproduces the recorded negative-sector constant `8/13`. -/
theorem negativeProlateHermiteTheta_zero : negativeProlateHermiteTheta 0 = 8 / 13 := by
  rw [negativeProlateHermiteTheta, negativeProlateHermiteWeightSum_zero,
    negativeProlateHermiteWeightSum_one]
  norm_num

theorem negativeProlateHermiteTheta_mem_Ioo (k : ℕ) :
    negativeProlateHermiteTheta k ∈ Set.Ioo 0 1 := by
  have hR := negativeProlateHermiteWeightSum_pos k
  have hnext := negativeProlateHermiteWeight_pos (k + 1)
  rw [negativeProlateHermiteTheta, negativeProlateHermiteWeightSum_succ]
  exact ⟨div_pos hR (add_pos hR hnext), (div_lt_one (add_pos hR hnext)).2 (by linarith)⟩

/-- **Depth-uniform floor in the negative sector.**  The top weight never drops below its
depth-zero value `8/13`.  For `k ≥ 1` the bound obtained is the stronger `13/21`, and
`13/21 > 8/13` because `13·13 = 169 > 168 = 8·21`. -/
theorem negativeProlateHermiteTheta_ge (k : ℕ) :
    (8 : ℝ) / 13 ≤ negativeProlateHermiteTheta k := by
  match k with
  | 0 => rw [negativeProlateHermiteTheta_zero]
  | (m + 1) =>
      have hR : (13 : ℝ) / 16 ≤ negativeProlateHermiteWeightSum (m + 1) := by
        rw [← negativeProlateHermiteWeightSum_one]
        exact negativeProlateHermiteWeightSum_mono (by omega)
      have hw : negativeProlateHermiteWeight (m + 2) ≤ 1 / 2 :=
        negativeProlateHermiteWeight_le_half (m + 2)
      have hwpos : 0 < negativeProlateHermiteWeight (m + 2) :=
        negativeProlateHermiteWeight_pos (m + 2)
      have hsucc : negativeProlateHermiteWeightSum (m + 2)
          = negativeProlateHermiteWeightSum (m + 1) + negativeProlateHermiteWeight (m + 2) :=
        negativeProlateHermiteWeightSum_succ (m + 1)
      have hden : (0 : ℝ) < negativeProlateHermiteWeightSum (m + 2) := by
        rw [hsucc]; linarith
      rw [negativeProlateHermiteTheta, le_div_iff₀ hden, hsucc]
      nlinarith [hR, hw, hwpos]

/-! ## Divergence and the limit -/

theorem negativeProlateHermiteWeightSum_ge_harmonic (k : ℕ) :
    harmonicSum (k + 1) / 4 ≤ negativeProlateHermiteWeightSum k := by
  have hstep : ∀ i ∈ Finset.range (k + 1),
      1 / ((i : ℝ) + 1) / 4 ≤ negativeProlateHermiteWeight i := by
    intro i _
    have h := centralBinomWeight_ge_inv (m := 2 * i + 1) (by omega)
    have hcast : ((2 * i + 1 : ℕ) : ℝ) = 2 * (i : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    refine le_trans ?_ h
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hi]
  have hsum : harmonicSum (k + 1) / 4
      = ∑ i ∈ Finset.range (k + 1), 1 / ((i : ℝ) + 1) / 4 := by
    unfold harmonicSum
    rw [div_eq_mul_inv, mul_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  exact Finset.sum_le_sum hstep

theorem tendsto_negativeProlateHermiteWeightSum_atTop :
    Tendsto negativeProlateHermiteWeightSum atTop atTop := by
  have hharm : Tendsto (fun k : ℕ => harmonicSum (k + 1) / 4) atTop atTop := by
    have hbase : Tendsto (fun k : ℕ => harmonicSum k / 4) atTop atTop := by
      have := Real.tendsto_sum_range_one_div_nat_succ_atTop
      have heq : ∀ k : ℕ, harmonicSum k = ∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 1) := fun _ => rfl
      exact (this.congr fun k => (heq k).symm).atTop_div_const (by norm_num)
    exact hbase.comp (tendsto_add_atTop_nat 1)
  exact tendsto_atTop_mono negativeProlateHermiteWeightSum_ge_harmonic hharm

/-- **The negative-sector top weight tends to one**, exactly as in the positive sector. -/
theorem tendsto_negativeProlateHermiteTheta_one :
    Tendsto negativeProlateHermiteTheta atTop (𝓝 1) := by
  have hgap : ∀ k : ℕ,
      |negativeProlateHermiteTheta k - 1|
        ≤ 1 / negativeProlateHermiteWeightSum (k + 1) := by
    intro k
    have hden : (0 : ℝ) < negativeProlateHermiteWeightSum (k + 1) :=
      negativeProlateHermiteWeightSum_pos (k + 1)
    have hsucc : negativeProlateHermiteWeightSum (k + 1)
        = negativeProlateHermiteWeightSum k + negativeProlateHermiteWeight (k + 1) :=
      negativeProlateHermiteWeightSum_succ k
    have hval : negativeProlateHermiteTheta k - 1
        = -(negativeProlateHermiteWeight (k + 1)
            / negativeProlateHermiteWeightSum (k + 1)) := by
      rw [negativeProlateHermiteTheta, div_sub_one hden.ne', ← neg_div]
      congr 1
      linarith [hsucc]
    have hnn : 0 ≤ negativeProlateHermiteWeight (k + 1)
        / negativeProlateHermiteWeightSum (k + 1) :=
      div_nonneg (negativeProlateHermiteWeight_pos (k + 1)).le hden.le
    rw [hval, abs_neg, abs_of_nonneg hnn]
    have hw : negativeProlateHermiteWeight (k + 1) ≤ 1 := by
      have := negativeProlateHermiteWeight_le_half (k + 1)
      linarith
    gcongr
  have hzero : Tendsto
      (fun k : ℕ => 1 / negativeProlateHermiteWeightSum (k + 1)) atTop (𝓝 0) := by
    have hshift : Tendsto (fun k : ℕ => negativeProlateHermiteWeightSum (k + 1)) atTop atTop :=
      tendsto_negativeProlateHermiteWeightSum_atTop.comp (tendsto_add_atTop_nat 1)
    have hinv := hshift.inv_tendsto_atTop
    have hfun :
        (fun k : ℕ => negativeProlateHermiteWeightSum (k + 1))⁻¹ =
          (fun k : ℕ => 1 / negativeProlateHermiteWeightSum (k + 1)) := by
      funext k
      simp
    rw [hfun] at hinv
    exact hinv
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hzero
  simpa [Real.dist_eq] using hgap k

end

end RHTower

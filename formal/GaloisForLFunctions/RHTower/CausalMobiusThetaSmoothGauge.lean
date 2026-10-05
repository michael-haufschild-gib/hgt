import GaloisForLFunctions.RHTower.CausalMobiusThetaSmoothGaugeProfile

/-!
# The smooth-gauge representative of the causal theta wavelet

On the initial cells `r ≤ N` the physical Möbius source is the affine line `C_N(r) = r H_N − 1`,
so any change of the test supported there with vanishing zeroth and first physical moments
**(21)** leaves `⟨C_N, q_N⟩_H` unchanged.  Multiplying `q_N` by the smooth cutoff `χ(r/N)` and
restoring both moments with two fixed smooth bumps gives the flattened test `q_N^flat`, with

* `B(N) = ⟨C_N, q_N^flat⟩_H + e_N`, `q_N^flat(r) = 0` for `r ≤ N/4`, `sup_N ‖q_N^flat‖_H < ∞`;
* `w_r q_N^flat(r) = N^{−3/2} G_N(r/N)` with `G_N` vanishing on `(−∞, 1/4]`, uniform Schwartz
  bounds, exact discrete sum `g(1/N)/√N` and `∫ G_N = O(N^{−2})` (Poisson summation);
* **(22)** for every `A > 0`, uniformly in residues and `1 ≤ Q ≤ N`,
  `|S_a| ≤ C_A/(Q√N) [N^{−2} + (Q/N)^A]` and `‖P_Q q_N^flat‖_H ≤ C_A √(Q/N) [N^{−2} + (Q/N)^A]`;
* `Σ |q_N^flat| ≤ C N^{3/2}`, `Σ (q_N^flat)² ≤ C N²`, and **(22a)**
  `Σ_r w_r |q_N^flat − P_Q q_N^flat| ≤ C N^{3/2}/Q²` (for every `Q ≥ 1`).

For the finitely many `N` at which the moment determinant is not yet controlled the original test
is kept.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open DeletionResidueMartingale

/-! ## The flattened test -/

/-- The flattening is applied at `N` once the moment determinant is controlled. -/
def gaugeActive (N : ℕ) : Prop := 1 ≤ N ∧ gaugeLimitDet / 2 ≤ gaugeDet N

theorem eventually_gaugeActive : ∀ᶠ N in atTop, gaugeActive N :=
  (eventually_ge_atTop 1).and eventually_gaugeDet_ge

theorem gaugeDet_ne_zero_of_active {N : ℕ} (h : gaugeActive N) : gaugeDet N ≠ 0 :=
  (lt_of_lt_of_le (by linarith [gaugeLimitDet_pos]) h.2).ne'

/-- The profile `G_N = χ D_N + c₁ψ₁ + c₂ψ₂` with the Cramer coefficients of `N`. -/
def flatProfile (N : ℕ) : ℝ → ℝ := gaugeProfile N (gaugeCoeffOne N) (gaugeCoeffTwo N)

/-- **The flattened test** `q_N^flat(r)`. -/
def flatCellWavelet (N r : ℕ) : ℝ := by
  classical
  exact if gaugeActive N then
      gaugeCutoff (r / N) * thetaCellWavelet N r + (r : ℝ) * (r + 1) / (N * Real.sqrt N) *
        (gaugeCoeffOne N * gaugeBumpOne (r / N) + gaugeCoeffTwo N * gaugeBumpTwo (r / N))
    else thetaCellWavelet N r

theorem flatCellWavelet_of_active {N : ℕ} (h : gaugeActive N) (r : ℕ) :
    flatCellWavelet N r = gaugeCutoff (r / N) * thetaCellWavelet N r +
      (r : ℝ) * (r + 1) / (N * Real.sqrt N) *
        (gaugeCoeffOne N * gaugeBumpOne (r / N) + gaugeCoeffTwo N * gaugeBumpTwo (r / N)) := by
  unfold flatCellWavelet; rw [if_pos h]

theorem flatCellWavelet_of_not_active {N : ℕ} (h : ¬ gaugeActive N) (r : ℕ) :
    flatCellWavelet N r = thetaCellWavelet N r := by
  unfold flatCellWavelet; rw [if_neg h]

/-- `w_r q_N^flat(r) = N^{−3/2} G_N(r/N)` (cell `j ↔ r = j + 1`). -/
theorem flatCellWavelet_mul_cellWeight {N : ℕ} (h : gaugeActive N) (j : ℕ) :
    flatCellWavelet N (j + 1) * cellWeight j = flatProfile N (((j + 1 : ℕ) : ℝ) / N) / (N * Real.sqrt N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast h.1
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  rw [flatCellWavelet_of_active h, add_mul, mul_assoc, thetaCellWavelet_mul_cellWeight, flatProfile,
    gaugeProfile, seedDifferenceProfile, cellWeight]
  have hx : (((j + 1 : ℕ) : ℝ) / N + 1 / N) = ((((j + 1 : ℕ) : ℝ) + 1) / N) := by
    field_simp
  rw [hx]
  push_cast
  field_simp
  ring

theorem flatCellWavelet_eq_mul_profile {N : ℕ} (h : gaugeActive N) {r : ℕ} (hr : 1 ≤ r) :
    flatCellWavelet N r = (r : ℝ) * (r + 1) * flatProfile N (r / N) / (N * Real.sqrt N) := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  have h1 := flatCellWavelet_mul_cellWeight h j
  rw [cellWeight] at h1
  have hj : ((j : ℝ) + 1) * ((j : ℝ) + 2) ≠ 0 := by positivity
  rw [mul_one_div, div_eq_iff hj] at h1
  rw [h1]
  push_cast
  ring

/-- `q_N^flat(r) = 0` for `r ≤ N/4`. -/
theorem flatCellWavelet_eq_zero_of_le {N : ℕ} (h : gaugeActive N) {r : ℕ} (hr : (r : ℝ) ≤ N / 4) :
    flatCellWavelet N r = 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast h.1
  have hx : (r : ℝ) / N ≤ 1 / 4 := by rw [div_le_iff₀ hNR]; linarith
  rw [flatCellWavelet_of_active h, gaugeCutoff_of_le hx, gaugeBumpOne, gaugeBumpTwo,
    gaugeBump_of_le (by linarith), gaugeBump_of_le (by linarith)]
  ring

theorem flatCellWavelet_eq_of_ge {N : ℕ} (h : gaugeActive N) {r : ℕ} (hr : (N : ℝ) / 2 ≤ r) :
    flatCellWavelet N r = thetaCellWavelet N r := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast h.1
  have hx : 1 / 2 ≤ (r : ℝ) / N := by rw [le_div_iff₀ hNR]; linarith
  rw [flatCellWavelet_of_active h, gaugeCutoff_of_ge hx, gaugeBumpOne, gaugeBumpTwo,
    gaugeBump_of_ge (by linarith), gaugeBump_of_ge (by linarith)]
  ring

theorem flatCellWavelet_eq_of_gt {N r : ℕ} (hr : N < r) : flatCellWavelet N r = thetaCellWavelet N r := by
  by_cases h : gaugeActive N
  · refine flatCellWavelet_eq_of_ge h ?_
    have : (N : ℝ) < r := by exact_mod_cast hr
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  · exact flatCellWavelet_of_not_active h r

/-! ## (21) The two vanishing physical moments of the change -/

theorem thetaCellWavelet_div_cell {N r : ℕ} (hr : 1 ≤ r) :
    thetaCellWavelet N r / ((r : ℝ) * (r + 1)) =
      (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)) / Real.sqrt N := by
  have hr0 : (r : ℝ) * (r + 1) ≠ 0 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    positivity
  unfold thetaCellWavelet
  field_simp

theorem flatChange_div_cell {N : ℕ} (h : gaugeActive N) {r : ℕ} (hr : 1 ≤ r) :
    (flatCellWavelet N r - thetaCellWavelet N r) / ((r : ℝ) * (r + 1)) =
      -((1 - gaugeCutoff (r / N)) * (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N))) /
          Real.sqrt N +
        (gaugeCoeffOne N * gaugeBumpOne (r / N) + gaugeCoeffTwo N * gaugeBumpTwo (r / N)) /
          (N * Real.sqrt N) := by
  have hr0 : (r : ℝ) * (r + 1) ≠ 0 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast h.1
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have hq := thetaCellWavelet_div_cell (N := N) hr
  rw [flatCellWavelet_of_active h]
  have hsplit : (gaugeCutoff (r / N) * thetaCellWavelet N r + (r : ℝ) * (r + 1) / (N * Real.sqrt N) *
      (gaugeCoeffOne N * gaugeBumpOne (r / N) + gaugeCoeffTwo N * gaugeBumpTwo (r / N)) -
        thetaCellWavelet N r) / ((r : ℝ) * (r + 1)) =
      -(1 - gaugeCutoff (r / N)) * (thetaCellWavelet N r / ((r : ℝ) * (r + 1))) +
        (gaugeCoeffOne N * gaugeBumpOne (r / N) + gaugeCoeffTwo N * gaugeBumpTwo (r / N)) /
          (N * Real.sqrt N) := by
    field_simp
    ring
  rw [hsplit, hq]
  ring

theorem sum_Icc_gaugeBump_eq (ψ : ℝ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ r ∈ Finset.Icc 1 N, ψ (r / N) = N * gaugeMomentZero ψ N := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [gaugeMomentZero, ← mul_assoc, mul_inv_cancel₀ hNR, one_mul]

theorem sum_Icc_mul_gaugeBump_eq (ψ : ℝ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ r ∈ Finset.Icc 1 N, (r : ℝ) * ψ (r / N) = (N : ℝ) ^ 2 * gaugeMomentOne ψ N := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [gaugeMomentOne, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  field_simp

/-- **(21), zeroth moment.** `Σ_{r≤N} (q^flat − q)(r)/(r(r+1)) = 0`. -/
theorem sum_flatChange_div_cell {N : ℕ} (h : gaugeActive N) :
    ∑ r ∈ Finset.Icc 1 N, (flatCellWavelet N r - thetaCellWavelet N r) / ((r : ℝ) * (r + 1)) = 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast h.1
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  rw [Finset.sum_congr rfl fun r hr => flatChange_div_cell h (Finset.mem_Icc.1 hr).1,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_Icc_gaugeBump_eq _ h.1,
    sum_Icc_gaugeBump_eq _ h.1]
  have hsolve := (gaugeCoeff_solve (gaugeDet_ne_zero_of_active h)).1
  have hrho : ∑ r ∈ Finset.Icc 1 N, (1 - gaugeCutoff (r / N)) *
      (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)) = gaugeRhsZero N := rfl
  rw [hrho, ← hsolve]
  field_simp
  ring

/-- **(21), first moment.** `Σ_{r≤N} r (q^flat − q)(r)/(r(r+1)) = 0`. -/
theorem sum_mul_flatChange_div_cell {N : ℕ} (h : gaugeActive N) :
    ∑ r ∈ Finset.Icc 1 N, (r : ℝ) * ((flatCellWavelet N r - thetaCellWavelet N r) /
      ((r : ℝ) * (r + 1))) = 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast h.1
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  rw [Finset.sum_congr rfl fun r hr => by rw [flatChange_div_cell h (Finset.mem_Icc.1 hr).1]]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have h1 : ∑ r ∈ Finset.Icc 1 N, (r : ℝ) * (-((1 - gaugeCutoff (r / N)) *
      (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N))) / Real.sqrt N) =
      -(N * gaugeRhsOne N) / Real.sqrt N := by
    rw [gaugeRhsOne, ← mul_assoc, mul_inv_cancel₀ hNR.ne', one_mul, ← Finset.sum_neg_distrib,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have h2 : ∑ r ∈ Finset.Icc 1 N, (r : ℝ) * ((gaugeCoeffOne N * gaugeBumpOne (r / N) +
      gaugeCoeffTwo N * gaugeBumpTwo (r / N)) / (N * Real.sqrt N)) =
      (gaugeCoeffOne N * ((N : ℝ) ^ 2 * gaugeMomentOne gaugeBumpOne N) +
        gaugeCoeffTwo N * ((N : ℝ) ^ 2 * gaugeMomentOne gaugeBumpTwo N)) / (N * Real.sqrt N) := by
    rw [← sum_Icc_mul_gaugeBump_eq _ h.1, ← sum_Icc_mul_gaugeBump_eq _ h.1, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [h1, h2]
  have hsolve := (gaugeCoeff_solve (gaugeDet_ne_zero_of_active h)).2
  rw [← hsolve]
  field_simp
  ring

/-! ## The flattened vector and the exact source identity -/

theorem flatChange_eq_zero_of_gt {N r : ℕ} (hr : N < r) :
    flatCellWavelet N r - thetaCellWavelet N r = 0 := by
  rw [flatCellWavelet_eq_of_gt hr, sub_self]

theorem summable_flatCellWavelet_sq {N : ℕ} (hN : 1 ≤ N) :
    Summable fun j => flatCellWavelet N (j + 1) ^ 2 * cellWeight j := by
  have hq := summable_thetaCellWavelet_sq hN
  have hfin : Summable fun j => (flatCellWavelet N (j + 1) ^ 2 - thetaCellWavelet N (j + 1) ^ 2) *
      cellWeight j :=
    summable_of_ne_finset_zero (s := Finset.range N) fun j hj => by
      have : N < j + 1 := by simp only [Finset.mem_range, not_lt] at hj; omega
      rw [flatCellWavelet_eq_of_gt this, sub_self, zero_mul]
  exact (hq.add hfin).congr fun j => by ring

/-- The flattened test as a physical vector. -/
def flatWaveletVec (N : ℕ) : Lp ℝ 2 cellMeasure := physVec fun j => flatCellWavelet N (j + 1)

theorem flatWaveletVec_apply {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    flatWaveletVec N j = flatCellWavelet N (j + 1) :=
  physVec_apply (summable_flatCellWavelet_sq hN) j

theorem flatWaveletVec_eq_of_not_active {N : ℕ} (h : ¬ gaugeActive N) :
    flatWaveletVec N = thetaWaveletVec N := by
  unfold flatWaveletVec thetaWaveletVec
  congr 1
  funext j
  exact flatCellWavelet_of_not_active h _

/-- The change of the test sums to zero against every affine source on the initial cells. -/
theorem sum_range_affine_mul_flatChange {N : ℕ} (h : gaugeActive N) (H : ℝ) :
    ∑ j ∈ Finset.range N, (((j + 1 : ℕ) : ℝ) * H - 1) *
      (flatCellWavelet N (j + 1) - thetaCellWavelet N (j + 1)) * cellWeight j = 0 := by
  have hcw : ∀ j : ℕ, cellWeight j = 1 / (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1)) := fun j => by
    rw [cellWeight]; push_cast; ring
  rw [Finset.sum_congr rfl fun j _ => by rw [hcw j],
    sum_range_succ_eq_sum_Icc_one N fun r => ((r : ℝ) * H - 1) *
      (flatCellWavelet N r - thetaCellWavelet N r) * (1 / ((r : ℝ) * (r + 1)))]
  · have hterm : ∀ r ∈ Finset.Icc 1 N, ((r : ℝ) * H - 1) *
        (flatCellWavelet N r - thetaCellWavelet N r) * (1 / ((r : ℝ) * (r + 1))) =
        H * ((r : ℝ) * ((flatCellWavelet N r - thetaCellWavelet N r) / ((r : ℝ) * (r + 1)))) -
          (flatCellWavelet N r - thetaCellWavelet N r) / ((r : ℝ) * (r + 1)) := by
      intro r _; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_mul_flatChange_div_cell h, sum_flatChange_div_cell h]
    ring

/-- **The flattened source identity** `B(N) = ⟨C_N, q_N^flat⟩_H + e_N`. -/
theorem causalMobiusThetaTail_natCast_eq_inner_flat {N : ℕ} (hN : 1 ≤ N) :
    causalMobiusThetaTail N = inner ℝ (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
      (flatWaveletVec N) + thetaCellDefect N := by
  rw [causalMobiusThetaTail_natCast_eq_inner hN]
  congr 1
  by_cases h : gaugeActive N
  swap
  · rw [flatWaveletVec_eq_of_not_active h]
  set C := sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N
  have h1 := hasSum_inner C (thetaWaveletVec N)
  have h2 := hasSum_inner C (flatWaveletVec N)
  have hC : ∀ j, C j = moebiusCell N (j + 1) := fun j => sourceVec_apply_eq_cell _ N j
  have hdiff : HasSum (fun j => C j * (flatCellWavelet N (j + 1) - thetaCellWavelet N (j + 1)) *
      cellWeight j) 0 := by
    have hfin : HasSum (fun j => C j * (flatCellWavelet N (j + 1) - thetaCellWavelet N (j + 1)) *
        cellWeight j) (∑ j ∈ Finset.range N, C j * (flatCellWavelet N (j + 1) -
          thetaCellWavelet N (j + 1)) * cellWeight j) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by
        have : N < j + 1 := by simp only [Finset.mem_range, not_lt] at hj; omega
        rw [flatChange_eq_zero_of_gt this, mul_zero, zero_mul]
    have hval : ∑ j ∈ Finset.range N, C j * (flatCellWavelet N (j + 1) - thetaCellWavelet N (j + 1)) *
        cellWeight j = 0 := by
      rw [← sum_range_affine_mul_flatChange h (moebiusHarmonic N)]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hC, moebiusCell, physical_moebius_cell_eq_reciprocal_tail (by omega)
        (by simpa using Finset.mem_range.1 hj)]
      rfl
    rwa [hval] at hfin
  have h3 := h1.add hdiff
  rw [add_zero] at h3
  refine h2.unique (h3.congr_fun fun j => ?_) |>.symm
  rw [flatWaveletVec_apply hN, thetaWaveletVec_apply hN]
  ring

/-- **The flattening preserves the total test mean** `Σ_r q_N^flat(r)/(r(r+1)) = g(1/N)/√N`. -/
theorem hasSum_flatCellWavelet_mul_cellWeight {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun j => flatCellWavelet N (j + 1) * cellWeight j) (thetaCuspSeed (1 / N) / Real.sqrt N) := by
  have h1 := hasSum_thetaCellWavelet_mul_cellWeight hN
  have hdiff : HasSum (fun j => (flatCellWavelet N (j + 1) - thetaCellWavelet N (j + 1)) * cellWeight j) 0 := by
    by_cases h : gaugeActive N
    · have hfin : HasSum (fun j => (flatCellWavelet N (j + 1) - thetaCellWavelet N (j + 1)) *
          cellWeight j) (∑ j ∈ Finset.range N, (flatCellWavelet N (j + 1) -
            thetaCellWavelet N (j + 1)) * cellWeight j) :=
        hasSum_sum_of_ne_finset_zero fun j hj => by
          have : N < j + 1 := by simp only [Finset.mem_range, not_lt] at hj; omega
          rw [flatChange_eq_zero_of_gt this, zero_mul]
      have hval : ∑ j ∈ Finset.range N, (flatCellWavelet N (j + 1) - thetaCellWavelet N (j + 1)) *
          cellWeight j = 0 := by
        have := sum_range_affine_mul_flatChange h 0
        rw [← neg_eq_zero, ← this, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rwa [hval] at hfin
    · simp only [flatCellWavelet_of_not_active h, sub_self, zero_mul]
      exact hasSum_zero
  have h3 := h1.add hdiff
  rw [add_zero] at h3
  exact h3.congr_fun fun j => by ring

/-! ## Gaussian size bounds for the flattened test -/

theorem cell_profile_rational_le {n a : ℝ} (hn : 1 ≤ n) (ha : 1 ≤ a) :
    a * (a + 1) * ((1 + (a / n) ^ 2) ^ 2)⁻¹ ≤ 4 * n ^ 4 * (1 / ((n + a - 1) * (n + a))) := by
  have hn0 : 0 < n := by linarith
  have hd : (1 + (a / n) ^ 2) ^ 2 = (n ^ 2 + a ^ 2) ^ 2 / n ^ 4 := by field_simp
  have hpos : 0 < n + a - 1 := by linarith
  rw [hd, inv_div, ← mul_div_assoc, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : a * (a + 1) ≤ 2 * (n ^ 2 + a ^ 2) := by nlinarith
  have h2 : (n + a - 1) * (n + a) ≤ 2 * (n ^ 2 + a ^ 2) := by nlinarith [sq_nonneg (n - a)]
  have hq : 0 < n ^ 2 + a ^ 2 := by positivity
  calc a * (a + 1) * n ^ 4 * ((n + a - 1) * (n + a)) ≤
        (2 * (n ^ 2 + a ^ 2)) * n ^ 4 * (2 * (n ^ 2 + a ^ 2)) := by gcongr
    _ = 4 * n ^ 4 * (n ^ 2 + a ^ 2) ^ 2 := by ring

theorem telescoping_cell_le (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun j : ℕ => 1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1))) ∧
      ∑' j : ℕ, 1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1)) ≤ 1 / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hT0 : ∀ j : ℕ, 0 ≤ 1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1)) := fun j => by positivity
  have hsum : ∀ M, ∑ j ∈ Finset.range M, 1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1)) ≤ 1 / N := by
    intro M
    have h := Finset.sum_range_sub' (fun j : ℕ => 1 / ((N : ℝ) + j)) M
    have hterm : ∀ j : ℕ, 1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1)) =
        1 / ((N : ℝ) + j) - 1 / ((N : ℝ) + ((j + 1 : ℕ) : ℝ)) := by
      intro j
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, h]
    simp only [Nat.cast_zero, add_zero]
    have : 0 ≤ 1 / ((N : ℝ) + M) := by positivity
    linarith
  exact ⟨summable_of_sum_range_le hT0 hsum, Real.tsum_le_of_sum_range_le hT0 hsum⟩

theorem exists_abs_flatProfile_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, gaugeActive N → ∀ x : ℝ,
    |flatProfile N x| ≤ M * ((1 + x ^ 2) ^ 2)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_gaugeCoeff_le
  obtain ⟨M, hM0, hM⟩ := exists_abs_iteratedDeriv_gaugeProfile_le 0 2 B
  refine ⟨M, hM0, fun N h x => ?_⟩
  have hc := hB N h.1 h.2
  have := hM N h.1 _ _ hc.1 hc.2 x
  simpa [flatProfile] using this

/-- `|q_N^flat(j+1)| ≤ 4 M N²√N /((N+j)(N+j+1))`. -/
theorem exists_abs_flatCellWavelet_le_telescoping : ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, gaugeActive N →
    ∀ j : ℕ, |flatCellWavelet N (j + 1)| ≤
      4 * M * ((N : ℝ) ^ 2 * Real.sqrt N) * (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1))) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_flatProfile_le
  refine ⟨M, hM0, fun N h j => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.1
  have hNR : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNR.le
  rw [flatCellWavelet_eq_mul_profile h (by omega), abs_div, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1)),
    abs_of_pos (by positivity : (0 : ℝ) < N * Real.sqrt N)]
  have hrat := cell_profile_rational_le hN1 (by simp : (1 : ℝ) ≤ (((j + 1 : ℕ) : ℝ)))
  have hb := hM N h ((((j + 1 : ℕ) : ℝ)) / N)
  have hT : (N : ℝ) + ((j + 1 : ℕ) : ℝ) - 1 = (N : ℝ) + j := by push_cast; ring
  rw [hT, show (N : ℝ) + ((j + 1 : ℕ) : ℝ) = (N : ℝ) + j + 1 by push_cast; ring] at hrat
  calc ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1) * |flatProfile N (((j + 1 : ℕ) : ℝ) / N)| /
        (N * Real.sqrt N)
      ≤ ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1) * (M * ((1 + (((j + 1 : ℕ) : ℝ) / N) ^ 2) ^ 2)⁻¹) /
          (N * Real.sqrt N) := by gcongr
    _ = M * (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1) * ((1 + (((j + 1 : ℕ) : ℝ) / N) ^ 2) ^ 2)⁻¹) /
          (N * Real.sqrt N) := by ring
    _ ≤ M * (4 * (N : ℝ) ^ 4 * (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1)))) / (N * Real.sqrt N) := by
          gcongr
    _ = 4 * M * ((N : ℝ) ^ 2 * Real.sqrt N) * (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1))) := by
          field_simp
          rw [Real.sq_sqrt hNR.le]

/-- **Uniform Gaussian decay:** `Σ |q_N^flat| ≤ C N^{3/2}`. -/
theorem exists_tsum_abs_flatCellWavelet_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, gaugeActive N →
    Summable (fun j => |flatCellWavelet N (j + 1)|) ∧
      ∑' j, |flatCellWavelet N (j + 1)| ≤ C * (N * Real.sqrt N) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_flatCellWavelet_le_telescoping
  refine ⟨4 * M, by positivity, fun N h => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.1
  have hNR : (0 : ℝ) < N := by linarith
  obtain ⟨hTs, hTle⟩ := telescoping_cell_le N h.1
  have hmaj := hTs.mul_left (4 * M * ((N : ℝ) ^ 2 * Real.sqrt N))
  have hs : Summable fun j => |flatCellWavelet N (j + 1)| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (hM N h) hmaj
  refine ⟨hs, ?_⟩
  calc ∑' j, |flatCellWavelet N (j + 1)| ≤
        ∑' j : ℕ, 4 * M * ((N : ℝ) ^ 2 * Real.sqrt N) * (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1))) :=
        Summable.tsum_le_tsum (hM N h) hs hmaj
    _ = 4 * M * ((N : ℝ) ^ 2 * Real.sqrt N) *
        ∑' j : ℕ, 1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1)) := tsum_mul_left
    _ ≤ 4 * M * ((N : ℝ) ^ 2 * Real.sqrt N) * (1 / N) := by gcongr
    _ = 4 * M * (N * Real.sqrt N) := by field_simp

/-- `Σ (q_N^flat)² ≤ C N²`. -/
theorem exists_tsum_flatCellWavelet_sq_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, gaugeActive N →
    Summable (fun j => flatCellWavelet N (j + 1) ^ 2) ∧
      ∑' j, flatCellWavelet N (j + 1) ^ 2 ≤ C * (N : ℝ) ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_flatCellWavelet_le_telescoping
  obtain ⟨C1, hC10, hC1⟩ := exists_tsum_abs_flatCellWavelet_le
  refine ⟨4 * M * C1, by positivity, fun N h => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.1
  have hNR : (0 : ℝ) < N := by linarith
  have hs1 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have hsq : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left hNR.le]
    nlinarith
  obtain ⟨hA, hAle⟩ := hC1 N h
  -- each value is at most `4 M N^{5/2}/N² ≤ 4 M √N`
  have hpt : ∀ j, |flatCellWavelet N (j + 1)| ≤ 4 * M * Real.sqrt N := by
    intro j
    refine (hM N h j).trans ?_
    have hT : 1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1)) ≤ 1 / (N : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    calc 4 * M * ((N : ℝ) ^ 2 * Real.sqrt N) * (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1))) ≤
          4 * M * ((N : ℝ) ^ 2 * Real.sqrt N) * (1 / (N : ℝ) ^ 2) := by gcongr
      _ = 4 * M * Real.sqrt N := by field_simp
  have hsq_le : ∀ j, flatCellWavelet N (j + 1) ^ 2 ≤ 4 * M * Real.sqrt N * |flatCellWavelet N (j + 1)| := by
    intro j
    rw [← sq_abs, sq]
    exact mul_le_mul_of_nonneg_right (hpt j) (abs_nonneg _)
  have hs : Summable fun j => flatCellWavelet N (j + 1) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hsq_le (hA.mul_left _)
  refine ⟨hs, ?_⟩
  calc ∑' j, flatCellWavelet N (j + 1) ^ 2 ≤ ∑' j, 4 * M * Real.sqrt N * |flatCellWavelet N (j + 1)| :=
        Summable.tsum_le_tsum hsq_le hs (hA.mul_left _)
    _ = 4 * M * Real.sqrt N * ∑' j, |flatCellWavelet N (j + 1)| := tsum_mul_left
    _ ≤ 4 * M * Real.sqrt N * (C1 * (N * Real.sqrt N)) := by gcongr
    _ = 4 * M * C1 * (N : ℝ) ^ 2 := by
        rw [show 4 * M * Real.sqrt N * (C1 * (N * Real.sqrt N)) =
          4 * M * C1 * N * (Real.sqrt N * Real.sqrt N) by ring, Real.mul_self_sqrt hNR.le]
        ring

/-- `sup_N ‖q_N^flat‖_H < ∞`. -/
theorem exists_norm_flatWaveletVec_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ‖flatWaveletVec N‖ ≤ B := by
  obtain ⟨Bq, hBq0, hBq⟩ := exists_norm_thetaWaveletVec_le
  obtain ⟨M, hM0, hM⟩ := exists_abs_flatCellWavelet_le_telescoping
  refine ⟨max (16 * M) Bq, le_max_of_le_right hBq0, fun N hN => ?_⟩
  by_cases h : gaugeActive N
  swap
  · rw [flatWaveletVec_eq_of_not_active h]; exact (hBq N hN).trans (le_max_right _ _)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNR : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNR.le
  obtain ⟨hTs, hTle⟩ := telescoping_cell_le N hN
  have hpt : ∀ j, flatCellWavelet N (j + 1) ^ 2 * cellWeight j ≤
      256 * M ^ 2 * N * (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1))) := by
    intro j
    by_cases hj : ((j + 1 : ℕ) : ℝ) ≤ N / 4
    · rw [flatCellWavelet_eq_zero_of_le h hj]; simp only [ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul]; positivity
    · replace hj := not_le.1 hj
      have hcw : cellWeight j ≤ 16 / (N : ℝ) ^ 2 := by
        rw [cellWeight, div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast at hj
        nlinarith
      have h1 := hM N h j
      have hT : 1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1)) ≤ 1 / (N : ℝ) ^ 2 := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have h2 : |flatCellWavelet N (j + 1)| ≤ 4 * M * Real.sqrt N := by
        refine h1.trans ?_
        calc 4 * M * ((N : ℝ) ^ 2 * Real.sqrt N) * (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1))) ≤
              4 * M * ((N : ℝ) ^ 2 * Real.sqrt N) * (1 / (N : ℝ) ^ 2) := by gcongr
          _ = 4 * M * Real.sqrt N := by field_simp
      rw [← sq_abs, sq]
      calc |flatCellWavelet N (j + 1)| * |flatCellWavelet N (j + 1)| * cellWeight j ≤
            (4 * M * ((N : ℝ) ^ 2 * Real.sqrt N) * (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1)))) *
              (4 * M * Real.sqrt N) * (16 / (N : ℝ) ^ 2) := by
            gcongr
            · exact (cellWeight_pos j).le
          _ = 256 * M ^ 2 * N * (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1))) := by
            field_simp
            rw [Real.sq_sqrt hNR.le]
            ring
  have hsq := hasSum_norm_sq (flatWaveletVec N)
  have hsq' : HasSum (fun j => flatCellWavelet N (j + 1) ^ 2 * cellWeight j) (‖flatWaveletVec N‖ ^ 2) :=
    hsq.congr_fun fun j => by rw [flatWaveletVec_apply hN]
  have hle : ‖flatWaveletVec N‖ ^ 2 ≤ (16 * M) ^ 2 := by
    rw [← hsq'.tsum_eq]
    calc ∑' j, flatCellWavelet N (j + 1) ^ 2 * cellWeight j ≤
          ∑' j : ℕ, 256 * M ^ 2 * N * (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1))) :=
          Summable.tsum_le_tsum hpt hsq'.summable (hTs.mul_left _)
      _ = 256 * M ^ 2 * N * ∑' j : ℕ, 1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1)) := tsum_mul_left
      _ ≤ 256 * M ^ 2 * N * (1 / N) := by gcongr
      _ = (16 * M) ^ 2 := by field_simp; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle |>.trans
    (le_max_left _ _)

/-! ## The profile `G_N`: vanishing, uniform Schwartz bounds, mean -/

theorem flatProfile_of_le (N : ℕ) {x : ℝ} (hx : x ≤ 1 / 4) : flatProfile N x = 0 :=
  gaugeProfile_of_le N _ _ hx

/-- **Uniform Schwartz seminorms:** `sup_x |x|^a |G_N^{(n)}(x)| ≤ C`, uniformly in `N`. -/
theorem exists_pow_mul_abs_iteratedDeriv_flatProfile_le (a n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, gaugeActive N → ∀ x : ℝ, |x| ^ a * |iteratedDeriv n (flatProfile N) x| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_gaugeCoeff_le
  obtain ⟨M, hM0, hM⟩ := exists_abs_iteratedDeriv_gaugeProfile_le n a B
  refine ⟨M, hM0, fun N h x => ?_⟩
  have hc := hB N h.1 h.2
  have h1 := hM N h.1 _ _ hc.1 hc.2 x
  have hx : |x| ^ a ≤ (1 + x ^ 2) ^ a := by
    apply pow_le_pow_left₀ (abs_nonneg x)
    nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - 1)]
  calc |x| ^ a * |iteratedDeriv n (flatProfile N) x| ≤ (1 + x ^ 2) ^ a * (M * ((1 + x ^ 2) ^ a)⁻¹) :=
        mul_le_mul hx h1 (abs_nonneg _) (by positivity)
    _ = M := by field_simp

/-- Uniform derivative bounds of order `≤ k` in the Poisson form `M (1+x²)^{−1}`. -/
theorem exists_flatProfile_poisson_bound (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, gaugeActive N →
    ∀ j ≤ k, ∀ x : ℝ, |iteratedDeriv j (flatProfile N) x| ≤ M * (1 + x ^ 2)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_gaugeCoeff_le
  choose M hM0 hM using fun j => exists_abs_iteratedDeriv_gaugeProfile_le j 1 B
  refine ⟨∑ j ∈ Finset.range (k + 1), M j, Finset.sum_nonneg fun j _ => hM0 j, fun N h j hj x => ?_⟩
  have hc := hB N h.1 h.2
  have h1 := hM j N h.1 _ _ hc.1 hc.2 x
  rw [pow_one] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Finset.single_le_sum (f := M) (fun i _ => hM0 i) (Finset.mem_range.2 (by omega))

theorem contDiff_flatProfile (N : ℕ) {n : ℕ∞} : ContDiff ℝ n (flatProfile N) :=
  contDiff_gaugeProfile N _ _

/-- The fibre sum of the flattened test is a full lattice sum of the profile. -/
theorem cellFibreSum_flatWaveletVec_eq {N : ℕ} (h : gaugeActive N) {Q b : ℕ} (hb : b < Q)
    (hs : Summable fun n : ℤ => flatProfile N (((b : ℝ) + 1) / N + ((Q : ℝ) / N) * n)) :
    cellFibreSum (flatWaveletVec N) Q b =
      (∑' n : ℤ, flatProfile N (((b : ℝ) + 1) / N + ((Q : ℝ) / N) * n)) / (N * Real.sqrt N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast h.1
  set f : ℤ → ℝ := fun n => flatProfile N (((b : ℝ) + 1) / N + ((Q : ℝ) / N) * n)
  have hneg : ∀ k : ℕ, f (-((k : ℤ) + 1)) = 0 := by
    intro k
    apply flatProfile_of_le
    have hbQ : (b : ℝ) + 1 ≤ Q := by exact_mod_cast hb
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have heq : ((b : ℝ) + 1) / N + ((Q : ℝ) / N) * ((-((k : ℤ) + 1) : ℤ) : ℝ) =
        (((b : ℝ) + 1) - Q * ((k : ℝ) + 1)) / N := by
      push_cast; field_simp; ring
    have : ((b : ℝ) + 1) / N + ((Q : ℝ) / N) * ((-((k : ℤ) + 1) : ℤ) : ℝ) ≤ 0 := by
      rw [heq]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hNR.le
    linarith
  have hsplit := tsum_of_nat_of_neg_add_one (f := f) (hs.comp_injective Nat.cast_injective)
    (by simp only [hneg]; exact summable_zero)
  simp only [hneg, tsum_zero, add_zero] at hsplit
  rw [hsplit, cellFibreSum, ← tsum_div_const]
  refine tsum_congr fun k => ?_
  rw [flatWaveletVec_apply h.1, flatCellWavelet_mul_cellWeight h]
  simp only [f]
  congr 2
  push_cast
  field_simp
  ring

/-- **`∫ G_N = O(N^{−2})`** (Poisson summation against the exact discrete mean). -/
theorem exists_abs_integral_flatProfile_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, gaugeActive N →
    |∫ x, flatProfile N x| ≤ C / (N : ℝ) ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_flatProfile_poisson_bound 2
  obtain ⟨Cs, hCs0, hCs⟩ := exists_abs_thetaCuspSeed_le_sq
  set Z : ℝ := ∑' n : ℤ, |(n : ℝ)| ^ (-2 : ℝ)
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨Cs + M * Z, by positivity, fun N h => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.1
  have hNR : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  obtain ⟨hsum, hP⟩ := summable_and_abs_tsum_progression_sub_integral_le (le_refl 2)
    (contDiff_flatProfile N (n := 2)) (hM N h) (γ := ((1 : ℕ) : ℝ) / N) (by positivity)
    ((((0 : ℕ) : ℝ) + 1) / N)
  have hfib := cellFibreSum_flatWaveletVec_eq h one_pos hsum
  have hmean : cellFibreSum (flatWaveletVec N) 1 0 = thetaCuspSeed (1 / N) / Real.sqrt N := by
    rw [cellFibreSum]
    have := hasSum_flatCellWavelet_mul_cellWeight h.1
    simp only [zero_add, one_mul]
    refine (HasSum.tsum_eq ?_)
    exact this.congr_fun fun k => by rw [flatWaveletVec_apply h.1]
  rw [hmean] at hfib
  have hlat : ∑' n : ℤ, flatProfile N ((((0 : ℕ) : ℝ) + 1) / N + (((1 : ℕ) : ℝ) / N) * n) =
      N * thetaCuspSeed (1 / N) := by
    rw [eq_div_iff (by positivity : (N : ℝ) * Real.sqrt N ≠ 0)] at hfib
    rw [← hfib]
    field_simp
  rw [hlat] at hP
  have hinv : (((1 : ℕ) : ℝ) / N)⁻¹ = N := by simp
  rw [hinv, show ((1 : ℕ) : ℝ) / N = 1 / N by simp, show 2 - 1 = 1 from rfl, pow_one,
    ← mul_sub, abs_mul, abs_of_pos hNR] at hP
  have h1 : |thetaCuspSeed (1 / N) - ∫ x, flatProfile N x| ≤ M * Z / (N : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc |thetaCuspSeed (1 / N) - ∫ x, flatProfile N x| * (N : ℝ) ^ 2 =
          (N * |thetaCuspSeed (1 / N) - ∫ x, flatProfile N x|) * N := by ring
      _ ≤ (M * (1 / N) * Z) * N := by gcongr
      _ = M * Z := by field_simp
  have h2 : |thetaCuspSeed (1 / N)| ≤ Cs / (N : ℝ) ^ 2 := by
    refine (hCs _).trans (le_of_eq ?_)
    field_simp
  calc |∫ x, flatProfile N x| ≤ |thetaCuspSeed (1 / N)| +
        |thetaCuspSeed (1 / N) - ∫ x, flatProfile N x| := by
        have := abs_sub_abs_le_abs_sub (thetaCuspSeed (1 / N)) (∫ x, flatProfile N x)
        have := abs_sub_comm (thetaCuspSeed (1 / N)) (∫ x, flatProfile N x)
        have := abs_sub_abs_le_abs_sub (∫ x, flatProfile N x) (thetaCuspSeed (1 / N))
        linarith
    _ ≤ Cs / (N : ℝ) ^ 2 + M * Z / (N : ℝ) ^ 2 := add_le_add h2 h1
    _ = (Cs + M * Z) / (N : ℝ) ^ 2 := by ring

/-! ## (22) Progression bounds below the physical scale -/

theorem pow_le_rpow_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {k : ℕ} {A : ℝ} (hA0 : 0 < A)
    (hA : A ≤ k) : x ^ k ≤ x ^ A := by
  rcases hx0.eq_or_lt with rfl | hpos
  · have hk : k ≠ 0 := by
      intro hk; rw [hk, Nat.cast_zero] at hA; linarith
    rw [zero_pow hk, Real.zero_rpow hA0.ne']
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hpos hx1 hA

/-- **(22), fibre form.** For every `A > 0`, uniformly in `1 ≤ Q ≤ N` and residues `b`,
`|S_b| ≤ C_A/(Q√N) [N^{−2} + (Q/N)^A]`. -/
theorem exists_abs_cellFibreSum_flat_le {A : ℝ} (hA : 0 < A) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, gaugeActive N → ∀ Q : ℕ, 1 ≤ Q → Q ≤ N → ∀ b : ℕ, b < Q →
      |cellFibreSum (flatWaveletVec N) Q b| ≤
        C / (Q * Real.sqrt N) * (((N : ℝ) ^ 2)⁻¹ + ((Q : ℝ) / N) ^ A) := by
  set k := max 2 ⌈A⌉₊ with hkdef
  have hk2 : 2 ≤ k := le_max_left _ _
  have hAk : A ≤ k := (Nat.le_ceil A).trans (by exact_mod_cast le_max_right 2 ⌈A⌉₊)
  obtain ⟨M, hM0, hM⟩ := exists_flatProfile_poisson_bound k
  obtain ⟨CI, hCI0, hCI⟩ := exists_abs_integral_flatProfile_le
  set Z : ℝ := ∑' n : ℤ, |(n : ℝ)| ^ (-2 : ℝ)
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨CI + M * Z, by positivity, fun N h Q hQ hQN b hb => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.1
  have hNR : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQN' : (Q : ℝ) ≤ N := by exact_mod_cast hQN
  have hx0 : (0 : ℝ) ≤ (Q : ℝ) / N := by positivity
  have hx1 : (Q : ℝ) / N ≤ 1 := by rw [div_le_one hNR]; exact hQN'
  obtain ⟨hsum, hP⟩ := summable_and_abs_tsum_progression_sub_integral_le hk2
    (contDiff_flatProfile N (n := k)) (hM N h) (γ := (Q : ℝ) / N) (by positivity) (((b : ℝ) + 1) / N)
  rw [cellFibreSum_flatWaveletVec_eq h hb hsum]
  set L := ∑' n : ℤ, flatProfile N (((b : ℝ) + 1) / N + ((Q : ℝ) / N) * n)
  set I := ∫ x, flatProfile N x
  have hinv : ((Q : ℝ) / N)⁻¹ = N / Q := inv_div _ _
  rw [hinv] at hP
  have hk1 : ((Q : ℝ) / N) ^ (k - 1) = ((Q : ℝ) / N) ^ k * ((N : ℝ) / Q) := by
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, pow_succ]
    field_simp
  have hI := hCI N h
  have hpowA := pow_le_rpow_of_le_one hx0 hx1 hA hAk
  have hL : |L| ≤ (CI + M * Z) * (((N : ℝ) ^ 2)⁻¹ + ((Q : ℝ) / N) ^ A) * ((N : ℝ) / Q) := by
    have h1 : |L| ≤ (N / Q) * |I| + |L - (N / Q) * I| := by
      have := abs_sub_abs_le_abs_sub L ((N / Q) * I)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < N / Q)] at this
      linarith
    have h2 : (N / Q) * |I| ≤ (N / Q) * (CI * ((N : ℝ) ^ 2)⁻¹) := by
      gcongr; rw [← div_eq_mul_inv]; exact hI
    have h3 : |L - (N / Q) * I| ≤ M * Z * ((Q : ℝ) / N) ^ A * ((N : ℝ) / Q) := by
      refine hP.trans ?_
      rw [hk1]
      calc M * (((Q : ℝ) / N) ^ k * ((N : ℝ) / Q)) * Z = M * Z * ((Q : ℝ) / N) ^ k * ((N : ℝ) / Q) := by ring
        _ ≤ M * Z * ((Q : ℝ) / N) ^ A * ((N : ℝ) / Q) := by gcongr
    have hrpow : 0 ≤ ((Q : ℝ) / N) ^ A := Real.rpow_nonneg hx0 _
    have hNQ : 0 ≤ (N : ℝ) / Q := by positivity
    calc |L| ≤ (N / Q) * (CI * ((N : ℝ) ^ 2)⁻¹) + M * Z * ((Q : ℝ) / N) ^ A * ((N : ℝ) / Q) := by
          linarith
      _ ≤ (CI + M * Z) * (((N : ℝ) ^ 2)⁻¹ + ((Q : ℝ) / N) ^ A) * ((N : ℝ) / Q) := by
          have hinvN : 0 ≤ ((N : ℝ) ^ 2)⁻¹ := by positivity
          nlinarith [mul_nonneg (mul_nonneg hM0 hZ0) (mul_nonneg hinvN hNQ),
            mul_nonneg hCI0 (mul_nonneg hrpow hNQ)]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < N * Real.sqrt N)]
  calc |L| / (N * Real.sqrt N) ≤
        (CI + M * Z) * (((N : ℝ) ^ 2)⁻¹ + ((Q : ℝ) / N) ^ A) * ((N : ℝ) / Q) / (N * Real.sqrt N) := by
        gcongr
    _ = (CI + M * Z) / (Q * Real.sqrt N) * (((N : ℝ) ^ 2)⁻¹ + ((Q : ℝ) / N) ^ A) := by
        field_simp

/-- **(22), projection form.** `‖P_Q q_N^flat‖_H ≤ C_A √(Q/N) [N^{−2} + (Q/N)^A]` for `1 ≤ Q ≤ N`. -/
theorem exists_norm_starProjection_periodicSpace_flat_le {A : ℝ} (hA : 0 < A) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, gaugeActive N → ∀ Q : ℕ, 1 ≤ Q → Q ≤ N →
      ‖(periodicSpace Q).starProjection (flatWaveletVec N)‖ ≤
        C * Real.sqrt ((Q : ℝ) / N) * (((N : ℝ) ^ 2)⁻¹ + ((Q : ℝ) / N) ^ A) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_cellFibreSum_flat_le hA
  refine ⟨2 * C, by positivity, fun N h Q hQ hQN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.1
  have hNR : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set E := ((N : ℝ) ^ 2)⁻¹ + ((Q : ℝ) / N) ^ A
  have hE0 : 0 ≤ E := add_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hP := norm_sq_starProjection_periodicSpace_le (by omega : 0 < Q) (flatWaveletVec N)
  have hb : ∀ b ∈ Finset.range Q, cellFibreSum (flatWaveletVec N) Q b ^ 2 ≤
      (C / (Q * Real.sqrt N) * E) ^ 2 := fun b hb => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC N h Q hQ hQN b (Finset.mem_range.1 hb)) 2
  have hsum : ∑ b ∈ Finset.range Q, cellFibreSum (flatWaveletVec N) Q b ^ 2 ≤
      Q * (C / (Q * Real.sqrt N) * E) ^ 2 := by
    calc _ ≤ ∑ b ∈ Finset.range Q, (C / (Q * Real.sqrt N) * E) ^ 2 := Finset.sum_le_sum hb
      _ = Q * (C / (Q * Real.sqrt N) * E) ^ 2 := by simp
  have hsq : ‖(periodicSpace Q).starProjection (flatWaveletVec N)‖ ^ 2 ≤
      (2 * C * Real.sqrt ((Q : ℝ) / N) * E) ^ 2 := by
    refine hP.trans ?_
    calc (Q : ℝ) * (Q + 1) * ∑ b ∈ Finset.range Q, cellFibreSum (flatWaveletVec N) Q b ^ 2 ≤
          Q * (Q + 1) * (Q * (C / (Q * Real.sqrt N) * E) ^ 2) := by gcongr
      _ = (Q + 1) * C ^ 2 * E ^ 2 / N := by
          field_simp
          rw [Real.sq_sqrt hNR.le]
          ring
      _ ≤ (2 * Q) * C ^ 2 * E ^ 2 / N := by gcongr; linarith
      _ ≤ (2 * C * Real.sqrt ((Q : ℝ) / N) * E) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
          rw [div_le_iff₀ hNR]
          field_simp
          nlinarith [sq_nonneg C, sq_nonneg E, hQR]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **(22a)** `Σ_r w_r |q_N^flat − P_Q q_N^flat| ≤ C N^{3/2}/Q²`, for every period `Q ≥ 1`. -/
theorem exists_tsum_cellWeight_abs_sub_projection_flat_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, gaugeActive N → ∀ Q : ℕ, 1 ≤ Q →
      Summable (fun j => cellWeight j *
        |flatWaveletVec N j - (periodicSpace Q).starProjection (flatWaveletVec N) j|) ∧
      ∑' j, cellWeight j * |flatWaveletVec N j - (periodicSpace Q).starProjection (flatWaveletVec N) j| ≤
        C * (N * Real.sqrt N) / (Q : ℝ) ^ 2 := by
  obtain ⟨C1, hC10, hC1⟩ := exists_tsum_abs_flatCellWavelet_le
  refine ⟨6 * C1, by positivity, fun N h Q hQ => ?_⟩
  obtain ⟨hs, hle⟩ := hC1 N h
  have hv : Summable fun j => |flatWaveletVec N j| := hs.congr fun j => by rw [flatWaveletVec_apply h.1]
  have hv' : ∑' j, |flatWaveletVec N j| = ∑' j, |flatCellWavelet N (j + 1)| :=
    tsum_congr fun j => by rw [flatWaveletVec_apply h.1]
  obtain ⟨hsum, hbound⟩ := tsum_cellWeight_abs_sub_starProjection_periodicSpace_le (by omega : 0 < Q)
    (flatWaveletVec N) hv
  refine ⟨hsum, hbound.trans ?_⟩
  rw [hv']
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc 6 / (Q : ℝ) ^ 2 * ∑' j, |flatCellWavelet N (j + 1)| ≤ 6 / (Q : ℝ) ^ 2 * (C1 * (N * Real.sqrt N)) := by
        gcongr
    _ = 6 * C1 * (N * Real.sqrt N) / (Q : ℝ) ^ 2 := by ring

end

end RHTower

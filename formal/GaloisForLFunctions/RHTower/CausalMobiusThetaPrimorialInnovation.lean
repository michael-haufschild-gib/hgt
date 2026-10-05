import GaloisForLFunctions.RHTower.CausalMobiusThetaTransitionClock
import GaloisForLFunctions.RHTower.CausalMobiusThetaMovingCusp
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Bertrand

/-!
# The prime-only innovation of the causal theta source

Replace the history clock `lcm(1,…,l)` by the primorial `R_l = ∏_{p ≤ l} p`, keeping the physical
measure.  With `F_l` the physical sequences periodic modulo `R_l` and `Π_l` its projection:

* **(1)** `C_N = I_N^sf + P_N^sf`, `I_N^sf = Σ_{d≤N} μ(d)(f_d − Π_{d−1} f_d)`;
* **(2)** only primes innovate: `I_N^sf = Σ_{p≤N} μ(p)(f_p − Π_{p−1}f_p)`;
* **(3)** the prime increments are orthogonal and `‖I_N^sf‖² ≤ Σ_p 1/(R_{p−1}+1) < 2`;
* **(4)** `‖P_N^sf‖ ≤ N + √2`, `|P_N^sf(r)| ≤ 2N`, `P_N^sf ∈ F_N`;
* the primorial grows faster than every power (Bertrand), so the clocks `l₋` (largest with
  `R ≤ N^{1−δ}`) and `l₊` (least with `R ≥ N^{5/4+δ}`) exist;
* **(7)** `B(N) = ⟨(Π_{l₊} − Π_{l₋})P_N^sf, q_N^flat⟩_H + O_δ(1) = Σ_{l₋<p≤l₊} ⟨(Π_p − Π_{p−1})P_N^sf,
  q_N^flat⟩_H + O_δ(1)`, and RH is equivalent to subpower growth of this prime-only covariance.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

namespace DeletionResidueMartingale

/-! ## Primorial clocks -/

theorem primorial_succ_eq (n : ℕ) :
    primorial (n + 1) = if (n + 1).Prime then (n + 1) * primorial n else primorial n := by
  unfold primorial
  rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_range_succ]
  split_ifs <;> ring

theorem primorial_dvd_primorial {m n : ℕ} (h : m ≤ n) : primorial m ∣ primorial n := by
  unfold primorial
  exact Finset.prod_dvd_prod_of_subset _ _ _
    (Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega)))

theorem prime_dvd_primorial {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) : p ∣ primorial n :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)

theorem squarefree_dvd_primorial {d n : ℕ} (hd : Squarefree d) (hn : ∀ p ∈ d.primeFactors, p ≤ n) :
    d ∣ primorial n := by
  rw [← Nat.prod_primeFactors_of_squarefree hd]
  unfold primorial
  refine Finset.prod_dvd_prod_of_subset _ _ id fun p hp => ?_
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hn p hp; omega), Nat.prime_of_mem_primeFactors hp⟩

theorem primorial_succ_of_not_prime {n : ℕ} (hn : ¬ (n + 1).Prime) : primorial (n + 1) = primorial n := by
  rw [primorial_succ_eq, if_neg hn]

theorem two_mul_primorial_le_of_prime {n : ℕ} (hn : (n + 1).Prime) :
    2 * primorial n ≤ primorial (n + 1) := by
  rw [primorial_succ_eq, if_pos hn]
  exact Nat.mul_le_mul_right _ hn.two_le

/-! ## Primorial histories -/

/-- The physical history `F_l` of sequences periodic modulo `R_l`. -/
abbrev primorialSpace (l : ℕ) : Submodule ℝ (Lp ℝ 2 cellMeasure) := periodicSpace (primorial l)

theorem periodicSpace_mono {Q Q' : ℕ} (h : Q ∣ Q') : periodicSpace Q ≤ periodicSpace Q' := by
  intro v hv
  change v ∈ lpMeas ℝ ℝ (residueSigma Q') 2 cellMeasure
  change v ∈ lpMeas ℝ ℝ (residueSigma Q) 2 cellMeasure at hv
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hv ⊢
  exact hv.mono (residueSigma_mono h)

theorem primorialSpace_mono {m n : ℕ} (h : m ≤ n) : primorialSpace m ≤ primorialSpace n :=
  periodicSpace_mono (primorial_dvd_primorial h)

theorem residueVec_mem_periodicSpace {d Q : ℕ} (h : d ∣ Q) : residueVec d ∈ periodicSpace Q := by
  refine mem_periodicSpace_of_apply Q _ (fun b => residue d b) fun j => ?_
  rw [residueVec_apply_eq_residue, residue, residue, Nat.add_mod j 1 d, Nat.add_mod (j % Q) 1 d,
    Nat.mod_mod_of_dvd j h]

theorem predictorVec_mem_periodicSpace (n L : ℕ) : predictorVec n L ∈ periodicSpace L := by
  refine mem_periodicSpace_of_apply L _ (fun b => residue n b) fun j => ?_
  exact cell_point_eq_of_ae (MemLp.coeFn_toLp _) j

/-- The `d`-th primorial innovation `f_d − Π_{d−1} f_d`. -/
def primorialIncrement (d : ℕ) : Lp ℝ 2 cellMeasure :=
  residueVec d - (primorialSpace (d - 1)).starProjection (residueVec d)

/-- `I_N^sf`. -/
def primorialInnovation (N : ℕ) : Lp ℝ 2 cellMeasure :=
  ∑ i ∈ Finset.range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) • primorialIncrement (i + 1)

/-- `P_N^sf`. -/
def primorialDrift (N : ℕ) : Lp ℝ 2 cellMeasure :=
  ∑ i ∈ Finset.range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
    (primorialSpace i).starProjection (residueVec (i + 1))

/-- **(1)** `C_N = I_N^sf + P_N^sf`. -/
theorem sourceVec_eq_primorialInnovation_add_drift (N : ℕ) :
    sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N =
      primorialInnovation N + primorialDrift N := by
  rw [sourceVec, primorialInnovation, primorialDrift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [primorialIncrement, Nat.add_sub_cancel, smul_sub]
  abel

/-- A squarefree composite atom (and the unit atom) is already predicted. -/
theorem primorialIncrement_eq_zero_of_not_prime {d : ℕ} (hd : ¬ d.Prime)
    (hμ : ArithmeticFunction.moebius d ≠ 0) : primorialIncrement d = 0 := by
  have hsq : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 hμ
  have hmem : residueVec d ∈ primorialSpace (d - 1) := by
    refine residueVec_mem_periodicSpace (squarefree_dvd_primorial hsq fun p hp => ?_)
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hd0 : d ≠ 0 := hsq.ne_zero
    have hle : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hpd
    have hne : p ≠ d := fun h => hd (h ▸ hpp)
    omega
  rw [primorialIncrement, Submodule.starProjection_eq_self_iff.2 hmem, sub_self]

/-- **(2)** Only primes innovate. -/
theorem primorialInnovation_eq_sum_primes (N : ℕ) :
    primorialInnovation N = ∑ i ∈ (Finset.range N).filter (fun i => (i + 1).Prime),
      ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) • primorialIncrement (i + 1) := by
  rw [primorialInnovation, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hp : (i + 1).Prime
  · rw [if_pos hp]
  · rw [if_neg hp]
    by_cases hμ : ArithmeticFunction.moebius (i + 1) = 0
    · simp [hμ]
    · rw [primorialIncrement_eq_zero_of_not_prime hp hμ, smul_zero]

theorem primorialIncrement_mem {p : ℕ} (hp : p.Prime) : primorialIncrement p ∈ primorialSpace p :=
  Submodule.sub_mem _ (residueVec_mem_periodicSpace (prime_dvd_primorial hp le_rfl))
    (primorialSpace_mono (by omega) (Submodule.starProjection_apply_mem _ _))

theorem primorialIncrement_orthogonal {d : ℕ} {w : Lp ℝ 2 cellMeasure} (hw : w ∈ primorialSpace (d - 1)) :
    inner ℝ (primorialIncrement d) w = 0 :=
  Submodule.starProjection_inner_eq_zero _ _ hw

theorem inner_primorialIncrement_eq_zero {p q : ℕ} (hp : p.Prime) (hpq : p < q) :
    inner ℝ (primorialIncrement q) (primorialIncrement p) = 0 :=
  primorialIncrement_orthogonal (primorialSpace_mono (by omega) (primorialIncrement_mem hp))

/-- Least squares against the periodic predictor: `‖f_d − Π_{d−1} f_d‖² ≤ 1/(R_{d−1}+1)`. -/
theorem norm_sq_primorialIncrement_le (d : ℕ) :
    ‖primorialIncrement d‖ ^ 2 ≤ 1 / ((primorial (d - 1) : ℝ) + 1) := by
  have h : ‖primorialIncrement d‖ ≤ ‖residueVec d - predictorVec d (primorial (d - 1))‖ := by
    rw [primorialIncrement, Submodule.starProjection_minimal]
    change _ ≤ ‖residueVec d -
      (⟨predictorVec d (primorial (d - 1)), predictorVec_mem_periodicSpace _ _⟩ : primorialSpace (d - 1))‖
    exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h |>.trans (residue_prediction_error _ _)

/-! ## (3) The prime innovation is uniformly bounded -/

theorem norm_sq_sum_primorialIncrement (S : Finset ℕ) (hS : ∀ i ∈ S, (i + 1).Prime) (c : ℕ → ℝ) :
    ‖∑ i ∈ S, c i • primorialIncrement (i + 1)‖ ^ 2 = ∑ i ∈ S, c i ^ 2 * ‖primorialIncrement (i + 1)‖ ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hS' : ∀ i ∈ S, (i + 1).Prime := fun i hi => hS i (Finset.mem_insert_of_mem hi)
    have ha' : (a + 1).Prime := hS a (Finset.mem_insert_self a S)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, norm_add_sq_real, ih hS', inner_sum,
      Finset.sum_eq_zero fun i hi => ?_, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    · ring
    · rw [inner_smul_left, inner_smul_right, conj_trivial]
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      rcases lt_or_gt_of_ne hne with h | h
      · rw [real_inner_comm, inner_primorialIncrement_eq_zero ha' (by omega)]; ring
      · rw [inner_primorialIncrement_eq_zero (hS' i hi) (by omega)]; ring

theorem prime_term_le_telescoping (i : ℕ) :
    (if (i + 1).Prime then 1 / ((primorial i : ℝ) + 1) else 0) ≤
      2 * (1 / (primorial i : ℝ) - 1 / (primorial (i + 1) : ℝ)) := by
  have hR : (0 : ℝ) < primorial i := by exact_mod_cast primorial_pos i
  split_ifs with hp
  · have h2 : (2 : ℝ) * primorial i ≤ primorial (i + 1) := by exact_mod_cast two_mul_primorial_le_of_prime hp
    have hR1 : (0 : ℝ) < primorial (i + 1) := by linarith
    have : 1 / (primorial (i + 1) : ℝ) ≤ 1 / (2 * primorial i) := one_div_le_one_div_of_le (by positivity) h2
    have h3 : 1 / ((primorial i : ℝ) + 1) ≤ 1 / (primorial i : ℝ) := one_div_le_one_div_of_le hR (by linarith)
    have h4 : 1 / (2 * (primorial i : ℝ)) = (1 / (primorial i : ℝ)) / 2 := by field_simp
    linarith
  · rw [primorial_succ_of_not_prime hp, sub_self, mul_zero]

/-- `Σ_{p≤N} 1/(R_{p−1}+1) ≤ 2(1 − 1/R_N) < 2`. -/
theorem sum_prime_inv_primorial_le (N : ℕ) :
    ∑ i ∈ (Finset.range N).filter (fun i => (i + 1).Prime), 1 / ((primorial i : ℝ) + 1) ≤
      2 * (1 - 1 / (primorial N : ℝ)) := by
  rw [Finset.sum_filter]
  refine (Finset.sum_le_sum fun i _ => prime_term_le_telescoping i).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_range_sub' (fun i => 1 / (primorial i : ℝ)) N]
  have h0 : primorial 0 = 1 := by decide
  simp [h0]

/-- **(3)** `‖I_N^sf‖² = Σ_p ‖f_p − Π_{p−1}f_p‖² ≤ Σ_p 1/(R_{p−1}+1) < 2`. -/
theorem norm_sq_primorialInnovation_le (N : ℕ) :
    ‖primorialInnovation N‖ ^ 2 = ∑ i ∈ (Finset.range N).filter (fun i => (i + 1).Prime),
        ‖primorialIncrement (i + 1)‖ ^ 2 ∧
      ‖primorialInnovation N‖ ^ 2 < 2 := by
  have hS : ∀ i ∈ (Finset.range N).filter (fun i => (i + 1).Prime), (i + 1).Prime :=
    fun i hi => (Finset.mem_filter.1 hi).2
  have heq : ‖primorialInnovation N‖ ^ 2 = ∑ i ∈ (Finset.range N).filter (fun i => (i + 1).Prime),
      ‖primorialIncrement (i + 1)‖ ^ 2 := by
    rw [primorialInnovation_eq_sum_primes, norm_sq_sum_primorialIncrement _ hS]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ArithmeticFunction.moebius_apply_prime (hS i hi)]
    simp
  refine ⟨heq, ?_⟩
  rw [heq]
  calc ∑ i ∈ (Finset.range N).filter (fun i => (i + 1).Prime), ‖primorialIncrement (i + 1)‖ ^ 2
      ≤ ∑ i ∈ (Finset.range N).filter (fun i => (i + 1).Prime), 1 / ((primorial i : ℝ) + 1) :=
        Finset.sum_le_sum fun i _ => by
          have := norm_sq_primorialIncrement_le (i + 1); simpa using this
    _ ≤ 2 * (1 - 1 / (primorial N : ℝ)) := sum_prime_inv_primorial_le N
    _ < 2 := by
        have : (0 : ℝ) < 1 / (primorial N : ℝ) := by
          have : (0 : ℝ) < primorial N := by exact_mod_cast primorial_pos N
          positivity
        linarith

theorem norm_primorialInnovation_le (N : ℕ) : ‖primorialInnovation N‖ ≤ Real.sqrt 2 :=
  Real.le_sqrt_of_sq_le (norm_sq_primorialInnovation_le N).2.le

/-! ## (4) The predictable part -/

theorem lp_apply_sum (s : Finset ℕ) (f : ℕ → Lp ℝ 2 cellMeasure) (j : ℕ) :
    (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact cell_point_eq_of_ae (Lp.coeFn_zero ℝ 2 cellMeasure) j
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, cell_point_eq_of_ae (Lp.coeFn_add _ _) j,
      Pi.add_apply, ih]

theorem starProjection_periodicSpace_apply_mem_Icc {Q d : ℕ} (hQ : 0 < Q) (j : ℕ) :
    0 ≤ (periodicSpace Q).starProjection (residueVec d) j ∧
      (periodicSpace Q).starProjection (residueVec d) j ≤ 1 := by
  rw [starProjection_periodicSpace_apply hQ]
  set b := j % Q
  have hV := cellFibreMass_pos b Q hQ
  have hs : Summable fun k => residueVec d (b + Q * k) * cellWeight (b + Q * k) :=
    summable_progression_of_summable (summable_mul_cellWeight_of_lp _) b Q hQ
  have hc := summable_cellWeight_progression b Q hQ
  have h0 : 0 ≤ cellFibreSum (residueVec d) Q b :=
    tsum_nonneg fun k => mul_nonneg (by rw [residueVec_apply_eq_residue]; exact (residue_bounds _ _).1)
      (cellWeight_pos _).le
  have h1 : cellFibreSum (residueVec d) Q b ≤ cellFibreMass Q b :=
    Summable.tsum_le_tsum (fun k => mul_le_of_le_one_left (cellWeight_pos _).le
      (by rw [residueVec_apply_eq_residue]; exact (residue_bounds _ _).2)) hs hc
  exact ⟨div_nonneg h0 hV.le, (div_le_one hV).2 h1⟩

theorem abs_primorialIncrement_apply_le (d j : ℕ) : |primorialIncrement d j| ≤ 1 := by
  rw [primorialIncrement, cell_point_eq_of_ae (Lp.coeFn_sub _ _) j, Pi.sub_apply,
    residueVec_apply_eq_residue]
  have h1 := residue_bounds d j
  have h2 := starProjection_periodicSpace_apply_mem_Icc (d := d) (primorial_pos (d - 1)) j
  rw [abs_le]; constructor <;> linarith [h2.1, h2.2]

/-- **(4)** `P_N^sf ∈ F_N`. -/
theorem primorialDrift_mem (N : ℕ) : primorialDrift N ∈ primorialSpace N :=
  Submodule.sum_mem _ fun _ hi => Submodule.smul_mem _ _
    (primorialSpace_mono (Nat.le_of_lt (Finset.mem_range.1 hi)) (Submodule.starProjection_apply_mem _ _))

theorem norm_sourceVec_moebius_le (N : ℕ) :
    ‖sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ ≤ N := by
  have h := hasSum_norm_sq (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
  have hle : ‖sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ ^ 2 ≤ (N : ℝ) ^ 2 := by
    rw [← h.tsum_eq, ← mul_one ((N : ℝ) ^ 2), ← hasSum_cellWeight.tsum_eq, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) h.summable (hasSum_cellWeight.summable.mul_left _)
    rw [sourceVec_apply_eq_cell]
    have := abs_moebiusCell_le N (j + 1)
    have hsq : moebiusCell N (j + 1) ^ 2 ≤ (N : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    exact mul_le_mul_of_nonneg_right hsq (cellWeight_pos j).le
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Nat.cast_nonneg _) two_ne_zero).1 hle

/-- **(4)** `‖P_N^sf‖ ≤ N + √2`. -/
theorem norm_primorialDrift_le (N : ℕ) : ‖primorialDrift N‖ ≤ N + Real.sqrt 2 := by
  have h := sourceVec_eq_primorialInnovation_add_drift N
  have hP : primorialDrift N = sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N -
      primorialInnovation N := by rw [h]; abel
  rw [hP]
  exact (norm_sub_le _ _).trans (add_le_add (norm_sourceVec_moebius_le N) (norm_primorialInnovation_le N))

/-- **(4)** `|P_N^sf(r)| ≤ 2N`. -/
theorem abs_primorialDrift_apply_le (N j : ℕ) : |primorialDrift N j| ≤ 2 * N := by
  have h := sourceVec_eq_primorialInnovation_add_drift N
  have hP : primorialDrift N j = sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N j -
      primorialInnovation N j := by
    rw [h, cell_point_eq_of_ae (Lp.coeFn_add _ _) j, Pi.add_apply]; ring
  have hC : |sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N j| ≤ N := by
    rw [sourceVec_apply_eq_cell]; exact abs_moebiusCell_le N (j + 1)
  have hI : |primorialInnovation N j| ≤ N := by
    rw [primorialInnovation, lp_apply_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range N, |(((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
          primorialIncrement (i + 1)) j| ≤ ∑ i ∈ Finset.range N, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [cell_point_eq_of_ae (Lp.coeFn_smul _ _) j, Pi.smul_apply, smul_eq_mul, abs_mul]
          exact mul_le_one₀ (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one) (abs_nonneg _)
            (abs_primorialIncrement_apply_le _ _)
      _ = N := by simp
  rw [hP]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ (N : ℝ) + N := add_le_add hC hI
    _ = 2 * N := by ring

/-! ## Growth of the primorial -/

/-- Bertrand: `n R_n ≤ R_{2n}`. -/
theorem mul_primorial_le_primorial_two_mul {n : ℕ} (hn : n ≠ 0) : n * primorial n ≤ primorial (2 * n) := by
  obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  rw [two_mul, primorial_add, mul_comm]
  refine Nat.mul_le_mul_left _ (le_trans (by omega : n ≤ p) ?_)
  refine Finset.single_le_prod' (f := fun p => p) (fun q hq => (Finset.mem_filter.1 hq).2.one_lt.le) ?_
  exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, by omega⟩, hp⟩

theorem two_pow_le_primorial_two_pow (k : ℕ) :
    2 ^ (∑ i ∈ Finset.range k, i) ≤ primorial (2 ^ k) := by
  induction k with
  | zero => simp [show primorial 1 = 1 by decide]
  | succ k ih =>
    have h := mul_primorial_le_primorial_two_mul (n := 2 ^ k) (by positivity)
    rw [← pow_succ'] at h
    rw [Finset.sum_range_succ, pow_add, mul_comm]
    calc 2 ^ k * 2 ^ (∑ i ∈ Finset.range k, i) ≤ 2 ^ k * primorial (2 ^ k) := Nat.mul_le_mul_left _ ih
      _ ≤ primorial (2 ^ (k + 1)) := h

/-- **The primorial grows faster than every fixed power.** -/
theorem eventually_rpow_le_primorial (c : ℝ) : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ primorial N := by
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (2 * |c| + 3)
  have hpow : ∀ k : ℕ, k₀ ≤ k →
      (2 : ℝ) ^ ((k + 1) * |c|) ≤ 2 ^ (((∑ i ∈ Finset.range k, i : ℕ)) : ℝ) := by
    intro k hk
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hkR : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    have hg := Finset.sum_range_id_mul_two k
    have hk1 : 1 ≤ k := by
      have : (0 : ℝ) < k₀ := by linarith [abs_nonneg c]
      exact_mod_cast (show (1 : ℝ) ≤ k by
        have : (1 : ℝ) ≤ k₀ := by exact_mod_cast (show 1 ≤ k₀ by exact_mod_cast this)
        linarith)
    have hgR : ((∑ i ∈ Finset.range k, i : ℕ) : ℝ) * 2 = (k : ℝ) * ((k : ℝ) - 1) := by
      have : ((∑ i ∈ Finset.range k, i) * 2 : ℕ) = k * (k - 1) := hg
      have h2 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1]; simp
      rw [← h2]; exact_mod_cast this
    nlinarith [abs_nonneg c]
  refine eventually_atTop.2 ⟨2 ^ k₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_two_pow) hN
  set k := Nat.log 2 N with hkdef
  have hk1 : 2 ^ k ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hk2 : N < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hkk : k₀ ≤ k := by
    rw [hkdef]; exact Nat.le_log_of_pow_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  calc (N : ℝ) ^ c ≤ (N : ℝ) ^ |c| := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (le_abs_self c)
    _ ≤ ((2 : ℝ) ^ (k + 1)) ^ |c| := Real.rpow_le_rpow hNR.le (by exact_mod_cast hk2.le) (abs_nonneg c)
    _ = (2 : ℝ) ^ ((k + 1) * |c|) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; ring_nf
    _ ≤ 2 ^ (((∑ i ∈ Finset.range k, i : ℕ)) : ℝ) := hpow k hkk
    _ = ((2 ^ (∑ i ∈ Finset.range k, i) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
    _ ≤ primorial (2 ^ k) := by exact_mod_cast two_pow_le_primorial_two_pow k
    _ ≤ primorial N := by exact_mod_cast primorial_mono hk1

theorem exists_primorial_ge (X : ℝ) : ∃ l : ℕ, X ≤ primorial l := by
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes ⌈X⌉₊
  refine ⟨p, ?_⟩
  have : p ≤ primorial p := Nat.le_of_dvd (primorial_pos p) (prime_dvd_primorial hp le_rfl)
  calc X ≤ ⌈X⌉₊ := Nat.le_ceil X
    _ ≤ p := by exact_mod_cast hp1
    _ ≤ primorial p := by exact_mod_cast this

end DeletionResidueMartingale

open DeletionResidueMartingale

/-! ## The transition clocks `l₋`, `l₊` -/

/-- `l₊`: the least primorial clock with `R_{l₊} ≥ N^{5/4+δ}`. -/
def primorialUpper (δ : ℝ) (N : ℕ) : ℕ := by
  classical exact Nat.find (exists_primorial_ge ((N : ℝ) ^ (5 / 4 + δ)))

/-- `l₋`: the largest clock `≤ l₊` with `R_{l₋} ≤ N^{1−δ}`. -/
def primorialLower (δ : ℝ) (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun l => (primorial l : ℝ) ≤ (N : ℝ) ^ (1 - δ)) (primorialUpper δ N)

theorem primorial_primorialUpper_ge (δ : ℝ) (N : ℕ) :
    (N : ℝ) ^ (5 / 4 + δ) ≤ primorial (primorialUpper δ N) := by
  classical
  unfold primorialUpper
  exact Nat.find_spec (exists_primorial_ge _)

theorem primorial_lt_of_lt_primorialUpper {δ : ℝ} {N l : ℕ} (hl : l < primorialUpper δ N) :
    (primorial l : ℝ) < (N : ℝ) ^ (5 / 4 + δ) := by
  classical
  unfold primorialUpper at hl
  exact not_le.1 (Nat.find_min _ hl)

theorem primorialLower_le_upper (δ : ℝ) (N : ℕ) : primorialLower δ N ≤ primorialUpper δ N := by
  classical
  unfold primorialLower
  exact Nat.findGreatest_le _

theorem primorial_primorialLower_le {δ : ℝ} (hδ1 : δ ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    (primorial (primorialLower δ N) : ℝ) ≤ (N : ℝ) ^ (1 - δ) := by
  classical
  have h0 : primorial 0 = 1 := by decide
  have hP0 : (primorial 0 : ℝ) ≤ (N : ℝ) ^ (1 - δ) := by
    rw [h0, Nat.cast_one]
    exact Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
  unfold primorialLower
  exact Nat.findGreatest_spec (P := fun l => (primorial l : ℝ) ≤ (N : ℝ) ^ (1 - δ)) (Nat.zero_le _) hP0

/-- `l₋` is the largest clock with `R ≤ N^{1−δ}` (for `N ≥ 2`). -/
theorem le_primorialLower {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 2 ≤ N) {l : ℕ}
    (hl : (primorial l : ℝ) ≤ (N : ℝ) ^ (1 - δ)) : l ≤ primorialLower δ N := by
  classical
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  by_contra hcon
  push Not at hcon
  by_cases hlu : l ≤ primorialUpper δ N
  · unfold primorialLower at hcon
    exact Nat.findGreatest_is_greatest hcon hlu hl
  · push Not at hlu
    have h1 := primorial_primorialUpper_ge δ N
    have h2 : (primorial (primorialUpper δ N) : ℝ) ≤ primorial l := by
      exact_mod_cast primorial_mono hlu.le
    have h3 : (N : ℝ) ^ (1 - δ) < (N : ℝ) ^ (5 / 4 + δ) :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)
    linarith

/-! ## (7) The prime-only transition -/

/-- The prime layers of the transition band. -/
def primorialTransitionLayers (δ : ℝ) (N : ℕ) : Finset ℕ := by
  classical exact (Finset.Ioc (primorialLower δ N) (primorialUpper δ N)).filter Nat.Prime

/-- **The prime-only transition covariance** of (7). -/
def primorialTransitionCovariance (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ l ∈ primorialTransitionLayers δ N,
    inner ℝ ((primorialSpace l).starProjection (primorialDrift N) -
      (primorialSpace (l - 1)).starProjection (primorialDrift N)) (flatWaveletVec N)

theorem sum_Ioc_sub_eq {V : Type*} [AddCommGroup V] (f : ℕ → V) {a b : ℕ} (h : a ≤ b) :
    ∑ l ∈ Finset.Ioc a b, (f l - f (l - 1)) = f b - f a := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih, Nat.add_sub_cancel]
    abel

/-- The middle difference telescopes over primes. -/
theorem inner_primorialProjection_diff_eq (δ : ℝ) (N : ℕ) :
    inner ℝ ((primorialSpace (primorialUpper δ N)).starProjection (primorialDrift N) -
      (primorialSpace (primorialLower δ N)).starProjection (primorialDrift N)) (flatWaveletVec N) =
        primorialTransitionCovariance δ N := by
  rw [← sum_Ioc_sub_eq (fun l => (primorialSpace l).starProjection (primorialDrift N))
    (primorialLower_le_upper δ N), sum_inner, primorialTransitionCovariance, primorialTransitionLayers,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun l hl => ?_
  split_ifs with hp
  · rfl
  · have hl1 : 1 ≤ l := by have := (Finset.mem_Ioc.1 hl).1; omega
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hR : primorial (m + 1) = primorial m := primorial_succ_of_not_prime hp
    simp only [Nat.add_sub_cancel, primorialSpace, hR, sub_self, inner_zero_left]

theorem abs_inner_primorialDrift_le (N : ℕ) (u : Lp ℝ 2 cellMeasure)
    (hu : Summable fun j => cellWeight j * |u j|) :
    |inner ℝ (primorialDrift N) u| ≤ 2 * N * ∑' j, cellWeight j * |u j| := by
  have h := hasSum_inner (primorialDrift N) u
  have hb : ∀ j, ‖primorialDrift N j * u j * cellWeight j‖ ≤ 2 * N * (cellWeight j * |u j|) := fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (cellWeight_pos j)]
    calc |primorialDrift N j| * |u j| * cellWeight j ≤ 2 * N * |u j| * cellWeight j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (abs_primorialDrift_apply_le N j)
            (abs_nonneg _)) (cellWeight_pos j).le
      _ = 2 * N * (cellWeight j * |u j|) := by ring
  rw [← h.tsum_eq, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (Summable.of_norm_bounded (hu.mul_left _) hb |>.norm)).trans
    (Summable.tsum_le_tsum hb (Summable.of_norm_bounded (hu.mul_left _) hb).norm (hu.mul_left _))

/-- **(7)** `B(N) = ⟨(Π_{l₊} − Π_{l₋})P_N^sf, q_N^flat⟩_H + O_δ(1)
`= Σ_{l₋<p≤l₊} ⟨(Π_p − Π_{p−1})P_N^sf, q_N^flat⟩_H + O_δ(1)`, for every `0 < δ < 1`. -/
theorem exists_abs_causalMobiusThetaTail_sub_primorialTransition_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |causalMobiusThetaTail N - inner ℝ ((primorialSpace (primorialUpper δ N)).starProjection
          (primorialDrift N) - (primorialSpace (primorialLower δ N)).starProjection (primorialDrift N))
          (flatWaveletVec N)| ≤ C ∧
      |causalMobiusThetaTail N - primorialTransitionCovariance δ N| ≤ C := by
  obtain ⟨Ce, hCe0, hCe⟩ := exists_abs_thetaCellDefect_le
  obtain ⟨Bf, hBf0, hBf⟩ := exists_norm_flatWaveletVec_le
  obtain ⟨CA, hCA0, hCA⟩ := exists_norm_starProjection_periodicSpace_flat_le (A := 1 / δ) (by positivity)
  obtain ⟨C22, hC220, hC22⟩ := exists_tsum_cellWeight_abs_sub_projection_flat_le
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 eventually_gaugeActive
  set Cact := Real.sqrt 2 * Bf + 2 * CA * (1 + Real.sqrt 2) + 2 * C22 + Ce
  set Cfin := ∑ N ∈ Finset.range N₀, |causalMobiusThetaTail N - primorialTransitionCovariance δ N|
  have hCfin0 : 0 ≤ Cfin := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨Cact + Cfin, by positivity, fun N hN => ?_⟩
  rw [inner_primorialProjection_diff_eq]
  suffices hmain : |causalMobiusThetaTail N - primorialTransitionCovariance δ N| ≤ Cact + Cfin from
    ⟨hmain, hmain⟩
  by_cases hNN : N < N₀
  · exact (Finset.single_le_sum
      (f := fun N : ℕ => |causalMobiusThetaTail (N : ℝ) - primorialTransitionCovariance δ N|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hNN)).trans (le_add_of_nonneg_left (by positivity))
  have h : gaugeActive N := hN₀ N (not_lt.1 hNN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNR : (0 : ℝ) < N := by linarith
  have hden : 1 ≤ (N : ℝ) ^ 2 * Real.sqrt N :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN1) (Real.one_le_sqrt.2 hN1)
  set P := primorialDrift N
  set q := flatWaveletVec N
  set Pm := (primorialSpace (primorialLower δ N)).starProjection
  set Pp := (primorialSpace (primorialUpper δ N)).starProjection
  have hB := causalMobiusThetaTail_natCast_eq_inner_flat hN
  rw [sourceVec_eq_primorialInnovation_add_drift, inner_add_left] at hB
  have hkey : causalMobiusThetaTail N - primorialTransitionCovariance δ N =
      inner ℝ (primorialInnovation N) q + inner ℝ (Pm P) q + inner ℝ (P - Pp P) q + thetaCellDefect N := by
    rw [hB, ← inner_primorialProjection_diff_eq]
    have : inner ℝ P q = inner ℝ (Pm P) q + inner ℝ (Pp P - Pm P) q + inner ℝ (P - Pp P) q := by
      rw [← inner_add_left, ← inner_add_left]; congr 1; abel
    rw [this]; ring
  -- bounds
  have e1 : |inner ℝ (primorialInnovation N) q| ≤ Real.sqrt 2 * Bf :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (norm_primorialInnovation_le N) (hBf N hN)
      (norm_nonneg _) (by positivity))
  have e2 : |inner ℝ (Pm P) q| ≤ 2 * CA * (1 + Real.sqrt 2) := by
    set R := primorial (primorialLower δ N)
    have hR1 : 1 ≤ R := primorial_pos _
    have hRle : (R : ℝ) ≤ (N : ℝ) ^ (1 - δ) := primorial_primorialLower_le hδ1.le hN
    have hNpow : (N : ℝ) ^ (1 - δ) ≤ N := by
      calc (N : ℝ) ^ (1 - δ) ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = N := Real.rpow_one _
    have hRN : R ≤ N := by exact_mod_cast hRle.trans hNpow
    have hP := hCA N h R hR1 hRN
    have hrat : ((R : ℝ) / N) ^ (1 / δ) ≤ (N : ℝ)⁻¹ := by
      have hx : (R : ℝ) / N ≤ (N : ℝ) ^ (-δ) := by
        rw [div_le_iff₀ hNR]
        calc (R : ℝ) ≤ (N : ℝ) ^ (1 - δ) := hRle
          _ = (N : ℝ) ^ (-δ) * N := by rw [sub_eq_neg_add, Real.rpow_add hNR, Real.rpow_one]
      calc ((R : ℝ) / N) ^ (1 / δ) ≤ ((N : ℝ) ^ (-δ)) ^ (1 / δ) :=
            Real.rpow_le_rpow (by positivity) hx (by positivity)
        _ = (N : ℝ)⁻¹ := by
            rw [← Real.rpow_mul hNR.le, show -δ * (1 / δ) = -1 by field_simp, Real.rpow_neg_one]
    have hsq : Real.sqrt ((R : ℝ) / N) ≤ 1 := by
      rw [Real.sqrt_le_one]; rw [div_le_one hNR]; exact_mod_cast hRN
    have hE : ((N : ℝ) ^ 2)⁻¹ + ((R : ℝ) / N) ^ (1 / δ) ≤ 2 / N := by
      have : ((N : ℝ) ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ := by apply inv_anti₀ hNR; nlinarith
      calc _ ≤ (N : ℝ)⁻¹ + (N : ℝ)⁻¹ := add_le_add this hrat
        _ = 2 / N := by ring
    have hPQ : ‖(periodicSpace R).starProjection q‖ ≤ CA * (2 / N) := by
      refine hP.trans ?_
      calc CA * Real.sqrt ((R : ℝ) / N) * (((N : ℝ) ^ 2)⁻¹ + ((R : ℝ) / N) ^ (1 / δ)) ≤
            CA * 1 * (2 / N) := by gcongr
        _ = CA * (2 / N) := by ring
    rw [show inner ℝ (Pm P) q = inner ℝ P (Pm q) from
      Submodule.inner_starProjection_left_eq_right _ _ _]
    calc |inner ℝ P (Pm q)| ≤ ‖P‖ * ‖Pm q‖ := abs_real_inner_le_norm _ _
      _ ≤ (N + Real.sqrt 2) * (CA * (2 / N)) :=
          mul_le_mul (norm_primorialDrift_le N) hPQ (norm_nonneg _) (by positivity)
      _ = 2 * CA * (1 + Real.sqrt 2 / N) := by field_simp
      _ ≤ 2 * CA * (1 + Real.sqrt 2) := by
          gcongr
          exact div_le_self (Real.sqrt_nonneg _) hN1
  have e3 : |inner ℝ (P - Pp P) q| ≤ 2 * C22 := by
    set R := primorial (primorialUpper δ N)
    have hR1 : 1 ≤ R := primorial_pos _
    have hRge := primorial_primorialUpper_ge δ N
    obtain ⟨hs, hle⟩ := hC22 N h R hR1
    have hpt : ∀ j, (q - Pp q) j = q j - Pp q j := fun j => cell_point_eq_of_ae (Lp.coeFn_sub _ _) j
    have hs' : Summable fun j => cellWeight j * |(q - Pp q) j| := hs.congr fun j => by rw [hpt]
    have hsa : inner ℝ (P - Pp P) q = inner ℝ P (q - Pp q) := by
      rw [inner_sub_left, inner_sub_right, Submodule.inner_starProjection_left_eq_right]
    rw [hsa]
    refine (abs_inner_primorialDrift_le N _ hs').trans ?_
    have hR2 : (N : ℝ) ^ 2 * Real.sqrt N ≤ (R : ℝ) ^ 2 := by
      have hX : (N : ℝ) ^ (5 / 4 + δ) ≥ (N : ℝ) ^ (5 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have hsq : ((N : ℝ) ^ (5 / 4 : ℝ)) ^ 2 = (N : ℝ) ^ 2 * Real.sqrt N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNR.le, Real.sqrt_eq_rpow,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Real.rpow_natCast (N : ℝ) 2,
          ← Real.rpow_add hNR]
        norm_num
      rw [← hsq]
      exact pow_le_pow_left₀ (by positivity) (hX.trans hRge) 2
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
    calc 2 * N * ∑' j, cellWeight j * |(q - Pp q) j| ≤ 2 * N * (C22 * (N * Real.sqrt N) / (R : ℝ) ^ 2) := by
          gcongr
          exact le_of_eq_of_le (tsum_congr fun j => by rw [hpt]) hle
      _ = 2 * C22 * ((N : ℝ) ^ 2 * Real.sqrt N / (R : ℝ) ^ 2) := by ring
      _ ≤ 2 * C22 * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; exact hR2
      _ = 2 * C22 := mul_one _
  have e4 : |thetaCellDefect N| ≤ Ce := (hCe N hN).trans (div_le_self hCe0 hden)
  rw [hkey]
  have := abs_add_le (inner ℝ (primorialInnovation N) q + inner ℝ (Pm P) q + inner ℝ (P - Pp P) q)
    (thetaCellDefect N)
  have := abs_add_le (inner ℝ (primorialInnovation N) q + inner ℝ (Pm P) q) (inner ℝ (P - Pp P) q)
  have := abs_add_le (inner ℝ (primorialInnovation N) q) (inner ℝ (Pm P) q)
  linarith

/-- **RH ⟺ subpower growth of the prime-only transition covariance** (each fixed `0 < δ < 1`). -/
theorem riemannHypothesis_iff_primorialTransition_subpower {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |primorialTransitionCovariance δ N| ≤ C * (N : ℝ) ^ ε := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_causalMobiusThetaTail_sub_primorialTransition_le hδ hδ1
  rw [riemannHypothesis_iff_causalMobiusThetaTail_nat_subpower]
  constructor
  · intro hB ε hε
    obtain ⟨C, hC⟩ := hB ε hε
    exact ⟨_, natPowerBound_of_abs_sub_le hε.le (fun N hN => (hD N hN).2) hC⟩
  · intro hT ε hε
    obtain ⟨C, hC⟩ := hT ε hε
    exact ⟨_, natPowerBound_of_abs_sub_le hε.le (fun N hN => by rw [abs_sub_comm]; exact (hD N hN).2) hC⟩

end

end RHTower

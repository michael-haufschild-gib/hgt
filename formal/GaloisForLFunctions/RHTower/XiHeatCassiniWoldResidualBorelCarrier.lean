import GaloisForLFunctions.RHTower.XiHeatCassiniWoldLowerHalfShiftGevreyKernel
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

/-!
# Source-marked Borel carrier for the Route-T Wold residual
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The eventual square-root-exponential Wold estimate extends across its finite prefix without
changing its exponent. -/
theorem exists_global_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_sqrt_rate :
    ∃ (C c : ℝ), 0 < c ∧ 0 ≤ C ∧ ∀ N : ℕ,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        C * Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)) := by
  obtain ⟨B, c, hc, hB, hrate⟩ :=
    exists_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate
  obtain ⟨N₀, htail⟩ := eventually_atTop.1 hrate
  let S : ℝ := ∑ N ∈ Finset.range N₀,
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      Real.exp (c * Real.sqrt (xiMassNthPrimeLogHeight N))
  let C : ℝ := B + S
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun N _ =>
      mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  have hC : 0 ≤ C := by dsimp only [C]; linarith
  have hBC : B ≤ C := by dsimp only [C]; linarith
  refine ⟨C, c, hc, hC, fun N => ?_⟩
  by_cases hN : N₀ ≤ N
  · calc
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
          B * Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)) := by
        simpa only [xiMassNthPrimeLogHeight] using htail N hN
      _ ≤ C * Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)) :=
        mul_le_mul_of_nonneg_right hBC (Real.exp_nonneg _)
  · have hmem : N ∈ Finset.range N₀ :=
      Finset.mem_range.mpr (Nat.lt_of_not_ge hN)
    have hterm :
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
            Real.exp (c * Real.sqrt (xiMassNthPrimeLogHeight N)) ≤ S := by
      dsimp only [S]
      exact Finset.single_le_sum
        (f := fun i : ℕ =>
          |xiHeatCassiniOrderedWoldResidualLogDiscrepancy i| *
            Real.exp (c * Real.sqrt (xiMassNthPrimeLogHeight i)))
        (fun i _ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)) hmem
    have hSC : S ≤ C := by dsimp only [C]; linarith
    calc
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| =
          (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
              Real.exp (c * Real.sqrt (xiMassNthPrimeLogHeight N))) *
            Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
        simp
      _ ≤ S * Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)) :=
        mul_le_mul_of_nonneg_right hterm (Real.exp_nonneg _)
      _ ≤ C * Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)) :=
        mul_le_mul_of_nonneg_right hSC (Real.exp_nonneg _)

/-- One source-labelled coefficient of the order-two Borel transform. -/
def xiHeatCassiniWoldResidualBorelAtom
    (x : ℝ) (xi : ℂ) (p : ℕ × ℕ) : ℂ :=
  xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom p.2 x p.1 * xi ^ p.2 /
    ((p.2.factorial : ℂ) ^ 2)

theorem norm_xiHeatCassiniWoldResidualBorelAtom
    (x : ℝ) (xi : ℂ) (N k : ℕ) :
    ‖xiHeatCassiniWoldResidualBorelAtom x xi (N, k)‖ =
      ‖xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x N‖ *
        ‖xi‖ ^ k / ((k.factorial : ℝ) ^ 2) := by
  simp [xiHeatCassiniWoldResidualBorelAtom, norm_pow]

/-- Central-binomial control in the exact factorial form needed by the order-two Borel carrier. -/
theorem factorial_two_mul_le_four_pow_mul_factorial_sq (k : ℕ) :
    ((2 * k).factorial : ℝ) ≤
      (4 : ℝ) ^ k * ((k.factorial : ℝ) ^ 2) := by
  have hid : (Nat.centralBinom k) * (k.factorial * k.factorial) =
      (2 * k).factorial := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have h := Nat.choose_mul_factorial_mul_factorial
      (Nat.le_mul_of_pos_left k (by omega : 0 < 2))
    have hsub : 2 * k - k = k := by omega
    simpa [hsub, mul_assoc] using h
  have hle : Nat.centralBinom k ≤ 4 ^ k := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    calc
      (2 * k).choose k ≤ 2 ^ (2 * k) := Nat.choose_le_two_pow _ _
      _ = 4 ^ k := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hnat : (2 * k).factorial ≤ 4 ^ k * (k.factorial * k.factorial) := by
    rw [← hid]
    exact Nat.mul_le_mul_right _ hle
  simpa [pow_two] using (by exact_mod_cast hnat :
    ((2 * k).factorial : ℝ) ≤
      (4 : ℝ) ^ k * ((k.factorial : ℝ) * (k.factorial : ℝ)))

/-- Square-root exponential decay absorbs a degree-`k` height moment with `(2k)!` cost. -/
theorem pow_mul_exp_neg_sqrt_le_even_factorial
    {c h : ℝ} (hc : 0 < c) (hh : 0 ≤ h) (k : ℕ) :
    h ^ k * Real.exp (-((c / 2) * Real.sqrt h)) ≤
      ((2 * k).factorial : ℝ) / (c / 2) ^ (2 * k) := by
  have hsqrt : 0 ≤ Real.sqrt h := Real.sqrt_nonneg _
  have hbase := Real.pow_div_factorial_le_exp
    ((c / 2) * Real.sqrt h) (mul_nonneg (by positivity) hsqrt) (2 * k)
  have hfac : 0 < ((2 * k).factorial : ℝ) := by positivity
  have hcpow : 0 < (c / 2) ^ (2 * k) := pow_pos (by positivity) _
  rw [div_le_iff₀ hfac] at hbase
  have hmul := mul_le_mul_of_nonneg_right hbase
    (Real.exp_nonneg (-((c / 2) * Real.sqrt h)))
  have hsqrtpow : (Real.sqrt h) ^ (2 * k) = h ^ k := by
    rw [pow_mul, Real.sq_sqrt hh]
  apply (le_div_iff₀ hcpow).2
  calc
    (h ^ k * Real.exp (-((c / 2) * Real.sqrt h))) * (c / 2) ^ (2 * k) =
        (c / 2) ^ (2 * k) * (Real.sqrt h) ^ (2 * k) *
          Real.exp (-((c / 2) * Real.sqrt h)) := by rw [hsqrtpow]; ring
    _ = (((c / 2) * Real.sqrt h) ^ (2 * k)) *
          Real.exp (-((c / 2) * Real.sqrt h)) := by rw [mul_pow]
    _ ≤ (Real.exp ((c / 2) * Real.sqrt h) * ((2 * k).factorial : ℝ)) *
          Real.exp (-((c / 2) * Real.sqrt h)) := hmul
    _ = ((2 * k).factorial : ℝ) := by
      rw [mul_comm (Real.exp _) _, mul_assoc, ← Real.exp_add]
      ring_nf
      simp

private theorem heightMoment_secondFactorial_le_geometric
    {c h H t : ℝ} (hc : 0 < c) (hh : 0 ≤ h) (hH : 0 ≤ H)
    (hHle : H ≤ 2 * h) (ht : 0 ≤ t) (k : ℕ) :
    Real.exp (-((c / 2) * Real.sqrt h)) * H ^ k * t ^ k /
        ((k.factorial : ℝ) ^ 2) ≤
      (32 * t / c ^ 2) ^ k := by
  have hHpow : H ^ k ≤ (2 : ℝ) ^ k * h ^ k := by
    calc
      H ^ k ≤ (2 * h) ^ k := pow_le_pow_left₀ hH hHle k
      _ = (2 : ℝ) ^ k * h ^ k := by rw [mul_pow]
  have hmom := pow_mul_exp_neg_sqrt_le_even_factorial hc hh k
  have hfac := factorial_two_mul_le_four_pow_mul_factorial_sq k
  have hkfac : 0 < ((k.factorial : ℝ) ^ 2) := by positivity
  have hcpow : 0 < (c / 2) ^ (2 * k) := pow_pos (by positivity) _
  have hratio :
      ((2 * k).factorial : ℝ) / ((k.factorial : ℝ) ^ 2) ≤ (4 : ℝ) ^ k := by
    exact (div_le_iff₀ hkfac).2 (by simpa [mul_comm] using hfac)
  calc
    Real.exp (-((c / 2) * Real.sqrt h)) * H ^ k * t ^ k /
        ((k.factorial : ℝ) ^ 2) ≤
      Real.exp (-((c / 2) * Real.sqrt h)) *
          ((2 : ℝ) ^ k * h ^ k) * t ^ k /
            ((k.factorial : ℝ) ^ 2) := by gcongr
    _ = (2 : ℝ) ^ k * t ^ k *
          (h ^ k * Real.exp (-((c / 2) * Real.sqrt h))) /
            ((k.factorial : ℝ) ^ 2) := by ring
    _ ≤ (2 : ℝ) ^ k * t ^ k *
          (((2 * k).factorial : ℝ) / (c / 2) ^ (2 * k)) /
            ((k.factorial : ℝ) ^ 2) := by gcongr
    _ = ((2 : ℝ) ^ k * t ^ k / (c / 2) ^ (2 * k)) *
          (((2 * k).factorial : ℝ) / ((k.factorial : ℝ) ^ 2)) := by ring
    _ ≤ ((2 : ℝ) ^ k * t ^ k / (c / 2) ^ (2 * k)) * (4 : ℝ) ^ k := by
      gcongr
    _ = ((2 * t) ^ k / ((c / 2) ^ 2) ^ k) * (4 : ℝ) ^ k := by
      rw [show (c / 2) ^ (2 * k) = ((c / 2) ^ 2) ^ k by rw [pow_mul], mul_pow]
    _ = (((2 * t) / (c / 2) ^ 2) ^ k) * (4 : ℝ) ^ k := by
      congr 1
      exact (div_pow _ _ _).symm
    _ = (((2 * t) / (c / 2) ^ 2) * 4) ^ k :=
      (mul_pow _ _ _).symm
    _ = (32 * t / c ^ 2) ^ k := by
      congr 1
      field_simp [hc.ne']
      ring

private theorem succ_div_factorial_succ_sq_le_inv_factorial_sq (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) / ((((k + 1).factorial : ℕ) : ℝ) ^ 2) ≤
      1 / ((k.factorial : ℝ) ^ 2) := by
  rw [Nat.factorial_succ]
  push_cast
  rw [div_le_div_iff₀ (by positivity :
      0 < ((((k : ℝ) + 1) * (k.factorial : ℝ)) ^ 2))
    (by positivity : 0 < ((k.factorial : ℝ) ^ 2))]
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hsq : (k : ℝ) + 1 ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) := by
    nlinarith [show 0 ≤ (k : ℝ) by positivity]
  calc
    ((k : ℝ) + 1) * ((k.factorial : ℝ) ^ 2) ≤
        ((k : ℝ) + 1) * ((k : ℝ) + 1) * ((k.factorial : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = 1 * ((((k : ℝ) + 1) * (k.factorial : ℝ)) ^ 2) := by ring

private theorem derivativeHeightMoment_secondFactorial_le_geometric
    {c h H t : ℝ} (hc : 0 < c) (hh : 0 ≤ h) (hH : 0 ≤ H)
    (hHle : H ≤ 2 * h) (ht : 0 ≤ t) (k : ℕ) :
    Real.exp (-((c / 2) * Real.sqrt h)) * ((k + 1 : ℕ) : ℝ) * H ^ k *
        t ^ (k + 1) / ((((k + 1).factorial : ℕ) : ℝ) ^ 2) ≤
      t * (32 * t / c ^ 2) ^ k := by
  have hnorm := succ_div_factorial_succ_sq_le_inv_factorial_sq k
  have hheight := heightMoment_secondFactorial_le_geometric
    hc hh hH hHle ht k
  have hbase : 0 ≤
      Real.exp (-((c / 2) * Real.sqrt h)) * H ^ k * t ^ k := by positivity
  calc
    Real.exp (-((c / 2) * Real.sqrt h)) * ((k + 1 : ℕ) : ℝ) * H ^ k *
        t ^ (k + 1) / ((((k + 1).factorial : ℕ) : ℝ) ^ 2) =
      (Real.exp (-((c / 2) * Real.sqrt h)) * H ^ k * t ^ k) *
        (t * (((k + 1 : ℕ) : ℝ) /
          ((((k + 1).factorial : ℕ) : ℝ) ^ 2))) := by
      rw [pow_succ]
      ring
    _ ≤ (Real.exp (-((c / 2) * Real.sqrt h)) * H ^ k * t ^ k) *
        (t * (1 / ((k.factorial : ℝ) ^ 2))) := by gcongr
    _ = t * (Real.exp (-((c / 2) * Real.sqrt h)) * H ^ k * t ^ k /
        ((k.factorial : ℝ) ^ 2)) := by ring
    _ ≤ t * (32 * t / c ^ 2) ^ k :=
      mul_le_mul_of_nonneg_left hheight ht

private theorem norm_xiHeatCassiniWoldResidualBorelAtom_le_majorant
    {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hres : ∀ N : ℕ,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        C * Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)))
    (x : ℝ) (xi : ℂ) (N k : ℕ) :
    ‖xiHeatCassiniWoldResidualBorelAtom x xi (N, k)‖ ≤
      C *
        (Real.exp (-(c / 2) * Real.sqrt (xiMassNthPrimeLogHeight N)) *
          xiHeatCassiniOrderedPrimeLogGap N) *
        (|x| * (32 * ‖xi‖ / c ^ 2) ^ k +
          ‖xi‖ * (32 * ‖xi‖ / c ^ 2) ^ (k - 1)) := by
  let h : ℝ := xiMassNthPrimeLogHeight N
  let H : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let d : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let t : ℝ := ‖xi‖
  let q : ℝ := 32 * t / c ^ 2
  have hh : 0 ≤ h := (xiMassNthPrimeLogHeight_pos N).le
  have hH : 0 ≤ H := (xiMassNthPrimeLogHeight_pos (N + 1)).le
  have hHle : H ≤ 2 * h := by
    simpa only [h, H] using xiMassNthPrimeLogHeight_succ_le_two_mul N
  have hd : 0 ≤ d := by
    simpa only [d] using xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hq : 0 ≤ q := by
    dsimp only [q]
    exact div_nonneg (mul_nonneg (by norm_num) ht) (sq_nonneg _)
  have hjet :
      ‖xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x N‖ ≤
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| * d *
          (H ^ k * |x| + (k : ℝ) * H ^ (k - 1)) := by
    simpa only [d, H] using
      norm_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom_le k x N
  have hresN :
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        C * Real.exp (-c * Real.sqrt h) := by simpa only [h] using hres N
  have hexpsplit : Real.exp (-c * Real.sqrt h) =
      Real.exp (-(c / 2) * Real.sqrt h) *
        Real.exp (-(c / 2) * Real.sqrt h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfirst :
      Real.exp (-(c / 2) * Real.sqrt h) * H ^ k * t ^ k /
          ((k.factorial : ℝ) ^ 2) ≤ q ^ k := by
    dsimp only [q]
    convert heightMoment_secondFactorial_le_geometric hc hh hH hHle ht k using 1
    all_goals ring_nf
  have hsecond :
      Real.exp (-(c / 2) * Real.sqrt h) * (k : ℝ) * H ^ (k - 1) * t ^ k /
          ((k.factorial : ℝ) ^ 2) ≤ t * q ^ (k - 1) := by
    cases k with
    | zero => simpa using ht
    | succ j =>
        dsimp only [q]
        convert derivativeHeightMoment_secondFactorial_le_geometric hc hh hH hHle ht j using 1
        all_goals simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
        all_goals ring_nf
  have hinner :
      |x| * (Real.exp (-(c / 2) * Real.sqrt h) * H ^ k * t ^ k /
          ((k.factorial : ℝ) ^ 2)) +
        (Real.exp (-(c / 2) * Real.sqrt h) * (k : ℝ) * H ^ (k - 1) * t ^ k /
          ((k.factorial : ℝ) ^ 2)) ≤
      |x| * q ^ k + t * q ^ (k - 1) :=
    add_le_add (mul_le_mul_of_nonneg_left hfirst (abs_nonneg x)) hsecond
  rw [norm_xiHeatCassiniWoldResidualBorelAtom]
  calc
    ‖xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x N‖ * t ^ k /
        ((k.factorial : ℝ) ^ 2) ≤
      (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| * d *
        (H ^ k * |x| + (k : ℝ) * H ^ (k - 1))) * t ^ k /
          ((k.factorial : ℝ) ^ 2) := by gcongr
    _ ≤ (C * Real.exp (-c * Real.sqrt h) * d *
        (H ^ k * |x| + (k : ℝ) * H ^ (k - 1))) * t ^ k /
          ((k.factorial : ℝ) ^ 2) := by gcongr
    _ = C * (Real.exp (-(c / 2) * Real.sqrt h) * d) *
        (|x| * (Real.exp (-(c / 2) * Real.sqrt h) * H ^ k * t ^ k /
            ((k.factorial : ℝ) ^ 2)) +
          (Real.exp (-(c / 2) * Real.sqrt h) * (k : ℝ) * H ^ (k - 1) * t ^ k /
            ((k.factorial : ℝ) ^ 2))) := by rw [hexpsplit]; ring
    _ ≤ C * (Real.exp (-(c / 2) * Real.sqrt h) * d) *
        (|x| * q ^ k + t * q ^ (k - 1)) := by
      exact mul_le_mul_of_nonneg_left hinner
        (mul_nonneg hC (mul_nonneg (Real.exp_nonneg _) hd))
    _ = C *
        (Real.exp (-(c / 2) * Real.sqrt (xiMassNthPrimeLogHeight N)) *
          xiHeatCassiniOrderedPrimeLogGap N) *
        (|x| * (32 * ‖xi‖ / c ^ 2) ^ k +
          ‖xi‖ * (32 * ‖xi‖ / c ^ 2) ^ (k - 1)) := by
      rfl

/-- The source-marked two-index Borel family is normally summable on one nontrivial disc whose
radius is independent of the real boundary coordinate. -/
theorem exists_radius_summable_norm_xiHeatCassiniWoldResidualBorelAtom :
    ∃ r : ℝ, 0 < r ∧ ∀ (x : ℝ) (xi : ℂ), ‖xi‖ < r →
      Summable (fun p : ℕ × ℕ =>
        ‖xiHeatCassiniWoldResidualBorelAtom x xi p‖) := by
  obtain ⟨C, c, hc, hC, hres⟩ :=
    exists_global_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_sqrt_rate
  refine ⟨c ^ 2 / 64, by positivity, ?_⟩
  intro x xi hxi
  let t : ℝ := ‖xi‖
  let q : ℝ := 32 * t / c ^ 2
  let f : ℕ → ℝ := fun N =>
    C * (Real.exp (-(c / 2) * Real.sqrt (xiMassNthPrimeLogHeight N)) *
      xiHeatCassiniOrderedPrimeLogGap N)
  let g : ℕ → ℝ := fun k => |x| * q ^ k + t * q ^ (k - 1)
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hq : 0 ≤ q := by
    dsimp only [q]
    exact div_nonneg (mul_nonneg (by norm_num) ht) hc2.le
  have ht64 : 64 * t < c ^ 2 := by
    have := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mp (by simpa only [t] using hxi)
    nlinarith
  have hqOne : q < 1 := by
    rw [show q = 32 * t / c ^ 2 by rfl, div_lt_iff₀ hc2]
    nlinarith
  have hgeom : Summable (fun k : ℕ => q ^ k) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hqOne
  have hpred : Summable (fun k : ℕ => q ^ (k - 1)) := by
    apply (summable_nat_add_iff 1).1
    simpa only [Nat.add_sub_cancel] using hgeom
  have hg : Summable g := by
    exact ((hgeom.mul_left |x|).add (hpred.mul_left t)).congr (fun k => by rfl)
  have hbase : Summable (fun N : ℕ =>
      Real.exp (-(c / 2) * Real.sqrt (xiMassNthPrimeLogHeight N)) *
        xiHeatCassiniOrderedPrimeLogGap N) :=
    summable_exp_neg_sqrt_primeLog_mul_successorGap (by linarith : 0 < c / 2)
  have hf : Summable f := by
    exact (hbase.mul_left C).congr (fun N => by rfl)
  have hmajor : Summable (fun p : ℕ × ℕ => f p.1 * g p.2) :=
    summable_mul_of_summable_norm hf.norm hg.norm
  exact Summable.of_nonneg_of_le (fun p => norm_nonneg _)
    (fun p => by
      simpa only [f, g, t, q] using
        norm_xiHeatCassiniWoldResidualBorelAtom_le_majorant hc hC hres x xi p.1 p.2)
    hmajor

/-- Complex-valued source-marked Borel family is absolutely summable on the same disc. -/
theorem exists_radius_summable_xiHeatCassiniWoldResidualBorelAtom :
    ∃ r : ℝ, 0 < r ∧ ∀ (x : ℝ) (xi : ℂ), ‖xi‖ < r →
      Summable (xiHeatCassiniWoldResidualBorelAtom x xi) := by
  obtain ⟨r, hr, hsum⟩ :=
    exists_radius_summable_norm_xiHeatCassiniWoldResidualBorelAtom
  exact ⟨r, hr, fun x xi hxi => (hsum x xi hxi).of_norm⟩

/-- Source-marked order-two Borel carrier. -/
def xiHeatCassiniWoldResidualBorelCarrier (x : ℝ) (xi : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, xiHeatCassiniWoldResidualBorelAtom x xi p

/-- The fixed-order source fibre is exactly the corresponding residual jet with one additional
factorial normalization. -/
theorem tsum_xiHeatCassiniWoldResidualBorelAtom_fixedOrder
    (x : ℝ) (xi : ℂ) (k : ℕ) :
    (∑' N : ℕ, xiHeatCassiniWoldResidualBorelAtom x xi (N, k)) =
      xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel k x * xi ^ k /
        ((k.factorial : ℂ) ^ 2) := by
  calc
    (∑' N : ℕ, xiHeatCassiniWoldResidualBorelAtom x xi (N, k)) =
        ∑' N : ℕ,
          xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x N *
            (xi ^ k / ((k.factorial : ℂ) ^ 2)) := by
      apply tsum_congr
      intro N
      simp only [xiHeatCassiniWoldResidualBorelAtom]
      ring
    _ = (∑' N : ℕ,
          xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom k x N) *
            (xi ^ k / ((k.factorial : ℂ) ^ 2)) := tsum_mul_right
    _ = xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel k x * xi ^ k /
          ((k.factorial : ℂ) ^ 2) := by
      rw [xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel]
      ring

/-- Inside one source-independent disc, the source-marked double series regroups exactly as the
second-factorial Borel series of the complete residual jet. -/
theorem exists_radius_xiHeatCassiniWoldResidualBorelCarrier_eq_jetSeries :
    ∃ r : ℝ, 0 < r ∧ ∀ (x : ℝ) (xi : ℂ), ‖xi‖ < r →
      xiHeatCassiniWoldResidualBorelCarrier x xi =
        ∑' k : ℕ,
          xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel k x * xi ^ k /
            ((k.factorial : ℂ) ^ 2) := by
  obtain ⟨r, hr, hsum⟩ :=
    exists_radius_summable_xiHeatCassiniWoldResidualBorelAtom
  refine ⟨r, hr, fun x xi hxi => ?_⟩
  have hs := hsum x xi hxi
  have hs' : Summable (Function.uncurry (fun N k : ℕ =>
      xiHeatCassiniWoldResidualBorelAtom x xi (N, k))) := by
    exact hs.congr (fun p => by rcases p with ⟨N, k⟩; rfl)
  calc
    xiHeatCassiniWoldResidualBorelCarrier x xi =
        ∑' N : ℕ, ∑' k : ℕ,
          xiHeatCassiniWoldResidualBorelAtom x xi (N, k) := by
      rw [xiHeatCassiniWoldResidualBorelCarrier, hs.tsum_prod]
    _ = ∑' k : ℕ, ∑' N : ℕ,
          xiHeatCassiniWoldResidualBorelAtom x xi (N, k) := by
      exact hs'.tsum_comm.symm
    _ = ∑' k : ℕ,
          xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetKernel k x * xi ^ k /
            ((k.factorial : ℂ) ^ 2) := by
      apply tsum_congr
      exact tsum_xiHeatCassiniWoldResidualBorelAtom_fixedOrder x xi

/-- The normally convergent source-marked carrier is holomorphic on a nontrivial disc, uniformly
in the choice of real boundary coordinate. -/
theorem exists_radius_differentiableOn_xiHeatCassiniWoldResidualBorelCarrier :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ,
      DifferentiableOn ℂ (xiHeatCassiniWoldResidualBorelCarrier x) (Metric.ball 0 r) := by
  obtain ⟨r, hr, hsum⟩ :=
    exists_radius_summable_norm_xiHeatCassiniWoldResidualBorelAtom
  refine ⟨r, hr, fun x z hz => ?_⟩
  have hzNorm : ‖z‖ < r := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  let rho : ℝ := (‖z‖ + r) / 2
  let R : ℝ := rho - ‖z‖
  have hrhoPos : 0 < rho := by dsimp only [rho]; positivity
  have hrho : rho < r := by dsimp only [rho]; linarith
  have hR : 0 < R := by dsimp only [R, rho]; linarith
  have hsumRho : Summable (fun p : ℕ × ℕ =>
      ‖xiHeatCassiniWoldResidualBorelAtom x (rho : ℂ) p‖) := by
    apply hsum x (rho : ℂ)
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrhoPos] using hrho
  have hdiff : ∀ p : ℕ × ℕ,
      DifferentiableOn ℂ (fun w : ℂ => xiHeatCassiniWoldResidualBorelAtom x w p)
        (Metric.ball z R) := by
    intro p
    unfold xiHeatCassiniWoldResidualBorelAtom
    fun_prop
  have hbound : ∀ p : ℕ × ℕ, ∀ w ∈ Metric.ball z R,
      ‖xiHeatCassiniWoldResidualBorelAtom x w p‖ ≤
        ‖xiHeatCassiniWoldResidualBorelAtom x (rho : ℂ) p‖ := by
    intro p w hw
    have hdist : ‖w - z‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hwNorm : ‖w‖ < rho := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ < R + ‖z‖ := by linarith
        _ = rho := by dsimp only [R]; ring
    rw [norm_xiHeatCassiniWoldResidualBorelAtom,
      norm_xiHeatCassiniWoldResidualBorelAtom]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrhoPos]
    gcongr
  have hdiffAt :=
    GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated
      hR hdiff hbound hsumRho
  change DifferentiableWithinAt ℂ
    (fun w : ℂ => ∑' p : ℕ × ℕ, xiHeatCassiniWoldResidualBorelAtom x w p)
      (Metric.ball 0 r) z
  exact hdiffAt.differentiableWithinAt

end

end RHTower

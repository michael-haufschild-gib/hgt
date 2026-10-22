import GaloisForLFunctions.RHTower.Suzuki.SuzukiCurvatureJordanAbscissaRigidity
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSelbergRemainderBridge
import GaloisForLFunctions.RHTower.MertensSecondTheorem

/-!
# Critical ordered cancellation of Suzuki curvature

The exact half-order-damped signed Suzuki curvature converges in its canonical checkpoint order,
although neither Jordan sector has finite mass.  The finite value is forced by Mertens' second
theorem: the smooth polar contribution supplies the harmonic logarithm, the prime atoms supply the
von-Mangoldt logarithm, and the exact Gamma-cell discrepancy is absolutely summable.

Thus scalar critical convergence is unconditional and cannot be the RH-bearing step in CCM-FU.
The remaining burden is uniform affine checkpoint cancellation before scalarization.
-/

noncomputable section

namespace RHTower

open Filter Topology ArithmeticFunction

/-- Absolutely summable Gamma correction in the critical ordered curvature series.  Index `n`
corresponds to endpoint `k = n + 3`, the first source-valid checkpoint cell. -/
def suzukiCheckpointCriticalArchCorrection (n : ℕ) : ℝ :=
  suzukiCheckpointCurvaturePowerDamping (1 / 2 : ℝ) (n + 2) *
    suzukiCheckpointSelbergArchRemainderCell (n + 3)

/-- Critical signed-curvature term in canonical checkpoint order, starting with cell `N = 2`. -/
def suzukiCheckpointCriticalOrderedTerm (n : ℕ) : ℝ :=
  suzukiCheckpointCurvaturePowerDamping (1 / 2 : ℝ) (n + 2) *
    suzukiCheckpointSignedCurvatureCell (n + 2)

/-- Natural-order critical signed-curvature prefix over the first `N` source-valid cells. -/
def suzukiCheckpointCriticalOrderedPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, suzukiCheckpointCriticalOrderedTerm n

/-- Canonical Mertens--Gamma finite part of critical Suzuki curvature. -/
def suzukiCheckpointCriticalOrderedLimit : ℝ :=
  (∑' n : ℕ, suzukiCheckpointCriticalArchCorrection n) +
    2 * Real.eulerMascheroniConstant - 3 / 2 + Real.log 2 / 2

/-- The exact Gamma correction gains a full extra power after critical damping. -/
theorem abs_suzukiCheckpointCriticalArchCorrection_le (n : ℕ) :
    |suzukiCheckpointCriticalArchCorrection n| ≤
      (5 / 3 : ℝ) * (((n + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let k := n + 3
  let x : ℝ := k
  let a := Real.sqrt ((k - 1 : ℕ) : ℝ)
  let b := Real.sqrt (k : ℝ)
  have hk : 3 ≤ k := by dsimp [k]; omega
  have hx : 0 < x := by dsimp [x]; positivity
  have hpred : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have ha : 0 < a := Real.sqrt_pos.mpr hpred
  have hb : 0 < b := Real.sqrt_pos.mpr (by simpa [x] using hx)
  have ha2 : a ^ 2 = ((k - 1 : ℕ) : ℝ) := Real.sq_sqrt hpred.le
  have ha1 : 1 ≤ a := by
    have hpred1 : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ k - 1)
    nlinarith [sq_nonneg (a - 1)]
  have hainv : a⁻¹ ≤ 1 := (inv_le_one₀ ha).2 ha1
  let A := suzukiCheckpointSelbergArchRemainderCell k
  have hsource := abs_weighted_suzukiCheckpointSelbergArchRemainderCell_le hk
  have hxA : x * |A| ≤ 5 / 3 := by
    have hrewrite : |(k : ℝ) * A| = x * |A| := by
      rw [abs_mul, abs_of_pos (by simpa [x] using hx)]
    rw [hrewrite] at hsource
    have hconst : (5 / 3 : ℝ) * a⁻¹ ≤ 5 / 3 := by nlinarith
    exact hsource.trans (by simpa [a] using hconst)
  have hpow : x ^ (-(3 / 2 : ℝ)) = (x * b)⁻¹ := by
    rw [Real.rpow_neg hx.le]
    have hpospow : x ^ (3 / 2 : ℝ) = x * b := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hx,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [hpospow]
  have hmain : b⁻¹ * |A| ≤ (5 / 3 : ℝ) * (x * b)⁻¹ := by
    rw [show b⁻¹ * |A| = |A| / b by ring,
      show (5 / 3 : ℝ) * (x * b)⁻¹ = (5 / 3 : ℝ) / (x * b) by ring,
      div_le_div_iff₀ hb (mul_pos hx hb)]
    have hm := mul_le_mul_of_nonneg_right hxA hb.le
    nlinarith
  unfold suzukiCheckpointCriticalArchCorrection suzukiCheckpointCurvaturePowerDamping
  have hkindex : n + 2 + 1 = k := by omega
  rw [hkindex]
  change |(x ^ (-(1 / 2 : ℝ))) * A| ≤ _
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  change |b⁻¹ * A| ≤ _
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hb.le), hpow]
  simpa [k, x, A] using hmain

/-- The source-free critical Gamma correction is absolutely summable. -/
theorem summable_suzukiCheckpointCriticalArchCorrection :
    Summable suzukiCheckpointCriticalArchCorrection := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ =>
      (((n + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    (summable_nat_add_iff 3).2 hbase
  have hmajor : Summable (fun n : ℕ =>
      (5 / 3 : ℝ) * (((n + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    Summable.mul_left _ hshift
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun n => abs_nonneg _)
    abs_suzukiCheckpointCriticalArchCorrection_le hmajor)

/-- Cellwise critical decomposition: summable Gamma defect plus harmonic mass minus Mertens mass. -/
theorem suzukiCheckpointCriticalOrderedTerm_eq (n : ℕ) :
    suzukiCheckpointCriticalOrderedTerm n =
      suzukiCheckpointCriticalArchCorrection n + 1 / ((n + 3 : ℕ) : ℝ) -
        vonMangoldt (n + 3) / ((n + 3 : ℕ) : ℝ) := by
  let k := n + 3
  let x : ℝ := k
  let b := Real.sqrt (k : ℝ)
  have hx : 0 < x := by dsimp [x, k]; positivity
  have hb : 0 < b := Real.sqrt_pos.mpr (by simpa [x] using hx)
  have hkindex : n + 2 + 1 = k := by omega
  have hkpred : n + 2 = k - 1 := by omega
  unfold suzukiCheckpointCriticalOrderedTerm suzukiCheckpointCriticalArchCorrection
    suzukiCheckpointCurvaturePowerDamping
  rw [hkindex]
  unfold suzukiCheckpointSignedCurvatureCell suzukiCheckpointSelbergArchRemainderCell
  rw [hkindex, criticalMellinAtomWeight_eq_div_sqrt, hkpred]
  change x ^ (-(1 / 2 : ℝ)) * (_ - vonMangoldt k / b) =
    x ^ (-(1 / 2 : ℝ)) * (_ - 1 / b) + 1 / x - vonMangoldt k / x
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  change b⁻¹ * (_ - vonMangoldt k / b) =
    b⁻¹ * (_ - 1 / b) + 1 / x - vonMangoldt k / x
  have hb2 : b ^ 2 = x := by
    dsimp [b, x]
    exact Real.sq_sqrt (by positivity)
  field_simp [hb.ne', hx.ne']
  rw [← hb2]
  ring

private theorem sum_range_add_three_eq_sum_Icc_sub
    {M : Type*} [AddCommGroup M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.range N, f (n + 3) =
      (∑ k ∈ Finset.Icc 1 (N + 2), f k) - ∑ k ∈ Finset.Icc 1 2, f k := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      change ((∑ k ∈ Finset.Icc 1 (N + 2), f k) -
          ∑ k ∈ Finset.Icc 1 2, f k) + f (N + 3) =
        (∑ k ∈ Finset.Icc 1 (N + 3), f k) - ∑ k ∈ Finset.Icc 1 2, f k
      have htop : (∑ k ∈ Finset.Icc 1 (N + 3), f k) =
          (∑ k ∈ Finset.Icc 1 (N + 2), f k) + f (N + 3) := by
        simpa only [show N + 3 = (N + 2) + 1 by omega] using
          (Finset.sum_Icc_succ_top (a := 1) (b := N + 2) (by omega) f)
      rw [htop]
      abel

/-- Exact centered finite-prefix law.  No infinite prime/archimedean separation occurs. -/
theorem suzukiCheckpointCriticalOrderedPrefix_eq_centered (N : ℕ) :
    suzukiCheckpointCriticalOrderedPrefix N =
      (∑ n ∈ Finset.range N, suzukiCheckpointCriticalArchCorrection n) +
        ((harmonic (N + 2) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ)) -
        ((∑ k ∈ Finset.Icc 1 (N + 2), vonMangoldt k / (k : ℝ)) -
          Real.log ((N + 2 : ℕ) : ℝ)) -
        (harmonic 2 : ℝ) + ∑ k ∈ Finset.Icc 1 2, vonMangoldt k / (k : ℝ) := by
  rw [suzukiCheckpointCriticalOrderedPrefix]
  conv_lhs =>
    enter [2, n]
    rw [suzukiCheckpointCriticalOrderedTerm_eq]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hH := sum_range_add_three_eq_sum_Icc_sub
    (fun k : ℕ => 1 / (k : ℝ)) N
  rw [← harmonic_eq_sum_Icc (N + 2), ← harmonic_eq_sum_Icc 2] at hH
  have hM := sum_range_add_three_eq_sum_Icc_sub
    (fun k : ℕ => vonMangoldt k / (k : ℝ)) N
  rw [hH, hM]
  ring

private theorem sum_vonMangoldt_div_Icc_one_two :
    (∑ k ∈ Finset.Icc 1 2, vonMangoldt k / (k : ℝ)) = Real.log 2 / 2 := by
  rw [show 2 = 1 + 1 by omega,
    Finset.sum_Icc_succ_top (a := 1) (b := 1) (by omega)
      (fun k : ℕ => vonMangoldt k / (k : ℝ))]
  norm_num [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- **Critical ordered cancellation.**  Natural checkpoint prefixes converge unconditionally to
the explicit Mertens--Gamma finite part. -/
theorem tendsto_suzukiCheckpointCriticalOrderedPrefix :
    Tendsto suzukiCheckpointCriticalOrderedPrefix atTop
      (nhds suzukiCheckpointCriticalOrderedLimit) := by
  have hshift : Tendsto (fun N : ℕ => N + 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hcorr : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N, suzukiCheckpointCriticalArchCorrection n) atTop
      (nhds (∑' n : ℕ, suzukiCheckpointCriticalArchCorrection n)) :=
    summable_suzukiCheckpointCriticalArchCorrection.hasSum.tendsto_sum_nat
  have hharm : Tendsto (fun N : ℕ =>
      (harmonic (N + 2) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ)) atTop
      (nhds Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp hshift
  have hmertens : Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.Icc 1 (N + 2), vonMangoldt k / (k : ℝ)) -
        Real.log ((N + 2 : ℕ) : ℝ)) atTop
      (nhds (-Real.eulerMascheroniConstant)) :=
    tendsto_sum_vonMangoldt_div_sub_log.comp hshift
  have h := (((hcorr.add hharm).sub hmertens).sub_const (harmonic 2 : ℝ)).add_const
    (∑ k ∈ Finset.Icc 1 2, vonMangoldt k / (k : ℝ))
  rw [sum_vonMangoldt_div_Icc_one_two] at h
  have hH2 : (harmonic 2 : ℝ) = 3 / 2 := by norm_num [harmonic]
  rw [hH2, show (∑' n : ℕ, suzukiCheckpointCriticalArchCorrection n) +
      Real.eulerMascheroniConstant - -Real.eulerMascheroniConstant - 3 / 2 +
      Real.log 2 / 2 = suzukiCheckpointCriticalOrderedLimit by
        unfold suzukiCheckpointCriticalOrderedLimit
        ring] at h
  exact h.congr fun N => by
    have hcenter := suzukiCheckpointCriticalOrderedPrefix_eq_centered N
    rw [hH2, sum_vonMangoldt_div_Icc_one_two] at hcenter
    exact hcenter.symm

/-- Critical signed curvature is not unconditionally summable. -/
theorem not_summable_suzukiCheckpointCriticalSignedCurvature :
    ¬ Summable (fun N : ℕ =>
      suzukiCheckpointCurvaturePowerDamping (1 / 2 : ℝ) N *
        suzukiCheckpointSignedCurvatureCell N) := by
  intro hs
  have habs := hs.abs
  have hpos : Summable (fun N : ℕ =>
      suzukiCheckpointCurvaturePowerDamping (1 / 2 : ℝ) N *
        suzukiCheckpointSignedCurvaturePositiveMass N) := by
    apply Summable.of_nonneg_of_le
    · intro N
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_max_right _ _)
    · intro N
      have hw : 0 ≤ suzukiCheckpointCurvaturePowerDamping (1 / 2 : ℝ) N :=
        Real.rpow_nonneg (by positivity) _
      calc
        suzukiCheckpointCurvaturePowerDamping (1 / 2 : ℝ) N *
            suzukiCheckpointSignedCurvaturePositiveMass N ≤
          suzukiCheckpointCurvaturePowerDamping (1 / 2 : ℝ) N *
            |suzukiCheckpointSignedCurvatureCell N| := by
              apply mul_le_mul_of_nonneg_left _ hw
              unfold suzukiCheckpointSignedCurvaturePositiveMass
              exact max_le (le_abs_self _) (abs_nonneg _)
        _ = |suzukiCheckpointCurvaturePowerDamping (1 / 2 : ℝ) N *
            suzukiCheckpointSignedCurvatureCell N| := by
              rw [abs_mul, abs_of_nonneg hw]
    · exact habs
  exact not_summable_suzukiCheckpointSignedCurvaturePositiveMass_powerDamping_of_le_half
    (le_rfl : (1 / 2 : ℝ) ≤ 1 / 2) hpos

/-- The canonical tail converges in order but not as an unconditional Lean `Summable` family. -/
theorem not_summable_suzukiCheckpointCriticalOrderedTerm :
    ¬ Summable suzukiCheckpointCriticalOrderedTerm := by
  intro hs
  apply not_summable_suzukiCheckpointCriticalSignedCurvature
  apply (summable_nat_add_iff 2).1
  exact hs.congr fun n => by
    simp only [suzukiCheckpointCriticalOrderedTerm]

/-- **Closed route-class no-go.**  Critical scalar checkpoint convergence is unconditional while
the signed family and both Jordan sectors remain non-summable.  Hence scalar convergence alone
cannot discharge the RH-bearing CCM-FU affine-current premise. -/
theorem suzukiCheckpointCriticalOrderedJordanCancellation :
    Tendsto suzukiCheckpointCriticalOrderedPrefix atTop
        (nhds suzukiCheckpointCriticalOrderedLimit) ∧
      ¬ Summable suzukiCheckpointCriticalOrderedTerm ∧
      ¬ Summable (fun N : ℕ =>
        suzukiCheckpointCurvaturePowerDamping (1 / 2 : ℝ) N *
          suzukiCheckpointSignedCurvaturePositiveMass N) ∧
      ¬ Summable (fun N : ℕ =>
        suzukiCheckpointCurvaturePowerDamping (1 / 2 : ℝ) N *
          suzukiCheckpointSignedCurvatureNegativeMass N) := by
  exact ⟨tendsto_suzukiCheckpointCriticalOrderedPrefix,
    not_summable_suzukiCheckpointCriticalOrderedTerm,
    not_summable_suzukiCheckpointSignedCurvaturePositiveMass_powerDamping_of_le_half
      (le_rfl : (1 / 2 : ℝ) ≤ 1 / 2),
    not_summable_suzukiCheckpointSignedCurvatureNegativeMass_powerDamping_of_le_half
      (le_rfl : (1 / 2 : ℝ) ≤ 1 / 2)⟩

end RHTower

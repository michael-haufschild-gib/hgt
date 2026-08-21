import GaloisForLFunctions.RHTower.CCMFUSuzukiPrimePowerSignClassification
import GaloisForLFunctions.RHTower.PsiRemainderSignChange

/-!
# Suzuki prime--polar--Gamma curvature as a Selberg-remainder current

The literal completed Suzuki cell is the negative critical half-density finite difference of
Selberg's discrete PNT remainder, up to one source-free Gamma cell.  The event-weighted prefix of
that Gamma correction is only `O(sqrt N)`.  Thus normalized Suzuki curvature and the normalized
weighted remainder-increment current have exactly the same cofinal limits.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower
open scoped Interval

/-- Negative critical half-density finite difference of `R = psi - id`. -/
def suzukiCheckpointSelbergIncrementCell (k : ℕ) : ℝ :=
  -(psiRemainder k - psiRemainder (k - 1)) / Real.sqrt k

/-- Source-free Gamma discrepancy between one regular Suzuki cell and the unit half-density
polar increment. -/
def suzukiCheckpointSelbergArchRemainderCell (k : ℕ) : ℝ :=
  (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
      screwRegularKernel t) - 1 / Real.sqrt k

/-- Exact cellwise Selberg-remainder decomposition of literal completed curvature. -/
theorem suzukiCheckpointSignedCurvatureCell_eq_selbergIncrement_add_arch
    {k : ℕ} (hk : 2 ≤ k) :
    suzukiCheckpointSignedCurvatureCell (k - 1) =
      suzukiCheckpointSelbergIncrementCell k +
        suzukiCheckpointSelbergArchRemainderCell k := by
  have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
  have hstep := psiRemainder_succ_sub (k - 1)
  rw [hsucc] at hstep
  unfold suzukiCheckpointSignedCurvatureCell suzukiCheckpointSelbergIncrementCell
    suzukiCheckpointSelbergArchRemainderCell
  rw [hsucc, criticalMellinAtomWeight_eq_div_sqrt, hstep]
  ring

/-- Event-weighted finite-difference current of the discrete Selberg remainder. -/
def suzukiCheckpointWeightedSelbergIncrementPrefix (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 3 (N + 2), (k : ℝ) *
    suzukiCheckpointSelbergIncrementCell k

/-- Event-weighted source-free Gamma remainder. -/
def suzukiCheckpointWeightedSelbergArchRemainderPrefix (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 3 (N + 2), (k : ℝ) *
    suzukiCheckpointSelbergArchRemainderCell k

/-- Exact prefix law: no prime, polar, or Gamma term is separately discarded. -/
theorem weightedSignedCurvaturePrefix_eq_selbergIncrement_add_arch (N : ℕ) :
    suzukiCheckpointWeightedSignedCurvaturePrefix N =
      suzukiCheckpointWeightedSelbergIncrementPrefix N +
        suzukiCheckpointWeightedSelbergArchRemainderPrefix N := by
  rw [suzukiCheckpointWeightedSignedCurvaturePrefix,
    suzukiCheckpointWeightedSelbergIncrementPrefix,
    suzukiCheckpointWeightedSelbergArchRemainderPrefix,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [suzukiCheckpointSignedCurvatureCell_eq_selbergIncrement_add_arch
    (by have := (Finset.mem_Ico.mp hk).1; omega : 2 ≤ k)]
  ring

private theorem natCast_div_sqrt_eq_sqrt {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * (1 / Real.sqrt k) = Real.sqrt k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  rw [mul_one_div]
  apply (div_eq_iff hsqrt.ne').2
  rw [← pow_two]
  exact (Real.sq_sqrt hkR.le).symm

/-- One weighted Gamma correction is at most the inverse square root of the preceding event,
with an explicit constant. -/
theorem abs_weighted_suzukiCheckpointSelbergArchRemainderCell_le
    {k : ℕ} (hk : 3 ≤ k) :
    |(k : ℝ) * suzukiCheckpointSelbergArchRemainderCell k| ≤
      (5 / 3 : ℝ) * (Real.sqrt (k - 1 : ℕ))⁻¹ := by
  let a := Real.sqrt ((k - 1 : ℕ) : ℝ)
  let b := Real.sqrt (k : ℝ)
  have hExp := sqrt_le_weightedExpHalfCell_le_sqrt_add_invSqrtPred
    (k := k) (by omega : 2 ≤ k)
  have hE0 : 0 ≤ 2 * (k : ℝ) * (b - a) - b := by
    change 0 ≤ 2 * (k : ℝ) *
      (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) - Real.sqrt k
    linarith [hExp.1]
  have hEle : 2 * (k : ℝ) * (b - a) - b ≤ a⁻¹ := by
    change 2 * (k : ℝ) *
      (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) - Real.sqrt k ≤
        (Real.sqrt (k - 1 : ℕ))⁻¹
    linarith [hExp.2]
  let T := (k : ℝ) *
    (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
      suzukiCheckpointArchTail t)
  have hT := suzukiCheckpointWeightedArchTailCell_nonneg_le hk
  have hT0 : 0 ≤ T := by simpa only [T] using hT.1
  have hTle : T ≤ (2 / 3 : ℝ) * a⁻¹ := by simpa only [T, a] using hT.2
  have hExpInt := integral_exp_half_log_cell (k := k - 1) (by omega : 1 ≤ k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hExpInt
  have hInv := natCast_div_sqrt_eq_sqrt (k := k) (by omega : 0 < k)
  have hterm :
      (k : ℝ) * suzukiCheckpointSelbergArchRemainderCell k =
        (2 * (k : ℝ) * (b - a) - b) - T := by
    unfold suzukiCheckpointSelbergArchRemainderCell
    rw [integral_screwRegularKernel_eq_expHalf_sub_archTail hk, hExpInt]
    change (k : ℝ) * ((2 * (b - a) - _) - 1 / b) = _
    have hInv' : (k : ℝ) * (1 / b) = b := by simpa only [b] using hInv
    dsimp only [T]
    rw [mul_sub, mul_sub, hInv']
    ring
  rw [hterm]
  calc
    |(2 * (k : ℝ) * (b - a) - b) - T| ≤
        |2 * (k : ℝ) * (b - a) - b| + |T| := abs_sub _ _
    _ = (2 * (k : ℝ) * (b - a) - b) + T := by
      rw [abs_of_nonneg hE0, abs_of_nonneg hT0]
    _ ≤ a⁻¹ + (2 / 3 : ℝ) * a⁻¹ := by linarith
    _ = (5 / 3 : ℝ) * (Real.sqrt (k - 1 : ℕ))⁻¹ := by
      dsimp only [a]
      ring

/-- The entire event-weighted Gamma discrepancy is only `O(sqrt N)`. -/
theorem abs_suzukiCheckpointWeightedSelbergArchRemainderPrefix_le (N : ℕ) :
    |suzukiCheckpointWeightedSelbergArchRemainderPrefix N| ≤
      7 * Real.sqrt (N + 2 : ℕ) := by
  rw [suzukiCheckpointWeightedSelbergArchRemainderPrefix]
  calc
    |∑ k ∈ Finset.Ico 3 (N + 2),
        (k : ℝ) * suzukiCheckpointSelbergArchRemainderCell k| ≤
      ∑ k ∈ Finset.Ico 3 (N + 2),
        |(k : ℝ) * suzukiCheckpointSelbergArchRemainderCell k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico 3 (N + 2),
        (10 / 3 : ℝ) * ((k : ℝ) ^ (-(1 / 2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk3 := (Finset.mem_Ico.mp hk).1
      have hcell := abs_weighted_suzukiCheckpointSelbergArchRemainderCell_le hk3
      refine hcell.trans ?_
      have hpredpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < k - 1)
      have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
      have ha : 0 < Real.sqrt ((k - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hpredpos
      have hb : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
      have hsqrtLe : Real.sqrt (k : ℝ) ≤
          2 * Real.sqrt ((k - 1 : ℕ) : ℝ) := by
        have hnat : k ≤ 4 * (k - 1) := by omega
        calc
          Real.sqrt (k : ℝ) ≤ Real.sqrt (4 * ((k - 1 : ℕ) : ℝ)) := by
            apply Real.sqrt_le_sqrt
            exact_mod_cast hnat
          _ = 2 * Real.sqrt ((k - 1 : ℕ) : ℝ) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
            norm_num
      have hinv : (Real.sqrt (k - 1 : ℕ))⁻¹ ≤
          2 * (Real.sqrt k)⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div,
          show 2 * (1 / Real.sqrt k) = 2 / Real.sqrt k by ring]
        rw [div_le_div_iff₀ ha hb]
        nlinarith
      rw [Real.rpow_neg hkpos.le, ← Real.sqrt_eq_rpow]
      nlinarith
    _ ≤ ∑ k ∈ Finset.Icc 1 (N + 2),
        (10 / 3 : ℝ) * ((k : ℝ) ^ (-(1 / 2 : ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢
        omega
      · intro k hk _
        positivity
    _ = (10 / 3 : ℝ) *
        (∑ k ∈ Finset.Icc 1 (N + 2), ((k : ℝ) ^ (-(1 / 2 : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤ (10 / 3 : ℝ) * (2 * Real.sqrt (N + 2 : ℕ)) := by
      gcongr
      exact sum_rpow_neg_half_le (N + 2)
    _ ≤ 7 * Real.sqrt (N + 2 : ℕ) := by
      nlinarith [Real.sqrt_nonneg ((N + 2 : ℕ) : ℝ)]

theorem tendsto_suzukiCheckpointWeightedSelbergArchRemainderPrefix_div_zero :
    Tendsto (fun N : ℕ =>
      suzukiCheckpointWeightedSelbergArchRemainderPrefix N / (N + 2 : ℕ))
      atTop (nhds 0) := by
  have hsqrt := tendsto_sqrt_natCast_div_natCast_atTop_zero.comp
    (Filter.tendsto_add_atTop_nat 2)
  have hmajor : Tendsto (fun N : ℕ =>
      7 * (Real.sqrt ((N + 2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    simpa using hsqrt.const_mul 7
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) (by
      filter_upwards with N
      have hXpos : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
      rw [abs_div, abs_of_pos hXpos]
      calc
        |suzukiCheckpointWeightedSelbergArchRemainderPrefix N| /
              ((N + 2 : ℕ) : ℝ) ≤
            (7 * Real.sqrt (N + 2 : ℕ)) / ((N + 2 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right
            (abs_suzukiCheckpointWeightedSelbergArchRemainderPrefix_le N) hXpos.le
        _ = 7 * (Real.sqrt ((N + 2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ)) := by ring)
      hmajor

theorem tendsto_normalizedSignedCurvature_sub_selbergIncrement_zero :
    Tendsto (fun N : ℕ =>
      suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 2 : ℕ) -
        suzukiCheckpointWeightedSelbergIncrementPrefix N / (N + 2 : ℕ))
      atTop (nhds 0) := by
  have h := tendsto_suzukiCheckpointWeightedSelbergArchRemainderPrefix_div_zero
  apply h.congr'
  exact Eventually.of_forall fun N => by
    change suzukiCheckpointWeightedSelbergArchRemainderPrefix N / (N + 2 : ℕ) =
      suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 2 : ℕ) -
        suzukiCheckpointWeightedSelbergIncrementPrefix N / (N + 2 : ℕ)
    rw [weightedSignedCurvaturePrefix_eq_selbergIncrement_add_arch]
    ring

theorem tendsto_normalizedSignedCurvature_iff_selbergIncrement (L : ℝ) :
    Tendsto (fun N : ℕ =>
      suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 2 : ℕ))
        atTop (nhds L) ↔
      Tendsto (fun N : ℕ =>
        suzukiCheckpointWeightedSelbergIncrementPrefix N / (N + 2 : ℕ))
        atTop (nhds L) := by
  have hdiff := tendsto_normalizedSignedCurvature_sub_selbergIncrement_zero
  constructor
  · intro hcurv
    have h := hcurv.sub hdiff
    simpa only [sub_zero] using h.congr'
      (Eventually.of_forall fun N => by ring)
  · intro hselberg
    have h := hselberg.add hdiff
    simpa only [add_zero] using h.congr'
      (Eventually.of_forall fun N => by ring)

end RHTower

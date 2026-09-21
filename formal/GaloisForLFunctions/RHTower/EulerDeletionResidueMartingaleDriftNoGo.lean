import GaloisForLFunctions.RHTower.EulerDeletionNestedProjectionCovariance
import GaloisForLFunctions.RHTower.EulerDeletionResidueMartingaleL2Limit
import GaloisForLFunctions.RHTower.EulerDeletionPhysicalCellMoebiusIdentity
import GaloisForLFunctions.RHTower.DeningerMobiusHarmonicZero
import GaloisForLFunctions.RHTower.BaezDuarteMobiusPrefixApproximation
import GaloisForLFunctions.RHTower.BaezDuarteMobiusCriticalTailObstruction

/-!
# Strong-convergence no-go for the Euler-deletion drift

The physical target is the literal constant-one vector on residue cells.
The raw source plus that target has exactly the full Báez--Duarte error
energy.  Since signed innovations converge strongly and each physical atom
has positive mass, the predictable drift has a fixed pointwise limit.
Consequently, uniform integrability of that drift at exponent two would make
the raw full error converge strongly to zero, contradicting the unconditional
critical-tail obstruction.

This rules out uniform-integrability and ordinary strong-convergence proofs
for the raw drift; it leaves the required cofinal signed drift estimate open.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open scoped BigOperators

namespace RHTower.DeletionResidueMartingale

private theorem norm_sq_integral (v : Lp ℝ 2 cellMeasure) :
    ‖v‖ ^ 2 = ∫ j, v j ^ 2 ∂cellMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

private theorem sq_apply_mul_cellWeight_le_norm_sq
    (v : Lp ℝ 2 cellMeasure) (j : ℕ) :
    v j ^ 2 * cellWeight j ≤ ‖v‖ ^ 2 := by
  have hi : Integrable (fun x => v x ^ 2) cellMeasure := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  let s : Set ℕ := {j}
  have hind : Integrable (s.indicator (fun x => v x ^ 2)) cellMeasure :=
    hi.indicator (measurableSet_singleton _)
  calc
    v j ^ 2 * cellWeight j = ∫ x in {j}, v x ^ 2 ∂cellMeasure := by
      rw [integral_singleton, cellMeasure_singleton]
      simp only [smul_eq_mul]
      ring
    _ = ∫ x, s.indicator (fun x => v x ^ 2) x ∂cellMeasure := by
      dsimp [s]
      exact (integral_indicator (measurableSet_singleton _)).symm
    _ ≤ ∫ x, v x ^ 2 ∂cellMeasure := by
      apply integral_mono_ae hind hi
      filter_upwards with x
      by_cases hx : x = j
      · subst x
        simp [s]
      · simp [s, hx, sq_nonneg]
    _ = ‖v‖ ^ 2 := (norm_sq_integral _).symm

/-- Strong `L²` convergence on the full-support physical cell measure is coordinatewise. -/
theorem tendsto_apply_of_tendsto_L2
    (F : ℕ → Lp ℝ 2 cellMeasure) (L : Lp ℝ 2 cellMeasure)
    (hF : Tendsto F atTop (𝓝 L)) (j : ℕ) :
    Tendsto (fun N => F N j) atTop (𝓝 (L j)) := by
  have hnorm : Tendsto (fun N => ‖F N - L‖) atTop (𝓝 0) := by
    have hdiff := hF.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => L) atTop (𝓝 L))
    simpa using hdiff.norm
  have hweight : 0 < cellWeight j := by
    unfold cellWeight
    positivity
  have hsq : Tendsto (fun N => (F N j - L j) ^ 2 * cellWeight j) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun N => ‖F N - L‖ ^ 2)
      (Filter.Eventually.of_forall fun N =>
        mul_nonneg (sq_nonneg _) hweight.le
      ) (Filter.Eventually.of_forall fun N => by
        have hpoint : (F N - L) j = F N j - L j :=
          cell_point_eq_of_ae (Lp.coeFn_sub (F N) L) j
        rw [← hpoint]
        exact sq_apply_mul_cellWeight_le_norm_sq (F N - L) j) (by
        simpa using hnorm.pow 2)
  have hdiffsq : Tendsto (fun N => (F N j - L j) ^ 2) atTop (𝓝 0) := by
    have hdiv := hsq.div_const (cellWeight j)
    convert hdiv using 1
    · ext N
      field_simp [ne_of_gt hweight]
    · simp
  have habs : Tendsto (fun N => |F N j - L j|) atTop (𝓝 0) := by
    simpa only [← Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hdiffsq.sqrt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using habs

/-- The raw Möbius residue source tends to `-1` at every fixed physical cell. -/
theorem tendsto_sourceVec_moebius_apply (j : ℕ) :
    Tendsto (fun N => sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N j)
      atTop (𝓝 (-1)) := by
  have hH : Tendsto deningerHarmonicPartial atTop (𝓝 0) := by
    simpa only [RHTower.deningerHarmonicLimit_eq_zero] using
      RHTower.deningerHarmonicPartial_tendsto
  have hmain : Tendsto (fun N : ℕ => ((j + 1 : ℕ) : ℝ) * deningerHarmonicPartial N - 1)
      atTop (𝓝 (-1)) := by
    simpa using (tendsto_const_nhds.mul hH).sub tendsto_const_nhds
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (j + 1)] with N hN
  rw [sourceVec_apply_eq_cell,
    RHTower.physical_moebius_cell_eq_reciprocal_tail (by omega) hN,
    RHTower.deningerHarmonicPartial_eq_sum_Icc]

private theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    (∑ i ∈ range N, f (i + 1)) = ∑ d ∈ Icc 1 N, f d := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      ∑ i ∈ range (N + 1), f (i + 1) =
          (∑ i ∈ range N, f (i + 1)) + f (N + 1) := by
        simpa using Finset.sum_range_succ (fun i => f (i + 1)) N
      _ = (∑ d ∈ Icc 1 N, f d) + f (N + 1) := by rw [ih]
      _ = ∑ d ∈ Icc 1 (N + 1), f d := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

private theorem moebius_cell_eq_neg_bdMobiusModularApproximant (N n : ℕ) :
    DeletionCoefficientTransfer.cell
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) N n =
      -RHTower.bdMobiusModularApproximant N n := by
  rw [DeletionCoefficientTransfer.cell, RHTower.bdMobiusModularApproximant, neg_neg]
  simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using
    (sum_range_succ_eq_sum_Icc
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (((n % d : ℕ) : ℝ) / (d : ℝ))) N)

/-- The literal constant-one physical target in the residue `L²` carrier. -/
def eulerDeletionPhysicalTarget : Lp ℝ 2 cellMeasure := Lp.const 2 cellMeasure 1

theorem eulerDeletionPhysicalTarget_apply (j : ℕ) : eulerDeletionPhysicalTarget j = 1 := by
  apply cell_point_eq_of_ae
  exact Lp.coeFn_const 2 cellMeasure 1

/-- Adding the physical target to the raw residue source gives exactly the full
Báez--Duarte error energy. -/
theorem sourceVec_moebius_add_target_norm_sq_eq_bdMobiusFullErrorEnergy (N : ℕ) :
    ‖sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N +
      eulerDeletionPhysicalTarget‖ ^ 2 = RHTower.bdMobiusFullErrorEnergy N := by
  let v : Lp ℝ 2 cellMeasure := sourceVec
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N + eulerDeletionPhysicalTarget
  have hi : Integrable (fun j => v j ^ 2) cellMeasure := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hsum := RHTower.hasSum_stepGram
    (s₁ := fun n => 1 - RHTower.bdMobiusModularApproximant N n)
    (s₂ := fun n => 1 - RHTower.bdMobiusModularApproximant N n)
    (RHTower.abs_one_sub_bdMobiusModularApproximant_le N)
    (RHTower.abs_one_sub_bdMobiusModularApproximant_le N)
  change ‖v‖ ^ 2 = _
  rw [norm_sq_integral, integral_countable hi]
  calc
    (∑' j, cellMeasure.real {j} • v j ^ 2) =
        ∑' j, (1 - RHTower.bdMobiusModularApproximant N (j + 1)) ^ 2 /
          (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
      apply tsum_congr
      intro j
      have hsum : v j = 1 - RHTower.bdMobiusModularApproximant N (j + 1) := by
        change (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N +
          eulerDeletionPhysicalTarget) j = _
        calc
          (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N +
              eulerDeletionPhysicalTarget) j =
              sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N j +
                eulerDeletionPhysicalTarget j :=
            cell_point_eq_of_ae (Lp.coeFn_add _ _) j
          _ = 1 - RHTower.bdMobiusModularApproximant N (j + 1) := by
            rw [sourceVec_apply_eq_cell, eulerDeletionPhysicalTarget_apply,
              moebius_cell_eq_neg_bdMobiusModularApproximant]
            ring
      rw [cellMeasure_singleton, hsum, cellWeight, smul_eq_mul]
      ring
    _ = RHTower.bdMobiusFullErrorEnergy N := by
      simpa only [RHTower.bdMobiusFullErrorEnergy, pow_two] using hsum.tsum_eq

/-- The pointwise limit forced on the predictable drift by the raw source and summable
innovation series. -/
def predictableDriftLimit : Lp ℝ 2 cellMeasure :=
  -eulerDeletionPhysicalTarget - martingaleLimit

private theorem predictableDrift_eq_source_sub_martingale (N : ℕ) :
    predictableDrift N =
      sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N - martingalePart N := by
  rw [source_eq_martingale_add_drift]
  abel

theorem tendsto_predictableDrift_apply (j : ℕ) :
    Tendsto (fun N => predictableDrift N j) atTop (𝓝 (predictableDriftLimit j)) := by
  have hsource := tendsto_sourceVec_moebius_apply j
  have hmart := tendsto_apply_of_tendsto_L2 martingalePart martingaleLimit
    tendsto_martingalePart j
  have hmain : Tendsto (fun N =>
      sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N j - martingalePart N j)
      atTop (𝓝 (-1 - martingaleLimit j)) := hsource.sub hmart
  have hlimit : predictableDriftLimit j = -1 - martingaleLimit j := by
    unfold predictableDriftLimit
    calc
      (-eulerDeletionPhysicalTarget - martingaleLimit) j =
          (-eulerDeletionPhysicalTarget) j - martingaleLimit j :=
        cell_point_eq_of_ae (Lp.coeFn_sub _ _) j
      _ = -eulerDeletionPhysicalTarget j - martingaleLimit j :=
        congrArg (fun x : ℝ => x - martingaleLimit j)
          (cell_point_eq_of_ae (Lp.coeFn_neg eulerDeletionPhysicalTarget) j)
      _ = -1 - martingaleLimit j := by rw [eulerDeletionPhysicalTarget_apply]
  rw [hlimit]
  refine hmain.congr' (Filter.Eventually.of_forall fun N => ?_)
  calc
    sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N j - martingalePart N j =
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N - martingalePart N) j :=
      (cell_point_eq_of_ae (Lp.coeFn_sub _ _) j).symm
    _ = predictableDrift N j :=
      (congrArg (fun v : Lp ℝ 2 cellMeasure => v j)
        (predictableDrift_eq_source_sub_martingale N)).symm

private theorem not_tendsto_predictableDrift_norm_sub_limit_zero :
    ¬ Tendsto (fun N => ‖predictableDrift N - predictableDriftLimit‖) atTop (𝓝 0) := by
  intro hDriftNorm
  have hMartNorm : Tendsto (fun N => ‖martingalePart N - martingaleLimit‖) atTop (𝓝 0) := by
    simpa using (tendsto_martingalePart.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => martingaleLimit) atTop (𝓝 martingaleLimit))).norm
  have hsourceTarget : Tendsto (fun N =>
      sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N + eulerDeletionPhysicalTarget)
      atTop (𝓝 0) := by
    have hbound : Tendsto (fun N => ‖martingalePart N - martingaleLimit‖ +
        ‖predictableDrift N - predictableDriftLimit‖) atTop (𝓝 0) := by
      simpa using hMartNorm.add hDriftNorm
    refine squeeze_zero_norm (fun N => ?_) hbound
    rw [source_eq_martingale_add_drift]
    unfold predictableDriftLimit
    convert norm_add_le (martingalePart N - martingaleLimit)
      (predictableDrift N - (-eulerDeletionPhysicalTarget - martingaleLimit)) using 1
    all_goals abel
  have henergy : Tendsto RHTower.bdMobiusFullErrorEnergy atTop (𝓝 0) := by
    have hsq := hsourceTarget.norm.pow 2
    convert hsq using 1
    · funext N
      exact (sourceVec_moebius_add_target_norm_sq_eq_bdMobiusFullErrorEnergy N).symm
    · norm_num
  exact RHTower.not_tendsto_bdMobiusFullErrorEnergy_zero henergy

/-- The drift converges at each positive-mass physical cell, but not strongly in physical `L²`.
Thus its missing mass cannot be repaired by an ordinary strong-convergence argument. -/
theorem not_tendsto_predictableDrift_strongL2 :
    ¬ Tendsto (fun N => predictableDrift N) atTop (𝓝 predictableDriftLimit) := by
  intro hstrong
  apply not_tendsto_predictableDrift_norm_sub_limit_zero
  simpa using (hstrong.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => predictableDriftLimit)
      atTop (𝓝 predictableDriftLimit))).norm

/-- Unit-valued `L²` coordinate vector on one positive-mass physical residue cell. -/
def eulerDeletionPhysicalCellBasis (j : ℕ) : Lp ℝ 2 cellMeasure :=
  indicatorConstLp 2 (measurableSet_singleton j) (measure_ne_top cellMeasure _) (1 : ℝ)

theorem eulerDeletionPhysicalCellBasis_apply (j k : ℕ) :
    eulerDeletionPhysicalCellBasis j k = if k = j then 1 else 0 := by
  unfold eulerDeletionPhysicalCellBasis
  rw [cell_point_eq_of_ae indicatorConstLp_coeFn]
  by_cases h : k = j <;> simp [h]

private theorem smul_eulerDeletionPhysicalCellBasis_apply (a : ℝ) (j k : ℕ) :
    (a • eulerDeletionPhysicalCellBasis j) k = a * (if k = j then 1 else 0) := by
  rw [cell_point_eq_of_ae (Lp.coeFn_smul a (eulerDeletionPhysicalCellBasis j))]
  change a * eulerDeletionPhysicalCellBasis j k = _
  rw [eulerDeletionPhysicalCellBasis_apply]

/-- Literal projection to physical cells through the fixed cutoff `K`. -/
def eulerDeletionPhysicalPrefix (K : ℕ) (v : Lp ℝ 2 cellMeasure) : Lp ℝ 2 cellMeasure :=
  ∑ j ∈ range (K + 1), v j • eulerDeletionPhysicalCellBasis j

private theorem apply_sum (s : Finset ℕ) (f : ℕ → Lp ℝ 2 cellMeasure) (j : ℕ) :
    (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [cell_point_eq_of_ae (Lp.coeFn_add (f a) (∑ i ∈ s, f i))]
    change f a j + (∑ i ∈ s, f i) j = _
    rw [ih]

theorem eulerDeletionPhysicalPrefix_apply (K j : ℕ) (v : Lp ℝ 2 cellMeasure) :
    eulerDeletionPhysicalPrefix K v j = if j ≤ K then v j else 0 := by
  unfold eulerDeletionPhysicalPrefix
  rw [apply_sum]
  simp_rw [smul_eulerDeletionPhysicalCellBasis_apply]
  by_cases hj : j ≤ K
  · simp [hj]
  · simp [hj]

/-- Literal complementary physical tail after the fixed-cell projection. -/
def eulerDeletionPhysicalTail (K : ℕ) (v : Lp ℝ 2 cellMeasure) : Lp ℝ 2 cellMeasure :=
  v - eulerDeletionPhysicalPrefix K v

theorem eulerDeletionPhysicalTail_apply (K j : ℕ) (v : Lp ℝ 2 cellMeasure) :
    eulerDeletionPhysicalTail K v j = if K < j then v j else 0 := by
  unfold eulerDeletionPhysicalTail
  rw [cell_point_eq_of_ae (Lp.coeFn_sub _ _)]
  change v j - eulerDeletionPhysicalPrefix K v j = _
  rw [eulerDeletionPhysicalPrefix_apply]
  by_cases h : K < j
  · have hnot : ¬ j ≤ K := by omega
    simp [h, hnot]
  · have hle : j ≤ K := by omega
    simp [h, hle]

private theorem tendsto_eulerDeletionPhysicalPrefix_drift_sub_limit (K : ℕ) :
    Tendsto (fun N => eulerDeletionPhysicalPrefix K
      (predictableDrift N - predictableDriftLimit)) atTop (𝓝 0) := by
  unfold eulerDeletionPhysicalPrefix
  have hcoord (j : ℕ) : Tendsto
      (fun N => (predictableDrift N - predictableDriftLimit) j) atTop (𝓝 0) := by
    have hmain := (tendsto_predictableDrift_apply j).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => predictableDriftLimit j)
        atTop (𝓝 (predictableDriftLimit j)))
    simpa only [sub_self] using hmain.congr'
      (Filter.Eventually.of_forall fun N =>
        (cell_point_eq_of_ae (Lp.coeFn_sub (predictableDrift N)
          predictableDriftLimit) j).symm)
  simpa only [zero_smul, Finset.sum_const_zero] using
    tendsto_finsetSum (range (K + 1)) (fun j _ =>
      (hcoord j).smul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => eulerDeletionPhysicalCellBasis j)
          atTop (𝓝 (eulerDeletionPhysicalCellBasis j))))

/-- The nonconvergent drift energy survives beyond every fixed physical cutoff.
This is a literal moving-tail statement, not merely abstract failure of compactness. -/
theorem not_tendsto_eulerDeletionPhysicalTail_drift_sub_limit_norm (K : ℕ) :
    ¬ Tendsto (fun N => ‖eulerDeletionPhysicalTail K
      (predictableDrift N - predictableDriftLimit)‖) atTop (𝓝 0) := by
  intro htail
  have htailVec : Tendsto (fun N => eulerDeletionPhysicalTail K
      (predictableDrift N - predictableDriftLimit)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr htail
  have hprefix := tendsto_eulerDeletionPhysicalPrefix_drift_sub_limit K
  have hdiff : Tendsto (fun N => predictableDrift N - predictableDriftLimit)
      atTop (𝓝 0) := by
    have hsum := htailVec.add hprefix
    convert hsum using 1
    · funext N
      unfold eulerDeletionPhysicalTail
      abel
    · abel
  have hstrong : Tendsto (fun N => predictableDrift N) atTop (𝓝 predictableDriftLimit) := by
    have hsum := hdiff.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => predictableDriftLimit)
        atTop (𝓝 predictableDriftLimit))
    convert hsum using 1 <;> abel
  exact not_tendsto_predictableDrift_strongL2 hstrong

/-- The raw Euler-deletion predictable drift is not uniformly integrable at the energy exponent.
Consequently it cannot be controlled by a Vitali/ordinary-strong-convergence proof. -/
theorem not_unifIntegrable_predictableDrift :
    ¬ UnifIntegrable (fun N => (predictableDrift N : ℕ → ℝ)) 2 cellMeasure := by
  intro hui
  have hae : ∀ᵐ j ∂cellMeasure,
      Tendsto (fun N => predictableDrift N j) atTop (𝓝 (predictableDriftLimit j)) :=
    Filter.Eventually.of_forall tendsto_predictableDrift_apply
  have hvitali : Tendsto (fun N => eLpNorm
      ((predictableDrift N : ℕ → ℝ) - (predictableDriftLimit : ℕ → ℝ)) 2 cellMeasure)
      atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
      (fun N => Lp.aestronglyMeasurable (predictableDrift N))
      (Lp.memLp predictableDriftLimit) hui hae
  have hvitaliLp : Tendsto (fun N => eLpNorm
      ((predictableDrift N - predictableDriftLimit : Lp ℝ 2 cellMeasure) : ℕ → ℝ)
      2 cellMeasure) atTop (𝓝 0) := by
    refine hvitali.congr' (Filter.Eventually.of_forall fun N => ?_)
    exact eLpNorm_congr_ae (Lp.coeFn_sub (predictableDrift N) predictableDriftLimit).symm
  have hDriftNorm : Tendsto
      (fun N => ‖predictableDrift N - predictableDriftLimit‖) atTop (𝓝 0) := by
    have hto := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hvitaliLp
    rw [show (fun N => ‖predictableDrift N - predictableDriftLimit‖) =
      fun N => (eLpNorm
        ((predictableDrift N - predictableDriftLimit : Lp ℝ 2 cellMeasure) : ℕ → ℝ)
        2 cellMeasure).toReal by
      funext N
      exact Lp.norm_def _]
    change Tendsto (ENNReal.toReal ∘ fun N => eLpNorm
      ((predictableDrift N - predictableDriftLimit : Lp ℝ 2 cellMeasure) : ℕ → ℝ)
      2 cellMeasure) atTop (𝓝 0)
    exact hto
  exact not_tendsto_predictableDrift_norm_sub_limit_zero hDriftNorm

end RHTower.DeletionResidueMartingale

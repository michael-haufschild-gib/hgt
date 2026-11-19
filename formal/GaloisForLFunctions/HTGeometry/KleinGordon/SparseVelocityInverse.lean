import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandWellPosed
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandLimit
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Sparse short-time observations determine a Klein–Gordon perturbation

The linear inverse step in Kumar–Senapati–Vashisth compares responses
for different coefficients. For the corpus band evolution, the difference
of two velocities starts with the compressed perturbation difference.
Agreement on any infinite subsequence of the times 1/(n+1) identifies
that compression. Unboundedly many such bands identify the full operator.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.KGSparseInverse

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "H" => Lp ℂ 2 (volume : Measure E)
local notation "Op" => H →L[ℂ] H

/-- Band-limited displacement, zero initial velocity. -/
def shot (W : Op) (R : ℝ) (x : H) := kgFieldVel (kgBandOp W R) (kgFreqLowOp R x) 0

private theorem shot_zero (W : Op) (R : ℝ) (x : H) : shot W R x 0 = 0 := by
  simp only [shot,kgFieldVel,kgSinOp_zero,ContinuousLinearMap.zero_apply,neg_zero,
    map_zero,intervalIntegral.integral_same,add_zero]

private theorem shot_derivative (W : Op) (R : ℝ) (x : H) :
    HasDerivAt (shot W R x) (-kgFreqSqLowOp R (kgLowPassOp R x)+kgBandOp W R x) 0 := by
  have h := hasDerivAt_kgFieldVel_band (norm_nonneg W) (le_rfl : ‖W‖ ≤ ‖W‖) R x 0 0
  rw [map_zero,kgFieldMild_zero (norm_nonneg _) le_rfl,kgFreqInvOp_kgFreqLowOp] at h
  have hid : kgBandOp W R (kgLowPassOp R x) = kgBandOp W R x := by
    simp only [kgBandOp_apply,kgLowPassOp_idem]
  rwa [hid] at h

private def clock (n : ℕ) : ℝ := 1/((n:ℝ)+1)

private theorem clock_tendsto : Tendsto clock atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun n => ?_⟩
  change clock n ≠ 0
  unfold clock
  positivity

/-- Exact recovery formula from the measured velocities. The free acceleration
cancels for all initial displacements, including data outside the band. -/
theorem velocity_difference_limit (W V : Op) (R : ℝ) (x : H) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1) •
      (shot W R x (1/((n:ℝ)+1))-shot V R x (1/((n:ℝ)+1)))) atTop
      (𝓝 (kgBandOp W R x-kgBandOp V R x)) := by
  have h := (hasDerivAt_iff_tendsto_slope.mp ((shot_derivative W R x).sub
    (shot_derivative V R x))).comp clock_tendsto
  have e : (-kgFreqSqLowOp R (kgLowPassOp R x)+kgBandOp W R x) -
      (-kgFreqSqLowOp R (kgLowPassOp R x)+kgBandOp V R x) =
      kgBandOp W R x-kgBandOp V R x := by abel
  simpa only [Function.comp_def,slope_def_module,clock,sub_zero,shot_zero,sub_self,
    sub_zero,one_div,inv_inv,e] using h

/-- Agreement times may depend on the initial displacement. Infinitely many
readings for each displacement determine exactly the compressed operator. -/
theorem sparse_shots_iff (W V : Op) (R : ℝ) :
    (∀ x : H, ∃ᶠ n : ℕ in atTop, shot W R x (1/((n:ℝ)+1)) =
      shot V R x (1/((n:ℝ)+1))) ↔ kgBandOp W R = kgBandOp V R := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    apply sub_eq_zero.mp
    apply tendsto_nhds_unique_of_frequently_eq (velocity_difference_limit W V R x) tendsto_const_nhds
    exact (h x).mono fun n hn => by rw [hn,sub_self,smul_zero]
  · intro he x
    apply Filter.Eventually.frequently
    apply Eventually.of_forall
    intro n
    simp only [shot,he]

/-- Perturbations differing by less than first order in every measured
velocity are precisely those with equal compression on the observed band. -/
theorem first_order_invisibility_iff (W V : Op) (R : ℝ) :
    (∀ x : H, Tendsto (fun n : ℕ => ((n:ℝ)+1) •
      (shot W R x (1/((n:ℝ)+1))-shot V R x (1/((n:ℝ)+1)))) atTop (𝓝 0)) ↔
      kgBandOp W R = kgBandOp V R := by
  constructor
  · intro h
    exact ContinuousLinearMap.ext fun x => sub_eq_zero.mp
      (tendsto_nhds_unique (velocity_difference_limit W V R x) (h x))
  · intro he x
    simpa only [he,sub_self] using velocity_difference_limit W V R x

/-- Sampling need only succeed on a cofinal set of bandwidths and on an
infinite subsequence of times at each recovered input and bandwidth. -/
theorem cofinal_shots_identify (W V : Op) :
    (∃ᶠ R : ℝ in atTop, ∀ x : H, ∃ᶠ n : ℕ in atTop,
      shot W R x (1/((n:ℝ)+1)) = shot V R x (1/((n:ℝ)+1))) ↔ W = V := by
  simp only [sparse_shots_iff]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    exact tendsto_nhds_unique_of_frequently_eq
      (tendsto_kgBandOp_apply (W₀ := W) x) (tendsto_kgBandOp_apply (W₀ := V) x)
      (h.mono fun R he => congrArg (fun A : Op => A x) he)
  · rintro rfl
    exact (Eventually.of_forall fun _ => rfl).frequently

end GaloisForLFunctions.HTGeometry.KGSparseInverse

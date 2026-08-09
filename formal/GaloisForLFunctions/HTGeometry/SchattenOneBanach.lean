import GaloisForLFunctions.HTGeometry.RectangularNuclearNormBound
import GaloisForLFunctions.RHTower.TraceNormLimit
import Mathlib.Analysis.Convex.TotallyBounded

/-!
# The Schatten-one Banach carrier

This module bundles approximation-number Schatten-one operators with their
genuine trace norm.  It proves the normed vector-space structure and the
trace-norm continuity of the positive rank-one embedding.  The Banach
completeness proof below is intrinsic: trace norm dominates operator norm,
and finite sums of approximation numbers pass to the operator-norm limit by
their one-Lipschitz law.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Linear subspace of all approximation-number Schatten-one operators. -/
def schattenOneSubmodule [CompleteSpace H] : Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | MemSchattenClass 1 T}
  zero_mem' := by
    exact memSchattenClass_of_hasRankLE one_pos (hasRankLE_zero (H := H) 0)
  add_mem' := fun hS hT ↦ hS.one_add hT
  smul_mem' := fun c _ hT ↦ memSchattenClass_one_smul hT c

/-- Schatten-one operators, bundled with their closed membership proof.

This is deliberately a structure rather than an abbreviation for the
underlying submodule: the submodule carries the operator norm, whereas this
carrier is endowed below with the strictly stronger trace norm. -/
structure SchattenOneOperator (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  val : H →L[ℂ] H
  property : MemSchattenClass 1 val

instance [CompleteSpace H] : Coe (SchattenOneOperator H) (H →L[ℂ] H) :=
  ⟨SchattenOneOperator.val⟩

@[ext] theorem SchattenOneOperator.ext [CompleteSpace H]
    {S T : SchattenOneOperator H}
    (h : (S : H →L[ℂ] H) = (T : H →L[ℂ] H)) : S = T := by
  cases S
  cases T
  cases h
  rfl

private noncomputable def schattenOneEquivSubmodule [CompleteSpace H] :
    SchattenOneOperator H ≃ schattenOneSubmodule (H := H) where
  toFun T := ⟨T.val, T.property⟩
  invFun T := ⟨T.val, T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance [CompleteSpace H] : AddCommGroup (SchattenOneOperator H) :=
  schattenOneEquivSubmodule.addCommGroup

noncomputable instance [CompleteSpace H] : Module ℂ (SchattenOneOperator H) :=
  schattenOneEquivSubmodule.module ℂ

@[simp] theorem SchattenOneOperator.coe_zero [CompleteSpace H] :
    ((0 : SchattenOneOperator H) : H →L[ℂ] H) = 0 := rfl

@[simp] theorem SchattenOneOperator.coe_add [CompleteSpace H]
    (S T : SchattenOneOperator H) :
    ((S + T : SchattenOneOperator H) : H →L[ℂ] H) =
      (S : H →L[ℂ] H) + (T : H →L[ℂ] H) := rfl

@[simp] theorem SchattenOneOperator.coe_neg [CompleteSpace H]
    (T : SchattenOneOperator H) :
    ((-T : SchattenOneOperator H) : H →L[ℂ] H) =
      -(T : H →L[ℂ] H) := rfl

@[simp] theorem SchattenOneOperator.coe_sub [CompleteSpace H]
    (S T : SchattenOneOperator H) :
    ((S - T : SchattenOneOperator H) : H →L[ℂ] H) =
      (S : H →L[ℂ] H) - (T : H →L[ℂ] H) := rfl

@[simp] theorem SchattenOneOperator.coe_smul [CompleteSpace H]
    (c : ℂ) (T : SchattenOneOperator H) :
    ((c • T : SchattenOneOperator H) : H →L[ℂ] H) =
      c • (T : H →L[ℂ] H) := rfl

section Normed

variable [CompleteSpace H]

theorem SchattenOneOperator.summable (T : SchattenOneOperator H) :
    Summable fun n ↦ approxNumber (T : H →L[ℂ] H) n :=
  T.property.one_summable

theorem SchattenOneOperator.isCompactOperator (T : SchattenOneOperator H) :
    IsCompactOperator (T : H →L[ℂ] H) :=
  T.property.isCompactOperator one_pos

noncomputable instance : NormedAddCommGroup (SchattenOneOperator H) :=
  letI : Norm (SchattenOneOperator H) :=
    ⟨fun T ↦ traceNorm H (T : H →L[ℂ] H)⟩
  NormedAddCommGroup.ofCore {
    norm_nonneg := fun T ↦ traceNorm_nonneg (T : H →L[ℂ] H)
    norm_eq_zero_iff := fun T ↦ by
      change traceNorm H (T : H →L[ℂ] H) = 0 ↔ T = 0
      rw [traceNorm_eq_zero_iff (SchattenOneOperator.summable T)]
      constructor
      · intro h
        exact SchattenOneOperator.ext h
      · rintro rfl
        rfl
    norm_smul := fun c T ↦ traceNorm_smul c (T : H →L[ℂ] H)
    norm_triangle := fun S T ↦ by
      change traceNorm H
          ((S : H →L[ℂ] H) + (T : H →L[ℂ] H)) ≤
        traceNorm H (S : H →L[ℂ] H) + traceNorm H (T : H →L[ℂ] H)
      exact traceNorm_add_le
        (SchattenOneOperator.isCompactOperator S)
        (SchattenOneOperator.isCompactOperator T)
        (SchattenOneOperator.summable S)
        (SchattenOneOperator.summable T) }

noncomputable instance : NormedSpace ℂ (SchattenOneOperator H) :=
  NormedSpace.mk fun c T ↦ by
    change traceNorm H (c • (T : H →L[ℂ] H)) ≤
      ‖c‖ * traceNorm H (T : H →L[ℂ] H)
    exact le_of_eq (traceNorm_smul c (T : H →L[ℂ] H))

@[simp] theorem SchattenOneOperator.norm_def (T : SchattenOneOperator H) :
    ‖T‖ = traceNorm H (T : H →L[ℂ] H) := rfl

/-- Forgetting the Schatten-one proof is contractive from trace norm to
operator norm. -/
theorem SchattenOneOperator.norm_coe_le (T : SchattenOneOperator H) :
    ‖(T : H →L[ℂ] H)‖ ≤ ‖T‖ := by
  exact norm_le_traceNorm (SchattenOneOperator.summable T)

/-- Continuous linear forgetful map from trace norm to operator norm. -/
noncomputable def schattenOneCoeCLM :
    SchattenOneOperator H →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun T ↦ (T : H →L[ℂ] H)
      map_add' := SchattenOneOperator.coe_add
      map_smul' := SchattenOneOperator.coe_smul }
    1 fun T ↦ by
      rw [one_mul]
      exact SchattenOneOperator.norm_coe_le T

@[simp] theorem schattenOneCoeCLM_apply (T : SchattenOneOperator H) :
    schattenOneCoeCLM T = (T : H →L[ℂ] H) := rfl

/-- The forgetful map is one-Lipschitz. -/
theorem schattenOne_coe_lipschitz :
    LipschitzWith 1 (fun T : SchattenOneOperator H ↦ (T : H →L[ℂ] H)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro S T
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  change ‖((S - T : SchattenOneOperator H) : H →L[ℂ] H)‖ ≤ ‖S - T‖
  exact SchattenOneOperator.norm_coe_le (S - T)

/-- Approximation numbers are one-Lipschitz in operator norm. -/
theorem approxNumber_lipschitz (n : ℕ) :
    LipschitzWith 1 (fun T : H →L[ℂ] H ↦ approxNumber T n) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro S T
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  rw [abs_le]
  constructor
  · have h := approxNumber_add_le (T - S) S 0 n
    rw [zero_add, approxNumber_zero_eq_norm, sub_add_cancel] at h
    rw [norm_sub_rev]
    linarith
  · have h := approxNumber_add_le (S - T) T 0 n
    rw [zero_add, approxNumber_zero_eq_norm, sub_add_cancel] at h
    linarith

/-- A uniform trace-norm bound survives an operator-norm limit.  This is the
Fatou-closedness statement needed for completeness of Schatten one. -/
theorem memSchattenClass_one_and_traceNorm_le_of_tendsto
    {T : ℕ → H →L[ℂ] H} {K : H →L[ℂ] H} {r : ℝ}
    (hT : ∀ m, MemSchattenClass 1 (T m))
    (hlim : Tendsto T atTop (nhds K))
    (hbound : ∀ᶠ m in atTop, traceNorm H (T m) ≤ r) :
    MemSchattenClass 1 K ∧ traceNorm H K ≤ r := by
  have hfinite (s : Finset ℕ) :
      ∑ n ∈ s, approxNumber K n ≤ r := by
    have hsumlim : Tendsto
        (fun m ↦ ∑ n ∈ s, approxNumber (T m) n) atTop
        (nhds (∑ n ∈ s, approxNumber K n)) := by
      apply tendsto_finset_sum
      intro n _
      exact (approxNumber_lipschitz (H := H) n).continuous.continuousAt.tendsto.comp hlim
    apply le_of_tendsto hsumlim
    filter_upwards [hbound] with m hm
    exact (((hT m).one_summable).sum_le_tsum s
      (fun n _ ↦ approxNumber_nonneg (T m) n)).trans hm
  have hsum : Summable fun n ↦ approxNumber K n :=
    summable_of_sum_le (fun n ↦ approxNumber_nonneg K n) hfinite
  exact ⟨memSchattenClass_one_of_summable hsum,
    Real.tsum_le_of_sum_le (fun n ↦ approxNumber_nonneg K n) hfinite⟩

/-- Nuclear norm of a rank-at-most-`N` operator is at most `N` times its
operator norm. -/
theorem traceNorm_le_rank_mul_norm_of_hasRankLE
    {T : H →L[ℂ] H} {N : ℕ} (hT : HasRankLE T N) :
    traceNorm H T ≤ (N : ℝ) * ‖T‖ := by
  have hmem : MemSchattenClass 1 T :=
    memSchattenClass_of_hasRankLE one_pos hT
  have hsum : Summable fun n ↦ approxNumber T n := hmem.one_summable
  have htailZero : ∀ n : ℕ, approxNumber T (n + N) = 0 := by
    intro n
    exact le_antisymm
      (by simpa using approxNumber_le T (n + N) T (hT.mono (Nat.le_add_left N n)))
      (approxNumber_nonneg T (n + N))
  have htail : ∑' n : ℕ, approxNumber T (n + N) = 0 := by
    simp [htailZero]
  rw [traceNorm, ← hsum.sum_add_tsum_nat_add N, htail, add_zero]
  calc
    ∑ n ∈ Finset.range N, approxNumber T n ≤
        ∑ _n ∈ Finset.range N, ‖T‖ := by
      exact Finset.sum_le_sum fun n _ ↦ approxNumber_le_norm T n
    _ = (N : ℝ) * ‖T‖ := by simp

/-- Schatten-one operators are complete for the trace norm. -/
noncomputable instance : CompleteSpace (SchattenOneOperator H) :=
  UniformSpace.complete_of_cauchySeq_tendsto fun u hu ↦ by
    have hcoeCauchy : CauchySeq (fun n ↦ (u n : H →L[ℂ] H)) := by
      simpa [Function.comp_def] using
        schattenOne_coe_lipschitz.cauchySeq_comp hu
    obtain ⟨K, hKlim⟩ := cauchySeq_tendsto_of_complete hcoeCauchy
    obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hu.isBounded_range
    have hglobal : ∀ᶠ n in atTop,
        traceNorm H (u n : H →L[ℂ] H) ≤ r := by
      filter_upwards [] with n
      simpa only [SchattenOneOperator.norm_def] using
        hr (u n) ⟨n, rfl⟩
    obtain ⟨hKmem, _⟩ :=
      memSchattenClass_one_and_traceNorm_le_of_tendsto
        (fun n ↦ (u n).property) hKlim hglobal
    let K₁ : SchattenOneOperator H := ⟨K, hKmem⟩
    refine ⟨K₁, Metric.tendsto_atTop.mpr ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hdiffLim : Tendsto
        (fun m ↦ (u n : H →L[ℂ] H) - (u m : H →L[ℂ] H)) atTop
        (nhds ((u n : H →L[ℂ] H) - K)) :=
      tendsto_const_nhds.sub hKlim
    have hdiffBound : ∀ᶠ m in atTop,
        traceNorm H ((u n : H →L[ℂ] H) - (u m : H →L[ℂ] H)) ≤ ε / 2 := by
      filter_upwards [eventually_atTop.mpr ⟨N, fun m hm ↦ hm⟩] with m hm
      have hnm := hN n hn m hm
      rw [dist_eq_norm] at hnm
      exact le_of_lt hnm
    obtain ⟨_, hdiff⟩ :=
      memSchattenClass_one_and_traceNorm_le_of_tendsto
        (fun m ↦ (u n).property.one_sub (u m).property)
        hdiffLim hdiffBound
    rw [dist_eq_norm]
    change traceNorm H ((u n : H →L[ℂ] H) - K) < ε
    exact hdiff.trans_lt (half_lt_self hε)

end Normed

section RankOne

variable [CompleteSpace H]

/-- A general rank-one operator as a bundled Schatten-one element. -/
noncomputable def rankOneSchattenOne (x y : H) : SchattenOneOperator H :=
  ⟨InnerProductSpace.rankOne ℂ x y,
    memSchattenClass_of_hasRankLE one_pos
      (by simpa [InnerProductSpace.rankOne_def] using
        deningerSmulRight_hasRankLE_one (innerSL ℂ y) x)⟩

@[simp] theorem rankOneSchattenOne_coe (x y : H) :
    (rankOneSchattenOne x y : H →L[ℂ] H) =
      InnerProductSpace.rankOne ℂ x y := rfl

/-- Trace norm of a rank-one operator is exactly the product of its two
vector norms. -/
@[simp] theorem norm_rankOneSchattenOne (x y : H) :
    ‖rankOneSchattenOne x y‖ = ‖x‖ * ‖y‖ := by
  change traceNorm H (InnerProductSpace.rankOne ℂ x y) = _
  rw [traceNorm_eq_norm_of_hasRankLE_one]
  · exact InnerProductSpace.norm_rankOne x y
  · simpa [InnerProductSpace.rankOne_def] using
      deningerSmulRight_hasRankLE_one (innerSL ℂ y) x

/-- Positive rank-one ray `|v⟩⟨v|` in the Schatten-one carrier. -/
noncomputable def positiveRankOneSchattenOne (v : H) : SchattenOneOperator H :=
  rankOneSchattenOne v v

@[simp] theorem norm_positiveRankOneSchattenOne (v : H) :
    ‖positiveRankOneSchattenOne v‖ = ‖v‖ ^ 2 := by
  change ‖rankOneSchattenOne v v‖ = ‖v‖ ^ 2
  rw [norm_rankOneSchattenOne, pow_two]

/-- Polarized difference identity for positive rank-one rays. -/
theorem positiveRankOneSchattenOne_sub (v w : H) :
    positiveRankOneSchattenOne v - positiveRankOneSchattenOne w =
      rankOneSchattenOne (v - w) v + rankOneSchattenOne w (v - w) := by
  apply SchattenOneOperator.ext
  change InnerProductSpace.rankOne ℂ v v -
      InnerProductSpace.rankOne ℂ w w =
    InnerProductSpace.rankOne ℂ (v - w) v +
      InnerProductSpace.rankOne ℂ w (v - w)
  ext z
  simp only [sub_apply, add_apply, InnerProductSpace.rankOne_apply]
  rw [inner_sub_left]
  module

/-- Exact local trace-norm continuity bound for the rank-one embedding. -/
theorem norm_positiveRankOneSchattenOne_sub_le (v w : H) :
    ‖positiveRankOneSchattenOne v - positiveRankOneSchattenOne w‖ ≤
      ‖v - w‖ * (‖v‖ + ‖w‖) := by
  rw [positiveRankOneSchattenOne_sub]
  calc
    ‖rankOneSchattenOne (v - w) v + rankOneSchattenOne w (v - w)‖ ≤
        ‖rankOneSchattenOne (v - w) v‖ +
          ‖rankOneSchattenOne w (v - w)‖ := norm_add_le _ _
    _ = ‖v - w‖ * (‖v‖ + ‖w‖) := by
      rw [norm_rankOneSchattenOne, norm_rankOneSchattenOne]
      ring

/-- The norm-to-trace-norm positive rank-one embedding is continuous. -/
theorem continuous_positiveRankOneSchattenOne :
    Continuous (positiveRankOneSchattenOne : H → SchattenOneOperator H) := by
  rw [continuous_iff_continuousAt]
  intro v
  show Tendsto positiveRankOneSchattenOne
    (nhds v) (nhds (positiveRankOneSchattenOne v))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun w ↦ norm_nonneg _)
    (fun w ↦ norm_positiveRankOneSchattenOne_sub_le w v) ?_
  have hcont : ContinuousAt
      (fun w : H ↦ ‖w - v‖ * (‖w‖ + ‖v‖)) v :=
    ((continuousAt_id.sub continuousAt_const).norm.mul
      (continuousAt_id.norm.add continuousAt_const))
  convert hcont.tendsto using 1 <;> simp

end RankOne

end RHTower

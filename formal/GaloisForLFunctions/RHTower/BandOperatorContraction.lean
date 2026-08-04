import GaloisForLFunctions.RHTower.BandLeakageEnvelope
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Order.ProjIcc

/-!
# The band operator is a contraction, and its norm tends to one

The variational bound compares the band Rayleigh quotient with the operator norm, and the leakage
envelope bounds the norm from below.  What is missing for a limit statement is the trivial half:
`‖B_c‖ <= 1`.  It is not formal — the kernel is not small — but spectral: the band quadratic form of a
test function is the spectral mass it carries inside the window, hence at most its total energy.

That comparison is proved for continuous test functions, and continuous functions are dense in the
interval `L²` (the band is compact and its measure is finite, so `WeaklyRegular` is automatic).  Every
class in `L²[-1, 1]` is therefore a limit of continuous ones, and both sides of the comparison are
continuous in the class, so the comparison holds everywhere.  Since a continuous function on `[-1, 1]`
is the restriction of one on the line (extend it by its endpoint values), the density argument sees all
of the continuous test functions the corpus lemmas are stated for.

For a symmetric operator the norm is the supremum of the absolute Rayleigh quotients, so
`0 <= ⟪B_c psi, psi⟫ <= ‖psi‖²` gives `‖B_c‖ <= 1`.  Together with the exponential leakage envelope
this pins the aperture asymptotics of the band operator:

```text
1 - 64 c² e^(-2c) <= ‖B_c‖ <= 1,        so    ‖B_c‖ -> 1 as c -> infinity.
```
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral FourierTransform

open _root_.RHTower

/-! ## The interval subtype as a compact finite measure space -/

theorem isFiniteMeasure_intervalVolume (a b : ℝ) :
    IsFiniteMeasure (volume : Measure (ClosedInterval a b)) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

theorem compactSpace_interval (a b : ℝ) : CompactSpace (ClosedInterval a b) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- **Continuous functions are dense in the interval `L²`.**  The band is compact and carries a finite
measure, so the measure is weakly regular and mathlib's density theorem applies. -/
theorem denseRange_toLp_interval (a b : ℝ) :
    DenseRange (ContinuousMap.toLp (E := ℝ) 2 (volume : Measure (ClosedInterval a b)) ℝ) := by
  haveI := isFiniteMeasure_intervalVolume a b
  haveI := compactSpace_interval a b
  exact ContinuousMap.toLp_denseRange ℝ (volume : Measure (ClosedInterval a b)) (p := 2) ℝ
    (by norm_num)

/-- Every continuous function on the band is the restriction of a continuous function on the line, so
the band classes of the corpus lemmas exhaust the range of `toLp`. -/
theorem exists_continuous_bandClass_eq (g : C(ClosedInterval (-1 : ℝ) 1, ℝ)) :
    ∃ (Φ : ℝ → ℝ) (hΦ : Continuous Φ),
      bandClass Φ hΦ = ContinuousMap.toLp 2 (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ℝ g := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  refine ⟨Set.IccExtend hle g, (continuous_IccExtend_iff (h := hle)).mpr g.continuous, ?_⟩
  rw [bandClass]
  congr 1
  ext x
  exact Set.IccExtend_val hle g x

/-! ## The band quadratic form on every `L²` class -/

/-- On a continuous test function the band form is at most the energy: the difference is the spectral
tail, which is an integral of a square. -/
theorem inner_bandOperatorL2_bandClass_le {c : ℝ} (hc : 0 < c) (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    (inner ℝ (bandOperatorL2 c (bandClass Φ hΦ)) (bandClass Φ hΦ) : ℝ)
      ≤ ‖bandClass Φ hΦ‖ ^ 2 := by
  have htail : (0 : ℝ) ≤ ∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ,
      ‖𝓕 (bandTrunc Φ) ξ‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Icc.compl fun ξ _ => by positivity
  rw [← leakage_eq_spectral_tail hc hΦ] at htail
  rw [inner_bandOperatorL2_bandClass, norm_sq_bandClass]
  linarith

/-- The band quadratic form is continuous in the class. -/
theorem continuous_inner_bandOperatorL2 (c : ℝ) :
    Continuous fun f : RealIntervalL2 (-1 : ℝ) 1 =>
      (inner ℝ (bandOperatorL2 c f) f : ℝ) := by
  have h : Continuous fun f : RealIntervalL2 (-1 : ℝ) 1 =>
      ((bandOperatorL2 c f, f) : RealIntervalL2 (-1 : ℝ) 1 × RealIntervalL2 (-1 : ℝ) 1) :=
    (bandOperatorL2 c).continuous.prodMk continuous_id
  exact continuous_inner.comp h

/-- A property of `L²` classes that is closed and holds on the continuous ones holds on all of them. -/
theorem forall_of_continuous_of_isClosed {P : RealIntervalL2 (-1 : ℝ) 1 → Prop}
    (hclosed : IsClosed {f | P f})
    (hcont : ∀ (Φ : ℝ → ℝ) (hΦ : Continuous Φ), P (bandClass Φ hΦ))
    (f : RealIntervalL2 (-1 : ℝ) 1) : P f := by
  have hsub : Set.range
      (ContinuousMap.toLp (E := ℝ) 2 (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ℝ)
      ⊆ {f | P f} := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨Φ, hΦ, hEq⟩ := exists_continuous_bandClass_eq g
    rw [← hEq]
    exact hcont Φ hΦ
  have hclos : closure (Set.range
      (ContinuousMap.toLp (E := ℝ) 2 (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ℝ))
      ⊆ {f | P f} := hclosed.closure_subset_iff.mpr hsub
  rw [(denseRange_toLp_interval (-1 : ℝ) 1).closure_range] at hclos
  exact hclos (Set.mem_univ f)

/-- **The band form is nonnegative on every `L²` class.** -/
theorem inner_bandOperatorL2_nonneg {c : ℝ} (hc : 0 < c) (f : RealIntervalL2 (-1 : ℝ) 1) :
    0 ≤ (inner ℝ (bandOperatorL2 c f) f : ℝ) := by
  refine forall_of_continuous_of_isClosed
    (P := fun f => 0 ≤ (inner ℝ (bandOperatorL2 c f) f : ℝ)) ?_ ?_ f
  · exact isClosed_le continuous_const (continuous_inner_bandOperatorL2 c)
  · intro Φ hΦ
    rw [inner_bandOperatorL2_bandClass]
    exact double_integral_sincKernel_nonneg hc.le hΦ

/-- **The band form is at most the energy on every `L²` class.**  The band operator is a positive
contraction: no class carries more spectral mass inside the window than it has in total. -/
theorem inner_bandOperatorL2_le_norm_sq {c : ℝ} (hc : 0 < c) (f : RealIntervalL2 (-1 : ℝ) 1) :
    (inner ℝ (bandOperatorL2 c f) f : ℝ) ≤ ‖f‖ ^ 2 := by
  refine forall_of_continuous_of_isClosed
    (P := fun f => (inner ℝ (bandOperatorL2 c f) f : ℝ) ≤ ‖f‖ ^ 2) ?_ ?_ f
  · exact isClosed_le (continuous_inner_bandOperatorL2 c) (continuous_norm.pow 2)
  · intro Φ hΦ
    exact inner_bandOperatorL2_bandClass_le hc Φ hΦ

/-! ## The operator norm -/

/-- **The band operator is a contraction.**  For a symmetric operator the norm is the supremum of the
absolute Rayleigh quotients, and every band Rayleigh quotient lies in `[0, 1]`. -/
theorem norm_bandOperatorL2_le_one {c : ℝ} (hc : 0 < c) : ‖bandOperatorL2 c‖ ≤ 1 := by
  have hsym : ((bandOperatorL2 c : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1) :
      RealIntervalL2 (-1 : ℝ) 1 →ₗ[ℝ] RealIntervalL2 (-1 : ℝ) 1).IsSymmetric := fun f g =>
    bandOperatorL2_symmetric c f g
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hsym]
  refine ciSup_le fun f => ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hpos : 0 < ‖f‖ ^ 2 := by
    have : 0 < ‖f‖ := norm_pos_iff.mpr hf
    positivity
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real, abs_div, abs_of_pos hpos, div_le_one hpos,
    abs_of_nonneg (inner_bandOperatorL2_nonneg hc f)]
  exact inner_bandOperatorL2_le_norm_sq hc f

/-- **The two-sided aperture estimate for the band norm.** -/
theorem abs_one_sub_norm_bandOperatorL2_le {c : ℝ} (hc : 1 ≤ c) :
    |1 - ‖bandOperatorL2 c‖| ≤ 64 * c ^ 2 * Real.exp (-(2 * c)) := by
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hup := one_sub_norm_bandOperatorL2_le_exp hc
  have hle := norm_bandOperatorL2_le_one hcpos
  rw [abs_le]
  refine ⟨?_, hup⟩
  have hpos : (0 : ℝ) ≤ 64 * c ^ 2 * Real.exp (-(2 * c)) := by positivity
  linarith

/-- The polynomial-times-exponential factor of the envelope vanishes at large aperture. -/
theorem tendsto_envelope_atTop :
    Filter.Tendsto (fun c : ℝ => 64 * c ^ 2 * Real.exp (-(2 * c))) Filter.atTop (nhds 0) := by
  have hmul : Filter.Tendsto (fun c : ℝ => 2 * c) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨max b 0, fun c hc => ?_⟩
    have h1 : b ≤ c := le_trans (le_max_left b 0) hc
    have h2 : (0 : ℝ) ≤ c := le_trans (le_max_right b 0) hc
    linarith
  have hbase : Filter.Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hcomp : Filter.Tendsto (fun c : ℝ => (2 * c) ^ 2 * Real.exp (-(2 * c))) Filter.atTop
      (nhds 0) := hbase.comp hmul
  have hscaled : Filter.Tendsto
      (fun c : ℝ => (16 : ℝ) * ((2 * c) ^ 2 * Real.exp (-(2 * c)))) Filter.atTop (nhds 0) := by
    have := hcomp.const_mul (16 : ℝ)
    simpa using this
  refine hscaled.congr fun c => ?_
  ring

/-- **The band norm tends to one.**  The leakage envelope squeezes it between `1 - 64 c² e^(-2c)` and
`1`: at large aperture the band operator is asymptotically the identity on its own scale. -/
theorem tendsto_norm_bandOperatorL2_atTop :
    Filter.Tendsto (fun c : ℝ => ‖bandOperatorL2 c‖) Filter.atTop (nhds 1) := by
  have hlow : Filter.Tendsto (fun c : ℝ => 1 - 64 * c ^ 2 * Real.exp (-(2 * c)))
      Filter.atTop (nhds 1) := by
    have h := tendsto_envelope_atTop
    have := (tendsto_const_nhds (α := ℝ) (x := (1 : ℝ)) (f := Filter.atTop)).sub h
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with c hc
    have := one_sub_norm_bandOperatorL2_le_exp hc
    linarith
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with c hc
    exact norm_bandOperatorL2_le_one hc

end GaloisForLFunctions.RHTower

end

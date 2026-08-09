import GaloisForLFunctions.HTGeometry.CriticalEulerMassWeilStokesShadowLaw
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Distributions MeasureTheory Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem testFunction_lineDeriv_one_eq_deriv
    (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (x : ℝ) :
    lineDeriv ℝ (f : ℝ → ℝ) x 1 = deriv (f : ℝ → ℝ) x := by
  rw [(f.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    fderiv_eq_smul_deriv]
  simp

theorem testFunction_lineDerivCLM_one_apply
    (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (x : ℝ) :
    (TestFunction.lineDerivCLM ℝ (1 : ℝ) f :
      𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) x = deriv (f : ℝ → ℝ) x := by
  rw [TestFunction.lineDerivCLM_apply]
  simp only [le_top, if_true]
  exact testFunction_lineDeriv_one_eq_deriv f x

noncomputable def positiveRampDistribution (a : ℝ) :
    𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
  TestFunction.integralAgainstBilinCLM
    (ContinuousLinearMap.mul ℝ ℝ) (volume.restrict (Ioi a)) (fun x : ℝ => x - a)

theorem rampWeight_locallyIntegrableOn (a : ℝ) :
    LocallyIntegrableOn (fun x : ℝ => x - a)
      ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ) (volume.restrict (Ioi a)) := by
  exact ((continuous_id.sub continuous_const).locallyIntegrable).locallyIntegrableOn _

@[simp] theorem positiveRampDistribution_apply
    (a : ℝ) (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    positiveRampDistribution a f = ∫ x in Ioi a, f x * (x - a) := by
  classical
  rw [positiveRampDistribution]
  change (if LocallyIntegrableOn (fun x : ℝ => x - a)
      ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ) (volume.restrict (Ioi a))
    then ∫ x, (ContinuousLinearMap.mul ℝ ℝ) (f x) (x - a) ∂(volume.restrict (Ioi a))
    else 0) = _
  rw [if_pos (rampWeight_locallyIntegrableOn a)]
  rfl

theorem testFunction_second_derivative_ramp_integral
    (a : ℝ) (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    (∫ x in Ioi a, deriv (deriv (f : ℝ → ℝ)) x * (x - a)) = f a := by
  have hfDerivSmooth := (contDiff_infty_iff_deriv.mp f.contDiff).2
  have hfSecondSmooth := (contDiff_infty_iff_deriv.mp hfDerivSmooth).2
  have huv' : IntegrableOn
      (fun x : ℝ => (x - a) * deriv (deriv (f : ℝ → ℝ)) x) (Ioi a) := by
    exact ((continuous_id.sub continuous_const).mul hfSecondSmooth.continuous)
      |>.integrable_of_hasCompactSupport (f.hasCompactSupport.deriv.deriv.mul_left)
      |>.integrableOn
  have hu'v : IntegrableOn (fun x : ℝ => (1 : ℝ) * deriv (f : ℝ → ℝ) x) (Ioi a) := by
    simpa only [one_mul] using (hfDerivSmooth.continuous
      |>.integrable_of_hasCompactSupport f.hasCompactSupport.deriv
      |>.integrableOn)
  have hzero : Tendsto
      (fun x : ℝ => (x - a) * deriv (f : ℝ → ℝ) x) (𝓝[>] a) (𝓝 0) := by
    have hcont : ContinuousAt
        (fun x : ℝ => (x - a) * deriv (f : ℝ → ℝ) x) a :=
      (continuousAt_id.sub continuousAt_const).mul hfDerivSmooth.continuous.continuousAt
    have ht : Tendsto (fun x : ℝ => (x - a) * deriv (f : ℝ → ℝ) x)
        (nhdsWithin a (Ioi a)) (𝓝 ((a - a) * deriv (f : ℝ → ℝ) a)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using ht
  have hsupp : HasCompactSupport
      (fun x : ℝ => (x - a) * deriv (f : ℝ → ℝ) x) :=
    f.hasCompactSupport.deriv.mul_left
  have hinfty : Tendsto
      (fun x : ℝ => (x - a) * deriv (f : ℝ → ℝ) x) atTop (𝓝 0) := by
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hsupp
    exact hsupp.filter_mono atTop_le_cocompact |>.tendsto
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := a) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun x : ℝ => x - a) (u' := fun _ => (1 : ℝ))
    (v := deriv (f : ℝ → ℝ)) (v' := deriv (deriv (f : ℝ → ℝ)))
    (fun x _ => (hasDerivAt_id x).sub_const a)
    (fun x _ => (hfDerivSmooth.differentiable (by simp) x).hasDerivAt)
    huv' hu'v hzero hinfty
  calc
    (∫ x in Ioi a, deriv (deriv (f : ℝ → ℝ)) x * (x - a)) =
        ∫ x in Ioi a, (x - a) * deriv (deriv (f : ℝ → ℝ)) x := by
      congr 1
      funext x
      ring
    _ = (0 : ℝ) - 0 - ∫ x in Ioi a, (1 : ℝ) * deriv (f : ℝ → ℝ) x := hibp
    _ = f a := by
      rw [show (fun x : ℝ => (1 : ℝ) * deriv (f : ℝ → ℝ) x) =
        deriv (f : ℝ → ℝ) by funext x; simp]
      rw [f.hasCompactSupport.integral_Ioi_deriv_eq (f.contDiff.of_le (by simp))]
      ring

theorem positiveRampDistribution_secondDerivative (a : ℝ) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
          (positiveRampDistribution a)) =
      (Distribution.delta a : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ)) := by
  ext f
  rw [Distribution.lineDerivCLM_apply, Distribution.lineDerivCLM_apply]
  simp only [neg_neg]
  rw [positiveRampDistribution_apply, Distribution.delta_apply]
  have hfirst :
      (fun x : ℝ => (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) f :
        𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) x) = deriv (f : ℝ → ℝ) := by
    funext x
    exact testFunction_lineDerivCLM_one_apply f x
  have hsecond :
      (fun x : ℝ => (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ)
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) f) :
          𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) x) =
        deriv (deriv (f : ℝ → ℝ)) := by
    funext x
    rw [testFunction_lineDerivCLM_one_apply]
    congr 1
  calc
    (∫ x in Ioi a, (TestFunction.lineDerivCLM ℝ (1 : ℝ)
        (TestFunction.lineDerivCLM ℝ (1 : ℝ) f) :
          𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) x * (x - a)) =
        ∫ x in Ioi a, deriv (deriv (f : ℝ → ℝ)) x * (x - a) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [congrFun hsecond x]
    _ = f a := testFunction_second_derivative_ramp_integral a f

theorem positiveRampDistribution_apply_eq_integral_max
    (a : ℝ) (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    positiveRampDistribution a f = ∫ x, f x * max (x - a) 0 := by
  rw [positiveRampDistribution_apply]
  calc
    (∫ x in Ioi a, f x * (x - a)) =
        ∫ x in Ioi a, f x * max (x - a) 0 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [max_eq_left (sub_nonneg.mpr hx.le)]
    _ = ∫ x, f x * max (x - a) 0 :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (by
        intro x hx
        rw [Set.mem_Ioi, not_lt] at hx
        rw [max_eq_right (sub_nonpos.mpr hx), mul_zero])

noncomputable def apertureCompactUpperBound (K : TopologicalSpace.Compacts ℝ) : ℝ :=
  Classical.choose K.isCompact.bddAbove

theorem apertureCompactUpperBound_spec (K : TopologicalSpace.Compacts ℝ)
    {x : ℝ} (hx : x ∈ (K : Set ℝ)) : x ≤ apertureCompactUpperBound K :=
  (Classical.choose_spec K.isCompact.bddAbove) hx

theorem positiveRampIndices_finite (K : TopologicalSpace.Compacts ℝ) :
    Set.Finite {n : ℕ | 2 ≤ n ∧
      Real.log (n : ℝ) ∈ Set.Icc 0 (max 0 (apertureCompactUpperBound K))} :=
  (positiveAtomicLocations_interval_finite 0
    (max 0 (apertureCompactUpperBound K))).subset (fun _ hn => hn.2)

noncomputable def positiveRampIndices (K : TopologicalSpace.Compacts ℝ) : Finset ℕ :=
  (positiveRampIndices_finite K).toFinset

@[simp] theorem mem_positiveRampIndices
    (K : TopologicalSpace.Compacts ℝ) (n : ℕ) :
    n ∈ positiveRampIndices K ↔
      2 ≤ n ∧ Real.log (n : ℝ) ∈
        Set.Icc 0 (max 0 (apertureCompactUpperBound K)) := by
  rw [positiveRampIndices, Set.Finite.mem_toFinset]
  rfl

theorem positiveRampDistribution_ofSupportedIn_eq_zero
    (K : TopologicalSpace.Compacts ℝ)
    (Ksub : (K : Set ℝ) ⊆ ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))
    (f : 𝓓_{K}(ℝ, ℝ)) {a : ℝ}
    (ha : max 0 (apertureCompactUpperBound K) < a) :
    positiveRampDistribution a (TestFunction.ofSupportedIn Ksub f) = 0 := by
  rw [positiveRampDistribution_apply]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  by_cases hfx : f x = 0
  · simp [hfx]
  · have hxK : x ∈ (K : Set ℝ) := f.support_subset hfx
    have hxUpper := apertureCompactUpperBound_spec K hxK
    have hUpperMax : apertureCompactUpperBound K ≤ max 0 (apertureCompactUpperBound K) :=
      le_max_right _ _
    exfalso
    exact (not_lt_of_ge (hxUpper.trans hUpperMax)) (ha.trans hx)

noncomputable def positiveRampProfileDistribution (c : ℕ → ℝ) :
    𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
  TestFunction.limitCLM ℝ
    (fun f => ∑ᶠ n : ℕ,
      if 2 ≤ n then c n * positiveRampDistribution (Real.log (n : ℝ)) f else 0)
    (fun K Ksub =>
      { toFun := fun f => ∑ n ∈ positiveRampIndices K,
          c n * positiveRampDistribution (Real.log (n : ℝ))
            (TestFunction.ofSupportedIn Ksub f)
        map_add' := by
          intro f g
          have hadd : TestFunction.ofSupportedIn Ksub (f + g) =
              TestFunction.ofSupportedIn Ksub f + TestFunction.ofSupportedIn Ksub g := rfl
          rw [hadd]
          simp only [map_add, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r f
          simp only [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          have hsmul : TestFunction.ofSupportedIn Ksub (r • f) =
              r • TestFunction.ofSupportedIn Ksub f := rfl
          rw [hsmul, map_smul]
          simp only [RingHom.id_apply, smul_eq_mul]
          ring
        cont := by fun_prop })
    (by
      intro K Ksub f
      change (∑ᶠ n : ℕ, if 2 ≤ n then
          c n * positiveRampDistribution (Real.log (n : ℝ))
            (TestFunction.ofSupportedIn Ksub f) else 0) =
        ∑ n ∈ positiveRampIndices K,
          c n * positiveRampDistribution (Real.log (n : ℝ))
            (TestFunction.ofSupportedIn Ksub f)
      calc
        (∑ᶠ n : ℕ, if 2 ≤ n then
            c n * positiveRampDistribution (Real.log (n : ℝ))
              (TestFunction.ofSupportedIn Ksub f) else 0) =
            ∑ n ∈ positiveRampIndices K, if 2 ≤ n then
              c n * positiveRampDistribution (Real.log (n : ℝ))
                (TestFunction.ofSupportedIn Ksub f) else 0 := by
          apply finsum_eq_finsetSum_of_support_subset
          intro n hn
          change n ∈ positiveRampIndices K
          rw [mem_positiveRampIndices]
          simp only [Function.mem_support, ne_eq] at hn
          by_cases hn2 : 2 ≤ n
          · refine ⟨hn2, Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)), ?_⟩
            by_contra hnot
            have hgt : max 0 (apertureCompactUpperBound K) < Real.log (n : ℝ) :=
              lt_of_not_ge hnot
            exact hn (by
              simp only [if_pos hn2]
              rw [positiveRampDistribution_ofSupportedIn_eq_zero K Ksub f hgt, mul_zero])
          · exact (hn (by simp only [if_neg hn2])).elim
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [if_pos (mem_positiveRampIndices K n |>.mp hn).1])

@[simp] theorem positiveRampProfileDistribution_apply
    (c : ℕ → ℝ) (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    positiveRampProfileDistribution c f =
      ∑ᶠ n : ℕ, if 2 ≤ n then
        c n * positiveRampDistribution (Real.log (n : ℝ)) f else 0 := rfl

def positiveRampProfileFunction (c : ℕ → ℝ) (L : ℝ) : ℝ :=
  ∑ᶠ n : ℕ, if 2 ≤ n then c n * max (L - Real.log (n : ℝ)) 0 else 0

theorem positiveRampProfileFunction_support_finite (c : ℕ → ℝ) (L : ℝ) :
    (Function.support fun n : ℕ => if 2 ≤ n then
      c n * max (L - Real.log (n : ℝ)) 0 else 0).Finite := by
  refine (positiveAtomicLocations_interval_finite 0 L).subset ?_
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  by_cases hn2 : 2 ≤ n
  · constructor
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    · have hmax : max (L - Real.log (n : ℝ)) 0 ≠ 0 := by
        intro hz
        exact hn (by simp only [if_pos hn2, hz, mul_zero])
      have hpos : 0 < L - Real.log (n : ℝ) := by
        by_contra hnot
        apply hmax
        exact max_eq_right (le_of_not_gt hnot)
      linarith
  · exact (hn (by simp only [if_neg hn2])).elim

theorem positiveRampLocalIndices_finite (L : ℝ) :
    Set.Finite {n : ℕ | 2 ≤ n ∧
      Real.log (n : ℝ) ∈ Set.Icc 0 (L + 1)} :=
  (positiveAtomicLocations_interval_finite 0 (L + 1)).subset (fun _ hn => hn.2)

noncomputable def positiveRampLocalIndices (L : ℝ) : Finset ℕ :=
  (positiveRampLocalIndices_finite L).toFinset

@[simp] theorem mem_positiveRampLocalIndices (L : ℝ) (n : ℕ) :
    n ∈ positiveRampLocalIndices L ↔
      2 ≤ n ∧ Real.log (n : ℝ) ∈ Set.Icc 0 (L + 1) := by
  rw [positiveRampLocalIndices, Set.Finite.mem_toFinset]
  rfl

/-- Every profile is locally a finite sum of affine ramps. This is the precise local
piecewise-linearity assertion at the logarithmic knot set. -/
theorem positiveRampProfileFunction_eventuallyEq_finset (c : ℕ → ℝ) (L : ℝ) :
    positiveRampProfileFunction c =ᶠ[𝓝 L]
      fun x => ∑ n ∈ positiveRampLocalIndices L,
        c n * max (x - Real.log (n : ℝ)) 0 := by
  filter_upwards [Iio_mem_nhds (show L < L + 1 by linarith)] with x hx
  rw [positiveRampProfileFunction]
  calc
    (∑ᶠ n : ℕ, if 2 ≤ n then
        c n * max (x - Real.log (n : ℝ)) 0 else 0) =
        ∑ n ∈ positiveRampLocalIndices L, if 2 ≤ n then
          c n * max (x - Real.log (n : ℝ)) 0 else 0 := by
      apply finsum_eq_finsetSum_of_support_subset
      intro n hn
      change n ∈ positiveRampLocalIndices L
      rw [mem_positiveRampLocalIndices]
      simp only [Function.mem_support, ne_eq] at hn
      by_cases hn2 : 2 ≤ n
      · refine ⟨hn2, Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)), ?_⟩
        by_contra hnot
        have hgt : L + 1 < Real.log (n : ℝ) := lt_of_not_ge hnot
        have hxlt : x < L + 1 := hx
        have hnonpos : x - Real.log (n : ℝ) ≤ 0 := by linarith
        exact hn (by simp only [if_pos hn2, max_eq_right hnonpos, mul_zero])
      · exact (hn (by simp only [if_neg hn2])).elim
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [if_pos (mem_positiveRampLocalIndices L n |>.mp hn).1]

theorem continuous_positiveRampProfileFunction (c : ℕ → ℝ) :
    Continuous (positiveRampProfileFunction c) := by
  rw [continuous_iff_continuousAt]
  intro L
  have hfinite : ContinuousAt
      (fun x : ℝ => ∑ n ∈ positiveRampLocalIndices L,
        c n * max (x - Real.log (n : ℝ)) 0) L := by fun_prop
  exact hfinite.congr_of_eventuallyEq (positiveRampProfileFunction_eventuallyEq_finset c L)

theorem positiveRampProfileDistribution_apply_eq_integral
    (c : ℕ → ℝ) (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    positiveRampProfileDistribution c f =
      ∫ x, f x * positiveRampProfileFunction c x := by
  let K : TopologicalSpace.Compacts ℝ := ⟨tsupport f, f.hasCompactSupport⟩
  have Ksub : (K : Set ℝ) ⊆ ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ) := f.tsupport_subset
  let fK : 𝓓_{K}(ℝ, ℝ) :=
    ContDiffMapSupportedIn.of_support_subset f.contDiff subset_closure
  have hOf : TestFunction.ofSupportedIn Ksub fK = f := by
    ext x
    rfl
  have hleft : positiveRampProfileDistribution c f =
      ∑ n ∈ positiveRampIndices K,
        c n * positiveRampDistribution (Real.log (n : ℝ)) f := by
    rw [positiveRampProfileDistribution_apply]
    calc
      (∑ᶠ n : ℕ, if 2 ≤ n then
          c n * positiveRampDistribution (Real.log (n : ℝ)) f else 0) =
          ∑ n ∈ positiveRampIndices K, if 2 ≤ n then
            c n * positiveRampDistribution (Real.log (n : ℝ)) f else 0 := by
        apply finsum_eq_finsetSum_of_support_subset
        intro n hn
        change n ∈ positiveRampIndices K
        rw [mem_positiveRampIndices]
        simp only [Function.mem_support, ne_eq] at hn
        by_cases hn2 : 2 ≤ n
        · refine ⟨hn2, Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)), ?_⟩
          by_contra hnot
          have hgt : max 0 (apertureCompactUpperBound K) < Real.log (n : ℝ) :=
            lt_of_not_ge hnot
          have hz := positiveRampDistribution_ofSupportedIn_eq_zero K Ksub fK hgt
          rw [hOf] at hz
          exact hn (by simp only [if_pos hn2, hz, mul_zero])
        · exact (hn (by simp only [if_neg hn2])).elim
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos (mem_positiveRampIndices K n |>.mp hn).1]
  have hpoint : (fun x : ℝ => f x * positiveRampProfileFunction c x) =
      fun x => ∑ n ∈ positiveRampIndices K,
        c n * (f x * max (x - Real.log (n : ℝ)) 0) := by
    funext x
    rw [positiveRampProfileFunction, mul_finsum]
    calc
      (∑ᶠ n : ℕ, f x * if 2 ≤ n then
          c n * max (x - Real.log (n : ℝ)) 0 else 0) =
          ∑ n ∈ positiveRampIndices K, f x * if 2 ≤ n then
            c n * max (x - Real.log (n : ℝ)) 0 else 0 := by
        apply finsum_eq_finsetSum_of_support_subset
        intro n hn
        change n ∈ positiveRampIndices K
        rw [mem_positiveRampIndices]
        simp only [Function.mem_support, ne_eq] at hn
        by_cases hn2 : 2 ≤ n
        · refine ⟨hn2, Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)), ?_⟩
          by_contra hnot
          have hgt : max 0 (apertureCompactUpperBound K) < Real.log (n : ℝ) :=
            lt_of_not_ge hnot
          by_cases hfx : f x = 0
          · exact hn (by simp only [hfx, zero_mul])
          · have hxK : x ∈ (K : Set ℝ) := by
              change x ∈ tsupport (f : ℝ → ℝ)
              exact subset_closure hfx
            have hxUpper := apertureCompactUpperBound_spec K hxK
            have hle : x ≤ max 0 (apertureCompactUpperBound K) :=
              hxUpper.trans (le_max_right _ _)
            have hxlog : x - Real.log (n : ℝ) ≤ 0 := by linarith
            exact hn (by simp only [if_pos hn2, max_eq_right hxlog, mul_zero])
        · exact (hn (by simp only [if_neg hn2, mul_zero])).elim
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos (mem_positiveRampIndices K n |>.mp hn).1]
        ring
  rw [hleft, hpoint]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [positiveRampDistribution_apply_eq_integral_max]
    rw [← MeasureTheory.integral_const_mul]
  · intro n hn
    have hcont : Continuous (fun x : ℝ =>
        c n * (f x * max (x - Real.log (n : ℝ)) 0)) := by fun_prop
    have hsupp : HasCompactSupport (fun x : ℝ =>
        c n * (f x * max (x - Real.log (n : ℝ)) 0)) :=
      f.hasCompactSupport.mul_right.mul_left
    exact hcont.integrable_of_hasCompactSupport hsupp

theorem positiveAtomicIndices_finiteR (K : TopologicalSpace.Compacts ℝ) :
    Set.Finite {n : ℕ | 2 ≤ n ∧ Real.log (n : ℝ) ∈ (K : Set ℝ)} := by
  obtain ⟨b, hb⟩ := K.isCompact.bddAbove
  refine (positiveAtomicLocations_interval_finite 0 b).subset ?_
  intro n hn
  rcases hn with ⟨hn2, hnK⟩
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  exact ⟨Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)), hb hnK⟩

noncomputable def positiveAtomicIndicesR (K : TopologicalSpace.Compacts ℝ) : Finset ℕ :=
  (positiveAtomicIndices_finiteR K).toFinset

@[simp] theorem mem_positiveAtomicIndicesR
    (K : TopologicalSpace.Compacts ℝ) (n : ℕ) :
    n ∈ positiveAtomicIndicesR K ↔
      2 ≤ n ∧ Real.log (n : ℝ) ∈ (K : Set ℝ) := by
  rw [positiveAtomicIndicesR, Set.Finite.mem_toFinset]
  rfl

noncomputable def positiveAtomicDistributionR (c : ℕ → ℝ) :
    𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
  TestFunction.limitCLM ℝ
    (fun f => ∑ᶠ n : ℕ, if 2 ≤ n then c n * f (Real.log (n : ℝ)) else 0)
    (fun K _ =>
      { toFun := fun f => ∑ n ∈ positiveAtomicIndicesR K,
          c n * f (Real.log (n : ℝ))
        map_add' := by
          intro f g
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r f
          simp only [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          simp
          ring
        cont := by fun_prop })
    (by
      intro K Ksub f
      change (∑ᶠ n : ℕ, if 2 ≤ n then c n * f (Real.log (n : ℝ)) else 0) =
        ∑ n ∈ positiveAtomicIndicesR K, c n * f (Real.log (n : ℝ))
      calc
        (∑ᶠ n : ℕ, if 2 ≤ n then c n * f (Real.log (n : ℝ)) else 0) =
            ∑ n ∈ positiveAtomicIndicesR K,
              if 2 ≤ n then c n * f (Real.log (n : ℝ)) else 0 := by
          apply finsum_eq_finsetSum_of_support_subset
          intro n hn
          change n ∈ positiveAtomicIndicesR K
          rw [mem_positiveAtomicIndicesR]
          simp only [Function.mem_support, ne_eq] at hn
          by_cases hn2 : 2 ≤ n
          · constructor
            · exact hn2
            · apply f.support_subset
              intro hz
              exact hn (by simp only [if_pos hn2, hz, mul_zero])
          · exact (hn (by simp only [if_neg hn2])).elim
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [if_pos (mem_positiveAtomicIndicesR K n |>.mp hn).1])

@[simp] theorem positiveAtomicDistributionR_apply
    (c : ℕ → ℝ) (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    positiveAtomicDistributionR c f =
      ∑ᶠ n : ℕ, if 2 ≤ n then c n * f (Real.log (n : ℝ)) else 0 := rfl

theorem positiveRampProfileDistribution_secondDerivative (c : ℕ → ℝ) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
          (positiveRampProfileDistribution c)) =
      positiveAtomicDistributionR c := by
  ext f
  rw [Distribution.lineDerivCLM_apply, Distribution.lineDerivCLM_apply]
  simp only [neg_neg, positiveRampProfileDistribution_apply,
    positiveAtomicDistributionR_apply]
  apply finsum_congr
  intro n
  by_cases hn : 2 ≤ n
  · simp only [if_pos hn]
    congr 1
    have h := congrArg
      (fun T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) => T f)
      (positiveRampDistribution_secondDerivative (Real.log (n : ℝ)))
    simpa only [Distribution.lineDerivCLM_apply, neg_neg,
      Distribution.delta_apply] using h
  · simp only [if_neg hn]

/-! ## Exact Route-L odd-current hinge transform -/

def oddAtomicHinge (L t : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * max (L - |t|) 0 * Real.sinh t

def suzukiApertureProfile (w : ℕ → ℝ) (L : ℝ) : ℝ :=
  ∑ᶠ n : ℕ, if 2 ≤ n then
    w n * Real.sinh (Real.log (n : ℝ)) * max (L - Real.log (n : ℝ)) 0 else 0

def reflectedOddAtomicPairing (w : ℕ → ℝ) (phi : ℝ → ℝ) : ℝ :=
  ∑ᶠ n : ℕ, if 2 ≤ n then
    -w n * (phi (Real.log (n : ℝ)) - phi (-Real.log (n : ℝ))) else 0

theorem oddAtomicHinge_difference {n : ℕ} (hn : 2 ≤ n) (L : ℝ) :
    oddAtomicHinge L (Real.log (n : ℝ)) - oddAtomicHinge L (-Real.log (n : ℝ)) =
      -max (L - Real.log (n : ℝ)) 0 * Real.sinh (Real.log (n : ℝ)) := by
  have hnlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [oddAtomicHinge, oddAtomicHinge, abs_of_pos hnlog, abs_neg, abs_of_pos hnlog,
    Real.sinh_neg]
  ring

/-- Paper Theorem 2.1, strengthened to every real aperture because both sides vanish correctly
outside the positive normalized chamber. -/
theorem reflectedOddAtomicPairing_hinge (w : ℕ → ℝ) (L : ℝ) :
    reflectedOddAtomicPairing w (oddAtomicHinge L) = suzukiApertureProfile w L := by
  apply finsum_congr
  intro n
  by_cases hn : 2 ≤ n
  · simp only [if_pos hn]
    rw [oddAtomicHinge_difference hn]
    ring
  · simp only [if_neg hn]

theorem suzukiApertureProfile_eq_positiveRampProfileFunction (w : ℕ → ℝ) :
    suzukiApertureProfile w =
      positiveRampProfileFunction (fun n => w n * Real.sinh (Real.log (n : ℝ))) := by
  funext L
  apply finsum_congr
  intro n
  by_cases hn : 2 ≤ n <;> simp [hn]

noncomputable def suzukiApertureProfileDistribution (w : ℕ → ℝ) :
    𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
  positiveRampProfileDistribution (fun n => w n * Real.sinh (Real.log (n : ℝ)))

/-- The locally finite profile distribution is literally integration against paper formula (3). -/
theorem suzukiApertureProfileDistribution_apply
    (w : ℕ → ℝ) (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    suzukiApertureProfileDistribution w f =
      ∫ L, f L * suzukiApertureProfile w L := by
  rw [suzukiApertureProfileDistribution,
    positiveRampProfileDistribution_apply_eq_integral,
    suzukiApertureProfile_eq_positiveRampProfileFunction]

/-- Paper equation (5): exact distributional second derivative of the full locally finite profile. -/
theorem suzukiApertureProfileDistribution_secondDerivative (w : ℕ → ℝ) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
          (suzukiApertureProfileDistribution w)) =
      positiveAtomicDistributionR (fun n =>
        w n * Real.sinh (Real.log (n : ℝ))) :=
  positiveRampProfileDistribution_secondDerivative _

/-! ## Normalized coefficient-space isomorphism -/

abbrev ApertureAtom := {n : ℕ // 2 ≤ n}

def apertureAtomLocation (n : ApertureAtom) : ℝ := Real.log (n : ℕ)

theorem apertureAtomLocation_pos (n : ApertureAtom) : 0 < apertureAtomLocation n := by
  exact Real.log_pos (by exact_mod_cast (show 1 < (n : ℕ) by omega))

theorem sinh_apertureAtomLocation_ne_zero (n : ApertureAtom) :
    Real.sinh (apertureAtomLocation n) ≠ 0 := by
  rw [Real.sinh_ne_zero]
  exact ne_of_gt (apertureAtomLocation_pos n)

/-- Paper Theorem 3.1 in its exact normalized slope-jump coordinates. The inverse divides each
atomic mass by the nonzero `sinh(log n)` factor. -/
noncomputable def apertureMassEquiv :
    (ApertureAtom → ℝ) ≃ₗ[ℝ] (ApertureAtom → ℝ) where
  toFun w n := w n * Real.sinh (apertureAtomLocation n)
  invFun m n := m n / Real.sinh (apertureAtomLocation n)
  left_inv w := by
    funext n
    exact mul_div_cancel_right₀ (w n) (sinh_apertureAtomLocation_ne_zero n)
  right_inv m := by
    funext n
    exact div_mul_cancel₀ (m n) (sinh_apertureAtomLocation_ne_zero n)
  map_add' w v := by
    funext n
    simp only [Pi.add_apply]
    ring
  map_smul' r w := by
    funext n
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem apertureMassEquiv_apply (w : ApertureAtom → ℝ) (n : ApertureAtom) :
    apertureMassEquiv w n = w n * Real.sinh (apertureAtomLocation n) := rfl

@[simp] theorem apertureMassEquiv_symm_apply (m : ApertureAtom → ℝ) (n : ApertureAtom) :
    apertureMassEquiv.symm m n = m n / Real.sinh (apertureAtomLocation n) := rfl

abbrev OddAtomicCoefficientSpace := ApertureAtom → ℝ

abbrev NormalizedApertureProfileSpace := ApertureAtom → ℝ

/-- Closed bijection `A → P` after removing the affine kernel by the paper normalization. -/
noncomputable def normalizedHingeTransform :
    OddAtomicCoefficientSpace ≃ₗ[ℝ] NormalizedApertureProfileSpace := apertureMassEquiv

def extendApertureMass (m : NormalizedApertureProfileSpace) (n : ℕ) : ℝ :=
  if hn : 2 ≤ n then m ⟨n, hn⟩ else 0

def normalizedApertureProfileFunction (m : NormalizedApertureProfileSpace) : ℝ → ℝ :=
  positiveRampProfileFunction (extendApertureMass m)

noncomputable def normalizedApertureProfileDistribution
    (m : NormalizedApertureProfileSpace) :
    𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
  positiveRampProfileDistribution (extendApertureMass m)

theorem normalizedApertureProfileDistribution_apply
    (m : NormalizedApertureProfileSpace)
    (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    normalizedApertureProfileDistribution m f =
      ∫ L, f L * normalizedApertureProfileFunction m L :=
  positiveRampProfileDistribution_apply_eq_integral _ _

theorem normalizedApertureProfileDistribution_secondDerivative
    (m : NormalizedApertureProfileSpace) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
          (normalizedApertureProfileDistribution m)) =
      positiveAtomicDistributionR (extendApertureMass m) :=
  positiveRampProfileDistribution_secondDerivative _

theorem normalizedApertureProfileFunction_vanishes_initially
    (m : NormalizedApertureProfileSpace)
    (L : {x : ℝ // 0 < x ∧ x ≤ Real.log 2}) :
    normalizedApertureProfileFunction m L = 0 := by
  unfold normalizedApertureProfileFunction positiveRampProfileFunction
  calc
    (∑ᶠ n : ℕ, if 2 ≤ n then
        extendApertureMass m n * max ((L : ℝ) - Real.log (n : ℝ)) 0 else 0) =
        ∑ᶠ _n : ℕ, (0 : ℝ) := by
      apply finsum_congr
      intro n
      by_cases hn : 2 ≤ n
      · rw [if_pos hn]
        have hlog : Real.log 2 ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hn)
        have hnonpos : (L : ℝ) - Real.log (n : ℝ) ≤ 0 := by linarith [L.prop.2]
        rw [max_eq_right hnonpos, mul_zero]
      · rw [if_neg hn]
    _ = 0 := finsum_zero

/-! ## Route-L and Mass coefficient weld -/

def oddEulerTorqueWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) / Real.sqrt n

def oddEulerTorqueAtomWeight (n : ApertureAtom) : ℝ := oddEulerTorqueWeight n

theorem routeLOddCurrent_positiveCoefficient (n : ApertureAtom) :
    (atomicPositionMul primeWeilKernel).pos n =
      -Complex.ofReal (oddEulerTorqueAtomWeight n) := by
  exact primeWeilTangent_positiveCoefficient_eq_log_div_sqrt (by omega)

theorem routeLOddCurrent_neg_eq_neg_pos (n : ApertureAtom) :
    (atomicPositionMul primeWeilKernel).neg n =
      -(atomicPositionMul primeWeilKernel).pos n := by
  rw [atomicPositionMul_primeWeilKernel]
  rfl

theorem routeLOddCurrent_negativeCoefficient (n : ApertureAtom) :
    (atomicPositionMul primeWeilKernel).neg n =
      Complex.ofReal (oddEulerTorqueAtomWeight n) := by
  rw [routeLOddCurrent_neg_eq_neg_pos, routeLOddCurrent_positiveCoefficient]
  simp

def massHalfDensityPrimeCoefficient (p : Nat.Primes) : ℝ :=
  Real.log (p : ℕ) / Real.sqrt (p : ℕ)

theorem oddEulerTorqueAtomWeight_prime (p : Nat.Primes) :
    oddEulerTorqueAtomWeight ⟨p, p.prop.two_le⟩ =
      massHalfDensityPrimeCoefficient p * Real.log (p : ℕ) := by
  rw [oddEulerTorqueAtomWeight, oddEulerTorqueWeight,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop, massHalfDensityPrimeCoefficient]
  ring

/-- Paper equation (6). -/
theorem apertureMass_massHalfDensityPrimeCoefficient (p : Nat.Primes) :
    apertureMassEquiv oddEulerTorqueAtomWeight ⟨p, p.prop.two_le⟩ =
      massHalfDensityPrimeCoefficient p * Real.log (p : ℕ) *
        Real.sinh (Real.log (p : ℕ)) := by
  rw [apertureMassEquiv_apply, oddEulerTorqueAtomWeight_prime]
  rfl

/-- Paper equation (7): exact primitive-prime Mass reconstruction. -/
theorem massHalfDensityPrimeCoefficient_reconstruction (p : Nat.Primes) :
    massHalfDensityPrimeCoefficient p =
      apertureMassEquiv oddEulerTorqueAtomWeight ⟨p, p.prop.two_le⟩ /
        (Real.log (p : ℕ) * Real.sinh (Real.log (p : ℕ))) := by
  rw [apertureMass_massHalfDensityPrimeCoefficient]
  have hpLog : Real.log (p : ℕ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast p.prop.one_lt))
  have hpSinh : Real.sinh (Real.log (p : ℕ)) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact hpLog
  field_simp

/-- Exact cross-route coefficient chain (8), with no scalar-analogy weakening. -/
theorem routeLSuzukiMass_primitivePrime_chain (p : Nat.Primes) :
    (atomicPositionMul primeWeilKernel).pos (p : ℕ) =
        -Complex.ofReal (oddEulerTorqueAtomWeight ⟨p, p.prop.two_le⟩) ∧
      apertureMassEquiv oddEulerTorqueAtomWeight ⟨p, p.prop.two_le⟩ =
        massHalfDensityPrimeCoefficient p * Real.log (p : ℕ) *
          Real.sinh (Real.log (p : ℕ)) ∧
      massHalfDensityPrimeCoefficient p =
        apertureMassEquiv oddEulerTorqueAtomWeight ⟨p, p.prop.two_le⟩ /
          (Real.log (p : ℕ) * Real.sinh (Real.log (p : ℕ))) :=
  ⟨routeLOddCurrent_positiveCoefficient ⟨p, p.prop.two_le⟩,
    apertureMass_massHalfDensityPrimeCoefficient p,
    massHalfDensityPrimeCoefficient_reconstruction p⟩

theorem primitivePrimeProjection_higherGrade_zero
    (p : Nat.Primes) (k : {j : ℕ // 2 ≤ j}) :
    primitivePrimePushforward
      (primitivePrimeClass (dirichletPointMass
        ⟨(p : ℕ) ^ (k : ℕ), pow_pos p.prop.pos (k : ℕ)⟩)) = 0 :=
  primitivePrimePushforward_pointMass_primePower_zero p k.prop

end

end GaloisForLFunctions.HTGeometry

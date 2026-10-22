import GaloisForLFunctions.RHTower.Suzuki.SuzukiHlogHilbertFormDomain
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Density of the `H^log` form domain in `L^2(-a, a)`

The `H^log(-a, a)` form domain consists of Fourier-side vectors in `L^2((1 + log⁺|ξ|) dξ)` whose
inverse Fourier transforms vanish outside the aperture `[-a, a]`. This module shows that Schwartz
functions lie in this weighted `L^2` space (since `1 + log⁺|x| ≤ 1 + |x|`), that every smooth
compactly supported real test function supported in `(-a, a)` comes from the form domain, and,
by the fundamental lemma of the calculus of variations, that the form domain embeds densely into
the aperture Hilbert space `L^2(-a, a) ⊆ L^2(ℝ)`.

## Main results

- `SchwartzMap.memLp_two_suzukiHlogMeasure`: every Schwartz function lies in
  `L^2((1 + log⁺|ξ|) dξ)`.
- `exists_suzukiHlogFormDomain_eq_smoothRealTest`: each smooth real test function with support
  in `(-a, a)` is the time-side image of a form-domain vector.
- `denseRange_suzukiHlogFormToAperture`: the form domain has dense image in `L^2(-a, a)`.

## Hypotheses

Unconditional. Test functions are assumed smooth with compact support inside `(-a, a)`; `a` is a
positive aperture.
-/

open MeasureTheory Set
open scoped ENNReal InnerProduct FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- The log weight is dominated linearly: `1 + log⁺|x| ≤ 1 + |x|`. -/
theorem suzukiLogWeight_le_one_add_abs (x : ℝ) :
    suzukiLogWeight x ≤ 1 + |x| := by
  unfold suzukiLogWeight
  have hmax : max (Real.log |x|) 0 ≤ |x| := by
    rw [max_le_iff]
    constructor
    · by_cases hx : x = 0
      · simp [hx]
      · have habs : 0 < |x| := abs_pos.mpr hx
        have hlog := Real.log_le_sub_one_of_pos habs
        linarith
    · exact abs_nonneg x
  linarith

/-- For a Schwartz function `F`, `x ↦ (1 + log⁺|x|) |F(x)|^2` is integrable. -/
theorem _root_.SchwartzMap.integrable_suzukiLogWeight_mul_norm_sq
    (F : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => suzukiLogWeight x * ‖F x‖ ^ 2) := by
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0 F
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have h0 : Integrable (fun x : ℝ => ‖F x‖) := F.integrable.norm
  have h1 : Integrable (fun x : ℝ => |x| * ‖F x‖) := by
    simpa [Real.norm_eq_abs] using F.integrable_pow_mul (volume : Measure ℝ) 1
  have hbase : Integrable (fun x : ℝ => (1 + |x|) * ‖F x‖) := by
    have hadd : Integrable
        ((fun x : ℝ => ‖F x‖) + fun x : ℝ => |x| * ‖F x‖) := h0.add h1
    exact hadd.congr (ae_of_all _ fun x => by simp [add_mul])
  have hmajor : Integrable (fun x : ℝ => C * ((1 + |x|) * ‖F x‖)) :=
    hbase.const_mul C
  refine Integrable.mono' hmajor
    (measurable_suzukiLogWeight.mul
      (F.continuous.norm.measurable.pow_const 2)).aestronglyMeasurable ?_
  filter_upwards with x
  have hC : ‖F x‖ ≤ C := SchwartzMap.norm_le_seminorm ℂ F x
  have hw := suzukiLogWeight_le_one_add_abs x
  have hn : 0 ≤ ‖F x‖ := norm_nonneg _
  have hweight : 0 ≤ suzukiLogWeight x := suzukiLogWeight_nonneg x
  have habs : 0 ≤ |x| := abs_nonneg x
  have hcalc : suzukiLogWeight x * ‖F x‖ ^ 2 ≤
      C * ((1 + |x|) * ‖F x‖) := calc
    suzukiLogWeight x * ‖F x‖ ^ 2 =
        (suzukiLogWeight x * ‖F x‖) * ‖F x‖ := by ring
    _ ≤ ((1 + |x|) * ‖F x‖) * ‖F x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw hn) hn
    _ ≤ ((1 + |x|) * ‖F x‖) * C :=
      mul_le_mul_of_nonneg_left hC (mul_nonneg (by positivity) hn)
    _ = C * ((1 + |x|) * ‖F x‖) := by ring
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hweight (sq_nonneg _)),
    abs_of_nonneg (mul_nonneg hC0 (mul_nonneg (add_nonneg zero_le_one habs) hn))] using hcalc

/-- Every Schwartz function lies in `L^2` of the log-weighted measure `(1 + log⁺|ξ|) dξ`. -/
theorem _root_.SchwartzMap.memLp_two_suzukiHlogMeasure (F : SchwartzMap ℝ ℂ) :
    MemLp (F : ℝ → ℂ) 2 suzukiHlogMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    F.continuous.aestronglyMeasurable).2
  unfold suzukiHlogMeasure
  rw [integrable_withDensity_iff_integrable_smul measurable_suzukiLogWeightNNReal]
  refine (F.integrable_suzukiLogWeight_mul_norm_sq).congr ?_
  filter_upwards with x
  rw [NNReal.smul_def, smul_eq_mul, coe_suzukiLogWeightNNReal]

def suzukiRealTestComplex (g : ℝ → ℝ) : ℝ → ℂ :=
  fun x => (g x : ℂ)

theorem contDiff_suzukiRealTestComplex {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiRealTestComplex g) := by
  exact hg.continuousLinearMap_comp Complex.ofRealCLM

theorem hasCompactSupport_suzukiRealTestComplex {g : ℝ → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (suzukiRealTestComplex g) := by
  change HasCompactSupport (Complex.ofRealCLM ∘ g)
  exact hg.comp_left (show Complex.ofRealCLM (0 : ℝ) = 0 by simp)

/-- A smooth compactly supported real function, viewed as a complex Schwartz function. -/
def suzukiRealTestSchwartz (g : ℝ → ℝ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_suzukiRealTestComplex hgsupp).toSchwartzMap
    (contDiff_suzukiRealTestComplex hgdiff)

/-- A smooth compactly supported real function, viewed as an element of `L^2(ℝ; ℂ)`. -/
def suzukiRealTestL2 (g : ℝ → ℝ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g) : SoninL2 :=
  (suzukiRealTestSchwartz g hgdiff hgsupp).toLp 2 volume

theorem suzukiRealTestL2_coeFn (g : ℝ → ℝ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g) :
    (suzukiRealTestL2 g hgdiff hgsupp : ℝ → ℂ) =ᵐ[volume]
      suzukiRealTestComplex g := by
  exact (suzukiRealTestSchwartz g hgdiff hgsupp).coeFn_toLp 2 volume

/-- The aperture Hilbert space: functions in `L^2(ℝ)` supported in `[-a, a]`. -/
abbrev suzukiApertureHilbert (a : SuzukiPositiveAperture) : Submodule ℂ SoninL2 :=
  physicalForbidden (centralInterval a.1) (measurableSet_centralInterval a.1)

/-- The form-domain embedding `H^log(-a, a) → L^2(-a, a)`, with codomain restricted to the aperture
Hilbert space. -/
def suzukiHlogFormToAperture (a : SuzukiPositiveAperture) :
    SuzukiHlogFormDomain a →L[ℂ] suzukiApertureHilbert a :=
  (suzukiHlogFormEmbedding a).codRestrict (suzukiApertureHilbert a) fun f => by
    rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
    exact ⟨suzukiHlogFormEmbedding a f,
      indicatorCutoff_suzukiHlogFormEmbedding a f⟩

@[simp] theorem suzukiHlogFormToAperture_coe
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    (suzukiHlogFormToAperture a f : SoninL2) = suzukiHlogFormEmbedding a f := rfl

/-- Every smooth compactly supported real `g` with `tsupport g ⊆ (-a, a)` is the time-side image of a
vector in the `H^log(-a, a)` form domain (namely the Fourier transform of `g`). -/
theorem exists_suzukiHlogFormDomain_eq_smoothRealTest
    (a : SuzukiPositiveAperture) (g : ℝ → ℝ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Ioo (-a.1) a.1) :
    ∃ f : SuzukiHlogFormDomain a,
      suzukiHlogFormEmbedding a f = suzukiRealTestL2 g hgdiff hgsupp := by
  let G : SchwartzMap ℝ ℂ := suzukiRealTestSchwartz g hgdiff hgsupp
  let F : SchwartzMap ℝ ℂ := 𝓕 G
  let hF : MemLp (F : ℝ → ℂ) 2 suzukiHlogMeasure :=
    F.memLp_two_suzukiHlogMeasure
  let w : SuzukiHlogFourierL2 := hF.toLp F
  have hwToL2 : suzukiHlogWeightedToL2 w = F.toLp 2 volume := by
    apply Lp.ext
    have hwFweighted : (w : ℝ → ℂ) =ᵐ[suzukiHlogMeasure] F :=
      hF.coeFn_toLp
    have hwFvolume : (w : ℝ → ℂ) =ᵐ[volume] F :=
      hwFweighted.filter_mono (ae_mono volume_le_suzukiHlogMeasure)
    filter_upwards [suzukiHlogWeightedToL2_coeFn w, hwFvolume,
      F.coeFn_toLp 2 volume] with x hw hFv hFL2
    rw [hw, hFv, hFL2]
  have htime : suzukiHlogFourierToTime w = G.toLp 2 volume := by
    apply fourierUnitary.injective
    rw [fourierUnitary_suzukiHlogFourierToTime, hwToL2]
    exact (SchwartzMap.toLp_fourier_eq G).symm
  have hfix : indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) (G.toLp 2 volume) = G.toLp 2 volume := by
    apply Lp.ext
    have hcoeG : (G.toLp 2 volume : ℝ → ℂ) =ᵐ[volume]
        suzukiRealTestComplex g := by
      simpa [G, suzukiRealTestL2] using
        suzukiRealTestL2_coeFn g hgdiff hgsupp
    filter_upwards [indicatorCutoff_ae (centralInterval a.1)
        (measurableSet_centralInterval a.1) (G.toLp 2 volume),
      hcoeG] with x hcut hcoe
    rw [hcut]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hcoe]
      have hgzero : g x = 0 := by
        apply Function.notMem_support.mp
        intro hxg
        apply hx
        exact Ioo_subset_Icc_self (hgaper (subset_tsupport g hxg))
      simp [suzukiRealTestComplex, hgzero]
  have hwker : w ∈ (suzukiHlogSupportDefect a).ker := by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)) (suzukiHlogFourierToTime w) = 0
    rw [htime, sub_apply, one_apply_eq_self, hfix, sub_self]
  refine ⟨⟨w, hwker⟩, ?_⟩
  change suzukiHlogFourierToTime w = suzukiRealTestL2 g hgdiff hgsupp
  exact htime

/-- Elements of the aperture Hilbert space are fixed by the cutoff to `[-a, a]`. -/
theorem indicatorCutoff_suzukiApertureHilbert
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) f.1 = f.1 := by
  rcases f.property with ⟨g, hg⟩
  change indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) g = f.1 at hg
  have hidem := indicatorCutoff_idempotent (centralInterval a.1)
    (measurableSet_centralInterval a.1)
  rw [isIdempotentElem_iff] at hidem
  calc
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) f.1 =
        indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
          (indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) g) := by
      rw [hg]
    _ = ((indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) *
        indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)) g) := rfl
    _ = indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) g := by
      rw [hidem]
    _ = f.1 := hg

/-- The `H^log(-a, a)` form domain embeds with dense range into `L^2(-a, a)`: a vector orthogonal to
all smooth test functions supported in `(-a, a)` vanishes. -/
theorem denseRange_suzukiHlogFormToAperture (a : SuzukiPositiveAperture) :
    DenseRange (suzukiHlogFormToAperture a) := by
  letI : CompleteSpace (suzukiApertureHilbert a) :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (show IsIdempotentElem (indicatorCutoff (centralInterval a.1)
        (measurableSet_centralInterval a.1)) from
        indicatorCutoff_idempotent (centralInterval a.1)
          (measurableSet_centralInterval a.1))).completeSpace_coe
  have hdense : Dense
      ((suzukiHlogFormToAperture a).toLinearMap.range : Set (suzukiApertureHilbert a)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro h hh
    have hinside : ∀ᵐ x : ℝ ∂volume, x ∈ Ioo (-a.1) a.1 → (h.1 : ℝ → ℂ) x = 0 := by
      apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (((Lp.memLp h.1).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
      intro g hgdiff hgsupp hgaper
      obtain ⟨f, hf⟩ := exists_suzukiHlogFormDomain_eq_smoothRealTest
        a g hgdiff hgsupp hgaper
      have horth : inner ℂ (suzukiHlogFormToAperture a f) h = 0 :=
        ((Submodule.mem_orthogonal _ _).mp hh) _ ⟨f, rfl⟩
      change inner ℂ (suzukiHlogFormEmbedding a f) h.1 = 0 at horth
      rw [MeasureTheory.L2.inner_def] at horth
      have htest : (suzukiHlogFormEmbedding a f : ℝ → ℂ) =ᵐ[volume]
          suzukiRealTestComplex g := by
        rw [hf]
        exact suzukiRealTestL2_coeFn g hgdiff hgsupp
      have hintegrand :
          (fun x : ℝ => inner ℂ
              ((suzukiHlogFormEmbedding a f : SoninL2) x) ((h.1 : SoninL2) x)) =ᵐ[volume]
            fun x => g x • (h.1 : ℝ → ℂ) x := by
        filter_upwards [htest] with x hx
        rw [hx]
        simp [suzukiRealTestComplex, RCLike.inner_apply, Complex.real_smul, mul_comm]
      rw [integral_congr_ae hintegrand] at horth
      exact horth
    have hfix := indicatorCutoff_suzukiApertureHilbert a h
    have hfixae :
        (indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) h.1 :
          ℝ → ℂ) =ᵐ[volume] (h.1 : ℝ → ℂ) := by
      rw [hfix]
    have houtside : ∀ᵐ x : ℝ ∂volume,
        x ∉ centralInterval a.1 → (h.1 : ℝ → ℂ) x = 0 := by
      filter_upwards [indicatorCutoff_ae (centralInterval a.1)
        (measurableSet_centralInterval a.1) h.1, hfixae] with x hcut hfae
      intro hx
      rw [← hfae, hcut, indicator_of_notMem hx]
    have hleft : ∀ᵐ x : ℝ ∂volume, x ≠ -a.1 := by
      rw [ae_iff]
      simp
    have hright : ∀ᵐ x : ℝ ∂volume, x ≠ a.1 := by
      rw [ae_iff]
      simp
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hinside, houtside, hleft, hright,
      Lp.coeFn_zero ℂ 2 volume] with x hin hout hxl hxr hzero
    change (h.1 : ℝ → ℂ) x = (0 : SoninL2) x
    rw [hzero]
    by_cases hx : x ∈ centralInterval a.1
    · apply hin
      rw [centralInterval, mem_Icc] at hx
      exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxl), lt_of_le_of_ne hx.2 hxr⟩
    · exact hout hx
  change Dense (Set.range (suzukiHlogFormToAperture a))
  have hrange : Set.range (suzukiHlogFormToAperture a) =
      ((suzukiHlogFormToAperture a).toLinearMap.range : Set (suzukiApertureHilbert a)) := by
    ext h
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f, rfl⟩
    · rintro ⟨f, hf⟩
      exact ⟨f, hf⟩
  rw [hrange]
  exact hdense

end RHTower

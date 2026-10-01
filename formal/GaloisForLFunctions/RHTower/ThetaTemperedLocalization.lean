import GaloisForLFunctions.RHTower.ThetaTemperedCompactDivision
import GaloisForLFunctions.RHTower.ThetaTemperedPointSupport
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Genuine compact localization of the original Xi-tempered kernel

Xi's entire nonzero source constructs compact Schwartz cutoffs isolating each
real zero. Multiplication by those actual cutoffs gives literal all-test point
support and the exact lower-multiplicity jet span. The localized original weak
tempered functional is independent of every compact isolating cutoff equal to
one near its center. No isolation or finite-jet representation is assumed in
the final actual-localization statements.
-/

open Set Filter
open scoped SchwartzMap ContDiff Topology

namespace RHTower

noncomputable section

/-- A literal zero germ excludes the center from the original closed test support. -/
theorem thetaSchwartz_notMem_tsupport_of_vanish_near (φ : 𝓢(ℝ, ℂ)) (t : ℝ)
    (hφ : ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → φ x = 0) :
    t ∉ tsupport (φ : ℝ → ℂ) := by
  rcases hφ with ⟨δ, hδ, hφ⟩
  apply notMem_tsupport_iff_eventuallyEq.mpr
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  exact hφ x (by simpa only [Real.dist_eq] using hx.le)

/-- Every real center has a neighborhood containing no distinct real Xi zero. -/
theorem thetaXiRealSymbol_exists_isolating_radius (t : ℝ) :
    ∃ δ > 0, ∀ x : ℝ, |x - t| < δ → thetaXiRealSymbol x = 0 → x = t := by
  have hnot : ¬ (∀ᶠ z in 𝓝 (t : ℂ), XiC z = 0) := by
    intro hz
    have hall := XiC_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ (t : ℂ)) hz (Set.mem_univ 0)
    exact XiC_zero_ne hall
  have hpunctured :=
    (XiC_analytic (t : ℂ) (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero
      |>.resolve_left hnot
  have hnear : ∀ᶠ z in 𝓝 (t : ℂ), z ≠ (t : ℂ) → XiC z ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      eventually_nhdsWithin_iff.mp hpunctured
  have hreal : ∀ᶠ x in 𝓝 t, x ≠ t → thetaXiRealSymbol x ≠ 0 := by
    have hc : Tendsto Complex.ofReal (𝓝 t) (𝓝 (t : ℂ)) :=
      Complex.continuous_ofReal.continuousAt
    filter_upwards [hc.eventually hnear] with x hx
    intro hxt
    exact hx (fun h => hxt (Complex.ofReal_injective h))
  rcases Metric.eventually_nhds_iff.mp hreal with ⟨δ, hδ, hnearδ⟩
  refine ⟨δ, hδ, fun x hx hzero => ?_⟩
  by_contra hxt
  exact (hnearδ (by simpa only [Real.dist_eq] using hx) hxt) hzero

/-- A genuine compact Schwartz cutoff is one near t and isolates its Xi zero. -/
theorem thetaXiRealSymbol_exists_isolating_cutoff (t : ℝ) :
    ∃ χ : 𝓢(ℝ, ℂ), HasCompactSupport (χ : ℝ → ℂ) ∧
      (∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → χ x = 1) ∧
      (∀ x ∈ tsupport (χ : ℝ → ℂ), thetaXiRealSymbol x = 0 → x = t) := by
  rcases thetaXiRealSymbol_exists_isolating_radius t with ⟨δ, hδ, hnear⟩
  let b : ContDiffBump t := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let g : ℝ → ℂ := fun x => (b x : ℂ)
  have hgcompact : HasCompactSupport g :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hgsmooth : ContDiff ℝ ∞ g :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hgsupport : tsupport g ⊆ tsupport (b : ℝ → ℝ) := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp only [g, hz, Complex.ofReal_zero])
  let χ : 𝓢(ℝ, ℂ) := hgcompact.toSchwartzMap hgsmooth
  refine ⟨χ, hgcompact, ⟨δ / 4, by positivity, ?_⟩, ?_⟩
  · intro x hx
    change (b x : ℂ) = 1
    have hbx : x ∈ Metric.closedBall t b.rIn := by
      apply Metric.mem_closedBall.mpr
      simpa only [Real.dist_eq] using hx
    rw [b.one_of_mem_closedBall hbx, Complex.ofReal_one]
  · intro x hx hzero
    have hbx := hgsupport hx
    rw [b.tsupport_eq] at hbx
    have hdist : dist x t ≤ δ / 2 := Metric.mem_closedBall.mp hbx
    have hsmall : |x - t| < δ := by
      rw [Real.dist_eq] at hdist
      linarith
    exact hnear x hsmall hzero

/-- One fixed actual cutoff, chosen from the unconditional existence theorem. -/
def thetaXiIsolatingCutoff (t : ℝ) : 𝓢(ℝ, ℂ) :=
  (thetaXiRealSymbol_exists_isolating_cutoff t).choose

theorem thetaXiIsolatingCutoff_hasCompactSupport (t : ℝ) :
    HasCompactSupport (thetaXiIsolatingCutoff t : ℝ → ℂ) :=
  (thetaXiRealSymbol_exists_isolating_cutoff t).choose_spec.1

theorem thetaXiIsolatingCutoff_eq_one_near (t : ℝ) :
    ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → thetaXiIsolatingCutoff t x = 1 :=
  (thetaXiRealSymbol_exists_isolating_cutoff t).choose_spec.2.1

theorem thetaXiIsolatingCutoff_isolates_zero (t : ℝ) :
    ∀ x ∈ tsupport (thetaXiIsolatingCutoff t : ℝ → ℂ),
      thetaXiRealSymbol x = 0 → x = t :=
  (thetaXiRealSymbol_exists_isolating_cutoff t).choose_spec.2.2

/-- Multiplication by an original Schwartz cutoff on the actual weak tempered dual. -/
def thetaTemperedLocalize (χ : 𝓢(ℝ, ℂ)) : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ (χ : ℝ → ℂ)

theorem thetaTemperedLocalize_apply (χ : 𝓢(ℝ, ℂ)) (Q : 𝓢'(ℝ, ℂ))
    (ψ : 𝓢(ℝ, ℂ)) :
    thetaTemperedLocalize χ Q ψ = Q (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ) :=
  TemperedDistribution.smulLeftCLM_apply_apply (χ : ℝ → ℂ) Q ψ

private theorem thetaSchwartz_cutoffProduct_coe (χ ψ : 𝓢(ℝ, ℂ)) :
    (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ : ℝ → ℂ) =
      fun x => χ x * ψ x := by
  funext x
  simpa only [smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth ψ x

/-- Compact cutoff products preserve both original closed-support inclusions. -/
theorem thetaSchwartz_cutoffProduct_compact_support (χ ψ : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) :
    HasCompactSupport (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ : ℝ → ℂ) ∧
      tsupport (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ : ℝ → ℂ) ⊆
        tsupport (χ : ℝ → ℂ) ∧
      tsupport (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ : ℝ → ℂ) ⊆
        tsupport (ψ : ℝ → ℂ) := by
  rw [thetaSchwartz_cutoffProduct_coe]
  exact ⟨hχ.mul_right, tsupport_mul_subset_left, tsupport_mul_subset_right⟩

/-- Actual pointwise multiplier commutation preserves the original Xi-kernel. -/
theorem thetaXiTemperedKernel_localize_mem_kernel (Q : 𝓢'(ℝ, ℂ))
    (hQ : thetaXiTemperedMultiplier Q = 0) (χ : 𝓢(ℝ, ℂ)) :
    thetaXiTemperedMultiplier (thetaTemperedLocalize χ Q) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  change Q (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ)
    (SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol ψ)) = 0
  have hcomm :
      SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ)
        (SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol ψ) =
      SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol
        (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ) := by
    apply SchwartzMap.ext
    intro x
    simp only [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply thetaXiRealSymbol_hasTemperateGrowth,
      smul_eq_mul]
    ring
  rw [hcomm]
  have hz := congrArg (fun T : 𝓢'(ℝ, ℂ) =>
    T (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ)) hQ
  change Q (SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol
    (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ)) = 0 at hz
  exact hz

/-- An actual compact isolating cutoff gives literal support at t on ALL tests. -/
theorem thetaXiTemperedKernel_localize_pointSupport (Q : 𝓢'(ℝ, ℂ))
    (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) (χ : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (hiso : ∀ x ∈ tsupport (χ : ℝ → ℂ), thetaXiRealSymbol x = 0 → x = t) :
    ∀ ψ : 𝓢(ℝ, ℂ), (∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → ψ x = 0) →
      thetaTemperedLocalize χ Q ψ = 0 := by
  intro ψ hψ
  have ht := thetaSchwartz_notMem_tsupport_of_vanish_near ψ t hψ
  rcases thetaSchwartz_cutoffProduct_compact_support χ ψ hχ with ⟨hc, hsχ, hsψ⟩
  change Q (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ) = 0
  apply thetaXiTemperedKernel_eq_zero_of_compact_tsupport_nonvanishing Q hQ _ hc
  intro x hx hzero
  have hxt := hiso x (hsχ hx) hzero
  exact ht (hxt ▸ hsψ hx)

/-- Continuity derives finite order, and actual Xi multiplicity bounds every local jet. -/
theorem thetaXiTemperedKernel_localize_mem_lowerJetSpan (Q : 𝓢'(ℝ, ℂ))
    (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) (χ : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (hiso : ∀ x ∈ tsupport (χ : ℝ → ℂ), thetaXiRealSymbol x = 0 → x = t) :
    thetaTemperedLocalize χ Q ∈ thetaXiTemperedLowerJetSpan t :=
  (thetaTemperedPointSupport_Xi_kernel_iff_lowerJetSpan (thetaTemperedLocalize χ Q) t).mp
    ⟨thetaXiTemperedKernel_localize_pointSupport Q hQ t χ hχ hiso,
      thetaXiTemperedKernel_localize_mem_kernel Q hQ χ⟩

/-- A compact isolating cutoff with a zero germ annihilates the whole original kernel. -/
theorem thetaXiTemperedKernel_localize_eq_zero_of_vanish_near (Q : 𝓢'(ℝ, ℂ))
    (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) (χ : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (hiso : ∀ x ∈ tsupport (χ : ℝ → ℂ), thetaXiRealSymbol x = 0 → x = t)
    (hvanish : ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → χ x = 0) :
    thetaTemperedLocalize χ Q = 0 := by
  have ht := thetaSchwartz_notMem_tsupport_of_vanish_near χ t hvanish
  apply ContinuousLinearMap.ext
  intro ψ
  rcases thetaSchwartz_cutoffProduct_compact_support χ ψ hχ with ⟨hc, hsχ, _⟩
  change Q (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ) = 0
  apply thetaXiTemperedKernel_eq_zero_of_compact_tsupport_nonvanishing Q hQ _ hc
  intro x hx hzero
  have hχx := hsχ hx
  exact ht (hiso x hχx hzero ▸ hχx)

/-- Two actual compact isolating cutoffs equal to one near t give the SAME functional. -/
theorem thetaXiTemperedKernel_localize_independent (Q : 𝓢'(ℝ, ℂ))
    (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) (χ χ' : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) (hχ' : HasCompactSupport (χ' : ℝ → ℂ))
    (hiso : ∀ x ∈ tsupport (χ : ℝ → ℂ), thetaXiRealSymbol x = 0 → x = t)
    (hiso' : ∀ x ∈ tsupport (χ' : ℝ → ℂ), thetaXiRealSymbol x = 0 → x = t)
    (hone : ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → χ x = 1)
    (hone' : ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → χ' x = 1) :
    thetaTemperedLocalize χ Q = thetaTemperedLocalize χ' Q := by
  have hsub : HasCompactSupport ((χ - χ' : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := hχ.sub hχ'
  have hsubiso : ∀ x ∈ tsupport ((χ - χ' : 𝓢(ℝ, ℂ)) : ℝ → ℂ),
      thetaXiRealSymbol x = 0 → x = t := by
    intro x hx hzero
    rcases tsupport_sub (χ : ℝ → ℂ) (χ' : ℝ → ℂ) hx with hx | hx
    · exact hiso x hx hzero
    · exact hiso' x hx hzero
  have hsubgerm : ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → (χ - χ') x = 0 := by
    rcases hone with ⟨δ, hδ, hone⟩
    rcases hone' with ⟨δ', hδ', hone'⟩
    refine ⟨min δ δ', lt_min_iff.mpr ⟨hδ, hδ'⟩, ?_⟩
    intro x hx
    change χ x - χ' x = 0
    apply sub_eq_zero.mpr
    rw [hone x (hx.trans (min_le_left _ _)), hone' x (hx.trans (min_le_right _ _))]
  have hz := thetaXiTemperedKernel_localize_eq_zero_of_vanish_near
    Q hQ t (χ - χ') hsub hsubiso hsubgerm
  apply ContinuousLinearMap.ext
  intro ψ
  change Q (SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ) =
    Q (SchwartzMap.smulLeftCLM ℂ (χ' : ℝ → ℂ) ψ)
  have hprod : SchwartzMap.smulLeftCLM ℂ ((χ - χ' : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ψ =
      SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) ψ -
        SchwartzMap.smulLeftCLM ℂ (χ' : ℝ → ℂ) ψ := by
    apply SchwartzMap.ext
    intro x
    simp only [SchwartzMap.smulLeftCLM_apply_apply (χ - χ').hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply χ'.hasTemperateGrowth, sub_apply,
      smul_eq_mul, sub_mul]
  have hzero := congrArg (fun T : 𝓢'(ℝ, ℂ) => T ψ) hz
  change Q (SchwartzMap.smulLeftCLM ℂ ((χ - χ' : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ψ) = 0 at hzero
  rw [hprod, map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- Canonical localization at every real point, constructed from the actual Xi source. -/
def thetaXiTemperedLocalization (t : ℝ) : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  thetaTemperedLocalize (thetaXiIsolatingCutoff t)

theorem thetaXiTemperedLocalization_pointSupport (Q : 𝓢'(ℝ, ℂ))
    (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) :
    ∀ ψ : 𝓢(ℝ, ℂ), (∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → ψ x = 0) →
      thetaXiTemperedLocalization t Q ψ = 0 :=
  thetaXiTemperedKernel_localize_pointSupport Q hQ t (thetaXiIsolatingCutoff t)
    (thetaXiIsolatingCutoff_hasCompactSupport t) (thetaXiIsolatingCutoff_isolates_zero t)

theorem thetaXiTemperedLocalization_mem_lowerJetSpan (Q : 𝓢'(ℝ, ℂ))
    (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) :
    thetaXiTemperedLocalization t Q ∈ thetaXiTemperedLowerJetSpan t :=
  thetaXiTemperedKernel_localize_mem_lowerJetSpan Q hQ t (thetaXiIsolatingCutoff t)
    (thetaXiIsolatingCutoff_hasCompactSupport t) (thetaXiIsolatingCutoff_isolates_zero t)

/-- The constructed canonical functional agrees with EVERY admitted isolating cutoff. -/
theorem thetaXiTemperedLocalization_eq_localize (Q : 𝓢'(ℝ, ℂ))
    (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) (χ : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (hiso : ∀ x ∈ tsupport (χ : ℝ → ℂ), thetaXiRealSymbol x = 0 → x = t)
    (hone : ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → χ x = 1) :
    thetaXiTemperedLocalization t Q = thetaTemperedLocalize χ Q :=
  thetaXiTemperedKernel_localize_independent Q hQ t (thetaXiIsolatingCutoff t) χ
    (thetaXiIsolatingCutoff_hasCompactSupport t) hχ
    (thetaXiIsolatingCutoff_isolates_zero t) hiso
    (thetaXiIsolatingCutoff_eq_one_near t) hone

end

end RHTower

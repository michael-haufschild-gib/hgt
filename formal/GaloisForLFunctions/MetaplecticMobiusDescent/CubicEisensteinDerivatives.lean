/-
Spatial derivative identities adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.SpatialSmoothnessOfTheCubicEisensteinSeries

/-!
# Spatial derivatives of the actual Eisenstein sum

On a neighborhood of a positive-height point, a compact cutoff and a
regularized height identify the actual summands with a compact smooth
family weighted by the convergent base-point series. Every iterated
Fréchet derivative therefore commutes with the actual cusp-row sum.
The height-profile identity also gives each summand's Laplace eigenvalue.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

theorem smoothEisenstein_iteratedFDeriv_tsum (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hp : 0<p 2) (k : ℕ) :
    Summable (fun r : CuspCosets => iteratedFDeriv ℝ k (smoothSummand s r) p) ∧
    iteratedFDeriv ℝ k (smoothEisenstein s) p =
      ∑'r : CuspCosets,iteratedFDeriv ℝ k (smoothSummand s r) p := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let χ : ContDiffBump p := ⟨1,2,by norm_num,by norm_num⟩
  let ψ : SpatialCoordinates → ℂ := fun q => (χ q:ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hcψ : HasCompactSupport ψ := by
    have he : Function.support ψ=Function.support (fun q => χ q) := by
      ext q
      simp [Function.mem_support,ψ]
    change IsCompact (closure (Function.support ψ))
    rw [he]
    exact χ.hasCompactSupport
  let F : CuspCosets → SpatialCoordinates → ℂ := fun r q =>
    summand 1 s r*(ψ q*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) q)
  have hsum := regular_eisenstein_compact_derivatives s hs deltaLoss hδ ψ hψ hcψ k p
  have hn : ∀ᶠq in 𝓝 p, deltaLoss<q 2 :=
    (isOpen_lt continuous_const (continuous_apply 2)).mem_nhds (by dsimp [deltaLoss]; linarith)
  have hlocal : ∀ᶠq in 𝓝 p, ∀r : CuspCosets,F r q=smoothSummand s r q := by
    filter_upwards [χ.eventuallyEq_one,hn] with q hχ hq r
    have hψq : ψ q=1 := by simp [ψ,hχ]
    dsimp only [F]
    rw [hψq,one_mul]
    exact normalized_row_summand s deltaLoss hδ r q hq.le
  have hi (r : CuspCosets) : iteratedFDeriv ℝ k (F r) p=
      iteratedFDeriv ℝ k (smoothSummand s r) p := by
    have hr : F r =ᶠ[𝓝 p] smoothSummand s r := hlocal.mono (fun q hq => hq r)
    exact (hr.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds
  have he : (fun q => ∑'r,F r q)=ᶠ[𝓝 p] smoothEisenstein s :=
    hlocal.mono (fun q hq => tsum_congr hq)
  refine ⟨hsum.1.congr hi,?_⟩
  calc
    _ = iteratedFDeriv ℝ k (fun q => ∑'r,F r q) p :=
      ((he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds).symm
    _ = ∑'r,iteratedFDeriv ℝ k (F r) p := hsum.2
    _ = _ := tsum_congr hi

lemma rowSmoothPower_eq_profile (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    rowSmoothPower s u p=positiveHeightPower s (rowHeight u p) := by
  rw [positiveHeightPower_eq_cpow s _ (rowHeight_pos u hu p hp)]
  unfold rowSmoothPower spatialHeightPower
  rw [logRatioPower_eq_cpow s hp (row_denominator_pos u hu p hp)]
  rfl

lemma rowSmoothPower_axisLaplacian (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (rowSmoothPower s u) p=s*(s-2)*rowSmoothPower s u p := by
  have he := axisLaplacian_congr_positive (rowSmoothPower s u)
    (fun q => positiveHeightPower s (rowHeight u q))
    (rowSmoothPower_eq_profile s u hu) p hp
  rw [he,rowProfile_laplacian (positiveHeightPower s)
    (fun v hv => positiveHeightPower_contDiffAt s v hv.ne') u hu p hp,rowSmoothPower_eq_profile s u hu p hp]
  have hv := rowHeight_pos u hu p hp
  rw [(positiveHeightPower_hasDerivAt s _ hv.ne').deriv,
    (positiveHeightPower_hasDerivAt_deriv s _ hv.ne').deriv]
  field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  ring

lemma smoothSummand_axisLaplacian (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (smoothSummand s r) p=s*(s-2)*smoothSummand s r p := by
  unfold smoothSummand
  rw [axisLaplacian_const_mul,
    rowSmoothPower_axisLaplacian s _ (embeddedRow_ne_zero r) p hp]
  ring

#print axioms smoothEisenstein_iteratedFDeriv_tsum
#print axioms smoothSummand_axisLaplacian
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

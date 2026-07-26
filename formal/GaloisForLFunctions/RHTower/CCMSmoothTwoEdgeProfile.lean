import GaloisForLFunctions.HTGeometry.BaireGenericAvoidance
import GaloisForLFunctions.HTGeometry.CompactSupportSmoothBaire
import GaloisForLFunctions.RHTower.CCMRectangularDirichletLandau
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Smooth fixed-support profiles for cofinal two-edge Weil detection

This module constructs the literal Fréchet space of smooth real boundary
profiles supported in `[eta, L - eta]`, its Laplace evaluation functionals,
and the residual set on which every positive-transverse Xi zero has nonzero
Laplace amplitude.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped Distributions

namespace RHTower

noncomputable section

/-- The compact support window `[eta, L - eta]` for a smooth boundary
profile. -/
def smoothBoundaryProfileCompact (eta L : ℝ) : Compacts ℝ :=
  ⟨Icc eta (L - eta), isCompact_Icc⟩

/-- The actual real Fréchet space `D_(eta,L)` from the two-edge card. -/
abbrev SmoothBoundaryProfile (eta L : ℝ) :=
  GaloisForLFunctions.HTGeometry.CompactSupportSmooth
    (smoothBoundaryProfileCompact eta L)

/-- The complex Laplace weight `s ↦ exp (-s w)`. -/
def smoothProfileLaplaceWeight (w : ℂ) (s : ℝ) : ℂ :=
  Complex.exp (-(s : ℂ) * w)

/-- Continuous real-linear Laplace evaluation on the fixed-support smooth
profile space. -/
def smoothProfileLaplaceCLM (eta L : ℝ) (w : ℂ) :
    SmoothBoundaryProfile eta L →L[ℝ] ℂ :=
  (ContDiffMapSupportedIn.integralAgainstBilinCLM
      (ContinuousLinearMap.mul ℝ ℂ) volume
      (smoothProfileLaplaceWeight w) :
    ContDiffMapSupportedIn ℝ ℂ ⊤ (smoothBoundaryProfileCompact eta L) →L[ℝ] ℂ).comp
    (ContDiffMapSupportedIn.postcompCLM Complex.ofRealCLM)

/-- The Laplace amplitude of a smooth boundary profile. -/
def smoothProfileLaplaceAmplitude {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (w : ℂ) : ℂ :=
  smoothProfileLaplaceCLM eta L w f

theorem smoothProfileLaplaceAmplitude_eq_integral
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (w : ℂ) :
    smoothProfileLaplaceAmplitude f w =
      ∫ s : ℝ, (f s : ℂ) * smoothProfileLaplaceWeight w s := by
  have hw : IntegrableOn (smoothProfileLaplaceWeight w)
      (↑(smoothBoundaryProfileCompact eta L) : Set ℝ) volume := by
    change IntegrableOn (smoothProfileLaplaceWeight w)
      (Icc eta (L - eta)) volume
    exact (by
      unfold smoothProfileLaplaceWeight
      fun_prop : Continuous (smoothProfileLaplaceWeight w)).continuousOn.integrableOn_compact
      isCompact_Icc
  simp [smoothProfileLaplaceAmplitude, smoothProfileLaplaceCLM, hw]

theorem continuous_smoothProfileLaplaceWeight (w : ℂ) :
    Continuous (smoothProfileLaplaceWeight w) := by
  unfold smoothProfileLaplaceWeight
  fun_prop

/-- A nonempty profile window makes every complex Laplace evaluation a
nonzero continuous real-linear functional. -/
theorem smoothProfileLaplaceCLM_ne_zero
    {eta L : ℝ} (hwindow : eta < L - eta) (w : ℂ) :
    smoothProfileLaplaceCLM eta L w ≠ 0 := by
  intro hzero
  let U : Set ℝ := Ioo eta (L - eta)
  have hUopen : IsOpen U := isOpen_Ioo
  have hweightLocal : LocallyIntegrableOn (smoothProfileLaplaceWeight w) U volume :=
    (continuous_smoothProfileLaplaceWeight w).locallyIntegrable.locallyIntegrableOn U
  have hintegral : ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • smoothProfileLaplaceWeight w x = 0 := by
    intro g hg hcompact hsupp
    have hsupp' : support g ⊆ Icc eta (L - eta) := by
      exact (subset_tsupport g).trans (hsupp.trans Ioo_subset_Icc_self)
    let p : SmoothBoundaryProfile eta L :=
      ContDiffMapSupportedIn.of_support_subset hg hsupp'
    have hpzero : smoothProfileLaplaceCLM eta L w p = 0 := by
      rw [hzero]
      rfl
    change smoothProfileLaplaceAmplitude p w = 0 at hpzero
    rw [smoothProfileLaplaceAmplitude_eq_integral] at hpzero
    simpa [p] using hpzero
  have hae := hUopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hweightLocal hintegral
  have haenot : ∀ᵐ x ∂volume, x ∉ U := by
    filter_upwards [hae] with x hx
    intro hxU
    exact Complex.exp_ne_zero _ (hx hxU)
  have hmeasureZero : volume U = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr haenot
  have hmeasurePos : 0 < volume U :=
    (Measure.measure_Ioo_pos volume).mpr hwindow
  exact hmeasurePos.ne' hmeasureZero

/-- Kernel of a nonzero continuous real-linear functional is nowhere dense
in any real topological module. -/
theorem isNowhereDense_ker_continuousLinearMap_of_ne_zero
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [ContinuousAdd E]
    [Module ℝ E] [ContinuousSMul ℝ E]
    (T : E →L[ℝ] ℂ) (hT : T ≠ 0) :
    IsNowhereDense (LinearMap.ker T.toLinearMap : Set E) := by
  apply GaloisForLFunctions.isNowhereDense_of_isClosed_of_interior_eq_empty
  · exact T.isClosed_ker
  · by_contra hne
    have hnonempty :
        (interior (LinearMap.ker T.toLinearMap : Set E)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hne
    have htop := Submodule.eq_top_of_nonempty_interior'
      (LinearMap.ker T.toLinearMap) hnonempty
    have hlinearZero : T.toLinearMap = 0 := LinearMap.ker_eq_top.mp htop
    apply hT
    ext x
    exact LinearMap.congr_fun hlinearZero x

/-- Profiles whose Laplace amplitude is nonzero at every positive-transverse
Xi zero copy. -/
def xiSmoothProfileGenericSet (eta L : ℝ) :
    Set (SmoothBoundaryProfile eta L) :=
  {f | ∀ q : XiRightZeroCopy,
    smoothProfileLaplaceAmplitude f (xiRightCenteredZero q) ≠ 0}

noncomputable local instance : Countable XiRightZeroCopy := inferInstance

/-- Simultaneous nonvanishing at the entire positive-transverse Xi divisor is
residual and dense in the literal smooth fixed-support profile space. -/
theorem xiSmoothProfileGenericSet_dense_residual
    {eta L : ℝ} (hwindow : eta < L - eta) :
    Dense (xiSmoothProfileGenericSet eta L) ∧
      xiSmoothProfileGenericSet eta L ∈ residual (SmoothBoundaryProfile eta L) := by
  let bad : XiRightZeroCopy → Set (SmoothBoundaryProfile eta L) := fun q =>
    LinearMap.ker (smoothProfileLaplaceCLM eta L
      (xiRightCenteredZero q)).toLinearMap
  have hbad : ∀ q, IsNowhereDense (bad q) := by
    intro q
    exact isNowhereDense_ker_continuousLinearMap_of_ne_zero _
      (smoothProfileLaplaceCLM_ne_zero hwindow _)
  have hres : (⋂ q, (bad q)ᶜ) ∈ residual (SmoothBoundaryProfile eta L) :=
    countable_iInter_mem.mpr fun q => (hbad q).isMeagre
  have heq : (⋂ q, (bad q)ᶜ) = xiSmoothProfileGenericSet eta L := by
    ext f
    simp [bad, xiSmoothProfileGenericSet, smoothProfileLaplaceAmplitude]
  rw [heq] at hres
  exact ⟨dense_of_mem_residual hres, hres⟩

end

end RHTower

import GaloisForLFunctions.HTGeometry.LocalSpectralLinearObserverLaw
import Mathlib.Analysis.Matrix.Spectrum

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Real onsite energies, embedded in the complex spectral field. -/
def complexOnsite
    {V : Type*} {A : V → Type*}
    (onsite : ∀ v, A v → ℝ) :
    ∀ v, A v → ℂ :=
  fun v a => onsite v a

/-- Real interaction controls, embedded in the complex spectral field. -/
def complexCoupling
    {E : Type*} (coupling : E → ℝ) : E → ℂ :=
  fun e => coupling e

/-- Every root of the characteristic equation of a Hermitian matrix is real. -/
theorem matrixCharpolyRelation_im_eq_zero_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (w : ℂ)
    (hroot : matrixCharpolyRelation (H, w) = 0) :
    w.im = 0 := by
  have hpoly : Polynomial.IsRoot H.charpoly w := by
    change H.charpoly.eval w = 0
    rw [Matrix.eval_charpoly]
    exact hroot
  have hspectrum : w ∈ spectrum ℂ H :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hpoly
  rw [hH.spectrum_eq_image_range] at hspectrum
  obtain ⟨r, ⟨i, rfl⟩, hw⟩ := hspectrum
  rw [← hw]
  simp

namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- A local interaction architecture whose independently controlled
interaction matrices are all Hermitian. -/
def HermitianInteractionFamily
    (L : FiniteLocalInteractionFamily V E A) : Prop :=
  ∀ e, (L.globalInteraction e).IsHermitian

omit [DecidableEq E] in
/-- Real onsite energies and real controls preserve Hermiticity of the full
affine local Hamiltonian family. -/
theorem affineMatrixFamily_complexOnsite_complexCoupling_isHermitian
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (coupling : E → ℝ) :
    (affineMatrixFamily
      (Matrix.diagonal
        (onsiteProductEnergy (complexOnsite onsite)))
      L.globalInteraction
      (complexCoupling coupling)).IsHermitian := by
  unfold affineMatrixFamily
  apply Matrix.IsHermitian.add
  · rw [Matrix.isHermitian_diagonal_iff]
    intro config
    rw [isSelfAdjoint_iff]
    simp [onsiteProductEnergy, complexOnsite]
  · refine Finset.sum_induction
      (fun e => complexCoupling coupling e • L.globalInteraction e)
      (fun M => M.IsHermitian)
      (fun M N hM hN => hM.add hN)
      Matrix.isHermitian_zero
      ?_
    intro e he
    exact (hL e).smul (by
      rw [isSelfAdjoint_iff]
      simp [complexCoupling])

/-- Each analytically selected local product eigenbranch remains real along
the real coupling slice near the uncoupled point. -/
theorem productEigenvalueBranch_im_eq_zero_eventually_realCoupling
    [∀ v, Nonempty (A v)]
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (config : ∀ v, A v) :
    ∀ᶠ coupling : E → ℝ in 𝓝 0,
      (L.productEigenvalueBranch (complexOnsite onsite)
        hinj config (complexCoupling coupling)).im = 0 := by
  have hroot :=
    (L.productEigenvalueBranch_spec
      (complexOnsite onsite) hinj config).2.2
  have hc : Tendsto
      (complexCoupling : (E → ℝ) → E → ℂ) (𝓝 0) (𝓝 0) := by
    have ha : AnalyticAt ℝ
        (complexCoupling : (E → ℝ) → E → ℂ) 0 := by
      apply AnalyticAt.pi
      intro e
      have hproj :
          AnalyticAt ℝ (fun c : E → ℝ => c e) 0 :=
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : E => ℝ) e).analyticAt 0
      have hout :
          AnalyticAt ℝ (fun r : ℝ => (r : ℂ)) 0 :=
        Complex.ofRealCLM.analyticAt 0
      simpa [complexCoupling] using
        hout.comp_of_eq' hproj rfl
    have hcont := ha.continuousAt
    have hz : complexCoupling (0 : E → ℝ) = 0 := by
      funext e
      simp [complexCoupling]
    rw [ContinuousAt] at hcont
    simpa only [hz] using hcont
  filter_upwards [hc.eventually hroot] with coupling hcouplingRoot
  exact matrixCharpolyRelation_im_eq_zero_of_isHermitian
    _ (L.affineMatrixFamily_complexOnsite_complexCoupling_isHermitian
      hL onsite coupling)
    _ hcouplingRoot

/-- The interaction-induced displacement of every selected energy branch is
real on real Hermitian controls near the uncoupled point. -/
theorem productSpectralInteractionShift_im_eq_zero_eventually_realCoupling
    [∀ v, Nonempty (A v)]
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (config : ∀ v, A v) :
    ∀ᶠ coupling : E → ℝ in 𝓝 0,
      (L.productSpectralInteractionShift
        (complexOnsite onsite) hinj config
        (complexCoupling coupling)).im = 0 := by
  filter_upwards
    [L.productEigenvalueBranch_im_eq_zero_eventually_realCoupling
      hL onsite hinj config] with coupling hreal
  unfold productSpectralInteractionShift
  rw [Complex.sub_im, hreal]
  simp [onsiteProductEnergy, complexOnsite]

/-- For a Hermitian local family, every spectral-gap observer produces a
genuine real energy-gap germ along real coupling space. -/
theorem spectralGapObserverResponse_im_eq_zero_eventually_realCoupling
    [∀ v, Nonempty (A v)]
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (left right : ∀ v, A v) :
    ∀ᶠ coupling : E → ℝ in 𝓝 0,
      (L.linearSpectralObserverResponse
        (complexOnsite onsite) hinj
        (spectralGapObserver left right)
        (complexCoupling coupling)).im = 0 := by
  filter_upwards
    [L.productSpectralInteractionShift_im_eq_zero_eventually_realCoupling
      hL onsite hinj left,
     L.productSpectralInteractionShift_im_eq_zero_eventually_realCoupling
      hL onsite hinj right] with coupling hleft hright
  rw [L.linearSpectralObserverResponse_spectralGapObserver]
  rw [Complex.sub_im, hleft, hright, sub_self]

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry

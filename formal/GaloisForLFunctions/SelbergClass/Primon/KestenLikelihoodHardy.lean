import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodKernel
import GaloisForLFunctions.RHTower.ArithmeticSchurFirstTraceNonclosability
import GaloisForLFunctions.HilbertMetric.NomologicalCrossGram

/-!
# The Hardy realization of prime likelihoods

Actual likelihoods in semicircle `L²` have the same Gram kernel as the real
Hardy vectors `(1,p⁻¹,p⁻²,…)`. Their finite linear spans are therefore
canonically isometric. The gamma-valuation Szegő kernel is the Gram kernel
of these likelihoods after the existing boundary-amplitude scaling.
-/

open MeasureTheory
open _root_.RHTower

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Real square-integrable observables of the semicircle spectral law. -/
abbrev SemicircleL2 := Lp ℝ 2 (semicircleSpectralLaw : Measure ℝ)

/-- Compact spectral support makes every continuous observable square-integrable. -/
theorem memLp_semicircle_continuous (f : C(ℝ, ℝ)) :
    MemLp f 2 (semicircleSpectralLaw : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq f.continuous.aestronglyMeasurable).2
  exact integrable_semicircleSpectralLaw_continuous ⟨_, f.continuous.pow 2⟩

/-- The almost-everywhere class of a continuous spectral observable. -/
def semicircleL2Observable (f : C(ℝ, ℝ)) : SemicircleL2 :=
  (memLp_semicircle_continuous f).toLp f

theorem coeFn_semicircleL2Observable (f : C(ℝ, ℝ)) :
    semicircleL2Observable f =ᵐ[(semicircleSpectralLaw : Measure ℝ)] f :=
  (memLp_semicircle_continuous f).coeFn_toLp

/-- The Hilbert inner product is the actual semicircle integral. -/
theorem inner_semicircleL2Observable (f g : C(ℝ, ℝ)) :
    inner ℝ (semicircleL2Observable f) (semicircleL2Observable g) =
      ∫ x, f x * g x ∂(semicircleSpectralLaw : Measure ℝ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_semicircleL2Observable f, coeFn_semicircleL2Observable g] with x hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- The prime likelihood as an actual semicircle `L²` vector. -/
def kestenLikelihoodVector (p : Nat.Primes) : SemicircleL2 :=
  semicircleL2Observable ⟨_, continuous_kestenLikelihood p⟩

/-- Equality of spectral and Hardy feature Gram kernels. -/
theorem inner_kestenLikelihoodVector (p q : Nat.Primes) :
    inner ℝ (kestenLikelihoodVector p) (kestenLikelihoodVector q) =
      inner ℝ (primeHardyKernel p) (primeHardyKernel q) := by
  rw [kestenLikelihoodVector, kestenLikelihoodVector, inner_semicircleL2Observable]
  change (∫ x, kestenLikelihood p x * kestenLikelihood q x
    ∂(semicircleSpectralLaw : Measure ℝ)) = _
  rw [integral_semicircleLikelihood_mul_likelihood, inner_primeHardyKernel]
  simp only [primeReciprocal, mul_inv_rev, one_div, mul_comm]

/-- Synthesis of finitely supported prime likelihood packets. -/
def kestenLikelihoodMap : (Nat.Primes →₀ ℝ) →ₗ[ℝ] SemicircleL2 :=
  Finsupp.linearCombination ℝ kestenLikelihoodVector

@[simp] theorem kestenLikelihoodMap_single (p : Nat.Primes) (c : ℝ) :
    kestenLikelihoodMap (Finsupp.single p c) = c • kestenLikelihoodVector p :=
  Finsupp.linearCombination_single ℝ c p

/-- Every pair of finite spectral packets has exactly its Hardy inner product. -/
theorem inner_kestenLikelihoodMap (c d : Nat.Primes →₀ ℝ) :
    inner ℝ (kestenLikelihoodMap c) (kestenLikelihoodMap d) =
      inner ℝ (primeHardyKernelMap c) (primeHardyKernelMap d) := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      simp only [map_add, inner_add_left, ih]
      congr 1
      clear ih
      induction d using Finsupp.induction with
      | zero => simp
      | single_add q b d hq hb ihd =>
          simp only [map_add, inner_add_right, ihd]
          congr 1
          simp only [kestenLikelihoodMap_single, primeHardyKernelMap_single,
            inner_smul_left, inner_smul_right, inner_kestenLikelihoodVector]

/-- Canonical isometry of the actual likelihood span with the prime Hardy span. -/
def kestenLikelihoodHardyEquiv :
    kestenLikelihoodMap.range ≃ₗᵢ[ℝ] primeHardyKernelMap.range :=
  _root_.HilbertMetric.NomologicalCrossGram.activeRangeIsometryEquiv
    kestenLikelihoodMap primeHardyKernelMap inner_kestenLikelihoodMap

/-- The span isometry preserves each finite prime packet, including its coefficients. -/
theorem kestenLikelihoodHardyEquiv_apply (c : Nat.Primes →₀ ℝ) :
    (kestenLikelihoodHardyEquiv ⟨kestenLikelihoodMap c, ⟨c, rfl⟩⟩ : PrimeHardy) =
      primeHardyKernelMap c :=
  _root_.HilbertMetric.NomologicalCrossGram.activeRangeIsometryEquiv_apply
    kestenLikelihoodMap primeHardyKernelMap inner_kestenLikelihoodMap c

/-- The inverse span isometry reconstructs the same likelihood packet. -/
theorem kestenLikelihoodHardyEquiv_symm_apply (c : Nat.Primes →₀ ℝ) :
    (kestenLikelihoodHardyEquiv.symm ⟨primeHardyKernelMap c, ⟨c, rfl⟩⟩ : SemicircleL2) =
      kestenLikelihoodMap c := by
  have h : kestenLikelihoodHardyEquiv ⟨kestenLikelihoodMap c, ⟨c, rfl⟩⟩ =
      ⟨primeHardyKernelMap c, ⟨c, rfl⟩⟩ :=
    Subtype.ext (kestenLikelihoodHardyEquiv_apply c)
  rw [← h, kestenLikelihoodHardyEquiv.symm_apply_apply]

/-- Gamma-valuation boundary amplitudes turn likelihoods into Szegő feature vectors. -/
theorem gammaValuationSzegoKernel_eq_likelihood_inner (p q : Nat.Primes) :
    xiTransverseGammaValuationSzegoKernel p q =
      inner ℝ (arithmeticPrimeSchurBoundaryAmplitude p • kestenLikelihoodVector p)
        (arithmeticPrimeSchurBoundaryAmplitude q • kestenLikelihoodVector q) := by
  rw [inner_smul_left, inner_smul_right, inner_kestenLikelihoodVector,
    xiTransverseGammaValuationSzegoKernel_eq_scaled_primeHardy_inner]
  simp only [conj_trivial]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon


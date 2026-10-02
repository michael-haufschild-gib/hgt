import GaloisForLFunctions.RHTower.PrimeBurnolFourierPair
import GaloisForLFunctions.RHTower.PrimeBurnolDepthCompletion
import GaloisForLFunctions.RHTower.EvenL2LogUnitary
import GaloisForLFunctions.HTGeometry.HalfLineMellinUnitary

/-!
# Exact completion of the Fourier-paired prime source

The canonical even-extension unitary carries the already proved single-prime depth density
onto the actual even physical carrier. The two-coordinate finite source core is dense, while
its bounded joint synthesis S(x,y)=x+Fourier(y) has the exact kernel x=-Fourier(y).
An explicit section and kernel projection split the completion. The inverse is unbounded
on the finite source core, and the original neutral coordinate does not descend. Canonical
section compression instead gives half the identity, with exact idempotence defect -I/4.

This classifies this actual source/Fourier completion. It does not identify a Gamma–Xi seam,
construct a Hardy projection or index, or prove a sub-unit source action.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators FourierTransform InnerProductSpace
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

def primeBurnolEvenColumn (pe : Nat.Primes × ℕ) : evenSubspace :=
  ⟨primeBurnolEvenFeatureLp pe, primeBurnolEvenFeatureLp_mem_evenSubspace pe⟩

def primeBurnolEvenExtension : primeBurnolHalfLineL2 ≃ₗᵢ[ℂ] evenSubspace :=
  halfLineExpUnitary.trans logEvenUnitary.symm

theorem primeBurnolEvenColumn_eq_extension (pe : Nat.Primes × ℕ) :
    primeBurnolEvenColumn pe = (Real.sqrt 2 : ℂ) •
      primeBurnolEvenExtension (primeBurnolWindowFeatureLp pe 0) := by
  apply logEvenUnitary.injective
  rw [map_smul]
  change logEvenUnitary (primeBurnolEvenColumn pe) =
    (Real.sqrt 2 : ℂ) • logEvenUnitary
      (logEvenUnitary.symm (halfLineExpUnitary (primeBurnolWindowFeatureLp pe 0)))
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  have hf := (ae_restrict_iff' measurableSet_Ioi).mp (primeBurnolWindowFeatureLp_coeFn pe 0)
  have hpull := realExp_quasiMeasurePreserving.ae hf
  have hraw := realExp_quasiMeasurePreserving.ae (primeBurnolEvenFeatureLp_coeFn pe)
  filter_upwards [logEvenUnitary_ae (primeBurnolEvenColumn pe),
    Lp.coeFn_smul (Real.sqrt 2 : ℂ) (halfLineExpUnitary (primeBurnolWindowFeatureLp pe 0)),
    halfLineExpUnitary_ae (primeBurnolWindowFeatureLp pe 0), hpull, hraw]
      with t hlog hsmul hhalf hp hr
  change primeBurnolEvenFeatureLp pe (Real.exp t) = _ at hr
  have hp' := hp (Real.exp_pos t)
  rw [hlog, hsmul, Pi.smul_apply, hhalf, smul_eq_mul, hp']
  change ((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
      primeBurnolEvenFeatureLp pe (Real.exp t) = _
  rw [hr, primeBurnolEvenFeature, abs_of_pos (Real.exp_pos t)]
  have hsqrt : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [hsqrt, Complex.ofReal_mul, mul_assoc]

def primeBurnolEvenDepthSpan (p : Nat.Primes) : Submodule ℂ evenSubspace :=
  Submodule.span ℂ (Set.range (fun n => primeBurnolEvenColumn (p,n)))

theorem dense_primeBurnolEvenDepthSpan (p : Nat.Primes) :
    Dense (primeBurnolEvenDepthSpan p : Set evenSubspace) := by
  have hd := primeBurnolEvenExtension.surjective.denseRange.dense_image
    primeBurnolEvenExtension.continuous (dense_primeBurnolLiteralDepthSpan p)
  have hmap : primeBurnolLiteralDepthSpan p ≤
      (primeBurnolEvenDepthSpan p).comap primeBurnolEvenExtension.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change primeBurnolEvenExtension (primeBurnolWindowFeatureLp (p,n) 0) ∈ primeBurnolEvenDepthSpan p
    have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    have heq : primeBurnolEvenExtension (primeBurnolWindowFeatureLp (p,n) 0) =
        (Real.sqrt 2 : ℂ)⁻¹ • primeBurnolEvenColumn (p,n) := by
      rw [primeBurnolEvenColumn_eq_extension, smul_smul, inv_mul_cancel₀ hsqrt, one_smul]
    rw [heq]
    exact (primeBurnolEvenDepthSpan p).smul_mem _ (Submodule.subset_span ⟨n,rfl⟩)
  apply hd.mono
  rintro _ ⟨x, hx, rfl⟩
  exact hmap hx

/-- Actual finite-source coordinate core before applying the Fourier channel. -/
def primeBurnolFourierCoordinateCore (p : Nat.Primes) : Submodule ℂ (evenSubspace × evenSubspace) :=
  (primeBurnolEvenDepthSpan p).prod (primeBurnolEvenDepthSpan p)

theorem dense_primeBurnolFourierCoordinateCore (p : Nat.Primes) :
    Dense (primeBurnolFourierCoordinateCore p : Set (evenSubspace × evenSubspace)) :=
  (dense_primeBurnolEvenDepthSpan p).prod (dense_primeBurnolEvenDepthSpan p)

/-- Bounded joint synthesis of the two completed literal source coordinates. -/
def primeBurnolFourierSynthesis : (evenSubspace × evenSubspace) →L[ℂ] evenSubspace :=
  ContinuousLinearMap.fst ℂ evenSubspace evenSubspace +
    evenFourierTransform ∘L ContinuousLinearMap.snd ℂ evenSubspace evenSubspace

@[simp] theorem primeBurnolFourierSynthesis_apply (z : evenSubspace × evenSubspace) :
    primeBurnolFourierSynthesis z = z.1 + evenFourierTransform z.2 := rfl

theorem primeBurnolFourierSynthesis_surjective : Function.Surjective primeBurnolFourierSynthesis := by
  intro v
  exact ⟨(v,0), by simp⟩

theorem primeBurnolFourierSynthesis_kernel (z : evenSubspace × evenSubspace) :
    primeBurnolFourierSynthesis z = 0 ↔ z.1 = -evenFourierTransform z.2 := by
  rw [primeBurnolFourierSynthesis_apply, eq_neg_iff_add_eq_zero]

/-- Canonical Fourier-diagonal section of completed synthesis. -/
def primeBurnolFourierSection : evenSubspace →L[ℂ] (evenSubspace × evenSubspace) :=
  ((1 / 2 : ℂ) • ContinuousLinearMap.id ℂ evenSubspace).prod
    ((1 / 2 : ℂ) • evenFourierTransform)

/-- Exact projection onto the completed kernel, retaining both mixed Fourier terms. -/
def primeBurnolFourierKernelProjection :
    (evenSubspace × evenSubspace) →L[ℂ] (evenSubspace × evenSubspace) :=
  ((1 / 2 : ℂ) • (ContinuousLinearMap.fst ℂ evenSubspace evenSubspace -
    evenFourierTransform ∘L ContinuousLinearMap.snd ℂ evenSubspace evenSubspace)).prod
  ((1 / 2 : ℂ) • (ContinuousLinearMap.snd ℂ evenSubspace evenSubspace -
    evenFourierTransform ∘L ContinuousLinearMap.fst ℂ evenSubspace evenSubspace))

theorem primeBurnolFourierSection_rightInverse (v : evenSubspace) :
    primeBurnolFourierSynthesis (primeBurnolFourierSection v) = v := by
  change (1/2 : ℂ) • v + evenFourierTransform ((1/2 : ℂ) • evenFourierTransform v) = v
  rw [map_smul, evenFourierTransform_involutive]
  module

theorem primeBurnolFourierKernelProjection_mem_kernel (z : evenSubspace × evenSubspace) :
    primeBurnolFourierSynthesis (primeBurnolFourierKernelProjection z) = 0 := by
  change (1/2 : ℂ) • (z.1 - evenFourierTransform z.2) +
    evenFourierTransform ((1/2 : ℂ) • (z.2 - evenFourierTransform z.1)) = 0
  rw [map_smul, map_sub, evenFourierTransform_involutive]
  module

theorem primeBurnolFourier_kernel_diagonal_decomposition (z : evenSubspace × evenSubspace) :
    primeBurnolFourierSection (primeBurnolFourierSynthesis z) +
      primeBurnolFourierKernelProjection z = z := by
  apply Prod.ext
  · change (1/2 : ℂ) • (z.1 + evenFourierTransform z.2) +
      (1/2 : ℂ) • (z.1 - evenFourierTransform z.2) = z.1
    module
  · change (1/2 : ℂ) • evenFourierTransform (z.1 + evenFourierTransform z.2) +
      (1/2 : ℂ) • (z.2 - evenFourierTransform z.1) = z.2
    rw [map_add, evenFourierTransform_involutive]
    module

theorem primeBurnolFourierKernelProjection_eq_self_iff (z : evenSubspace × evenSubspace) :
    primeBurnolFourierKernelProjection z = z ↔ primeBurnolFourierSynthesis z = 0 := by
  constructor
  · intro h
    rw [← h]
    exact primeBurnolFourierKernelProjection_mem_kernel z
  · intro h
    have hd := primeBurnolFourier_kernel_diagonal_decomposition z
    simpa only [h, map_zero, zero_add] using hd

theorem primeBurnolFourierKernelProjection_idempotent (z : evenSubspace × evenSubspace) :
    primeBurnolFourierKernelProjection (primeBurnolFourierKernelProjection z) =
      primeBurnolFourierKernelProjection z :=
  (primeBurnolFourierKernelProjection_eq_self_iff _).mpr
    (primeBurnolFourierKernelProjection_mem_kernel z)

theorem primeBurnolEvenColumn_ne_zero (pe : Nat.Primes × ℕ) : primeBurnolEvenColumn pe ≠ 0 := by
  intro hz
  have hzLp : primeBurnolEvenFeatureLp pe = 0 := congrArg Subtype.val hz
  have hae : primeBurnolEvenFeature pe =ᵐ[volume] fun _ => (0 : ℂ) := by
    have h := primeBurnolEvenFeatureLp_coeFn pe
    rw [hzLp] at h
    exact h.symm.trans (Lp.coeFn_zero ℂ 2 volume)
  have hpoint := congrFun (Measure.eq_of_ae_eq hae
    (continuous_primeBurnolEvenFeature pe) continuous_const) 1
  simp only [primeBurnolEvenFeature, abs_one, primeBurnolWindowFeature,
    primeBurnolComplexExponent, Complex.ofReal_zero,
    Complex.ofReal_one, mul_one] at hpoint
  exact (mul_ne_zero (primeBurnolAmplitude_ne_zero pe) (Complex.exp_ne_zero _)) hpoint

def primeBurnolFourierKernelWitness (pe : Nat.Primes × ℕ) : evenSubspace × evenSubspace :=
  (-evenFourierTransform (primeBurnolEvenColumn pe), primeBurnolEvenColumn pe)

theorem primeBurnolFourierKernelWitness_ne_zero (pe : Nat.Primes × ℕ) :
    primeBurnolFourierKernelWitness pe ≠ 0 := by
  intro hz
  exact primeBurnolEvenColumn_ne_zero pe (congrArg Prod.snd hz)

@[simp] theorem primeBurnolFourierKernelWitness_synthesis (pe : Nat.Primes × ℕ) :
    primeBurnolFourierSynthesis (primeBurnolFourierKernelWitness pe) = 0 := by
  change -evenFourierTransform (primeBurnolEvenColumn pe) +
    evenFourierTransform (primeBurnolEvenColumn pe) = 0
  exact neg_add_cancel _

def primeBurnolFourierNeutral :
    (evenSubspace × evenSubspace) →L[ℂ] (evenSubspace × evenSubspace) :=
  (ContinuousLinearMap.fst ℂ evenSubspace evenSubspace).prod 0

/-- Neutral coordinate compression through the canonical Fourier-diagonal section. -/
def primeBurnolFourierNeutralCompression : evenSubspace →L[ℂ] evenSubspace :=
  primeBurnolFourierSynthesis ∘L primeBurnolFourierNeutral ∘L primeBurnolFourierSection

theorem primeBurnolFourierNeutralCompression_eq_half :
    primeBurnolFourierNeutralCompression = (1/2 : ℂ) • ContinuousLinearMap.id ℂ evenSubspace := by
  apply ContinuousLinearMap.ext
  intro v
  change (1/2 : ℂ) • v + evenFourierTransform 0 = (1/2 : ℂ) • v
  rw [map_zero, add_zero]

theorem primeBurnolFourierNeutralCompression_idempotence_defect :
    primeBurnolFourierNeutralCompression * primeBurnolFourierNeutralCompression -
      primeBurnolFourierNeutralCompression =
      (-1/4 : ℂ) • ContinuousLinearMap.id ℂ evenSubspace := by
  rw [primeBurnolFourierNeutralCompression_eq_half]
  apply ContinuousLinearMap.ext
  intro v
  change (1/2 : ℂ) • ((1/2 : ℂ) • v) - (1/2 : ℂ) • v = (-1/4 : ℂ) • v
  module

/-- The literal neutral coordinate projection does not preserve the completed source kernel. -/
theorem primeBurnolFourierNeutral_not_kernel_preserving (pe : Nat.Primes × ℕ) :
    primeBurnolFourierSynthesis
      (primeBurnolFourierNeutral (primeBurnolFourierKernelWitness pe)) ≠ 0 := by
  change -evenFourierTransform (primeBurnolEvenColumn pe) + evenFourierTransform 0 ≠ 0
  rw [map_zero, add_zero]
  apply neg_ne_zero.mpr
  intro h
  apply primeBurnolEvenColumn_ne_zero pe
  have := congrArg evenFourierTransform h
  simpa only [evenFourierTransform_involutive, map_zero] using this

/-- No finite physical channel bound controls the inverse on the complete finite-depth core. -/
theorem primeBurnolFourierCoordinateCore_inverse_escape (p : Nat.Primes) (C : ℝ) :
    ∃ z ∈ primeBurnolFourierCoordinateCore p,
      C * ‖primeBurnolFourierSynthesis z‖ < ‖z‖ := by
  by_contra! hbound
  have hclosed : IsClosed {z : evenSubspace × evenSubspace |
      ‖z‖ ≤ C * ‖primeBurnolFourierSynthesis z‖} :=
    isClosed_le continuous_norm (continuous_const.mul primeBurnolFourierSynthesis.continuous.norm)
  have hle := hclosed.closure_subset_iff.mpr hbound
    ((dense_primeBurnolFourierCoordinateCore p) (primeBurnolFourierKernelWitness (p,0)))
  change ‖primeBurnolFourierKernelWitness (p,0)‖ ≤
    C * ‖primeBurnolFourierSynthesis (primeBurnolFourierKernelWitness (p,0))‖ at hle
  rw [primeBurnolFourierKernelWitness_synthesis, norm_zero, mul_zero] at hle
  exact primeBurnolFourierKernelWitness_ne_zero (p,0) (norm_le_zero_iff.mp hle)

end RHTower

import GaloisForLFunctions.HTGeometry.LinearPMapBoundedUnitaryTransport
import GaloisForLFunctions.RHTower.SoninEvenCarrier

/-!
# Closed weight-one Clifford--Dirac operator on the log line

This module constructs the maximal Fourier-coordinate realization of `∂ₓ + aR`, proves its
closedness, identifies its exact natural square domain with the maximal quadratic-energy domain,
and proves that square self-adjoint. It then transports both operators to physical log-line `L²`.
-/

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Set Filter
open scoped ENNReal LinearPMap

namespace RHTower

/-- Maximal multiplication by the Fourier coordinate. -/
def weightOneSpectralCoordinate : SoninL2 →ₗ.[ℂ] SoninL2 :=
  GaloisForLFunctions.HTGeometry.maximalRealL2Mul volume id

/-- Fourier realization of the weak derivative: multiplication by `2πiξ`. -/
def weightOneSpectralDerivative : SoninL2 →ₗ.[ℂ] SoninL2 :=
  (2 * Real.pi * Complex.I : ℂ) • weightOneSpectralCoordinate

/-- Spectral realization of `∂ + aR` on the maximal first-coordinate domain. -/
def weightOneSpectralDirac (a : ℝ) : SoninL2 →ₗ.[ℂ] SoninL2 :=
  (((a : ℂ) • l2Reflection).toLinearMap +ᵥ weightOneSpectralDerivative)

@[simp] theorem weightOneSpectralCoordinate_domain :
    weightOneSpectralCoordinate.domain =
      GaloisForLFunctions.HTGeometry.maximalRealL2MulDomain volume id := rfl

@[simp] theorem weightOneSpectralDerivative_domain :
    weightOneSpectralDerivative.domain = weightOneSpectralCoordinate.domain := rfl

@[simp] theorem weightOneSpectralDirac_domain (a : ℝ) :
    (weightOneSpectralDirac a).domain = weightOneSpectralCoordinate.domain := rfl

theorem l2Reflection_mem_weightOneSpectralCoordinate_domain
    (f : SoninL2) (hf : f ∈ weightOneSpectralCoordinate.domain) :
    l2Reflection f ∈ weightOneSpectralCoordinate.domain := by
  let fM : weightOneSpectralCoordinate.domain := ⟨f, hf⟩
  change MemLp (fun x : ℝ => (x : ℂ) * (l2Reflection f : ℝ → ℂ) x) 2 volume
  refine (memLp_congr_ae ?_).mpr (Lp.memLp (-l2Reflection (weightOneSpectralCoordinate fM)))
  have hMneg :=
    (GaloisForLFunctions.HTGeometry.maximalRealL2Mul_apply_ae volume id fM).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_neg (l2Reflection (weightOneSpectralCoordinate fM)),
    l2Reflection_ae (weightOneSpectralCoordinate fM), hMneg,
    l2Reflection_ae f] with x hneg hrefM hM href
  change (weightOneSpectralCoordinate fM : ℝ → ℂ) (-x) =
    ((-x : ℝ) : ℂ) * (f : ℝ → ℂ) (-x) at hM
  rw [hneg, Pi.neg_apply, hrefM, hM, href]
  push_cast
  ring

theorem weightOneSpectralCoordinate_l2Reflection
    (f : weightOneSpectralCoordinate.domain) :
    weightOneSpectralCoordinate
        ⟨l2Reflection (f : SoninL2),
          l2Reflection_mem_weightOneSpectralCoordinate_domain f f.property⟩ =
      -l2Reflection (weightOneSpectralCoordinate f) := by
  apply Lp.ext
  have hMneg :=
    (GaloisForLFunctions.HTGeometry.maximalRealL2Mul_apply_ae volume id f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [GaloisForLFunctions.HTGeometry.maximalRealL2Mul_apply_ae volume id
      ⟨l2Reflection (f : SoninL2),
        l2Reflection_mem_weightOneSpectralCoordinate_domain f f.property⟩,
    l2Reflection_ae (weightOneSpectralCoordinate f), hMneg,
    l2Reflection_ae (f : SoninL2),
    Lp.coeFn_neg (l2Reflection (weightOneSpectralCoordinate f))]
      with x hleft hrefM hM href hneg
  change (weightOneSpectralCoordinate
      ⟨l2Reflection (f : SoninL2),
        l2Reflection_mem_weightOneSpectralCoordinate_domain f f.property⟩ : ℝ → ℂ) x =
    (x : ℂ) * (l2Reflection (f : SoninL2) : ℝ → ℂ) x at hleft
  change (weightOneSpectralCoordinate f : ℝ → ℂ) (-x) =
    ((-x : ℝ) : ℂ) * (f : ℝ → ℂ) (-x) at hM
  rw [hleft, hneg, Pi.neg_apply, hrefM, hM, href]
  push_cast
  ring

theorem weightOneSpectralDirac_isClosed (a : ℝ) :
    (weightOneSpectralDirac a).IsClosed := by
  apply GaloisForLFunctions.HTGeometry.LinearPMap.IsClosed.continuousLinearMap_vadd
  apply GaloisForLFunctions.HTGeometry.LinearPMap.IsClosed.smul_of_ne
  · exact (GaloisForLFunctions.HTGeometry.maximalRealL2Mul_isSelfAdjoint
      volume measurable_id).isClosed
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero

@[simp] theorem weightOneSpectralDirac_apply (a : ℝ)
    (f : (weightOneSpectralDirac a).domain) :
    weightOneSpectralDirac a f =
      (a : ℂ) • l2Reflection (f : SoninL2) +
        (2 * Real.pi * Complex.I : ℂ) • weightOneSpectralCoordinate
          ⟨(f : SoninL2), f.property⟩ := rfl

/-- Real Fourier energy of the Clifford square. -/
def weightOneSpectralSquareEnergy (a ξ : ℝ) : ℝ :=
  a ^ 2 - (2 * Real.pi) ^ 2 * ξ ^ 2

/-- Maximal real multiplier expected from the natural square of the spectral Dirac operator. -/
def weightOneSpectralSquare (a : ℝ) : SoninL2 →ₗ.[ℂ] SoninL2 :=
  GaloisForLFunctions.HTGeometry.maximalRealL2Mul volume
    (weightOneSpectralSquareEnergy a)

theorem measurable_weightOneSpectralSquareEnergy (a : ℝ) :
    Measurable (weightOneSpectralSquareEnergy a) := by
  unfold weightOneSpectralSquareEnergy
  fun_prop

theorem weightOneSpectralSquare_isSelfAdjoint (a : ℝ) :
    IsSelfAdjoint (weightOneSpectralSquare a) :=
  GaloisForLFunctions.HTGeometry.maximalRealL2Mul_isSelfAdjoint volume
    (measurable_weightOneSpectralSquareEnergy a)

private theorem memLp_coordinate_of_memLp_squareCoordinate (f : SoninL2)
    (h2 : MemLp (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x) 2 volume) :
    MemLp (fun x : ℝ => (x : ℂ) * (f : ℝ → ℂ) x) 2 volume := by
  have hsum : MemLp
      ((fun x : ℝ => (f : ℝ → ℂ) x) +
        fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x) 2 volume :=
    (Lp.memLp f).add h2
  apply hsum.of_le
  · exact ((Complex.continuous_ofReal.comp continuous_id).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  · filter_upwards with x
    change ‖(x : ℂ) * (f : ℝ → ℂ) x‖ ≤
      ‖(f : ℝ → ℂ) x + ((x ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x‖
    have heq : (f : ℝ → ℂ) x + ((x ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x =
        (((1 + x ^ 2 : ℝ) : ℂ)) * (f : ℝ → ℂ) x := by
      push_cast
      ring
    rw [heq, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hx : |x| ≤ |1 + x ^ 2| := by
      have hpos : 0 ≤ 1 + x ^ 2 := by positivity
      conv_rhs => rw [abs_of_nonneg hpos]
      nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

private theorem memLp_squareCoordinate_of_memLp_energy (a : ℝ) (f : SoninL2)
    (hE : MemLp (fun x : ℝ => (weightOneSpectralSquareEnergy a x : ℂ) *
      (f : ℝ → ℂ) x) 2 volume) :
    MemLp (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x) 2 volume := by
  have hraw : MemLp (fun x : ℝ =>
      ((a ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x -
        (weightOneSpectralSquareEnergy a x : ℂ) * (f : ℝ → ℂ) x) 2 volume :=
    ((Lp.memLp f).const_mul ((a ^ 2 : ℝ) : ℂ)).sub hE
  have hscaled := hraw.const_mul ((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹)
  refine (memLp_congr_ae ?_).mpr hscaled
  filter_upwards with x
  change ((x ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x =
    ((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) *
      (((a ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x -
        (weightOneSpectralSquareEnergy a x : ℂ) * (f : ℝ → ℂ) x)
  unfold weightOneSpectralSquareEnergy
  have hpi : ((2 * Real.pi) ^ 2 : ℝ) ≠ 0 := by
    positivity
  push_cast
  field_simp
  ring

private theorem memLp_energy_of_memLp_squareCoordinate (a : ℝ) (f : SoninL2)
    (h2 : MemLp (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x) 2 volume) :
    MemLp (fun x : ℝ => (weightOneSpectralSquareEnergy a x : ℂ) *
      (f : ℝ → ℂ) x) 2 volume := by
  have hraw : MemLp (fun x : ℝ =>
      ((a ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x -
        (((2 * Real.pi) ^ 2 : ℝ) : ℂ) *
          (((x ^ 2 : ℝ) : ℂ) * (f : ℝ → ℂ) x)) 2 volume :=
    ((Lp.memLp f).const_mul ((a ^ 2 : ℝ) : ℂ)).sub
      (h2.const_mul ((((2 * Real.pi) ^ 2 : ℝ) : ℂ)))
  refine (memLp_congr_ae ?_).mpr hraw
  filter_upwards with x
  unfold weightOneSpectralSquareEnergy
  push_cast
  ring

theorem weightOneSpectralSquare_domain_iff_secondCoordinate (a : ℝ) (f : SoninL2) :
    f ∈ (weightOneSpectralSquare a).domain ↔
      ∃ hf : f ∈ weightOneSpectralCoordinate.domain,
        weightOneSpectralCoordinate ⟨f, hf⟩ ∈ weightOneSpectralCoordinate.domain := by
  constructor
  · intro hE
    change MemLp (fun x : ℝ => (weightOneSpectralSquareEnergy a x : ℂ) *
      (f : ℝ → ℂ) x) 2 volume at hE
    have h2 := memLp_squareCoordinate_of_memLp_energy a f hE
    have h1 := memLp_coordinate_of_memLp_squareCoordinate f h2
    have hf : f ∈ weightOneSpectralCoordinate.domain := h1
    refine ⟨hf, ?_⟩
    change MemLp (fun x : ℝ => (x : ℂ) *
      (weightOneSpectralCoordinate ⟨f, hf⟩ : ℝ → ℂ) x) 2 volume
    refine (memLp_congr_ae ?_).mpr h2
    filter_upwards [GaloisForLFunctions.HTGeometry.maximalRealL2Mul_apply_ae
      volume id ⟨f, hf⟩] with x hx
    change (weightOneSpectralCoordinate ⟨f, hf⟩ : ℝ → ℂ) x =
      (x : ℂ) * (f : ℝ → ℂ) x at hx
    rw [hx]
    push_cast
    ring
  · rintro ⟨hf, hsecond⟩
    change MemLp (fun x : ℝ => (x : ℂ) *
      (weightOneSpectralCoordinate ⟨f, hf⟩ : ℝ → ℂ) x) 2 volume at hsecond
    have h2 : MemLp (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) *
        (f : ℝ → ℂ) x) 2 volume := by
      refine (memLp_congr_ae ?_).mpr hsecond
      filter_upwards [GaloisForLFunctions.HTGeometry.maximalRealL2Mul_apply_ae
        volume id ⟨f, hf⟩] with x hx
      change (weightOneSpectralCoordinate ⟨f, hf⟩ : ℝ → ℂ) x =
        (x : ℂ) * (f : ℝ → ℂ) x at hx
      rw [hx]
      push_cast
      ring
    exact memLp_energy_of_memLp_squareCoordinate a f h2

theorem weightOneSpectralDirac_apply_mem_domain_iff (a : ℝ)
    (f : (weightOneSpectralDirac a).domain) :
    weightOneSpectralDirac a f ∈ (weightOneSpectralDirac a).domain ↔
      weightOneSpectralCoordinate ⟨(f : SoninL2), f.property⟩ ∈
        weightOneSpectralCoordinate.domain := by
  let c : ℂ := 2 * Real.pi * Complex.I
  let fM : weightOneSpectralCoordinate.domain :=
    ⟨(f : SoninL2), by
      simpa only [weightOneSpectralDirac_domain] using f.property⟩
  change weightOneSpectralDirac a f ∈ weightOneSpectralCoordinate.domain ↔
    weightOneSpectralCoordinate fM ∈ weightOneSpectralCoordinate.domain
  have hc : c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have href : l2Reflection (f : SoninL2) ∈ weightOneSpectralCoordinate.domain :=
    l2Reflection_mem_weightOneSpectralCoordinate_domain f fM.property
  have har : (a : ℂ) • l2Reflection (f : SoninL2) ∈
      weightOneSpectralCoordinate.domain :=
    weightOneSpectralCoordinate.domain.smul_mem (a : ℂ) href
  constructor
  · intro hq
    have hsub := weightOneSpectralCoordinate.domain.sub_mem hq har
    have heq : weightOneSpectralDirac a f - (a : ℂ) • l2Reflection (f : SoninL2) =
        c • weightOneSpectralCoordinate fM := by
      rw [weightOneSpectralDirac_apply]
      dsimp only [c, fM]
      abel
    rw [heq] at hsub
    have hcM : c • weightOneSpectralCoordinate fM ∈
        weightOneSpectralCoordinate.domain := hsub
    have hinv := weightOneSpectralCoordinate.domain.smul_mem c⁻¹ hcM
    rw [inv_smul_smul₀ hc] at hinv
    exact hinv
  · intro hM
    have hcM : c • weightOneSpectralCoordinate fM ∈
        weightOneSpectralCoordinate.domain :=
      weightOneSpectralCoordinate.domain.smul_mem c hM
    have hadd := weightOneSpectralCoordinate.domain.add_mem har hcM
    have heq : (a : ℂ) • l2Reflection (f : SoninL2) +
        c • weightOneSpectralCoordinate fM = weightOneSpectralDirac a f := by
      rw [weightOneSpectralDirac_apply]
    rw [heq] at hadd
    exact hadd

/-- Exact natural-square domain: `f ∈ D(Q_a)` and `Q_a f ∈ D(Q_a)`. -/
theorem weightOneSpectralSquare_domain_iff_naturalDiracSquare (a : ℝ) (f : SoninL2) :
    f ∈ (weightOneSpectralSquare a).domain ↔
      ∃ hf : f ∈ (weightOneSpectralDirac a).domain,
        weightOneSpectralDirac a ⟨f, hf⟩ ∈ (weightOneSpectralDirac a).domain := by
  rw [weightOneSpectralSquare_domain_iff_secondCoordinate]
  constructor
  · rintro ⟨hf, hsecond⟩
    refine ⟨hf, ?_⟩
    exact (weightOneSpectralDirac_apply_mem_domain_iff a ⟨f, hf⟩).2 hsecond
  · rintro ⟨hf, hq⟩
    refine ⟨hf, ?_⟩
    exact (weightOneSpectralDirac_apply_mem_domain_iff a ⟨f, hf⟩).1 hq

theorem weightOneSpectralSquare_domain_le_dirac (a : ℝ) :
    (weightOneSpectralSquare a).domain ≤ (weightOneSpectralDirac a).domain := by
  intro f hf
  exact (weightOneSpectralSquare_domain_iff_naturalDiracSquare a f).1 hf |>.choose

theorem weightOneSpectralSquare_mem_iff_dirac_apply_mem (a : ℝ) (f : SoninL2)
    (hf : f ∈ (weightOneSpectralDirac a).domain) :
    f ∈ (weightOneSpectralSquare a).domain ↔
      weightOneSpectralDirac a ⟨f, hf⟩ ∈ (weightOneSpectralDirac a).domain := by
  constructor
  · intro hsquare
    obtain ⟨hf', hQ⟩ :=
      (weightOneSpectralSquare_domain_iff_naturalDiracSquare a f).1 hsquare
    simpa only [Subsingleton.elim hf' hf] using hQ
  · intro hQ
    exact (weightOneSpectralSquare_domain_iff_naturalDiracSquare a f).2 ⟨hf, hQ⟩

theorem weightOneSpectralDirac_apply_ae (a : ℝ)
    (f : (weightOneSpectralDirac a).domain) :
    (weightOneSpectralDirac a f : ℝ → ℂ) =ᵐ[volume]
      fun x => (a : ℂ) * (f : SoninL2) (-x) +
        (2 * Real.pi * Complex.I : ℂ) * (x : ℂ) * (f : SoninL2) x := by
  let fM : weightOneSpectralCoordinate.domain :=
    ⟨(f : SoninL2), by
      simpa only [weightOneSpectralDirac_domain] using f.property⟩
  have hQ : weightOneSpectralDirac a f =
      (a : ℂ) • l2Reflection (f : SoninL2) +
        (2 * Real.pi * Complex.I : ℂ) • weightOneSpectralCoordinate fM := by
    rw [weightOneSpectralDirac_apply]
  rw [hQ]
  filter_upwards [Lp.coeFn_add ((a : ℂ) • l2Reflection (f : SoninL2))
      ((2 * Real.pi * Complex.I : ℂ) •
        weightOneSpectralCoordinate fM),
    Lp.coeFn_smul (a : ℂ) (l2Reflection (f : SoninL2)),
    l2Reflection_ae (f : SoninL2),
    Lp.coeFn_smul (2 * Real.pi * Complex.I : ℂ)
      (weightOneSpectralCoordinate fM),
    GaloisForLFunctions.HTGeometry.maximalRealL2Mul_apply_ae volume id
      fM] with x hadd ha href hc hM
  change (weightOneSpectralCoordinate fM : ℝ → ℂ) x =
    (x : ℂ) * (f : SoninL2) x at hM
  rw [hadd, Pi.add_apply, ha, Pi.smul_apply, href, hc, Pi.smul_apply, hM]
  change (a : ℂ) * (f : SoninL2) (-x) +
      (2 * Real.pi * Complex.I : ℂ) * ((x : ℂ) * (f : SoninL2) x) = _
  ring

/-- On its exact natural composition domain, the spectral Clifford square is the maximal real
quadratic-energy multiplier. -/
theorem weightOneSpectralDirac_sq_apply (a : ℝ)
    (f : (weightOneSpectralSquare a).domain)
    (hf : (f : SoninL2) ∈ (weightOneSpectralDirac a).domain)
    (hQ : weightOneSpectralDirac a ⟨(f : SoninL2), hf⟩ ∈
      (weightOneSpectralDirac a).domain) :
    weightOneSpectralDirac a
        ⟨weightOneSpectralDirac a ⟨(f : SoninL2), hf⟩, hQ⟩ =
      weightOneSpectralSquare a f := by
  let qf : (weightOneSpectralDirac a).domain :=
    ⟨weightOneSpectralDirac a ⟨(f : SoninL2), hf⟩, hQ⟩
  apply Lp.ext
  have hqneg := (weightOneSpectralDirac_apply_ae a ⟨(f : SoninL2), hf⟩).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [weightOneSpectralDirac_apply_ae a qf, hqneg,
    weightOneSpectralDirac_apply_ae a ⟨(f : SoninL2), hf⟩,
    GaloisForLFunctions.HTGeometry.maximalRealL2Mul_apply_ae volume
      (weightOneSpectralSquareEnergy a) f] with x hqq hqneg hq hsquare
  change (weightOneSpectralDirac a qf : ℝ → ℂ) x =
    (weightOneSpectralSquare a f : ℝ → ℂ) x
  change (weightOneSpectralSquare a f : ℝ → ℂ) x =
    (weightOneSpectralSquareEnergy a x : ℂ) * (f : SoninL2) x at hsquare
  rw [hqq, hsquare]
  have hqneg' : (qf : SoninL2) (-x) =
      (a : ℂ) * (f : SoninL2) x +
        (2 * Real.pi * Complex.I : ℂ) * ((-x : ℝ) : ℂ) * (f : SoninL2) (-x) := by
    simpa only [Function.comp_apply, neg_neg] using hqneg
  change (qf : SoninL2) x =
    (a : ℂ) * (f : SoninL2) (-x) +
      (2 * Real.pi * Complex.I : ℂ) * (x : ℂ) * (f : SoninL2) x at hq
  rw [hqneg', hq]
  unfold weightOneSpectralSquareEnergy
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Closed log-line realization of `∂ₓ + aR`, obtained by inverse Fourier transport. -/
def weightOneLogDirac (a : ℝ) : SoninL2 →ₗ.[ℂ] SoninL2 :=
  GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap fourierUnitary
    (weightOneSpectralDirac a)

/-- Self-adjoint log-line square transported from the maximal real spectral multiplier. -/
def weightOneLogSquare (a : ℝ) : SoninL2 →ₗ.[ℂ] SoninL2 :=
  GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap fourierUnitary
    (weightOneSpectralSquare a)

@[simp] theorem weightOneLogDirac_domain (a : ℝ) :
    (weightOneLogDirac a).domain =
      (weightOneSpectralDirac a).domain.comap
        fourierUnitary.toLinearEquiv.toLinearMap := rfl

@[simp] theorem weightOneLogSquare_domain (a : ℝ) :
    (weightOneLogSquare a).domain =
      (weightOneSpectralSquare a).domain.comap
        fourierUnitary.toLinearEquiv.toLinearMap := rfl

theorem weightOneLogDirac_isClosed (a : ℝ) : (weightOneLogDirac a).IsClosed :=
  GaloisForLFunctions.HTGeometry.LinearPMap.IsClosed.unitaryConjugate
    (weightOneSpectralDirac_isClosed a)

theorem weightOneLogSquare_isSelfAdjoint (a : ℝ) :
    IsSelfAdjoint (weightOneLogSquare a) :=
  GaloisForLFunctions.HTGeometry.IsSelfAdjoint.unitaryConjugate fourierUnitary
    (weightOneSpectralSquare_isSelfAdjoint a)

@[simp] theorem fourierUnitary_weightOneLogDirac_apply (a : ℝ)
    (f : (weightOneLogDirac a).domain) :
    fourierUnitary (weightOneLogDirac a f) =
      weightOneSpectralDirac a
        (GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
          fourierUnitary (weightOneSpectralDirac a) f) := by
  simp only [weightOneLogDirac,
    GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem weightOneLogSquare_domain_le_dirac (a : ℝ) :
    (weightOneLogSquare a).domain ≤ (weightOneLogDirac a).domain := by
  intro f hf
  exact weightOneSpectralSquare_domain_le_dirac a hf

/-- Explicit natural-domain criterion. Once `f ∈ D(Q_a)` is fixed, membership in the square
domain is equivalent to `Q_a f ∈ D(Q_a)`. -/
theorem weightOneLogSquare_mem_iff_dirac_apply_mem (a : ℝ) (f : SoninL2)
    (hf : f ∈ (weightOneLogDirac a).domain) :
    f ∈ (weightOneLogSquare a).domain ↔
      weightOneLogDirac a ⟨f, hf⟩ ∈ (weightOneLogDirac a).domain := by
  let fspec : (weightOneSpectralDirac a).domain :=
    GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
      fourierUnitary (weightOneSpectralDirac a) ⟨f, hf⟩
  change fourierUnitary f ∈ (weightOneSpectralSquare a).domain ↔
    fourierUnitary (weightOneLogDirac a ⟨f, hf⟩) ∈
      (weightOneSpectralDirac a).domain
  rw [fourierUnitary_weightOneLogDirac_apply]
  exact weightOneSpectralSquare_mem_iff_dirac_apply_mem a (fourierUnitary f)
    fspec.property

/-- The log-line natural square is exactly the unitary transport of the maximal quadratic-energy
multiplier. -/
theorem weightOneLogDirac_sq_apply (a : ℝ)
    (f : (weightOneLogSquare a).domain)
    (hf : (f : SoninL2) ∈ (weightOneLogDirac a).domain)
    (hQ : weightOneLogDirac a ⟨(f : SoninL2), hf⟩ ∈
      (weightOneLogDirac a).domain) :
    weightOneLogDirac a ⟨weightOneLogDirac a ⟨(f : SoninL2), hf⟩, hQ⟩ =
      weightOneLogSquare a f := by
  let fsq : (weightOneSpectralSquare a).domain :=
    GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
      fourierUnitary (weightOneSpectralSquare a) f
  let fspec : (weightOneSpectralDirac a).domain :=
    GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
      fourierUnitary (weightOneSpectralDirac a) ⟨(f : SoninL2), hf⟩
  have hQspec : weightOneSpectralDirac a fspec ∈
      (weightOneSpectralDirac a).domain := by
    change fourierUnitary (weightOneLogDirac a ⟨(f : SoninL2), hf⟩) ∈
      (weightOneSpectralDirac a).domain at hQ
    rw [fourierUnitary_weightOneLogDirac_apply] at hQ
    exact hQ
  apply fourierUnitary.injective
  calc
    fourierUnitary
        (weightOneLogDirac a
          ⟨weightOneLogDirac a ⟨(f : SoninL2), hf⟩, hQ⟩) =
        weightOneSpectralDirac a
          ⟨weightOneSpectralDirac a fspec, hQspec⟩ := by
      rw [fourierUnitary_weightOneLogDirac_apply]
      congr 2
      apply Subtype.ext
      rw [fourierUnitary_weightOneLogDirac_apply]
    _ = weightOneSpectralSquare a fsq :=
      weightOneSpectralDirac_sq_apply a fsq fspec.property hQspec
    _ = fourierUnitary (weightOneLogSquare a f) := by
      simp only [weightOneLogSquare,
        GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply,
        LinearIsometryEquiv.apply_symm_apply]

end RHTower

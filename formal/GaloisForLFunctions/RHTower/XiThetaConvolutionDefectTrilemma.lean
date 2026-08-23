import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert
import GaloisForLFunctions.HTGeometry.EntireMultiplierDefectUniversality
import GaloisForLFunctions.HTGeometry.PeriodIncidenceMultiplier
import GaloisForLFunctions.RHTower.XiThetaL2Cyclicity
import GaloisForLFunctions.RHTower.XiCSchwartzRestriction
import GaloisForLFunctions.RHTower.PrimeScreenAlmostPeriodicNoGo
import GaloisForLFunctions.RHTower.WeldBoundedSpectralGauge
import GaloisForLFunctions.RHTower.XiHedenmalmJordanMatrix

/-!
# Theta convolution Hilbert--analytic defect trilemma

This file closes the literal Hilbert side of the theta-convolution trilemma.  Convolution by the
normalized theta-cusp Schwartz source extends to a bounded operator on `L²(ℝ)`.  Under the unitary
Fourier transform it is multiplication by `XiC` on the real axis.  Since that symbol is real and
nonzero almost everywhere, the operator is self-adjoint and injective with dense range.  Since the
symbol tends to zero at infinity, unit vectors supported on the escaping intervals `[N,N+1]` are
sent to zero, so the range is not closed.

The analytic defect is retained by the existing entire multiplier quotient: analytic order recovers
the complete divisor, its semisimple translation character is unitary exactly at a real point, and
the full source-derived local Jordan block is Hermitian exactly at a real simple divisor point.
-/

open Complex Filter Matrix MeasureTheory Set Topology
open scoped ENNReal FourierTransform

namespace RHTower

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

private theorem exists_xiConvolutionMultiplierBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖XiC (t : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_XiC_ofReal_le (δ := 0) (by norm_num) (by
    have hpi := Real.pi_pos
    linarith)
  refine ⟨C, hC, fun t => ?_⟩
  simpa using hbound t

/-- A global bound for the real-axis completed theta multiplier. -/
noncomputable def xiConvolutionMultiplierBound : ℝ :=
  Classical.choose exists_xiConvolutionMultiplierBound

theorem xiConvolutionMultiplierBound_nonneg : 0 ≤ xiConvolutionMultiplierBound :=
  (Classical.choose_spec exists_xiConvolutionMultiplierBound).1

theorem norm_XiC_ofReal_le_xiConvolutionMultiplierBound (t : ℝ) :
    ‖XiC (t : ℂ)‖ ≤ xiConvolutionMultiplierBound :=
  (Classical.choose_spec exists_xiConvolutionMultiplierBound).2 t

theorem measurable_xiThetaMultiplierSymbol : Measurable (fun t : ℝ => XiC (t : ℂ)) :=
  continuous_XiC_ofReal.measurable

/-- Multiplication by `XiC` on the real spectral `L²` space. -/
def xiThetaSpectralMultiplier :
    Lp (α := ℝ) ℂ 2 volume →L[ℂ] Lp (α := ℝ) ℂ 2 volume :=
  lpBoundedMulCLM measurable_xiThetaMultiplierSymbol xiConvolutionMultiplierBound_nonneg
    norm_XiC_ofReal_le_xiConvolutionMultiplierBound

theorem xiThetaSpectralMultiplier_ae (f : Lp (α := ℝ) ℂ 2 volume) :
    xiThetaSpectralMultiplier f =ᵐ[volume]
      fun t : ℝ => XiC (t : ℂ) * (f : ℝ → ℂ) t :=
  lpBoundedMulCLM_coeFn measurable_xiThetaMultiplierSymbol xiConvolutionMultiplierBound_nonneg
    norm_XiC_ofReal_le_xiConvolutionMultiplierBound f

theorem xiThetaSpectralMultiplier_injective :
    Function.Injective xiThetaSpectralMultiplier :=
  lpBoundedMulCLM_injective_of_ae_ne_zero measurable_xiThetaMultiplierSymbol
    xiConvolutionMultiplierBound_nonneg norm_XiC_ofReal_le_xiConvolutionMultiplierBound
    ae_XiC_ofReal_ne_zero

theorem star_XiC_ofReal (t : ℝ) :
    (starRingEnd ℂ) (XiC (t : ℂ)) = XiC (t : ℂ) := by
  rw [XiC_ofReal]
  simp

theorem inner_xiThetaSpectralMultiplier
    (f g : Lp (α := ℝ) ℂ 2 volume) :
    (inner ℂ (xiThetaSpectralMultiplier f) g : ℂ) =
      inner ℂ f (xiThetaSpectralMultiplier g) :=
  lpBoundedMulCLM_inner_general measurable_xiThetaMultiplierSymbol
    xiConvolutionMultiplierBound_nonneg norm_XiC_ofReal_le_xiConvolutionMultiplierBound
    star_XiC_ofReal f g

theorem xiThetaSpectralMultiplier_denseRange :
    DenseRange xiThetaSpectralMultiplier := by
  apply denseRange_lpBoundedMulCLM_of_ae_ne_zero measurable_xiThetaMultiplierSymbol
    xiConvolutionMultiplierBound_nonneg norm_XiC_ofReal_le_xiConvolutionMultiplierBound
  · intro t
    exact Complex.conj_eq_iff_im.mpr (XiC_ofReal t ▸ Complex.ofReal_im (Xi t))
  · exact ae_XiC_ofReal_ne_zero

/-- The bounded physical theta-convolution operator, obtained by unitary Fourier conjugation. -/
def xiThetaConvolutionOperator :
    Lp (α := ℝ) ℂ 2 volume →L[ℂ] Lp (α := ℝ) ℂ 2 volume :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearIsometry.toContinuousLinearMap.comp
    (xiThetaSpectralMultiplier.comp
      (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearIsometry.toContinuousLinearMap)

/-- Fourier conjugation identifies theta convolution with multiplication by `XiC`. -/
theorem fourier_xiThetaConvolutionOperator (f : Lp (α := ℝ) ℂ 2 volume) :
    (Lp.fourierTransformₗᵢ ℝ ℂ) (xiThetaConvolutionOperator f) =
      xiThetaSpectralMultiplier ((Lp.fourierTransformₗᵢ ℝ ℂ) f) := by
  simp [xiThetaConvolutionOperator]

theorem inner_xiThetaConvolutionOperator
    (f g : Lp (α := ℝ) ℂ 2 volume) :
    (inner ℂ (xiThetaConvolutionOperator f) g : ℂ) =
      inner ℂ f (xiThetaConvolutionOperator g) := by
  have hU1 : ∀ u v : Lp (α := ℝ) ℂ 2 volume,
      (inner ℂ ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u) v : ℂ) =
        inner ℂ u ((Lp.fourierTransformₗᵢ ℝ ℂ) v) := by
    intro u v
    have h := (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map
      ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u) v
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  have hU2 : ∀ u v : Lp (α := ℝ) ℂ 2 volume,
      (inner ℂ u ((Lp.fourierTransformₗᵢ ℝ ℂ).symm v) : ℂ) =
        inner ℂ ((Lp.fourierTransformₗᵢ ℝ ℂ) u) v := by
    intro u v
    have h := (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map u
      ((Lp.fourierTransformₗᵢ ℝ ℂ).symm v)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  rw [show xiThetaConvolutionOperator f =
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm
        (xiThetaSpectralMultiplier ((Lp.fourierTransformₗᵢ ℝ ℂ) f)) from rfl,
    show xiThetaConvolutionOperator g =
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm
        (xiThetaSpectralMultiplier ((Lp.fourierTransformₗᵢ ℝ ℂ) g)) from rfl,
    hU1, hU2]
  exact inner_xiThetaSpectralMultiplier _ _

/-- Theta convolution is self-adjoint on `L²(ℝ)`. -/
theorem xiThetaConvolutionOperator_selfAdjoint :
    IsSelfAdjoint xiThetaConvolutionOperator :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr inner_xiThetaConvolutionOperator

/-- Literal Schwartz convolution by the normalized theta-cusp source. -/
def xiThetaSchwartzConvolution (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) xiThetaSchwartzSource f

theorem xiThetaSchwartzConvolution_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    xiThetaSchwartzConvolution f x =
      MeasureTheory.convolution (xiThetaSchwartzSource : ℝ → ℂ) (f : ℝ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume x := by
  exact SchwartzMap.convolution_apply _ _ _ _

/-- The Fourier-defined bounded operator is exactly the `L²` extension of literal convolution by
the theta-cusp Schwartz source. -/
theorem xiThetaConvolutionOperator_toLp (f : SchwartzMap ℝ ℂ) :
    xiThetaConvolutionOperator (f.toLp 2 volume) =
      (xiThetaSchwartzConvolution f).toLp 2 volume := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_xiThetaConvolutionOperator]
  change xiThetaSpectralMultiplier (𝓕 (f.toLp 2 volume)) =
    𝓕 ((xiThetaSchwartzConvolution f).toLp 2 volume)
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [xiThetaSpectralMultiplier_ae ((𝓕 f).toLp 2 volume),
    (𝓕 f).coeFn_toLp (p := 2) (μ := (volume : Measure ℝ)),
    (𝓕 (xiThetaSchwartzConvolution f)).coeFn_toLp
      (p := 2) (μ := (volume : Measure ℝ))] with t hmul hf hconv
  rw [hmul, hf, hconv, xiThetaSchwartzConvolution, SchwartzMap.fourier_convolution]
  simp only [SchwartzMap.pairing_apply_apply, fourier_xiThetaSchwartzSource]
  rfl

/-- The Hilbert kernel of theta convolution is zero. -/
theorem xiThetaConvolutionOperator_injective :
    Function.Injective xiThetaConvolutionOperator := by
  intro f g h
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  apply xiThetaSpectralMultiplier_injective
  rw [← fourier_xiThetaConvolutionOperator, ← fourier_xiThetaConvolutionOperator, h]

/-- The theta-convolution range is dense, so its reduced Hilbert cokernel vanishes. -/
theorem xiThetaConvolutionOperator_denseRange :
    DenseRange xiThetaConvolutionOperator := by
  have hright : DenseRange (fun f : Lp (α := ℝ) ℂ 2 volume =>
      xiThetaSpectralMultiplier ((Lp.fourierTransformₗᵢ ℝ ℂ) f)) :=
    xiThetaSpectralMultiplier_denseRange.comp
      (Lp.fourierTransformₗᵢ ℝ ℂ).surjective.denseRange
      xiThetaSpectralMultiplier.continuous
  have hfull : DenseRange (fun f : Lp (α := ℝ) ℂ 2 volume =>
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm
        (xiThetaSpectralMultiplier ((Lp.fourierTransformₗᵢ ℝ ℂ) f))) :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm.surjective.denseRange.comp hright
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous
  have heq : (xiThetaConvolutionOperator :
      Lp (α := ℝ) ℂ 2 volume → Lp (α := ℝ) ℂ 2 volume) =
      fun f => (Lp.fourierTransformₗᵢ ℝ ℂ).symm
        (xiThetaSpectralMultiplier ((Lp.fourierTransformₗᵢ ℝ ℂ) f)) := by
    funext f
    rfl
  rw [heq]
  exact hfull

/-- Unit spectral packets on the escaping intervals `[N,N+1]`. -/
abbrev xiThetaSpectralUnitVector (N : ℕ) : Lp (α := ℝ) ℂ 2 volume :=
  GaloisForLFunctions.RHTower.weldSpectralUnitVector N

theorem norm_xiThetaSpectralUnitVector (N : ℕ) : ‖xiThetaSpectralUnitVector N‖ = 1 :=
  GaloisForLFunctions.RHTower.norm_weldSpectralUnitVector N

theorem tendsto_xiThetaSpectralMultiplier_unitVector_zero :
    Tendsto (fun N : ℕ => xiThetaSpectralMultiplier (xiThetaSpectralUnitVector N))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  have hnormXi : Tendsto (fun t : ℝ => ‖XiC (t : ℂ)‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp tendsto_XiC_ofReal_atTop
  obtain ⟨a, ha⟩ := (Metric.tendsto_atTop.mp hnormXi) (ε / 2) (by positivity)
  have ha' : ∀ b : ℝ, a ≤ b → ‖XiC (b : ℂ)‖ < ε / 2 := by
    intro b hb
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using ha b hb
  obtain ⟨N₀ : ℕ, hN₀⟩ := exists_nat_ge a
  refine ⟨N₀, fun N hN => ?_⟩
  have hpoint : ∀ᵐ x : ℝ ∂volume,
      ‖((xiThetaSpectralMultiplier (xiThetaSpectralUnitVector N) :
          Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ) x‖ ≤
        ‖(((ε / 2 : ℝ) : ℂ) • xiThetaSpectralUnitVector N :
          Lp (α := ℝ) ℂ 2 volume) x‖ := by
    filter_upwards [xiThetaSpectralMultiplier_ae (xiThetaSpectralUnitVector N),
      GaloisForLFunctions.RHTower.weldSpectralUnitVector_ae N,
      Lp.coeFn_smul ((ε / 2 : ℝ) : ℂ) (xiThetaSpectralUnitVector N)]
      with x hmul hunit hsmul
    rw [hmul, hsmul, norm_mul, Pi.smul_apply, norm_smul]
    by_cases hx : x ∈ GaloisForLFunctions.RHTower.weldSpectralInterval N
    · rw [hunit, Set.indicator_of_mem hx, norm_one, mul_one, mul_one]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (ha' x (le_trans hN₀ (le_trans (by exact_mod_cast hN) hx.1))).le
    · rw [hunit, Set.indicator_of_notMem hx, norm_zero, mul_zero, mul_zero]
  have hle := Lp.norm_le_norm_of_ae_le hpoint
  have hhalf : ‖((ε / 2 : ℝ) : ℂ)‖ = ε / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_smul, norm_xiThetaSpectralUnitVector, mul_one, hhalf] at hle
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact lt_of_le_of_lt hle (by linarith)

theorem xiThetaSpectralMultiplier_not_isClosed_range :
    ¬ IsClosed (Set.range xiThetaSpectralMultiplier) := by
  apply GaloisForLFunctions.not_isClosed_range_of_injective_of_unit_vectors_tendsto_zero
    xiThetaSpectralMultiplier xiThetaSpectralMultiplier_injective xiThetaSpectralUnitVector
    norm_xiThetaSpectralUnitVector tendsto_xiThetaSpectralMultiplier_unitVector_zero

/-- Physical unit vectors obtained from the escaping spectral packets. -/
def xiThetaConvolutionUnitVector (N : ℕ) : Lp (α := ℝ) ℂ 2 volume :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm (xiThetaSpectralUnitVector N)

theorem norm_xiThetaConvolutionUnitVector (N : ℕ) :
    ‖xiThetaConvolutionUnitVector N‖ = 1 := by
  rw [xiThetaConvolutionUnitVector,
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map,
    norm_xiThetaSpectralUnitVector]

theorem tendsto_xiThetaConvolutionOperator_unitVector_zero :
    Tendsto (fun N : ℕ => xiThetaConvolutionOperator (xiThetaConvolutionUnitVector N))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_zero_iff_norm_tendsto_zero.mp
    tendsto_xiThetaSpectralMultiplier_unitVector_zero
  convert h using 1
  funext N
  rw [← (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map,
    fourier_xiThetaConvolutionOperator, xiThetaConvolutionUnitVector]
  simp

/-- The theta-convolution range is not closed. -/
theorem xiThetaConvolutionOperator_not_isClosed_range :
    ¬ IsClosed (Set.range xiThetaConvolutionOperator) := by
  apply GaloisForLFunctions.not_isClosed_range_of_injective_of_unit_vectors_tendsto_zero
    xiThetaConvolutionOperator xiThetaConvolutionOperator_injective xiThetaConvolutionUnitVector
    norm_xiThetaConvolutionUnitVector tendsto_xiThetaConvolutionOperator_unitVector_zero

theorem xiThetaConvolutionOperator_ker :
    LinearMap.ker (xiThetaConvolutionOperator :
      Lp (α := ℝ) ℂ 2 volume →ₗ[ℂ] Lp (α := ℝ) ℂ 2 volume) = ⊥ :=
  LinearMap.ker_eq_bot.mpr xiThetaConvolutionOperator_injective

theorem closure_range_xiThetaConvolutionOperator :
    closure (Set.range xiThetaConvolutionOperator) = Set.univ :=
  dense_iff_closure_eq.mp xiThetaConvolutionOperator_denseRange

/-! ## Analytic defect and positivity boundary -/

/-- On each semisimple local fibre, real translation is unitary exactly at a real divisor point. -/
theorem xiThetaDefectCharacter_unitary_iff_real (rho : XiDivisorSupport) :
    (∀ a : ℝ,
      ‖GaloisForLFunctions.HTGeometry.EntireDefect.defectCharacter
        (xiSpectralPointSupport rho) a‖ = 1) ↔
      (xiSpectralPointSupport rho).im = 0 :=
  GaloisForLFunctions.HTGeometry.EntireDefect.norm_defectCharacter_eq_one_iff _

/-- The complete local source jet admits its canonical positive Hermitian realization exactly at a
real simple divisor point. -/
theorem xiThetaFullLocalJetHermitian_iff_real_and_simple (rho : XiDivisorSupport) :
    (xiLocalJordanMatrix rho).IsHermitian ↔
      (starRingEnd ℂ) (xiSpectralPointSupport rho) = xiSpectralPointSupport rho ∧
        xiSupportMultiplicity rho = 1 :=
  xiLocalJordanMatrix_isHermitian_iff rho

/-- Global positive Hermitian realization of every full local source jet is exactly RH plus
simplicity of every Xi zero. -/
theorem all_xiThetaFullLocalJetsHermitian_iff_rh_and_simple :
    (∀ rho : XiDivisorSupport, (xiLocalJordanMatrix rho).IsHermitian) ↔
      RiemannHypothesis ∧ XiZerosSimple :=
  all_xiLocalJordanMatrix_isHermitian_iff_rh_and_simple

/-! ## Arbitrary positive local jet Hilbertizations -/

/-- Sesquilinear form associated with a candidate Hermitian metric on a local jet. -/
def xiThetaJetForm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (x y : Fin n → ℂ) : ℂ :=
  star x ⬝ᵥ (H *ᵥ y)

theorem xiThetaJetForm_smul_left {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (x y : Fin n → ℂ) :
    xiThetaJetForm H (c • x) y = (starRingEnd ℂ) c * xiThetaJetForm H x y := by
  simp [xiThetaJetForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  ring

theorem xiThetaJetForm_smul_right {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (x y : Fin n → ℂ) :
    xiThetaJetForm H x (c • y) = c * xiThetaJetForm H x y := by
  simp [xiThetaJetForm, Matrix.mulVec_smul, smul_eq_mul]

theorem xiThetaJetForm_add_right {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (x y z : Fin n → ℂ) :
    xiThetaJetForm H x (y + z) = xiThetaJetForm H x y + xiThetaJetForm H x z := by
  simp [xiThetaJetForm, Matrix.mulVec_add]

/-- A faithful positive inner product in which the full local jet generator is self-adjoint.
Equivalently, its real exponential flow is unitary for this positive Hilbertization. -/
structure XiThetaPositiveJetHilbertization (rho : XiDivisorSupport) where
  coeff : Matrix (Fin (xiSupportMultiplicity rho)) (Fin (xiSupportMultiplicity rho)) ℂ
  positive : ∀ x : Fin (xiSupportMultiplicity rho) → ℂ, x ≠ 0 →
    0 < (xiThetaJetForm coeff x x).re
  generator_symmetric : ∀ x y : Fin (xiSupportMultiplicity rho) → ℂ,
    xiThetaJetForm coeff ((xiLocalJordanMatrix rho).mulVec x) y =
      xiThetaJetForm coeff x ((xiLocalJordanMatrix rho).mulVec y)

theorem xiLocalJordanMatrix_mulVec_single_zero (rho : XiDivisorSupport) :
    (xiLocalJordanMatrix rho).mulVec (Pi.single (⟨0, xiSupportMultiplicity_pos rho⟩ :
      Fin (xiSupportMultiplicity rho)) 1) =
      xiSpectralPointSupport rho • Pi.single
        (⟨0, xiSupportMultiplicity_pos rho⟩ : Fin (xiSupportMultiplicity rho)) 1 := by
  classical
  rw [Matrix.mulVec_single_one]
  ext i
  by_cases hi : i = (⟨0, xiSupportMultiplicity_pos rho⟩ : Fin (xiSupportMultiplicity rho))
  · subst i
    simp [xiLocalJordanMatrix]
  · have hval : i.val ≠ 0 := by
      intro h
      apply hi
      exact Fin.ext h
    simp [xiLocalJordanMatrix, hi, hval]

theorem xiLocalJordanMatrix_mulVec_single_one (rho : XiDivisorSupport)
    (hm2 : 2 ≤ xiSupportMultiplicity rho) :
    (xiLocalJordanMatrix rho).mulVec (Pi.single (⟨1, hm2⟩ :
      Fin (xiSupportMultiplicity rho)) 1) =
      Pi.single (⟨0, xiSupportMultiplicity_pos rho⟩ : Fin (xiSupportMultiplicity rho)) 1 +
        xiSpectralPointSupport rho • Pi.single
          (⟨1, hm2⟩ : Fin (xiSupportMultiplicity rho)) 1 := by
  classical
  rw [Matrix.mulVec_single_one]
  ext i
  let i0 : Fin (xiSupportMultiplicity rho) := ⟨0, xiSupportMultiplicity_pos rho⟩
  let i1 : Fin (xiSupportMultiplicity rho) := ⟨1, hm2⟩
  by_cases hi0 : i = i0
  · subst i
    simp [xiLocalJordanMatrix, i0]
  · by_cases hi1 : i = i1
    · subst i
      simp [xiLocalJordanMatrix, i1]
    · have hval0 : i.val ≠ 0 := by
        intro h
        apply hi0
        exact Fin.ext h
      have hval1 : i.val ≠ 1 := by
        intro h
        apply hi1
        exact Fin.ext h
      simp [xiLocalJordanMatrix, i0, i1, hi0, hi1, hval0]

/-- **Exact full-jet positivity boundary.**  An arbitrary faithful positive Hilbertization making
the complete local source-jet generator self-adjoint exists exactly when the divisor point is real
and simple.  Thus full-jet unitarizability cannot hide a nontrivial unipotent Jordan part. -/
theorem nonempty_xiThetaPositiveJetHilbertization_iff (rho : XiDivisorSupport) :
    Nonempty (XiThetaPositiveJetHilbertization rho) ↔
      (starRingEnd ℂ) (xiSpectralPointSupport rho) = xiSpectralPointSupport rho ∧
        xiSupportMultiplicity rho = 1 := by
  constructor
  · rintro ⟨F⟩
    let i0 : Fin (xiSupportMultiplicity rho) := ⟨0, xiSupportMultiplicity_pos rho⟩
    let e0 : Fin (xiSupportMultiplicity rho) → ℂ := Pi.single i0 1
    have he0 : e0 ≠ 0 := by
      intro h
      have := congrFun h i0
      simp [e0] at this
    let q : ℂ := xiThetaJetForm F.coeff e0 e0
    have hqpos : 0 < q.re := F.positive e0 he0
    have hqne : q ≠ 0 := by
      intro hq
      rw [hq] at hqpos
      simp at hqpos
    have hsym00 := F.generator_symmetric e0 e0
    rw [show (xiLocalJordanMatrix rho).mulVec e0 =
        xiSpectralPointSupport rho • e0 by
          exact xiLocalJordanMatrix_mulVec_single_zero rho,
      xiThetaJetForm_smul_left, xiThetaJetForm_smul_right] at hsym00
    have hreal : (starRingEnd ℂ) (xiSpectralPointSupport rho) =
        xiSpectralPointSupport rho :=
      mul_right_cancel₀ hqne hsym00
    refine ⟨hreal, ?_⟩
    by_contra hm
    have hm2 : 2 ≤ xiSupportMultiplicity rho := by
      have hmpos := xiSupportMultiplicity_pos rho
      omega
    let i1 : Fin (xiSupportMultiplicity rho) := ⟨1, hm2⟩
    let e1 : Fin (xiSupportMultiplicity rho) → ℂ := Pi.single i1 1
    have hsym01 := F.generator_symmetric e0 e1
    rw [show (xiLocalJordanMatrix rho).mulVec e0 =
        xiSpectralPointSupport rho • e0 by
          exact xiLocalJordanMatrix_mulVec_single_zero rho,
      show (xiLocalJordanMatrix rho).mulVec e1 =
        e0 + xiSpectralPointSupport rho • e1 by
          exact xiLocalJordanMatrix_mulVec_single_one rho hm2,
      xiThetaJetForm_smul_left, xiThetaJetForm_add_right,
      xiThetaJetForm_smul_right, hreal] at hsym01
    have hqzero : q = 0 := by
      linear_combination -hsym01
    exact hqne hqzero
  · rintro ⟨hreal, hm⟩
    haveI : Subsingleton (Fin (xiSupportMultiplicity rho)) := by
      rw [hm]
      infer_instance
    refine ⟨⟨1, ?_, ?_⟩⟩
    · intro x hx
      have hcalc : xiThetaJetForm (1 : Matrix (Fin (xiSupportMultiplicity rho))
          (Fin (xiSupportMultiplicity rho)) ℂ) x x =
          ∑ k, (starRingEnd ℂ) (x k) * x k := by
        simp [xiThetaJetForm, dotProduct]
      rw [hcalc]
      have hre : (∑ k, (starRingEnd ℂ) (x k) * x k).re = ∑ k, ‖x k‖ ^ 2 := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [mul_comm, Complex.mul_conj]
        simp [Complex.normSq_eq_norm_sq]
        norm_cast
      rw [hre]
      obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hx (funext hcon)
      refine Finset.sum_pos' (fun i _ => by positivity) ⟨k, Finset.mem_univ k, ?_⟩
      have : 0 < ‖x k‖ := norm_pos_iff.mpr hk
      positivity
    · intro x y
      have hA (z : Fin (xiSupportMultiplicity rho) → ℂ) :
          (xiLocalJordanMatrix rho).mulVec z = xiSpectralPointSupport rho • z := by
        ext i
        rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single i]
        · simp [xiLocalJordanMatrix]
        · intro b hb
          have hbi : b = i := Subsingleton.elim _ _
          exact (hb hbi).elim
      rw [hA x, hA y, xiThetaJetForm_smul_left, xiThetaJetForm_smul_right, hreal]

end

end RHTower

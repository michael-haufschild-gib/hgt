import GaloisForLFunctions.RHTower.SuzukiTestSpectralDensity
import GaloisForLFunctions.HTGeometry.LinearIsometryCompletion
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

/-!
# `H_W` is isometrically `L²(τ)`

The spectral map `ψ ↦ (√(m_γ) ψ̂(γ))_γ` carries the test space isometrically into the weighted
sequence space `L²(τ)`: the Weil norm of a test function is exactly the weighted spectral mass.  Its
range is dense, so the extension to the completion is an isometric isomorphism `H_W ≅ L²(τ)`.

This is Lemma 5.4 of the source.  Suzuki obtains it from Kreĭn--Langer's spectral theory of screw
functions; here the isometry is the definition of the Weil form and the density is the
exponential-series uniqueness of `ExponentialSeriesUniqueness`.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The spectral-value sequence space `L²(τ)` of the source: square-summable sequences on the
support of the Xi divisor, with the multiplicity weights absorbed into the coordinates. -/
abbrev SuzukiTauSpace : Type := lp (fun _ : XiDivisorSupport => ℂ) 2

theorem suzukiTestSpectral_add (ψ φ : SuzukiTest) (ρ : XiDivisorSupport) :
    suzukiTestSpectral (ψ + φ) ρ = suzukiTestSpectral ψ ρ + suzukiTestSpectral φ ρ := by
  have h := suzukiTestFourier_add ψ φ (⟨ρ, ⟨0, xiSupportMult_pos ρ⟩⟩ : XiZeroCopy)
  rwa [suzukiTestFourier_eq_spectral, suzukiTestFourier_eq_spectral,
    suzukiTestFourier_eq_spectral] at h

theorem suzukiTestSpectral_smul (c : ℂ) (ψ : SuzukiTest) (ρ : XiDivisorSupport) :
    suzukiTestSpectral (c • ψ) ρ = c * suzukiTestSpectral ψ ρ := by
  have h := suzukiTestFourier_smul c ψ (⟨ρ, ⟨0, xiSupportMult_pos ρ⟩⟩ : XiZeroCopy)
  rwa [suzukiTestFourier_eq_spectral, suzukiTestFourier_eq_spectral] at h

/-- The weighted spectral sequence of a test function. -/
def suzukiSpectralSeqFun (ψ : SuzukiTest) (ρ : XiDivisorSupport) : ℂ :=
  ((Real.sqrt (xiSupportMult ρ : ℝ) : ℝ) : ℂ) * suzukiTestSpectral ψ ρ

theorem normSq_suzukiSpectralSeqFun (ψ : SuzukiTest) (ρ : XiDivisorSupport) :
    ‖suzukiSpectralSeqFun ψ ρ‖ ^ 2
      = (xiSupportMult ρ : ℝ) * ‖suzukiTestSpectral ψ ρ‖ ^ 2 := by
  have hm : (0 : ℝ) ≤ (xiSupportMult ρ : ℝ) := Nat.cast_nonneg _
  rw [suzukiSpectralSeqFun, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hm]

theorem memLp_suzukiSpectralSeqFun (hRH : RiemannHypothesis) (ψ : SuzukiTest) :
    Memℓp (suzukiSpectralSeqFun ψ) 2 := by
  refine memℓp_gen ?_
  have hsum := summable_mult_normSq_suzukiTestSpectral hRH ψ
  refine hsum.congr fun ρ => ?_
  rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  exact (normSq_suzukiSpectralSeqFun ψ ρ).symm

section

variable [hRH : Fact RiemannHypothesis]

/-- **The spectral map** `ψ ↦ (√(m_γ) ψ̂(γ))_γ` from the test space to `L²(τ)`. -/
def suzukiSpectralMap : SuzukiWeilTest →ₗᵢ[ℂ] SuzukiTauSpace where
  toFun ψ := ⟨suzukiSpectralSeqFun ψ.toTest, memLp_suzukiSpectralSeqFun hRH.out ψ.toTest⟩
  map_add' := by
    intro ψ φ
    refine lp.ext ?_
    funext ρ
    show suzukiSpectralSeqFun (ψ.toTest + φ.toTest) ρ
      = suzukiSpectralSeqFun ψ.toTest ρ + suzukiSpectralSeqFun φ.toTest ρ
    rw [suzukiSpectralSeqFun, suzukiSpectralSeqFun, suzukiSpectralSeqFun,
      suzukiTestSpectral_add]
    ring
  map_smul' := by
    intro c ψ
    refine lp.ext ?_
    funext ρ
    show suzukiSpectralSeqFun (c • ψ.toTest) ρ = c * suzukiSpectralSeqFun ψ.toTest ρ
    rw [suzukiSpectralSeqFun, suzukiSpectralSeqFun, suzukiTestSpectral_smul]
    ring
  norm_map' := by
    intro ψ
    set f : SuzukiTauSpace :=
      ⟨suzukiSpectralSeqFun ψ.toTest, memLp_suzukiSpectralSeqFun hRH.out ψ.toTest⟩ with hf
    have h1 : (0 : ℝ) ≤ ‖f‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ ‖ψ‖ := norm_nonneg _
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    have hcast : ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) := by norm_num
    have hrpow := lp.norm_rpow_eq_tsum hp f
    rw [hcast] at hrpow
    simp only [Real.rpow_natCast] at hrpow
    have hleft : (∑' ρ : XiDivisorSupport, ‖(f : ∀ _ : XiDivisorSupport, ℂ) ρ‖ ^ 2)
        = (suzukiWeilInner ψ ψ).re := by
      have hbase := hasSum_mult_normSq_suzukiTestSpectral hRH.out ψ.toTest
      refine HasSum.tsum_eq (hbase.congr_fun fun ρ => ?_)
      exact normSq_suzukiSpectralSeqFun ψ.toTest ρ
    have hnorm : ‖ψ‖ ^ 2 = RCLike.re (inner ℂ ψ ψ : ℂ) := norm_sq_eq_re_inner ψ
    have hsq : ‖f‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [hrpow, hleft, hnorm]
      rfl
    show ‖f‖ = ‖ψ‖
    rw [← Real.sqrt_sq h1, ← Real.sqrt_sq h2, hsq]

@[simp] theorem suzukiSpectralMap_apply (ψ : SuzukiWeilTest) (ρ : XiDivisorSupport) :
    ((suzukiSpectralMap ψ : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ
      = suzukiSpectralSeqFun ψ.toTest ρ := rfl

omit hRH in
theorem hasSum_normSq_lp (y : SuzukiTauSpace) :
    HasSum (fun ρ : XiDivisorSupport => ‖(y : ∀ _ : XiDivisorSupport, ℂ) ρ‖ ^ 2)
      ((inner ℂ y y : ℂ).re) := by
  have hb := lp.hasSum_inner (𝕜 := ℂ) y y
  have hre := Complex.hasSum_re hb
  refine hre.congr_fun ?_
  intro ρ
  have : (inner ℂ ((y : ∀ _ : XiDivisorSupport, ℂ) ρ)
      ((y : ∀ _ : XiDivisorSupport, ℂ) ρ) : ℂ)
      = (((‖(y : ∀ _ : XiDivisorSupport, ℂ) ρ‖ ^ 2 : ℝ)) : ℂ) := by
    rw [RCLike.inner_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [this]
  exact (Complex.ofReal_re _).symm

/-- **Lemma 5.4, density.**  The spectral values of test functions are dense in `L²(τ)`. -/
theorem denseRange_suzukiSpectralMap :
    DenseRange (suzukiSpectralMap : SuzukiWeilTest → SuzukiTauSpace) := by
  have hbot : (LinearMap.range
      (suzukiSpectralMap : SuzukiWeilTest →ₗᵢ[ℂ] SuzukiTauSpace).toLinearMap)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hmpos : ∀ ρ : XiDivisorSupport, (0 : ℝ) < Real.sqrt (xiSupportMult ρ : ℝ) := by
      intro ρ
      refine Real.sqrt_pos.mpr ?_
      exact_mod_cast xiSupportMult_pos ρ
    have hmne : ∀ ρ : XiDivisorSupport,
        ((Real.sqrt (xiSupportMult ρ : ℝ) : ℝ) : ℂ) ≠ 0 := by
      intro ρ
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt (hmpos ρ)
    set a : XiDivisorSupport → ℂ := fun ρ =>
      (y : ∀ _ : XiDivisorSupport, ℂ) ρ / ((Real.sqrt (xiSupportMult ρ : ℝ) : ℝ) : ℂ) with ha
    have hmnn : ∀ ρ : XiDivisorSupport, (0 : ℝ) ≤ (xiSupportMult ρ : ℝ) :=
      fun ρ => Nat.cast_nonneg _
    have hmne0 : ∀ ρ : XiDivisorSupport, ((xiSupportMult ρ : ℝ)) ≠ 0 := by
      intro ρ
      have := hmpos ρ
      nlinarith [Real.sq_sqrt (hmnn ρ)]
    have hnorma : ∀ ρ : XiDivisorSupport,
        (xiSupportMult ρ : ℝ) * ‖a ρ‖ ^ 2 = ‖(y : ∀ _ : XiDivisorSupport, ℂ) ρ‖ ^ 2 := by
      intro ρ
      rw [ha, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hmnn ρ)]
      rw [mul_div_cancel₀ _ (hmne0 ρ)]
    have hsummable : Summable
        (fun ρ : XiDivisorSupport => (xiSupportMult ρ : ℝ) * ‖a ρ‖ ^ 2) :=
      (hasSum_normSq_lp y).summable.congr fun ρ => (hnorma ρ).symm
    have hmsq : ∀ ρ : XiDivisorSupport,
        ((xiSupportMult ρ : ℝ) : ℂ)
          = ((Real.sqrt (xiSupportMult ρ : ℝ) : ℝ) : ℂ)
            * ((Real.sqrt (xiSupportMult ρ : ℝ) : ℝ) : ℂ) := by
      intro ρ
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (Real.sqrt_nonneg _)]
      congr 1
      rw [Real.sqrt_mul_self (Real.sqrt_nonneg _), Real.mul_self_sqrt (hmnn ρ)]
    have horth : ∀ ψ : SuzukiTest,
        (∑' ρ : XiDivisorSupport,
          ((xiSupportMult ρ : ℝ) : ℂ) * (starRingEnd ℂ) (a ρ)
            * suzukiTestSpectral ψ ρ) = 0 := by
      intro ψ
      have hzero : (inner ℂ (suzukiSpectralMap (ψ : SuzukiWeilTest)) y : ℂ) = 0 :=
        Submodule.mem_orthogonal _ _ |>.mp hy _ ⟨(ψ : SuzukiWeilTest), rfl⟩
      have hb := lp.hasSum_inner (𝕜 := ℂ) (suzukiSpectralMap (ψ : SuzukiWeilTest)) y
      rw [hzero] at hb
      have hconj := hb.map (starRingEnd ℂ) Complex.continuous_conj
      rw [map_zero] at hconj
      refine HasSum.tsum_eq (hconj.congr_fun ?_)
      intro ρ
      show ((xiSupportMult ρ : ℝ) : ℂ) * (starRingEnd ℂ) (a ρ) * suzukiTestSpectral ψ ρ
        = (starRingEnd ℂ)
          (inner ℂ (suzukiSpectralSeqFun ψ ρ) ((y : ∀ _ : XiDivisorSupport, ℂ) ρ) : ℂ)
      rw [RCLike.inner_apply, map_mul, Complex.conj_conj, suzukiSpectralSeqFun,
        ha, map_div₀, Complex.conj_ofReal, hmsq ρ]
      field_simp
    have hazero := eq_zero_of_orthogonal_suzukiTestSpectral hRH.out hsummable horth
    refine lp.ext ?_
    funext ρ
    have hy0 : (y : ∀ _ : XiDivisorSupport, ℂ) ρ
        = ((Real.sqrt (xiSupportMult ρ : ℝ) : ℝ) : ℂ) * a ρ := by
      rw [ha]
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (hmne ρ), mul_one]
    show (y : ∀ _ : XiDivisorSupport, ℂ) ρ = (0 : SuzukiTauSpace) ρ
    rw [hy0, hazero ρ, mul_zero]
    rfl
  have hclosure := Submodule.topologicalClosure_eq_top_iff.mpr hbot
  have hdense := Submodule.dense_iff_topologicalClosure_eq_top.mpr hclosure
  exact hdense

/-- **Lemma 5.4.**  `H_W` is isometrically isomorphic to `L²(τ)` by `[ψ] ↦ (ψ̂(γ))_γ`. -/
def suzukiWeilTauEquiv : SuzukiHW ≃ₗᵢ[ℂ] SuzukiTauSpace :=
  LinearIsometryEquiv.ofSurjective
    (completionExtendₗᵢ (suzukiSpectralMap : SuzukiWeilTest →ₗᵢ[ℂ] SuzukiTauSpace))
    (denseRange_completionExtendₗᵢ_of_denseRange _ denseRange_suzukiSpectralMap)

@[simp] theorem suzukiWeilTauEquiv_coe (ψ : SuzukiWeilTest) :
    suzukiWeilTauEquiv (ψ : SuzukiHW) = suzukiSpectralMap ψ :=
  completionExtendₗᵢ_coe _ ψ

end

end RHTower


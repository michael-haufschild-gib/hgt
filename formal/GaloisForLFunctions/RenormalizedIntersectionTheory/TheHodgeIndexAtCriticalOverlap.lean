import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.ABoundedOverlapRateSeesASemilocalWindow
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheHodgeIndexAtGrowingOverlap
import GaloisForLFunctions.AdelicKreinGeometry.ThePontryaginExtensionsOfWeilsCorrelation
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits

/-!
# The Hodge index at critical overlap

Every finite rational Weil Gram is a limit of complete-matrix compressions at
one fixed multiple of `loglog N · (logloglog N)²`. Positivity on the pole
hyperplane bounds each compression's negative index by one. Lower
semicontinuity and the evenness of the zeta index then force RH.

The multiple can depend on the finite family. The equivalence therefore
quantifies over every fixed multiple; it asserts no universal multiple.
-/

noncomputable section
open MeasureTheory Filter Topology Finset Matrix
open scoped RealInnerProductSpace ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticCastelnuovoSeveri
  GaloisForLFunctions.HeckeKreinToeplitz GaloisForLFunctions.AdelicKreinGeometry
  GaloisForLFunctions.TransMetzlerWeilPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SpacingScaleHarmonicAnalysis

namespace GaloisForLFunctions.RenormalizedIntersectionTheory
private theorem real_compression_energy {ι J : Type*} [Fintype ι] [Fintype J]
    (A : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (v : ι → EuclideanSpace ℝ J) (M : ℝ) (c : ι → ℝ) :
    c ⬝ᵥ ((fun i j => M * ⟪A (v i), v j⟫) *ᵥ c) =
      M * ⟪A (∑ i, c i • v i), ∑ i, c i • v i⟫ := by
  simp only [dotProduct, mulVec, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

private theorem compression_index_le_one {ι J : Type*} [Fintype ι] [Fintype J]
    (A : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (v : ι → EuclideanSpace ℝ J) (p : EuclideanSpace ℝ J)
    {M : ℝ} (hM : 0 ≤ M)
    (hpos : ∀ x, ⟪x, p⟫ = 0 → 0 ≤ ⟪A x, x⟫) :
    hermNegIndex (fun i j => ((M * ⟪A (v i), v j⟫ : ℝ) : ℂ)) ≤ 1 := by
  let ℓ : (ι → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun c => ∑ i, c i * (⟪v i, p⟫ : ℂ)
      map_add' := fun c d => by simp only [Pi.add_apply, add_mul, sum_add_distrib]
      map_smul' := fun a c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum, RingHom.id_apply] }
  have hb := negIndex_le_card_of_nonneg_on_ker
    (fun i j => ((M * ⟪A (v i), v j⟫ : ℝ) : ℂ)) (fun _ : Fin 1 => ℓ) ?_
  · simpa only [Fintype.card_fin] using hb
  intro c hc
  have hz := hc 0
  have hr : ⟪∑ i, (c i).re • v i, p⟫ = 0 := by
    have h := congrArg Complex.re hz
    simpa only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.zero_re,
      sum_inner, real_inner_smul_left] using h
  have hi : ⟪∑ i, (c i).im • v i, p⟫ = 0 := by
    have h := congrArg Complex.im hz
    simpa only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, Complex.zero_im,
      sum_inner, real_inner_smul_left] using h
  change 0 ≤ hermQuad ((fun i j => M * ⟪A (v i), v j⟫ : Matrix ι ι ℝ).map (↑)) c
  rw [hermQuad_map_ofReal, real_compression_energy, real_compression_energy]
  exact add_nonneg (mul_nonneg hM (hpos _ hr)) (mul_nonneg hM (hpos _ hi))

/-- Positivity on the pole hyperplane at every fixed critical multiple is RH. -/
theorem riemannHypothesis_iff_steklovUnitProfile_hodgeIndex_critical :
    RiemannHypothesis ↔ ∀ K : ℝ, 1 ≤ K → ∀ᶠ N : ℕ in atTop,
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 →
          0 ≤ completeWeilEnergy steklovUnitProfile (2 * K * dcScale N) N x := by
  constructor
  · intro hRH K hK
    filter_upwards [eventually_ge_atTop 1, dcScale_atTop.eventually_gt_atTop 0]
      with N hN hS
    have hc : 0 < 2 * K * dcScale N :=
      mul_pos (mul_pos two_pos (zero_lt_one.trans_le hK)) hS
    have hw : 0 < 2 * K * dcScale N / N := div_pos hc (by exact_mod_cast hN)
    have hφ : ContDiff ℝ 2 steklovUnitProfile :=
      contDiff_steklovUnitProfile.of_le (natCast_le_infty 2)
    have hfull := (forall_completeWeilEnergy_nonneg_iff hφ steklovUnitProfile_eq_zero
      integral_steklovUnitProfile_sq_pos (by rw [integral_steklovUnitProfile]; norm_num)
      hc hN).mpr (fun y => weilQuad_atomicTest_nonneg_of_RH hRH
        (contDiff_recentredProfile hφ) (vanishesOff_recentredProfile steklovUnitProfile_eq_zero)
        (div_pos two_pos hw) N y)
    exact fun x _ => hfull x
  · intro H
    have hκ : negIndex ArithmeticPositiveDuality.ratCorr ≤ 1 := by
      apply negIndex_le_iff.mpr
      intro n q
      obtain ⟨K, hK, N, hN, v, hv⟩ := exists_ratCorr_completeWeil_gram_limit q
      have hlim := eventually_le_hermNegIndex (gram_isHermitian isHermKernel_ratCorr q) hv
      have hb : ∀ᶠ m : ℕ in atTop,
          hermNegIndex (fun i j => (((∫ u, atomDilate steklovUnitProfile
            (2 * K * dcScale (N m) / N m) u ^ 2) *
            ⟪(completeWeilMatrix steklovUnitProfile (2 * K * dcScale (N m)) (N m)).toEuclideanLin
              (v m i), v m j⟫ : ℝ) : ℂ)) ≤ 1 := by
        filter_upwards [hN.eventually (H K hK)] with m hm
        exact compression_index_le_one _ (v m) (normalizedRamanujanHorizonVector 1 (N m))
          (integral_nonneg fun u => sq_nonneg _) hm
      obtain ⟨m, hm, hm'⟩ := (hlim.and hb).exists
      exact_mod_cast hm.trans hm'
    rw [negIndex_ratCorr] at hκ
    exact riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mpr
      (negIndex_zetaKernel_le_one_iff.mp hκ)

end GaloisForLFunctions.RenormalizedIntersectionTheory

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.riemannHypothesis_iff_steklovUnitProfile_hodgeIndex_critical

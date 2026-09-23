import GaloisForLFunctions.RHTower.XiHedenmalmReciprocalOperator
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.HTGeometry.BalancedHilbertDefectPolarization

/-!
# The FE--Schwarz endpoint reflection-defect energy

At the completion boundary `z = i/2`, the paired centered resolvent term becomes the product of
the raw reciprocal Xi coordinate with the conjugate reciprocal coordinate at its critical-line
reflection.  Summing the pointwise polarization square gives an exact global identity:

`endpoint defect = 2 * (raw Hermitian mass - completed endpoint curvature)`.

The defect is nonnegative and vanishes exactly under RH.  Consequently the reverse scalar
inequality, from the Hermitian raw mass to the completed endpoint curvature, is itself equivalent
to RH.  This is the precise norm budget required of a successful Connes source carrier.
-/

open Complex

namespace RHTower


noncomputable section

def xiRawReciprocalCoordinate (q : XiZeroCopy) : ℂ := ((q.1 : ℂ))⁻¹

theorem XiC_I_half_ne : XiC (I / 2) ≠ 0 := by
  intro h
  have hzero : xi 0 = 0 := by
    change xi (1 / 2 + (I / 2) * I) = 0 at h
    have harg : (1 / 2 : ℂ) + (I / 2) * I = 0 := by
      field_simp
      rw [Complex.I_sq]
      ring
    rw [harg] at h
    exact h
  let ρ : XiDivisorSupport := ⟨0, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hs := xi_divisor_support_re_mem_open_unit ρ
  norm_num at hs

lemma endpoint_term_eq (q : XiZeroCopy) :
    xiReciprocalSquareResolventTerm (I / 2) q =
      xiRawReciprocalCoordinate q *
        (starRingEnd ℂ) (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)) := by
  rw [xiReciprocalSquareResolventTerm, xiZeroCopyReciprocalSquare_eq]
  rw [xiRawReciprocalCoordinate, xiRawReciprocalCoordinate]
  have hr0 : (q.1 : ℂ) ≠ 0 := by
    have hs := xi_divisor_support_re_mem_open_unit q.1
    intro h
    rw [h] at hs
    norm_num at hs
  have hr1 : (q.1 : ℂ) ≠ 1 := by
    have hs := xi_divisor_support_re_mem_open_unit q.1
    intro h
    rw [h] at hs
    norm_num at hs
  have hrhalf : (q.1 : ℂ) ≠ 1 / 2 := xi_divisor_support_ne_half q.1
  have hlinear : 1 - 2 * (q.1 : ℂ) ≠ 0 := by
    intro h
    apply hrhalf
    linear_combination -h / 2
  have hpoly :
      1 - (q.1 : ℂ) * 4 + (q.1 : ℂ) ^ (2 : ℕ) * 4 ≠ 0 := by
    rw [show 1 - (q.1 : ℂ) * 4 + (q.1 : ℂ) ^ (2 : ℕ) * 4 =
      (1 - 2 * (q.1 : ℂ)) ^ (2 : ℕ) by ring]
    exact pow_ne_zero 2 hlinear
  have hline : ((xiZeroCopyLineConjEquiv q).1 : ℂ) =
      1 - (starRingEnd ℂ) (q.1 : ℂ) := rfl
  rw [hline, map_inv₀, map_sub, map_one]
  have hstar : (starRingEnd ℂ) ((starRingEnd ℂ) (q.1 : ℂ)) = (q.1 : ℂ) := by
    simp
  rw [hstar]
  have hmu : xiCentralReciprocalSquare (q.1 : ℂ) =
      -4 / (2 * (q.1 : ℂ) - 1) ^ (2 : ℕ) := by
    rw [xiCentralReciprocalSquare]
    field_simp [hrhalf, hlinear]
    ring
  have hzsq : (I / 2 : ℂ) ^ (2 : ℕ) = -1 / 4 := by
    field_simp
    rw [Complex.I_sq]
    ring
  rw [hmu, hzsq]
  have hL : 2 * (q.1 : ℂ) - 1 ≠ 0 := by
    intro h
    apply hlinear
    linear_combination -h
  have hquad : (2 * (q.1 : ℂ) - 1) ^ (2 : ℕ) - 1 ≠ 0 := by
    rw [show (2 * (q.1 : ℂ) - 1) ^ (2 : ℕ) - 1 =
      4 * (q.1 : ℂ) * ((q.1 : ℂ) - 1) by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hr0) (sub_ne_zero.mpr hr1)
  have hden :
      1 - (-1 / 4 : ℂ) * (-4 / (2 * (q.1 : ℂ) - 1) ^ (2 : ℕ)) =
        ((2 * (q.1 : ℂ) - 1) ^ (2 : ℕ) - 1) /
          (2 * (q.1 : ℂ) - 1) ^ (2 : ℕ) := by
    field_simp [hL]
  rw [hden]
  have hone : 1 - (q.1 : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  field_simp [hr0, hr1, hL, hquad, hone]
  ring

theorem summable_norm_xiRawReciprocalCoordinate_sq :
    Summable (fun q : XiZeroCopy => ‖xiRawReciprocalCoordinate q‖ ^ (2 : ℕ)) := by
  rw [summable_sigma_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · intro ρ
    exact (hasSum_fintype _).summable
  · have hweighted := xi_zero_multiplicity_inv_sq_summable
    apply hweighted.congr
    intro ρ
    rw [tsum_fintype]
    simp only [xiRawReciprocalCoordinate, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, norm_inv]
    have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
      le_of_lt (xi_divisor_pos_on_support ρ)
    have hcast :
        (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℝ) =
          ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    rw [hcast, div_eq_mul_inv, inv_pow]

def xiEndpointReflectionDefectEnergy : ℝ :=
  ∑' q : XiZeroCopy,
    ‖xiRawReciprocalCoordinate q -
      xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ (2 : ℕ)

def xiRawReciprocalHermitianMass : ℝ :=
  ∑' q : XiZeroCopy, ‖xiRawReciprocalCoordinate q‖ ^ (2 : ℕ)

def xiEndpointCompletedCurvature : ℝ :=
  (-logDeriv XiC (I / 2) / (I / 2)).re

lemma norm_sub_sq_eq (z w : ℂ) :
    ‖z - w‖ ^ (2 : ℕ) = ‖z‖ ^ (2 : ℕ) + ‖w‖ ^ (2 : ℕ) -
      2 * (z * (starRingEnd ℂ) w).re := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm,
    Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.conj_re, Complex.conj_im, Complex.mul_re]
  ring

theorem summable_xiEndpointReflectionDefectEnergy :
    Summable (fun q : XiZeroCopy =>
      ‖xiRawReciprocalCoordinate q -
        xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ (2 : ℕ)) := by
  have hA := summable_norm_xiRawReciprocalCoordinate_sq
  have hB : Summable (fun q : XiZeroCopy =>
      ‖xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ (2 : ℕ)) :=
    hA.comp_injective xiZeroCopyLineConjEquiv.injective
  exact
    GaloisForLFunctions.HTGeometry.summable_norm_sub_sq_of_summable_norm_sq hA hB

theorem summable_xiEndpointCrossTerm :
    Summable (fun q : XiZeroCopy =>
      xiRawReciprocalCoordinate q *
        (starRingEnd ℂ) (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))) := by
  exact (summable_xiReciprocalSquareResolventTerm XiC_I_half_ne).congr
    (fun q => endpoint_term_eq q)

theorem xiEndpointCompletedCurvature_eq_cross_re :
    xiEndpointCompletedCurvature =
      (∑' q : XiZeroCopy,
        xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re := by
  have hlog := logDeriv_XiC_eq_relativeResolventTrace XiC_I_half_ne
  have hres := xiRelativeResolventTrace_eq_reciprocalSquareResolvent XiC_I_half_ne
  rw [xiEndpointCompletedCurvature, hlog, hres]
  have hz : (I / 2 : ℂ) ≠ 0 := by exact div_ne_zero I_ne_zero (by norm_num)
  have hsum :
      (∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm (I / 2) q) =
        ∑' q : XiZeroCopy,
          xiRawReciprocalCoordinate q *
            (starRingEnd ℂ)
              (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)) := by
    apply tsum_congr
    intro q
    exact endpoint_term_eq q
  rw [hsum]
  congr 1
  field_simp [hz]

theorem xiEndpointReflectionDefectEnergy_eq_mass_sub_source :
    xiEndpointReflectionDefectEnergy =
      2 * (xiRawReciprocalHermitianMass - xiEndpointCompletedCurvature) := by
  have hA := summable_norm_xiRawReciprocalCoordinate_sq
  have hC := summable_xiEndpointCrossTerm
  have hpolar :=
    GaloisForLFunctions.HTGeometry.tsum_norm_sub_equiv_sq_eq_two_mul_mass_sub_re_inner
      (𝕜 := ℂ) xiZeroCopyLineConjEquiv xiRawReciprocalCoordinate hA
  calc
    xiEndpointReflectionDefectEnergy =
        2 * ((∑' q : XiZeroCopy, ‖xiRawReciprocalCoordinate q‖ ^ (2 : ℕ)) -
          ∑' q : XiZeroCopy,
            (xiRawReciprocalCoordinate q *
              (starRingEnd ℂ)
                (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re) := by
      rw [xiEndpointReflectionDefectEnergy]
      simpa only
        [GaloisForLFunctions.HTGeometry.re_inner_complex_eq_mul_conj_re]
        using hpolar
    _ = 2 * (xiRawReciprocalHermitianMass - xiEndpointCompletedCurvature) := by
      rw [xiRawReciprocalHermitianMass,
        xiEndpointCompletedCurvature_eq_cross_re, ← Complex.re_tsum hC]

theorem xiEndpointReflectionDefectEnergy_nonneg :
    0 ≤ xiEndpointReflectionDefectEnergy :=
  tsum_nonneg (fun _q => sq_nonneg _)

theorem xiEndpointCompletedCurvature_le_rawMass :
    xiEndpointCompletedCurvature ≤ xiRawReciprocalHermitianMass := by
  have h := xiEndpointReflectionDefectEnergy_nonneg
  rw [xiEndpointReflectionDefectEnergy_eq_mass_sub_source] at h
  linarith

theorem xiEndpointReflectionDefectEnergy_eq_zero_iff_rh :
    xiEndpointReflectionDefectEnergy = 0 ↔ RiemannHypothesis := by
  have hfix :=
    GaloisForLFunctions.HTGeometry.tsum_norm_sub_equiv_sq_eq_zero_iff
      xiZeroCopyLineConjEquiv xiRawReciprocalCoordinate
        summable_norm_xiRawReciprocalCoordinate_sq
  rw [xiEndpointReflectionDefectEnergy, hfix]
  constructor
  · intro hfixed
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hcoord := hfixed q
    have hrho : (q.1 : ℂ) = ((xiZeroCopyLineConjEquiv q).1 : ℂ) := by
      have hinv := congrArg Inv.inv hcoord
      simpa [xiRawReciprocalCoordinate] using hinv
    change (q.1 : ℂ) = 1 - (starRingEnd ℂ) (q.1 : ℂ) at hrho
    have hbeta : (q.1 : ℂ).re = 1 / 2 := by
      have hre := congrArg Complex.re hrho
      change (q.1 : ℂ).re = 1 - (q.1 : ℂ).re at hre
      linarith
    have him : (xiSpectralPoint q).im = 0 := by
      rw [xiSpectralPoint]
      simp [Complex.mul_im, hbeta]
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [him]
  · intro hRH q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    have hline := xiSpectralPoint_lineConj q
    rw [ht] at hline
    have hspectral :
        xiSpectralPoint (xiZeroCopyLineConjEquiv q) = xiSpectralPoint q := by
      rw [hline, ht]
      simp
    have hsupport : (xiZeroCopyLineConjEquiv q).1 = q.1 := by
      apply xiSpectralPointSupport_injective
      simpa only [← xiSpectralPoint_eq_support] using hspectral
    rw [xiRawReciprocalCoordinate, xiRawReciprocalCoordinate, hsupport]

theorem xiRawReciprocalHermitianMass_le_endpointCurvature_iff_rh :
    xiRawReciprocalHermitianMass ≤ xiEndpointCompletedCurvature ↔
      RiemannHypothesis := by
  constructor
  · intro hupper
    have hlower := xiEndpointCompletedCurvature_le_rawMass
    have heq : xiRawReciprocalHermitianMass = xiEndpointCompletedCurvature :=
      le_antisymm hupper hlower
    rw [← xiEndpointReflectionDefectEnergy_eq_zero_iff_rh,
      xiEndpointReflectionDefectEnergy_eq_mass_sub_source, heq, sub_self,
      mul_zero]
  · intro hRH
    have hzero := xiEndpointReflectionDefectEnergy_eq_zero_iff_rh.mpr hRH
    rw [xiEndpointReflectionDefectEnergy_eq_mass_sub_source] at hzero
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    have hsub : xiRawReciprocalHermitianMass - xiEndpointCompletedCurvature = 0 :=
      (mul_eq_zero.mp hzero).resolve_left htwo
    exact le_of_eq (sub_eq_zero.mp hsub)

end
end RHTower

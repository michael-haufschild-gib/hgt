import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OriginDegreeDoesNotDescendThroughPoissonBoundaries

/-!
# Positive origin degree survives on pole-blind Poisson boundaries

Applying the polynomial `s(s-1)` through the actual negative Euler operator gives
a nonzero boundary with both pole values zero. Its sharp square is a positive
origin-degree boundary and a pure-source principal cycle. Even an arbitrary
normalized correction depending on the two pole values cannot make this degree
descend through Poisson cohomology.
-/

noncomputable section
open Complex RHTower
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A cap producer for the boundary transform `s(s-1)xi(s)`. -/
def meyerPoleBlindXiCap : DeningerMeyerCap :=
  deningerMeyerNegativeEuler (deningerMeyerNegativeEuler deningerMeyerXiCapSource) -
    deningerMeyerNegativeEuler deningerMeyerXiCapSource

theorem meyerPoleBlindXiCap_mellin (s : ℂ) :
    deningerMeyerBoundaryMellin meyerPoleBlindXiCap s = s * (s - 1) * xi s := by
  change deningerMeyerBoundaryMellinLM s (_ - _) = _
  rw [map_sub]
  change deningerMeyerBoundaryMellin
      (deningerMeyerNegativeEuler (deningerMeyerNegativeEuler deningerMeyerXiCapSource)) s -
    deningerMeyerBoundaryMellin (deningerMeyerNegativeEuler deningerMeyerXiCapSource) s = _
  simp only [deningerMeyerBoundaryMellin_negativeEuler, deningerMeyerXiCapSource_mellin]
  ring

theorem meyerPoleBlindXiCap_boundary_ne_zero :
    deningerMeyerStrongLogSumLM meyerPoleBlindXiCap ≠ 0 := by
  intro hz
  have h := meyerPoleBlindXiCap_mellin 2
  change deningerMeyerStrongLogMellinLM 2
    (deningerMeyerStrongLogSumLM meyerPoleBlindXiCap) = _ at h
  rw [hz, map_zero] at h
  have htwo : (2 : ℂ) * (2 - 1) ≠ 0 := by norm_num
  exact (mul_ne_zero htwo xi_two_ne_zero) h.symm

/-- A genuine boundary sharp square invisible to both pole evaluations has positive origin degree. -/
theorem exists_meyer_pole_blind_boundary_positive_originDegree :
    ∃ q : DeningerMeyerStrongLogTarget,
      q ∈ LinearMap.range deningerMeyerStrongLogSumLM ∧
      deningerMeyerStrongLogMellinLM 0 q = 0 ∧
      deningerMeyerStrongLogMellinLM 1 q = 0 ∧ 0 < (meyerOriginDegree q).re := by
  let g := deningerMeyerStrongLogSumLM meyerPoleBlindXiCap
  let q := deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)
  have hm0 : deningerMeyerStrongLogMellin g 0 = 0 := by
    change deningerMeyerBoundaryMellin meyerPoleBlindXiCap 0 = 0
    rw [meyerPoleBlindXiCap_mellin, zero_mul, zero_mul]
  have hm1 : deningerMeyerStrongLogMellin g 1 = 0 := by
    change deningerMeyerBoundaryMellin meyerPoleBlindXiCap 1 = 0
    rw [meyerPoleBlindXiCap_mellin, sub_self, mul_zero, zero_mul]
  refine ⟨q, ?_, ?_, ?_, meyerOriginDegree_sharp_square_pos
    meyerPoleBlindXiCap_boundary_ne_zero⟩
  · obtain ⟨f, hf⟩ := deningerMeyerSourceConvolution_boundary
      (deningerMeyerSourceSharp g) meyerPoleBlindXiCap
    refine ⟨f, ?_⟩
    rw [hf, deningerMeyerSourceConvolution_comm]
  · change deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g
      (deningerMeyerSourceSharp g)) 0 = 0
    rw [deningerMeyerSourceConvolution_mellin, hm0, zero_mul]
  · change deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g
      (deningerMeyerSourceSharp g)) 1 = 0
    rw [deningerMeyerSourceConvolution_mellin, hm1, zero_mul]

/-- Some genuine principal cycle needs no fibre compensation and has positive source mass. -/
theorem exists_meyer_pure_source_principal_positive_originDegree :
    ∃ (f : DeningerMeyerCap) (q : DeningerMeyerStrongLogTarget),
      q ≠ 0 ∧ meyerPrincipalCycle f = (0, 0, q) ∧ 0 < (meyerOriginDegree q).re := by
  obtain ⟨q, ⟨f, hf⟩, h0, h1, hp⟩ :=
    exists_meyer_pole_blind_boundary_positive_originDegree
  refine ⟨f, q, ?_, ?_, hp⟩
  · intro hz
    rw [hz, map_zero, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  · simp only [meyerPrincipalCycle, hf, meyerPoleA, meyerPoleB, h0, h1,
      Complex.zero_re, neg_zero]

/-- All intersection readings miss a nonzero pure source with positive origin degree. -/
theorem exists_meyer_pure_source_radical_positive_originDegree :
    ∃ q : DeningerMeyerStrongLogTarget,
      q ≠ 0 ∧ 0 < (meyerOriginDegree q).re ∧
      ∀ x : MeyerScalingCycle,
        meyerScalingPair (0, 0, q) x = 0 ∧ meyerScalingPair x (0, 0, q) = 0 := by
  obtain ⟨f, q, hn, he, hp⟩ := exists_meyer_pure_source_principal_positive_originDegree
  refine ⟨q, hn, hp, fun x => ?_⟩
  rw [← he]
  exact ⟨meyerPrincipalCycle_pair_left f x, meyerPrincipalCycle_pair_right x f⟩

/-- No correction using only the two pole values makes origin degree a quotient degree. -/
theorem meyerOriginDegree_pole_correction_not_cohomology_degree :
    ¬ ∃ (F : ℂ → ℂ → ℂ) (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ),
      ∀ g : DeningerMeyerStrongLogTarget,
        d (Submodule.Quotient.mk g) = meyerOriginDegree g +
          F (deningerMeyerStrongLogMellinLM 0 g) (deningerMeyerStrongLogMellinLM 1 g) -
          F 0 0 := by
  rintro ⟨F, d, hd⟩
  obtain ⟨q, hq, h0, h1, hp⟩ := exists_meyer_pole_blind_boundary_positive_originDegree
  have hz : (Submodule.Quotient.mk q : DeningerMeyerStrongLogCohomology) = 0 :=
    (Submodule.Quotient.mk_eq_zero (LinearMap.range deningerMeyerStrongLogSumLM)).mpr hq
  have he := hd q
  rw [hz, map_zero, h0, h1, add_sub_cancel_right] at he
  rw [← he, Complex.zero_re] at hp
  exact lt_irrefl _ hp

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

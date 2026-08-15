import GaloisForLFunctions.RHTower.XiWardCubicPrimeGammaMixedSecantGraph
import GaloisForLFunctions.RHTower.GaussHodgeWeilFundamentalSymmetry
import GaloisForLFunctions.RHTower.DeningerPrimeGammaEulerSectorObstruction

/-!
# Prime--Gamma secant fundamental-symmetry gap (W-H206)

W-H203 leaves a precise sign seam: its reflected prime--Gamma source cup is a sum of complex
bilinear secant squares, whereas the target cubic trace is Hermitian.  The tempting repair is to
insert the unconditional Weil fundamental symmetry `J`.  This module proves exactly what that
repair costs.

For every square-summable test, its positive `J`-metric energy minus its ordinary Weil diagonal is
one half of the reflection-difference energy.  More sharply, any single nondegenerate Cauchy
secant whose two poles lie in the strict lower Euler sector has nonzero reflection difference at
every off-line divisor point.  Consequently the `J`-metric/Weil gap of this one fixed secant is
zero if and only if RH, and it is strictly positive under `not RH`.

Thus the Schwarz shorting requested after W-H203 is not a routine unconditional identification:
even for one literal coefficient-free source secant, annihilating its fundamental-symmetry gap is
already exactly RH.  A viable Ward completion must prove a genuinely one-sided quantitative
source bound retaining this gap; it cannot erase the gap by identifying the two metrics.
-/

open Complex

namespace RHTower

noncomputable section

/-- A nondegenerate Cauchy secant with both poles in the strict lower Euler sector has nonzero
reflection difference at every off-line Xi divisor copy. -/
theorem xiWardCubicPrimeGammaLowerSecant_pairDif_ne_zero
    (z0 z1 : DeningerPrimeGammaLowerPoint) (hz : z0 ≠ z1)
    (q : XiZeroCopy) (hq : (xiSpectralPoint q).im ≠ 0) :
    xiWeilPairDif (xiWardCubicPrimeGammaLowerSecantTest z0 z1) q ≠ 0 := by
  let a := xiSpectralPoint q
  let b := (starRingEnd ℂ) a
  have haIm := xiSpectralPoint_im_mem_openHalf q
  have hz0Im := deningerPrimeGammaLowerPoint_im_lt z0
  have hz1Im := deningerPrimeGammaLowerPoint_im_lt z1
  have ha0 : a ≠ (z0 : ℂ) := by
    intro h
    have := congrArg Complex.im h
    dsimp [a] at this
    linarith
  have ha1 : a ≠ (z1 : ℂ) := by
    intro h
    have := congrArg Complex.im h
    dsimp [a] at this
    linarith
  have hb0 : b ≠ (z0 : ℂ) := by
    intro h
    have := congrArg Complex.im h
    dsimp [b, a] at this
    linarith
  have hb1 : b ≠ (z1 : ℂ) := by
    intro h
    have := congrArg Complex.im h
    dsimp [b, a] at this
    linarith
  have hab : a - b ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    dsimp [a, b] at him
    apply hq
    linarith
  have hsum : a + b - (z1 : ℂ) - (z0 : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    dsimp [a, b] at him
    linarith
  intro hdif
  rw [xiWeilPairDif, xiSpectralPoint_lineConj] at hdif
  change xiWardCubicPrimeGammaLowerSecantTest z0 z1 a -
      xiWardCubicPrimeGammaLowerSecantTest z0 z1 b = 0 at hdif
  have heq : xiWardCubicPrimeGammaLowerSecantTest z0 z1 a =
      xiWardCubicPrimeGammaLowerSecantTest z0 z1 b := sub_eq_zero.mp hdif
  rw [xiWardCubicPrimeGammaLowerSecantTest_factorization hz ha0 ha1,
    xiWardCubicPrimeGammaLowerSecantTest_factorization hz hb0 hb1] at heq
  have hprod : (a - (z1 : ℂ)) * (a - (z0 : ℂ)) =
      (b - (z1 : ℂ)) * (b - (z0 : ℂ)) := by
    have hinv := congrArg (fun x : ℂ => x⁻¹) heq
    simpa [mul_inv_rev, mul_comm] using hinv
  have hfactor : (a - b) * (a + b - (z1 : ℂ) - (z0 : ℂ)) = 0 := by
    calc
      (a - b) * (a + b - (z1 : ℂ) - (z0 : ℂ)) =
          (a - (z1 : ℂ)) * (a - (z0 : ℂ)) -
            (b - (z1 : ℂ)) * (b - (z0 : ℂ)) := by ring
      _ = 0 := sub_eq_zero.mpr hprod
  exact (mul_ne_zero hab hsum) hfactor

/-- Every finite lower source secant is square-summable on the complete Xi divisor. -/
theorem xiWardCubicPrimeGammaLowerSecant_squareSummable
    (z0 z1 : DeningerPrimeGammaLowerPoint) :
    XiWeilSquareSummable (xiWardCubicPrimeGammaLowerSecantTest z0 z1) := by
  let F0 := xiWeilCauchyTest (z0 : ℂ)
  let F1 := xiWeilCauchyTest (z1 : ℂ)
  let dz : ℂ := (z1 : ℂ) - z0
  have hF0 : XiWeilSquareSummable F0 := XiWeilSquareSummable_cauchy _
  have hF1 : XiWeilSquareSummable F1 := XiWeilSquareSummable_cauchy _
  have hsum := hF1.add (hF0.const_smul (-1))
  have hscaled := hsum.const_smul dz⁻¹
  apply hscaled.congr
  intro a
  simp [xiWardCubicPrimeGammaLowerSecantTest, F0, F1, dz,
    div_eq_mul_inv]
  ring_nf

/-- One fixed nondegenerate strict-Euler secant has zero reflection-difference energy exactly
under RH.  No family of test functions is needed. -/
theorem riemannHypothesis_iff_fixedPrimeGammaSecant_pairDifEnergy_zero
    (z0 z1 : DeningerPrimeGammaLowerPoint) (hz : z0 ≠ z1) :
    RiemannHypothesis ↔
      (∑' q : XiZeroCopy,
        ‖xiWeilPairDif (xiWardCubicPrimeGammaLowerSecantTest z0 z1) q‖ ^ 2) = 0 := by
  let F := xiWardCubicPrimeGammaLowerSecantTest z0 z1
  have hFsq : XiWeilSquareSummable F :=
    xiWardCubicPrimeGammaLowerSecant_squareSummable z0 z1
  constructor
  · intro hRH
    exact (riemannHypothesis_iff_forall_pairDifEnergy_eq_zero.mp hRH) F hFsq
  · intro hzero
    by_contra hnRH
    rw [riemannHypothesis_iff_xi_zero_re_eq_half] at hnRH
    obtain ⟨rho, hrho⟩ := not_forall.mp hnRH
    obtain ⟨hzeroRho, hre⟩ := Classical.not_imp.mp hrho
    have hXiC : XiC (((rho : ℂ) - 1 / 2) * (-Complex.I)) = 0 := by
      rw [XiC]
      have harg : 1 / 2 + ((rho : ℂ) - 1 / 2) * -Complex.I * Complex.I = rho := by
        have hI : (-Complex.I) * Complex.I = 1 := by
          rw [neg_mul, Complex.I_mul_I]
          ring
        linear_combination ((rho : ℂ) - 1 / 2) * hI
      rw [harg]
      exact hzeroRho
    obtain ⟨q0, hq0⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hXiC
    have him : ((((rho : ℂ) - 1 / 2) * (-Complex.I))).im ≠ 0 := by
      simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
      norm_num
      intro h
      apply hre
      linarith
    have hqIm : (xiSpectralPoint q0).im ≠ 0 := by rwa [hq0]
    have hne : xiWeilPairDif F q0 ≠ 0 :=
      xiWardCubicPrimeGammaLowerSecant_pairDif_ne_zero z0 z1 hz q0 hqIm
    have hsum : Summable (fun q : XiZeroCopy => ‖xiWeilPairDif F q‖ ^ 2) :=
      xiWeilPairDif_squareSummable hFsq
    have hle : ‖xiWeilPairDif F q0‖ ^ 2 ≤
        ∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ 2 :=
      hsum.le_tsum q0 (fun q _ => sq_nonneg _)
    have hpos : 0 < ‖xiWeilPairDif F q0‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hne)
    change (∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ 2) = 0 at hzero
    rw [hzero] at hle
    linarith

/-- **W-H206 exact gap law.**  The positive `J`-metric energy exceeds the ordinary diagonal Weil
value by exactly half the reflection-difference energy. -/
theorem xiWeilParityFlip_energy_sub_weil_eq_half_pairDifEnergy
    {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    (xiWeilPolarization F (xiWeilParityFlip F)).re -
        (xiWeilPolarization F F).re =
      (1 / 2 : ℝ) *
        ∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ 2 := by
  have hline := xiWeil_squareSummable_lineConj hF
  have hplus := xiWeilPairSum_squareSummable hF
  have hdif := xiWeilPairDif_squareSummable hF
  have hpoint : ∀ q : XiZeroCopy,
      ‖xiWeilPairSum F q‖ ^ 2 + ‖xiWeilPairDif F q‖ ^ 2 =
        2 * (‖F (xiSpectralPoint q)‖ ^ 2 +
          ‖F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖ ^ 2) := by
    intro q
    rw [xiWeilPairSum, xiWeilPairDif,
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add, Complex.normSq_sub]
    ring
  have hlineTsum :
      (∑' q : XiZeroCopy,
        ‖F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖ ^ 2) =
      ∑' q : XiZeroCopy, ‖F (xiSpectralPoint q)‖ ^ 2 := by
    exact xiZeroCopyLineConjEquiv.tsum_eq
      (fun q : XiZeroCopy => ‖F (xiSpectralPoint q)‖ ^ 2)
  have htotal :
      (∑' q : XiZeroCopy, ‖xiWeilPairSum F q‖ ^ 2) +
          (∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ 2) =
        4 * ∑' q : XiZeroCopy, ‖F (xiSpectralPoint q)‖ ^ 2 := by
    rw [← hplus.tsum_add hdif]
    calc
      (∑' q : XiZeroCopy,
          (‖xiWeilPairSum F q‖ ^ 2 + ‖xiWeilPairDif F q‖ ^ 2)) =
          ∑' q : XiZeroCopy,
            2 * (‖F (xiSpectralPoint q)‖ ^ 2 +
              ‖F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖ ^ 2) :=
        tsum_congr hpoint
      _ = 2 * ((∑' q : XiZeroCopy, ‖F (xiSpectralPoint q)‖ ^ 2) +
          ∑' q : XiZeroCopy,
            ‖F (xiSpectralPoint (xiZeroCopyLineConjEquiv q))‖ ^ 2) := by
        rw [tsum_mul_left, hF.tsum_add hline]
      _ = 4 * ∑' q : XiZeroCopy, ‖F (xiSpectralPoint q)‖ ^ 2 := by
        rw [hlineTsum]
        ring
  have hJ := (xiWeilParityFlip_hasSum_sq hF).tsum_eq
  have hW := xiWeilPolarization_re_eq_krein hF
  nlinarith

/-- **W-H206 fixed witness.**  For one nondegenerate strict-Euler secant, equality of the
positive `J`-metric and the ordinary Weil diagonal is equivalent to RH. -/
theorem riemannHypothesis_iff_fixedPrimeGammaSecant_fundamentalSymmetryGap_zero
    (z0 z1 : DeningerPrimeGammaLowerPoint) (hz : z0 ≠ z1) :
    RiemannHypothesis ↔
      (xiWeilPolarization
          (xiWardCubicPrimeGammaLowerSecantTest z0 z1)
          (xiWeilParityFlip
            (xiWardCubicPrimeGammaLowerSecantTest z0 z1))).re -
        (xiWeilPolarization
          (xiWardCubicPrimeGammaLowerSecantTest z0 z1)
          (xiWardCubicPrimeGammaLowerSecantTest z0 z1)).re = 0 := by
  rw [xiWeilParityFlip_energy_sub_weil_eq_half_pairDifEnergy
    (xiWardCubicPrimeGammaLowerSecant_squareSummable z0 z1)]
  constructor
  · intro hRH
    rw [(riemannHypothesis_iff_fixedPrimeGammaSecant_pairDifEnergy_zero
      z0 z1 hz).mp hRH]
    ring
  · intro h
    apply (riemannHypothesis_iff_fixedPrimeGammaSecant_pairDifEnergy_zero
      z0 z1 hz).mpr
    linarith

/-- Under failure of RH the fixed secant fundamental-symmetry gap is strictly positive. -/
theorem fixedPrimeGammaSecant_fundamentalSymmetryGap_pos_of_not_rh
    (z0 z1 : DeningerPrimeGammaLowerPoint) (hz : z0 ≠ z1)
    (hnRH : ¬ RiemannHypothesis) :
    0 <
      (xiWeilPolarization
          (xiWardCubicPrimeGammaLowerSecantTest z0 z1)
          (xiWeilParityFlip
            (xiWardCubicPrimeGammaLowerSecantTest z0 z1))).re -
        (xiWeilPolarization
          (xiWardCubicPrimeGammaLowerSecantTest z0 z1)
          (xiWardCubicPrimeGammaLowerSecantTest z0 z1)).re := by
  let F := xiWardCubicPrimeGammaLowerSecantTest z0 z1
  have hgap := xiWeilParityFlip_energy_sub_weil_eq_half_pairDifEnergy
    (xiWardCubicPrimeGammaLowerSecant_squareSummable z0 z1)
  have hnonneg : 0 ≤
      (xiWeilPolarization F (xiWeilParityFlip F)).re -
        (xiWeilPolarization F F).re := by
    rw [hgap]
    positivity
  have hne :
      (xiWeilPolarization F (xiWeilParityFlip F)).re -
        (xiWeilPolarization F F).re ≠ 0 := by
    intro hzero
    exact hnRH
      ((riemannHypothesis_iff_fixedPrimeGammaSecant_fundamentalSymmetryGap_zero
        z0 z1 hz).mpr hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end

end RHTower

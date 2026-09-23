import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFECocycleHyperbolicModulusOrientation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBogoliubovCCRCompletionEndpoint

/-!
# Source-FE modular Bogoliubov dilation no-go

The literal Birmingham--Mokhtari source-FE cocycle expands on one member of each reflected Xi
orbit and contracts on the other. This module canonically chooses the expanding member and embeds
its exact squared gain into a minimal two-mode bosonic Bogoliubov fibre.

The resulting Nambu map preserves the full signed Hermitian form on every orbit, including tilted
ones. Its partner number is reflection invariant, vanishes exactly on the critical wall, and is
strictly positive off it. Thus conservative `SU(1,1)`/CCR scattering does not force the missing
source Ward law: off-wall source gain is absorbed as genuine partner production without violating
pseudo-unitarity.

Partner-vacuum extinction is pointwise equivalent to HB optical darkness, Deninger Ward
cancellation, FZZ-P equilibrium, PW-B balance, and canonical-copy RBH balance. Universal
extinction is exactly RH. This is an unconditional scattering no-go and positive survivor, not an
assertion that the physical augmented source realizes vacuum extinction.

`[NEW] [BOGOLIUBOV DILATION] [NO-GO] [POSITIVE SURVIVOR] [LEAN-PROVED]`
-/

open Complex Real
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Squared source-FE gain on the expanding representative of one reflection orbit. -/
def hbXiPeierlsUnitSourceFEOrbitExpandingGain (q : XiZeroCopy) : ℝ :=
  if (q.1 : ℂ).re ≤ 1 / 2 then
    Complex.normSq (hbXiPeierlsUnitSourceFECocycle q)
  else
    Complex.normSq
      (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q))

/-- Partner occupation in the minimal bosonic completion of the expanding source-FE gain. -/
def hbXiPeierlsUnitSourceFEOrbitPartnerNumber (q : XiZeroCopy) : ℝ :=
  hbXiPeierlsUnitSourceFEOrbitExpandingGain q - 1

/-- Positive-sheet coefficient of the source-FE orbit completion. -/
def hbXiPeierlsUnitSourceFEOrbitBogoliubovGain (q : XiZeroCopy) : ℝ :=
  Real.sqrt (hbXiPeierlsUnitSourceFEOrbitExpandingGain q)

/-- Canonical real pair amplitude of the source-FE orbit completion. -/
def hbXiPeierlsUnitSourceFEOrbitBogoliubovPair (q : XiZeroCopy) : ℂ :=
  (Real.sqrt (hbXiPeierlsUnitSourceFEOrbitPartnerNumber q) : ℂ)

/-- The chosen reflection-orbit gain lies on the positive bosonic sheet. -/
theorem hbXiPeierlsUnitSourceFEOrbitExpandingGain_ge_one (q : XiZeroCopy) :
    1 ≤ hbXiPeierlsUnitSourceFEOrbitExpandingGain q := by
  rw [hbXiPeierlsUnitSourceFEOrbitExpandingGain]
  split_ifs with h
  · by_cases hline : (q.1 : ℂ).re = 1 / 2
    · exact le_of_eq ((normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).2 hline).symm
    · exact le_of_lt ((one_lt_normSq_hbXiPeierlsUnitSourceFECocycle_iff q).2
        (lt_of_le_of_ne h hline))
  · have hright : 1 / 2 < (q.1 : ℂ).re := lt_of_not_ge h
    have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) :=
      xiZeroReflectEquiv_apply q.1
    have hrefleft : ((xiZeroCopyReflectEquiv q).1 : ℂ).re < 1 / 2 := by
      rw [href]
      norm_num
      linarith
    exact le_of_lt
      ((one_lt_normSq_hbXiPeierlsUnitSourceFECocycle_iff
        (xiZeroCopyReflectEquiv q)).2 hrefleft)

/-- Partner occupation is nonnegative on every reflected Xi orbit. -/
theorem hbXiPeierlsUnitSourceFEOrbitPartnerNumber_nonneg (q : XiZeroCopy) :
    0 ≤ hbXiPeierlsUnitSourceFEOrbitPartnerNumber q := by
  rw [hbXiPeierlsUnitSourceFEOrbitPartnerNumber]
  linarith [hbXiPeierlsUnitSourceFEOrbitExpandingGain_ge_one q]

/-- The expanding orbit gain reaches the identity exactly on the critical wall. -/
theorem hbXiPeierlsUnitSourceFEOrbitExpandingGain_eq_one_iff (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEOrbitExpandingGain q = 1 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsUnitSourceFEOrbitExpandingGain]
  split_ifs with h
  · exact normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q
  · constructor
    · intro hgain
      have hrefline :=
        (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff
          (xiZeroCopyReflectEquiv q)).1 hgain
      have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) :=
        xiZeroReflectEquiv_apply q.1
      rw [href] at hrefline
      norm_num at hrefline
      linarith
    · intro hline
      exact False.elim (h hline.le)

/-- Partner vacuum is exactly critical-line placement. -/
theorem hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsUnitSourceFEOrbitPartnerNumber, sub_eq_zero,
    hbXiPeierlsUnitSourceFEOrbitExpandingGain_eq_one_iff]

/-- Every tilted orbit necessarily has strictly positive partner occupation. -/
theorem hbXiPeierlsUnitSourceFEOrbitPartnerNumber_pos_iff (q : XiZeroCopy) :
    0 < hbXiPeierlsUnitSourceFEOrbitPartnerNumber q ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hpos hline
    have hz := (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q).2 hline
    linarith
  · intro hline
    exact lt_of_le_of_ne
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_nonneg q)
      (Ne.symm
        ((hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q).not.mpr hline))

/-- Exact square of the positive-sheet Bogoliubov gain. -/
theorem hbXiPeierlsUnitSourceFEOrbitBogoliubovGain_sq (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEOrbitBogoliubovGain q ^ (2 : ℕ) =
      hbXiPeierlsUnitSourceFEOrbitExpandingGain q := by
  rw [hbXiPeierlsUnitSourceFEOrbitBogoliubovGain, Real.sq_sqrt]
  linarith [hbXiPeierlsUnitSourceFEOrbitExpandingGain_ge_one q]

/-- The pair-amplitude norm square is the literal source-orbit partner number. -/
theorem norm_hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_sq (q : XiZeroCopy) :
    ‖hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q‖ ^ (2 : ℕ) =
      hbXiPeierlsUnitSourceFEOrbitPartnerNumber q := by
  rw [hbXiPeierlsUnitSourceFEOrbitBogoliubovPair, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
  exact hbXiPeierlsUnitSourceFEOrbitPartnerNumber_nonneg q

/-- Every literal source-FE reflection orbit has an exact two-mode bosonic CCR completion. -/
theorem hbXiPeierlsUnitSourceFEOrbit_isTwoModeBosonicCCR (q : XiZeroCopy) :
    IsTwoModeBosonicCCR
      (hbXiPeierlsUnitSourceFEOrbitBogoliubovGain q)
      (hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q) := by
  rw [IsTwoModeBosonicCCR,
    hbXiPeierlsUnitSourceFEOrbitBogoliubovGain_sq,
    norm_hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_sq,
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber]
  ring

/-- Positive-norm Nambu output of the source-FE orbit completion. -/
def hbXiPeierlsUnitSourceFEOrbitBogoliubovPositiveOutput
    (q : XiZeroCopy) (x y : ℂ) : ℂ :=
  (hbXiPeierlsUnitSourceFEOrbitBogoliubovGain q : ℂ) * x +
    hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q * y

/-- Partner Nambu output of the source-FE orbit completion. -/
def hbXiPeierlsUnitSourceFEOrbitBogoliubovPartnerOutput
    (q : XiZeroCopy) (x y : ℂ) : ℂ :=
  conj (hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q) * x +
    (hbXiPeierlsUnitSourceFEOrbitBogoliubovGain q : ℂ) * y

/-- The source-specific completion preserves the full Nambu signed Hermitian form, on and off the
critical wall. -/
theorem hbXiPeierlsUnitSourceFEOrbitBogoliubov_preserves_signedHermitian
    (q : XiZeroCopy) (x y : ℂ) :
    conj (hbXiPeierlsUnitSourceFEOrbitBogoliubovPositiveOutput q x y) *
          hbXiPeierlsUnitSourceFEOrbitBogoliubovPositiveOutput q x y -
        conj (hbXiPeierlsUnitSourceFEOrbitBogoliubovPartnerOutput q x y) *
          hbXiPeierlsUnitSourceFEOrbitBogoliubovPartnerOutput q x y =
      conj x * x - conj y * y := by
  let a : ℝ := hbXiPeierlsUnitSourceFEOrbitBogoliubovGain q
  let b : ℂ := hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q
  have hccr := hbXiPeierlsUnitSourceFEOrbit_isTwoModeBosonicCCR q
  change a ^ (2 : ℕ) - ‖b‖ ^ (2 : ℕ) = 1 at hccr
  have hccrC := congrArg (fun r : ℝ => (r : ℂ)) hccr
  push_cast at hccrC
  change (a : ℂ) ^ (2 : ℕ) - (‖b‖ : ℂ) ^ (2 : ℕ) = 1 at hccrC
  have hnormC : (‖b‖ : ℂ) ^ (2 : ℕ) = conj b * b := by
    rw [show (‖b‖ : ℂ) ^ (2 : ℕ) = ((‖b‖ ^ (2 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [hnormC] at hccrC
  change conj ((a : ℂ) * x + b * y) * ((a : ℂ) * x + b * y) -
      conj (conj b * x + (a : ℂ) * y) *
        (conj b * x + (a : ℂ) * y) = conj x * x - conj y * y
  simp only [map_add, map_mul, conj_ofReal, conj_conj]
  linear_combination (conj x * x - conj y * y) * hccrC

/-- The expanding gain is intrinsic to the reflection orbit. -/
theorem hbXiPeierlsUnitSourceFEOrbitExpandingGain_reflect (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEOrbitExpandingGain (xiZeroCopyReflectEquiv q) =
      hbXiPeierlsUnitSourceFEOrbitExpandingGain q := by
  have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) :=
    xiZeroReflectEquiv_apply q.1
  rw [hbXiPeierlsUnitSourceFEOrbitExpandingGain,
    hbXiPeierlsUnitSourceFEOrbitExpandingGain]
  by_cases hleft : (q.1 : ℂ).re ≤ 1 / 2
  · by_cases hline : (q.1 : ℂ).re = 1 / 2
    · have hrefline : ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≤ 1 / 2 := by
        rw [href]
        norm_num
        linarith
      rw [if_pos hleft, if_pos hrefline]
      have hq := (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).2 hline
      have hr :=
        (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff
          (xiZeroCopyReflectEquiv q)).2 (by
            rw [href]
            norm_num
            linarith)
      rw [hq, hr]
    · have hstrict : (q.1 : ℂ).re < 1 / 2 := lt_of_le_of_ne hleft hline
      have hrefnot : ¬ ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≤ 1 / 2 := by
        rw [href]
        norm_num
        linarith
      rw [if_pos hleft, if_neg hrefnot, xiZeroCopyReflectEquiv_apply_apply]
  · have hstrict : 1 / 2 < (q.1 : ℂ).re := lt_of_not_ge hleft
    have hrefleft : ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≤ 1 / 2 := by
      rw [href]
      norm_num
      linarith
    rw [if_neg hleft, if_pos hrefleft]

/-- Source partner occupation is reflection invariant. -/
theorem hbXiPeierlsUnitSourceFEOrbitPartnerNumber_reflect (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber (xiZeroCopyReflectEquiv q) =
      hbXiPeierlsUnitSourceFEOrbitPartnerNumber q := by
  rw [hbXiPeierlsUnitSourceFEOrbitPartnerNumber,
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber,
    hbXiPeierlsUnitSourceFEOrbitExpandingGain_reflect]

/-- Universal partner-vacuum scattering of the literal source-FE orbit is exactly RH. -/
theorem forall_hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_rh :
    (∀ q : XiZeroCopy, hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0) ↔
      RiemannHypothesis := by
  rw [← forall_normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_rh]
  constructor
  · intro h q
    exact (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).2
      ((hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q).1 (h q))
  · intro h q
    exact (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q).2
      ((normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).1 (h q))

/-- Partner vacuum and HB canonical optical darkness are pointwise identical. -/
theorem hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_opticalPower_zero
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 ↔
      hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 := by
  calc
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 ↔
        (q.1 : ℂ).re = 1 / 2 :=
      hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q
    _ ↔ Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1 :=
      (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).symm
    _ ↔ hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 :=
      normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_opticalPower_zero n q

/-- Partner vacuum and Deninger reflect-gauge Ward cancellation are pointwise identical. -/
theorem hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_sharedWardCharge_zero
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 ↔
      fzzCigarParityDeningerReflectGaugeWardCharge q = 0 := by
  calc
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 ↔
        Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1 :=
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q).trans
        (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).symm
    _ ↔ _ :=
      normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_sharedWardCharge_zero n q

/-- Partner vacuum and FZZ-P information equilibrium are pointwise identical. -/
theorem hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_informationForce_zero
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 ↔
      fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re = 0 := by
  calc
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 ↔
        Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1 :=
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q).trans
        (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).symm
    _ ↔ _ := normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_informationForce_zero n q

/-- Partner vacuum and PW-B balance are pointwise identical at every recoil grade. -/
theorem hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_pwBalance_zero
    (n : ℕ) (q : XiZeroCopy) (k : ℕ) :
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 ↔
      schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k = 0 := by
  calc
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 ↔
        Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1 :=
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q).trans
        (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).symm
    _ ↔ _ := normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_pwBalance_zero n q k

/-- On the canonical divisor copy, partner vacuum and RBH multiplicity-leading balance coincide. -/
theorem hbXiPeierlsUnitSourceFEOrbitPartnerNumber_firstCopy_eq_zero_iff_rbhBalance_zero
    (n : ℕ) (rho : XiDivisorSupport) :
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber
        (reflectedBiHeatFirstDivisorCopy rho) = 0 ↔
      reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 := by
  calc
    hbXiPeierlsUnitSourceFEOrbitPartnerNumber
          (reflectedBiHeatFirstDivisorCopy rho) = 0 ↔
        Complex.normSq
          (hbXiPeierlsUnitSourceFECocycle
            (reflectedBiHeatFirstDivisorCopy rho)) = 1 :=
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff
        (reflectedBiHeatFirstDivisorCopy rho)).trans
        (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff
          (reflectedBiHeatFirstDivisorCopy rho)).symm
    _ ↔ _ :=
      normSq_hbXiPeierlsUnitSourceFECocycle_firstCopy_eq_one_iff_rbhBalance_zero n rho

end

end RHTower

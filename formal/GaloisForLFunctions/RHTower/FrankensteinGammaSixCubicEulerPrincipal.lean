import GaloisForLFunctions.RHTower.XiGammaSixFilteredBoundaryHarmonicResidue
import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanHessianDomination
import GaloisForLFunctions.RHTower.SourceHorizontalEulerGammaCubicNegativeRenormalizedChannel

/-!
# Gamma-six / Euler cubic principal-source splice

At a retained off-wall Gamma-six boundary, the exact harmonic residue is not
replaced by an abstract scalar counterterm. After the literal third Euler
jet, it is represented by the complete pre-Xi Euler cubic source atom. This
file records the coefficientwise principal-class identity and its summable
remainder.
-/

open Filter Topology
open scoped BigOperators
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Literal cubic Euler renormalization of one Gamma-six boundary coefficient. -/
def gammaSixCubicEulerPrincipalDefect
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  gammaSixFilteredBoundaryAsymptoticResidue m
      (primeDepthBVWoldXiCenteredRate q.1) *
      sourceHorizontalEulerGammaCubicAtom p -
    Real.log (p : ℝ) ^ 3 * gammaSixFilteredBoundarySecondJet m q p

/-- Exact coefficientwise split into Euler-versus-harmonic correction and literal Gamma-six loss. -/
theorem gammaSixCubicEulerPrincipalDefect_eq
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixCubicEulerPrincipalDefect m q p =
      gammaSixFilteredBoundaryAsymptoticResidue m
          (primeDepthBVWoldXiCenteredRate q.1) *
        (sourceHorizontalEulerGammaCubicAtom p -
          Real.log (p : ℝ) ^ 3 / (p : ℝ)) +
      Real.log (p : ℝ) ^ 3 * gammaSixFilteredBoundaryHarmonicDefect m q p := by
  rw [gammaSixCubicEulerPrincipalDefect,
    gammaSixFilteredBoundarySecondJet_eq_harmonic_sub_defect]
  ring

/-- Complete Euler cubic atom dominates its bare prime-harmonic principal part. -/
theorem sourceHorizontalEulerGammaCubicAtom_sub_log_cube_div_nonneg
    (p : Nat.Primes) :
    0 ≤ sourceHorizontalEulerGammaCubicAtom p -
      Real.log (p : ℝ) ^ 3 / (p : ℝ) := by
  let P : ℝ := p
  have hP0 : 0 < P := by
    dsimp [P]
    exact_mod_cast p.2.pos
  have hP1 : (1 : ℝ) < P := by
    dsimp [P]
    exact_mod_cast p.2.one_lt
  have hq0 : 0 ≤ P⁻¹ := (inv_pos.mpr hP0).le
  have hq1 : P⁻¹ < 1 := (inv_lt_one₀ hP0).2 hP1
  have hbase0 : 0 ≤ 1 - P⁻¹ := by linarith
  have hbase1 : 1 - P⁻¹ ≤ 1 := by linarith
  have hden : 0 < (1 - P⁻¹) ^ 3 := pow_pos (by linarith) 3
  have hpow : (1 - P⁻¹) ^ 3 ≤ 1 := pow_le_one₀ hbase0 hbase1
  have hratio : 1 ≤ (1 + P⁻¹) / (1 - P⁻¹) ^ 3 := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hlog : 0 ≤ Real.log P ^ 3 := by
    exact pow_nonneg (Real.log_nonneg hP1.le) _
  have hscale : Real.log P ^ 3 * P⁻¹ ≤
      Real.log P ^ 3 * (P⁻¹ * ((1 + P⁻¹) / (1 - P⁻¹) ^ 3)) := by
    gcongr
    have hnonneg : 0 ≤ P⁻¹ *
        ((1 + P⁻¹) / (1 - P⁻¹) ^ 3 - 1) :=
      mul_nonneg hq0 (by linarith)
    linarith
  have hdiv : Real.log P ^ 3 / P = Real.log P ^ 3 * P⁻¹ := by
    field_simp [hP0.ne']
  rw [sourceHorizontalEulerGammaCubicAtom_eq p]
  change 0 ≤ Real.log P ^ 3 *
      (P⁻¹ * (1 + P⁻¹) / (1 - P⁻¹) ^ 3) - Real.log P ^ 3 / P
  rw [hdiv]
  exact sub_nonneg.mpr (by convert hscale using 1; ring)

/-- Complete Euler cubic source has a strictly larger principal coefficient than the bare atom. -/
theorem sourceHorizontalEulerGammaCubicAtom_sub_log_cube_div_pos
    (p : Nat.Primes) :
    0 < sourceHorizontalEulerGammaCubicAtom p -
      Real.log (p : ℝ) ^ 3 / (p : ℝ) := by
  let P : ℝ := p
  have hP0 : 0 < P := by
    dsimp [P]
    exact_mod_cast p.2.pos
  have hP1 : (1 : ℝ) < P := by
    dsimp [P]
    exact_mod_cast p.2.one_lt
  have hq : 0 < P⁻¹ := inv_pos.mpr hP0
  have hq1 : P⁻¹ < 1 := (inv_lt_one₀ hP0).2 hP1
  have hbase0 : 0 ≤ 1 - P⁻¹ := by linarith
  have hbase1 : 1 - P⁻¹ < 1 := by linarith
  have hden : 0 < (1 - P⁻¹) ^ 3 := pow_pos (by linarith) 3
  have hpow : (1 - P⁻¹) ^ 3 < 1 :=
    pow_lt_one₀ hbase0 hbase1 (by norm_num)
  have hratio : 1 < (1 + P⁻¹) / (1 - P⁻¹) ^ 3 := by
    apply (lt_div_iff₀ hden).2
    nlinarith
  have hlog : 0 < Real.log P ^ 3 :=
    pow_pos (Real.log_pos hP1) _
  have hscale : Real.log P ^ 3 * P⁻¹ <
      Real.log P ^ 3 * (P⁻¹ * ((1 + P⁻¹) / (1 - P⁻¹) ^ 3)) := by
    calc
      Real.log P ^ 3 * P⁻¹ = (Real.log P ^ 3 * P⁻¹) * 1 := by ring
      _ < (Real.log P ^ 3 * P⁻¹) *
          ((1 + P⁻¹) / (1 - P⁻¹) ^ 3) :=
        mul_lt_mul_of_pos_left hratio (mul_pos hlog hq)
      _ = Real.log P ^ 3 *
          (P⁻¹ * ((1 + P⁻¹) / (1 - P⁻¹) ^ 3)) := by ring
  have hdiv : Real.log P ^ 3 / P = Real.log P ^ 3 * P⁻¹ := by
    field_simp [hP0.ne']
  rw [sourceHorizontalEulerGammaCubicAtom_eq p]
  change 0 < Real.log P ^ 3 *
      (P⁻¹ * (1 + P⁻¹) / (1 - P⁻¹) ^ 3) - Real.log P ^ 3 / P
  rw [hdiv]
  exact sub_pos.mpr (by convert hscale using 1; ring)

/-- Euler-versus-harmonic correction is bounded by its source-natural Wold defect. -/
theorem sourceHorizontalEulerGammaCubicAtom_sub_log_cube_div_le_woldDefect
    (p : Nat.Primes) :
    sourceHorizontalEulerGammaCubicAtom p -
        Real.log (p : ℝ) ^ 3 / (p : ℝ) ≤
      sourceHorizontalEulerGammaWoldCubicDefect p := by
  let P : ℝ := p
  have hP0 : 0 < P := by
    dsimp [P]
    exact_mod_cast p.2.pos
  have hP1 : (1 : ℝ) < P := by
    dsimp [P]
    exact_mod_cast p.2.one_lt
  have hq0 : 0 ≤ P⁻¹ := (inv_pos.mpr hP0).le
  have hq1 : P⁻¹ < 1 := (inv_lt_one₀ hP0).2 hP1
  have hbase0 : 0 ≤ 1 - P⁻¹ := by linarith
  have hbase1 : 1 - P⁻¹ ≤ 1 := by linarith
  have hpow : (1 - P⁻¹) ^ 3 ≤ 1 := pow_le_one₀ hbase0 hbase1
  have hlog : 0 ≤ Real.log P ^ 3 :=
    pow_nonneg (Real.log_nonneg hP1.le) _
  have hWold : Real.log P ^ 3 * P⁻¹ * (1 - P⁻¹) ^ 3 ≤
      Real.log P ^ 3 / P := by
    have hprod : Real.log P ^ 3 * P⁻¹ * (1 - P⁻¹) ^ 3 ≤
        Real.log P ^ 3 * P⁻¹ := by
      calc
        Real.log P ^ 3 * P⁻¹ * (1 - P⁻¹) ^ 3 ≤
            (Real.log P ^ 3 * P⁻¹) * 1 :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hlog hq0)
        _ = Real.log P ^ 3 * P⁻¹ := by ring
    have hdiv : Real.log P ^ 3 / P = Real.log P ^ 3 * P⁻¹ := by
      field_simp [hP0.ne']
    rwa [hdiv]
  rw [sourceHorizontalEulerGammaWoldCubicDefect, woldCubicAtom_eq]
  change sourceHorizontalEulerGammaCubicAtom p - Real.log P ^ 3 / P ≤
    sourceHorizontalEulerGammaCubicAtom p -
      (Real.log P ^ 3 * P⁻¹ * (1 - P⁻¹) ^ 3)
  linarith

/-- Source renormalization leaves a positive, coefficientwise finite remainder. -/
theorem gammaSixCubicEulerPrincipalDefect_nonneg
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ gammaSixCubicEulerPrincipalDefect m q p := by
  rw [gammaSixCubicEulerPrincipalDefect_eq]
  have hres : 0 ≤ gammaSixFilteredBoundaryAsymptoticResidue m
      (primeDepthBVWoldXiCenteredRate q.1) := by
    unfold gammaSixFilteredBoundaryAsymptoticResidue
    split <;> positivity
  have heuler := sourceHorizontalEulerGammaCubicAtom_sub_log_cube_div_nonneg p
  have hgamma := gammaSixFilteredBoundaryHarmonicDefect_nonneg hm q p
  have hlog : 0 ≤ Real.log (p : ℝ) ^ 3 := by
    exact pow_nonneg (Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)) _
  positivity

/-- Literal finite Gamma-six loss remains summable after the third Euler jet. -/
theorem summable_log_cube_mul_gammaSixFilteredBoundaryHarmonicDefect
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ 3 * gammaSixFilteredBoundaryHarmonicDefect m q p) := by
  by_cases ht : primeDepthBVWoldXiCenteredRate q.1 = 0
  · have hzero : gammaSixFilteredBoundaryHarmonicDefect m q = 0 := by
      funext p
      rw [gammaSixFilteredBoundaryHarmonicDefect,
        gammaSixFilteredBoundaryAsymptoticResidue, if_pos ht,
        gammaSixFilteredBoundarySecondJet_eq_factorized hm q p, ht]
      simp
    simp [hzero]
  let u : ℝ := |primeDepthBVWoldXiCenteredRate q.1|
  let C : ℝ := Real.log 2 / (m : ℝ) ^ 2
  let A : ℝ := (((2 * m : ℕ) : ℝ)) + 5
  have hu : 0 < u := by
    dsimp [u]
    exact abs_pos.mpr ht
  have hsqNat : Summable (fun n : ℕ =>
      Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ (2 : ℝ)) :=
    HTGeometry.summable_log_pow_div_nat_rpow 3 (by norm_num)
  have hsqBase : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ 3 / (p : ℝ) ^ (2 : ℝ)) :=
    hsqNat.comp_injective Subtype.val_injective
  have hsq : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ 3 * (p : ℝ)⁻¹ ^ 2) := by
    refine hsqBase.congr fun p => ?_
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    rw [Real.rpow_two]
    field_simp [hp0]
  have htailNat : Summable (fun n : ℕ =>
      Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ (1 + u)) :=
    HTGeometry.summable_log_pow_div_nat_rpow 3 (by linarith)
  have htailBase : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ 3 / (p : ℝ) ^ (1 + u)) :=
    htailNat.comp_injective Subtype.val_injective
  have htail : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ 3 *
        ((p : ℝ)⁻¹ * (p : ℝ) ^ (-u))) := by
    refine htailBase.congr fun p => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    rw [div_eq_mul_inv, ← Real.rpow_neg hp0.le,
      ← Real.rpow_neg_one, ← Real.rpow_add hp0]
    congr 1
    ring_nf
  have hmajor : Summable (fun p : Nat.Primes =>
      C * A * (Real.log (p : ℝ) ^ 3 * (p : ℝ)⁻¹ ^ 2) +
      C * 2 * (Real.log (p : ℝ) ^ 3 *
        ((p : ℝ)⁻¹ * (p : ℝ) ^ (-u)))) :=
    ((hsq.mul_left (C * A)).congr fun p => by ring).add
      ((htail.mul_left (C * 2)).congr fun p => by ring)
  apply Summable.of_nonneg_of_le
    (fun p => mul_nonneg
      (pow_nonneg (Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)) _)
      (gammaSixFilteredBoundaryHarmonicDefect_nonneg hm q p))
    (fun p => ?_) hmajor
  have hlog : 0 ≤ Real.log (p : ℝ) ^ 3 :=
    pow_nonneg (Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)) _
  calc
    Real.log (p : ℝ) ^ 3 * gammaSixFilteredBoundaryHarmonicDefect m q p ≤
        Real.log (p : ℝ) ^ 3 *
          (C * A * (p : ℝ)⁻¹ ^ 2 + C * 2 *
            ((p : ℝ)⁻¹ * (p : ℝ) ^ (-u))) := by
      apply mul_le_mul_of_nonneg_left _ hlog
      simpa only [u, C, A] using
        gammaSixFilteredBoundaryHarmonicDefect_le hm q ht p
    _ = C * A * (Real.log (p : ℝ) ^ 3 * (p : ℝ)⁻¹ ^ 2) +
        C * 2 * (Real.log (p : ℝ) ^ 3 *
          ((p : ℝ)⁻¹ * (p : ℝ) ^ (-u))) := by ring

/-- **Cubic principal-source law.** At every retained Xi divisor copy, unfiltered Gamma-six
boundary current after its literal third Euler jet equals complete pre-Xi Euler cubic source atom
modulo a positive absolutely summable correction. -/
theorem summable_gammaSixCubicEulerPrincipalDefect
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Summable (gammaSixCubicEulerPrincipalDefect m q) := by
  let R : ℝ := gammaSixFilteredBoundaryAsymptoticResidue m
    (primeDepthBVWoldXiCenteredRate q.1)
  have hR : 0 ≤ R := by
    dsimp [R, gammaSixFilteredBoundaryAsymptoticResidue]
    split <;> positivity
  have hEuler : Summable (fun p : Nat.Primes => R *
      (sourceHorizontalEulerGammaCubicAtom p -
        Real.log (p : ℝ) ^ 3 / (p : ℝ))) := by
    apply Summable.of_nonneg_of_le
      (fun p => mul_nonneg hR
        (sourceHorizontalEulerGammaCubicAtom_sub_log_cube_div_nonneg p))
      (fun p => ?_)
      (summable_sourceHorizontalEulerGammaWoldCubicDefect.mul_left R)
    exact mul_le_mul_of_nonneg_left
      (sourceHorizontalEulerGammaCubicAtom_sub_log_cube_div_le_woldDefect p) hR
  have hGamma := summable_log_cube_mul_gammaSixFilteredBoundaryHarmonicDefect hm q
  have hsum := hEuler.add hGamma
  refine hsum.congr fun p => ?_
  simpa only [R] using (gammaSixCubicEulerPrincipalDefect_eq m q p).symm

/-- Cubic principal splice retains both functional-equation orientations on one prime carrier. -/
theorem gammaSixCubicEulerPrincipalDefect_copyReflect
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixCubicEulerPrincipalDefect m (xiZeroCopyReflectEquiv q) p =
      gammaSixCubicEulerPrincipalDefect m q p := by
  rw [gammaSixCubicEulerPrincipalDefect,
    gammaSixCubicEulerPrincipalDefect,
    HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_copyReflect,
    HedenmalmThetaSource.gammaSixFilteredBoundarySecondJet_copyReflect hm q p]
  simp [gammaSixFilteredBoundaryAsymptoticResidue]

/-- Off neutral wall cubic source correction is strictly positive at every retained prime label. -/
theorem gammaSixCubicEulerPrincipalDefect_pos_of_centeredRate_ne_zero
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy)
    (ht : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) (p : Nat.Primes) :
    0 < gammaSixCubicEulerPrincipalDefect m q p := by
  rw [gammaSixCubicEulerPrincipalDefect_eq]
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hres : 0 < gammaSixFilteredBoundaryAsymptoticResidue m
      (primeDepthBVWoldXiCenteredRate q.1) := by
    rw [gammaSixFilteredBoundaryAsymptoticResidue, if_neg ht]
    exact div_pos (Real.log_pos (by norm_num)) (sq_pos_of_pos hmpos)
  have heuler := sourceHorizontalEulerGammaCubicAtom_sub_log_cube_div_pos p
  have hgamma := gammaSixFilteredBoundaryHarmonicDefect_nonneg hm q p
  have hlog : 0 ≤ Real.log (p : ℝ) ^ 3 := by
    exact pow_nonneg (Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)) _
  exact add_pos_of_pos_of_nonneg (mul_pos hres heuler) (mul_nonneg hlog hgamma)

/-- Cubic principal correction vanishes at a prime exactly on neutral horizontal wall. -/
theorem gammaSixCubicEulerPrincipalDefect_eq_zero_iff_centeredRate_eq_zero
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixCubicEulerPrincipalDefect m q p = 0 ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  constructor
  · intro hzero
    by_contra ht
    have hpos := gammaSixCubicEulerPrincipalDefect_pos_of_centeredRate_ne_zero hm q ht p
    linarith
  · intro ht
    rw [gammaSixCubicEulerPrincipalDefect,
      gammaSixFilteredBoundaryAsymptoticResidue, if_pos ht,
      gammaSixFilteredBoundarySecondJet_eq_factorized hm q p, ht]
    simp

end

end RHTower

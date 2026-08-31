import GaloisForLFunctions.RHTower.XiWardCellRandomizedAnnulusCoercivity
import GaloisForLFunctions.RHTower.XiCriticalLineThinStripSourceProjector

/-!
# Source rectangles for the triangular Ward receiver

The deterministic half-cell tent in
`XiWardCellRandomizedAnnulusCoercivity` removes every divisor-dependent sign
choice.  This file supplies its linear source primitive.  A raw Ward Cauchy
column is a rational weight whose only pole lies in the upper centered half
plane.  It is therefore holomorphic on every lower-half rectangle containing
strict-right Xi points.  The local Guinand--Weil rectangle theorem then turns
its continued pole--Gamma--von-Mangoldt contour exactly into the finite Ward
response sum in that height window.

No approximation theorem and no zero-fitted coefficient is used.  Remaining
quadratic task is to average products of these fixed rectangle responses
against the already formalized interval autocorrelation and prove the sharp
source budget.
-/

open Complex Set intervalIntegral
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Rational Cauchy weight whose value at a centered spectral point is one
raw anti-causal Ward mode. -/
def xiWardCauchySourceWeight (w z : ℂ) : ℂ :=
  2 * (w + I * z)⁻¹

/-- The sole pole of the Ward Cauchy source weight. -/
def xiWardCauchySourcePoleFreeDomain (w : ℂ) : Set ℂ :=
  {z | z ≠ I * w}

theorem isOpen_xiWardCauchySourcePoleFreeDomain (w : ℂ) :
    IsOpen (xiWardCauchySourcePoleFreeDomain w) := by
  rw [xiWardCauchySourcePoleFreeDomain]
  exact isOpen_compl_singleton

/-- The rational Ward weight is holomorphic away from its explicit upper
half-plane pole. -/
theorem analyticOnNhd_xiWardCauchySourceWeight (w : ℂ) :
    AnalyticOnNhd ℂ (xiWardCauchySourceWeight w)
      (xiWardCauchySourcePoleFreeDomain w) := by
  intro z hz
  have hden : w + I * z ≠ 0 := by
    rw [show w + I * z = I * (z - I * w) by
      rw [mul_sub, ← mul_assoc, I_mul_I]
      ring]
    exact mul_ne_zero I_ne_zero (sub_ne_zero.mpr hz)
  unfold xiWardCauchySourceWeight
  exact analyticAt_const.mul
    ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).inv hden)

/-- Every rectangle contained in the closed lower centered half-plane avoids
the Ward weight pole whenever the observation node has positive real part. -/
theorem lowerHalf_rectangle_subset_xiWardCauchySourcePoleFreeDomain
    {w z₁ z₂ : ℂ} (hw : 0 < w.re) (him : z₁.im ≤ z₂.im)
    (hupper : z₂.im ≤ 0) :
    (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆
      xiWardCauchySourcePoleFreeDomain w := by
  intro z hz
  have hzIm := (Complex.mem_reProdIm.mp hz).2
  rw [uIcc_of_le him] at hzIm
  rw [xiWardCauchySourcePoleFreeDomain, Set.mem_setOf_eq]
  intro hzw
  have himEq := congrArg Complex.im hzw
  simp only [mul_im, I_re, zero_mul, I_im, one_mul, zero_add] at himEq
  have hzupper : z.im ≤ z₂.im := hzIm.2
  linarith

/-- Normalized local pole--Gamma--von-Mangoldt contour carrying one Ward
Cauchy column. -/
def xiWardCauchySourceRectangleResponse
    (w z₁ z₂ : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    rectIntegral
      (fun z => xiWardCauchySourceWeight w z *
        continuedPrimeArchSourceRelativeTrace z)
      z₁ z₂

/-- **Local source-to-Ward weld.**  On every admissible lower-half rectangle,
the normalized continued prime--archimedean contour is exactly the sum of
the Ward Cauchy weight over all enclosed Xi multiplicity copies. -/
theorem xiWardCauchySourceRectangleResponse_eq_xiZeroCopy_sum
    {w z₁ z₂ : ℂ}
    (hrect : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆
      xiWardCauchySourcePoleFreeDomain w)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    xiWardCauchySourceRectangleResponse w z₁ z₂ =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiWardCauchySourceWeight w (xiSpectralPoint q) := by
  have hres :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum_local
      (isOpen_xiWardCauchySourcePoleFreeDomain w)
      (analyticOnNhd_xiWardCauchySourceWeight w)
      hrect hre him hbot htop hright hleft
  have hconvert :
      (∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
          ((analyticOrderAt XiC z).toNat : ℂ) *
            xiWardCauchySourceWeight w z) =
        ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          xiWardCauchySourceWeight w (xiSpectralPoint q) := by
    calc
      (∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
          ((analyticOrderAt XiC z).toNat : ℂ) *
            xiWardCauchySourceWeight w z) =
          ∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
            (xiSpectralMultiplicity z : ℂ) *
              xiWardCauchySourceWeight w z := by
        apply Finset.sum_congr rfl
        intro z hz
        have hzero : XiC z = 0 := (mem_xiCClosedRectangleZeros.mp hz).2
        rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat hzero]
      _ = ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          xiWardCauchySourceWeight w (xiSpectralPoint q) :=
        (sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
          (xiWardCauchySourceWeight w) z₁ z₂).symm
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [xiWardCauchySourceRectangleResponse, hres,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul, hconvert]

/-- Lower-half specialization: pole avoidance is automatic from geometry. -/
theorem xiWardCauchySourceRectangleResponse_eq_xiZeroCopy_sum_lowerHalf
    {w z₁ z₂ : ℂ} (hw : 0 < w.re)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im) (hupper : z₂.im ≤ 0)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    xiWardCauchySourceRectangleResponse w z₁ z₂ =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiWardCauchySourceWeight w (xiSpectralPoint q) := by
  exact xiWardCauchySourceRectangleResponse_eq_xiZeroCopy_sum
    (lowerHalf_rectangle_subset_xiWardCauchySourcePoleFreeDomain
      hw him.le hupper)
    hre him hbot htop hright hleft

/-- Pairing one upper strict-right copy with its Schwarz mate turns two
source Cauchy weights into the raw Ward Schwarz-pair response exactly. -/
theorem xiWardCauchySourceWeight_add_conj_eq_schwarzPairResponse
    (q : XiRightUpperZeroCopy) (w : ℂ) :
    xiWardCauchySourceWeight w (xiSpectralPoint q.1.1) +
        xiWardCauchySourceWeight w
          (xiSpectralPoint (xiRightZeroCopyConjEquiv q.1).1) =
      xiAntiCausalWardSchwarzPairResponse q w := by
  unfold xiWardCauchySourceWeight xiAntiCausalWardSchwarzPairResponse
    xiRightCenteredZero
  ring

/-- Forgetful embedding of upper strict-right pair representatives into the
global Xi multiplicity-copy carrier. -/
def xiRightUpperZeroCopyEmbedding : XiRightUpperZeroCopy ↪ XiZeroCopy where
  toFun q := q.1.1
  inj' := by
    intro q r h
    apply Subtype.ext
    apply Subtype.ext
    exact h

/-- The Schwarz mate of each upper strict-right representative, embedded in
the global Xi multiplicity-copy carrier. -/
def xiRightUpperConjZeroCopyEmbedding : XiRightUpperZeroCopy ↪ XiZeroCopy where
  toFun q := (xiRightZeroCopyConjEquiv q.1).1
  inj' := by
    intro q r h
    apply Subtype.ext
    apply xiRightZeroCopyConjEquiv.injective
    apply Subtype.ext
    exact h

/-- Sum of two source rectangles intended for one positive-height interval
and its Schwarz-reflected negative-height interval. -/
def xiWardPairedSourceRectangleResponse
    (w z₁ z₂ z₁' z₂' : ℂ) : ℂ :=
  xiWardCauchySourceRectangleResponse w z₁ z₂ +
    xiWardCauchySourceRectangleResponse w z₁' z₂'

/-- Once the two fixed rectangles contain exactly a finite upper packet and
its Schwarz mates, their source contours equal the finite raw Ward response.
All analytic source work is isolated in the two contour equalities; remaining
hypotheses are literal finite-set bookkeeping. -/
theorem xiWardPairedSourceRectangleResponse_eq_finset_response
    (S : Finset XiRightUpperZeroCopy) (w z₁ z₂ z₁' z₂' : ℂ)
    (hsource : xiWardCauchySourceRectangleResponse w z₁ z₂ =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiWardCauchySourceWeight w (xiSpectralPoint q))
    (hsource' : xiWardCauchySourceRectangleResponse w z₁' z₂' =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁' z₂',
        xiWardCauchySourceWeight w (xiSpectralPoint q))
    (hpacket : xiZeroCopyClosedRectangle z₁ z₂ =
      S.map xiRightUpperZeroCopyEmbedding)
    (hpacket' : xiZeroCopyClosedRectangle z₁' z₂' =
      S.map xiRightUpperConjZeroCopyEmbedding) :
    xiWardPairedSourceRectangleResponse w z₁ z₂ z₁' z₂' =
      ∑ q ∈ S, xiAntiCausalWardSchwarzPairResponse q w := by
  rw [xiWardPairedSourceRectangleResponse, hsource, hsource', hpacket, hpacket']
  simp only [Finset.sum_map]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  exact xiWardCauchySourceWeight_add_conj_eq_schwarzPairResponse q w

/-! ## Exact quadratic source bridge -/

/-- Real-line energy of the finite Ward response carried by one upper packet
and its Schwarz mates. -/
def xiWardFinitePairRealEnergyAtLine
    (sigma : ℝ) (S : Finset XiRightUpperZeroCopy) : ℝ :=
  ∫ t : ℝ,
    (∑ q ∈ S,
      (xiAntiCausalWardSchwarzPairResponse q
        ((sigma : ℂ) + I * (t : ℂ))).re) ^ 2

/-- **Finite Gram expansion.**  The real-line energy of a finite Ward packet
is exactly its ordered-pair cross-energy sum. -/
theorem xiWardFinitePairRealEnergyAtLine_eq_pair_sum
    {sigma : ℝ} (hsigma : 0 < sigma)
    (S : Finset XiRightUpperZeroCopy) :
    xiWardFinitePairRealEnergyAtLine sigma S =
      ∑ q ∈ S, ∑ r ∈ S, xiWardPairRealCrossEnergyAtLine sigma q r := by
  have hterm : ∀ q ∈ S, ∀ r ∈ S,
      MeasureTheory.Integrable (fun t : ℝ =>
        (xiAntiCausalWardSchwarzPairResponse q
          ((sigma : ℂ) + I * (t : ℂ))).re *
        (xiAntiCausalWardSchwarzPairResponse r
          ((sigma : ℂ) + I * (t : ℂ))).re) := by
    intro q hq r hr
    exact integrable_re_xiAntiCausalWardSchwarzPairResponse_mul hsigma q r
  have hpoint : ∀ t : ℝ,
      (∑ q ∈ S,
        (xiAntiCausalWardSchwarzPairResponse q
          ((sigma : ℂ) + I * (t : ℂ))).re) ^ 2 =
        ∑ q ∈ S, ∑ r ∈ S,
          (xiAntiCausalWardSchwarzPairResponse q
            ((sigma : ℂ) + I * (t : ℂ))).re *
          (xiAntiCausalWardSchwarzPairResponse r
            ((sigma : ℂ) + I * (t : ℂ))).re := by
    intro t
    rw [pow_two, Finset.sum_mul_sum]
  unfold xiWardFinitePairRealEnergyAtLine
  rw [show (fun t : ℝ =>
      (∑ q ∈ S,
        (xiAntiCausalWardSchwarzPairResponse q
          ((sigma : ℂ) + I * (t : ℂ))).re) ^ 2) =
      (fun t : ℝ => ∑ q ∈ S, ∑ r ∈ S,
        (xiAntiCausalWardSchwarzPairResponse q
          ((sigma : ℂ) + I * (t : ℂ))).re *
        (xiAntiCausalWardSchwarzPairResponse r
          ((sigma : ℂ) + I * (t : ℂ))).re) from
    funext hpoint]
  rw [show (fun t : ℝ => ∑ q ∈ S, ∑ r ∈ S,
      (xiAntiCausalWardSchwarzPairResponse q
        ((sigma : ℂ) + I * (t : ℂ))).re *
      (xiAntiCausalWardSchwarzPairResponse r
        ((sigma : ℂ) + I * (t : ℂ))).re) =
      (fun t : ℝ => ∑ p ∈ S ×ˢ S,
        (xiAntiCausalWardSchwarzPairResponse p.1
          ((sigma : ℂ) + I * (t : ℂ))).re *
        (xiAntiCausalWardSchwarzPairResponse p.2
          ((sigma : ℂ) + I * (t : ℂ))).re) from
    funext fun t => (Finset.sum_product S S (fun p =>
      (xiAntiCausalWardSchwarzPairResponse p.1
        ((sigma : ℂ) + I * (t : ℂ))).re *
      (xiAntiCausalWardSchwarzPairResponse p.2
        ((sigma : ℂ) + I * (t : ℂ))).re)).symm]
  rw [show (∑ q ∈ S, ∑ r ∈ S,
      xiWardPairRealCrossEnergyAtLine sigma q r) =
      ∑ p ∈ S ×ˢ S,
        xiWardPairRealCrossEnergyAtLine sigma p.1 p.2 from
    (Finset.sum_product S S (fun p =>
      xiWardPairRealCrossEnergyAtLine sigma p.1 p.2)).symm]
  rw [MeasureTheory.integral_finsetSum _ fun p hp =>
    hterm p.1 (Finset.mem_product.mp hp).1
      p.2 (Finset.mem_product.mp hp).2]
  rfl

/-- Real-line energy of one paired source-rectangle response.  Its definition
contains only fixed Cauchy weights and the continued prime--archimedean
relative trace. -/
def xiWardPairedSourceRectangleRealEnergyAtLine
    (sigma : ℝ) (z₁ z₂ z₁' z₂' : ℂ) : ℝ :=
  ∫ t : ℝ,
    (xiWardPairedSourceRectangleResponse
      ((sigma : ℂ) + I * (t : ℂ)) z₁ z₂ z₁' z₂').re ^ 2

/-- A pointwise contour-to-packet identity passes exactly to real-line
quadratic energy. -/
theorem xiWardPairedSourceRectangleRealEnergyAtLine_eq_finite
    (sigma : ℝ) (S : Finset XiRightUpperZeroCopy)
    (z₁ z₂ z₁' z₂' : ℂ)
    (hresponse : ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          ((sigma : ℂ) + I * (t : ℂ)) z₁ z₂ z₁' z₂' =
        ∑ q ∈ S, xiAntiCausalWardSchwarzPairResponse q
          ((sigma : ℂ) + I * (t : ℂ))) :
    xiWardPairedSourceRectangleRealEnergyAtLine sigma z₁ z₂ z₁' z₂' =
      xiWardFinitePairRealEnergyAtLine sigma S := by
  unfold xiWardPairedSourceRectangleRealEnergyAtLine
    xiWardFinitePairRealEnergyAtLine
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [hresponse t, Complex.re_sum]

/-- Source-only annulus energy obtained by subtracting the wide Ward line
from the narrow Ward line. -/
def xiWardPairedSourceRectangleAnnulusEnergy
    (z₁ z₂ z₁' z₂' : ℂ) : ℝ :=
  xiWardPairedSourceRectangleRealEnergyAtLine
      (51 / 100) z₁ z₂ z₁' z₂' -
    xiWardPairedSourceRectangleRealEnergyAtLine
      (1051 / 100) z₁ z₂ z₁' z₂'

/-- **Exact quadratic source weld.**  If both fixed source contours render the
same finite packet on the two Ward lines, their annulus energy is exactly the
ordered-pair Ward annulus.  No Xi divisor occurs in the quantity on the left. -/
theorem xiWardPairedSourceRectangleAnnulusEnergy_eq_pair_sum
    (S : Finset XiRightUpperZeroCopy) (z₁ z₂ z₁' z₂' : ℂ)
    (hnarrow : ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ)) z₁ z₂ z₁' z₂' =
        ∑ q ∈ S, xiAntiCausalWardSchwarzPairResponse q
          (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ)))
    (hwide : ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ)) z₁ z₂ z₁' z₂' =
        ∑ q ∈ S, xiAntiCausalWardSchwarzPairResponse q
          (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ))) :
    xiWardPairedSourceRectangleAnnulusEnergy z₁ z₂ z₁' z₂' =
      ∑ q ∈ S, ∑ r ∈ S,
        (xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
          xiWardPairRealCrossEnergyAtLine (1051 / 100) q r) := by
  rw [xiWardPairedSourceRectangleAnnulusEnergy,
    xiWardPairedSourceRectangleRealEnergyAtLine_eq_finite
      (51 / 100) S z₁ z₂ z₁' z₂' hnarrow,
    xiWardPairedSourceRectangleRealEnergyAtLine_eq_finite
      (1051 / 100) S z₁ z₂ z₁' z₂' hwide,
    xiWardFinitePairRealEnergyAtLine_eq_pair_sum (by norm_num) S,
    xiWardFinitePairRealEnergyAtLine_eq_pair_sum (by norm_num) S]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_sub_distrib]

/-! ## Sliding-window realization of the triangular statistic -/

/-- Indicator that ordinate `beta` belongs to the half-unit window indexed by
the translation parameter `u`.  Its support as a function of `u` is the fixed
interval `[-beta, 1/2-beta]`. -/
def wardHalfCellWindow (beta u : ℝ) : ℝ :=
  (Set.Icc (-beta) (1 / 2 - beta)).indicator (fun _ => (1 : ℝ)) u

/-- Products of two translated half-cell windows are integrable. -/
theorem integrable_wardHalfCellWindow_mul (beta gamma : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ =>
      wardHalfCellWindow beta u * wardHalfCellWindow gamma u) := by
  have hfun : (fun u : ℝ =>
      wardHalfCellWindow beta u * wardHalfCellWindow gamma u) =
      (Set.Icc (max (-beta) (-gamma))
        (min (1 / 2 - beta) (1 / 2 - gamma))).indicator
          (fun _ => (1 : ℝ)) := by
    funext u
    have hmem : u ∈ Set.Icc (max (-beta) (-gamma))
        (min (1 / 2 - beta) (1 / 2 - gamma)) ↔
        u ∈ Set.Icc (-beta) (1 / 2 - beta) ∧
          u ∈ Set.Icc (-gamma) (1 / 2 - gamma) := by
      simp only [Set.mem_Icc, max_le_iff, le_min_iff]
      aesop
    unfold wardHalfCellWindow
    by_cases h : u ∈ Set.Icc (-beta) (1 / 2 - beta) ∧
        u ∈ Set.Icc (-gamma) (1 / 2 - gamma)
    · rw [Set.indicator_of_mem h.1,
        Set.indicator_of_mem h.2, Set.indicator_of_mem (hmem.mpr h)]
      norm_num
    · rw [Set.indicator_of_notMem (fun hu => h (hmem.mp hu))]
      rcases not_and_or.mp h with hb | hg
      · rw [Set.indicator_of_notMem hb]
        ring
      · rw [Set.indicator_of_notMem hg]
        ring
  rw [hfun]
  have hfin : (MeasureTheory.volume
      (Set.Icc (max (-beta) (-gamma))
        (min (1 / 2 - beta) (1 / 2 - gamma)))) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hfin).integrable_indicator
    measurableSet_Icc

/-- Exact normalized overlap of two translated half-cell windows. -/
theorem two_mul_integral_wardHalfCellWindow_mul
    (beta gamma : ℝ) :
    2 * ∫ u : ℝ, wardHalfCellWindow beta u * wardHalfCellWindow gamma u =
      wardHalfCellTent (beta - gamma) := by
  unfold wardHalfCellWindow
  rw [show (fun u : ℝ =>
      (Set.Icc (-beta) (1 / 2 - beta)).indicator
          (fun _ => (1 : ℝ)) u *
        (Set.Icc (-gamma) (1 / 2 - gamma)).indicator
          (fun _ => (1 : ℝ)) u) =
      (fun u : ℝ =>
        (Set.Icc (-beta) (1 / 2 - beta)).indicator
            (fun _ => (1 : ℝ)) (u + 0) *
          (Set.Icc (-gamma) (1 / 2 - gamma)).indicator
            (fun _ => (1 : ℝ)) u) by
    funext u
    rw [add_zero]]
  rw [integral_indicator_Icc_shift_mul_Icc
    (-beta) (1 / 2 - beta) (-gamma) (1 / 2 - gamma) 0]
  have hshape := min_sub_max_eq
    (-gamma) (1 / 2 - gamma) (beta - gamma)
  norm_num only [sub_zero] at hshape ⊢
  rw [show min (1 / 2 - gamma) (1 / 2 - beta) -
      max (-gamma) (-beta) = 1 / 2 - |beta - gamma| by
    convert hshape using 1 <;> ring]
  rfl

/-- Unscaled ordered-pair Ward annulus in one translated half-cell. -/
def xiWardSlidingHalfCellAnnulusEnergy
    (S : Finset XiRightUpperZeroCopy) (u : ℝ) : ℝ :=
  ∑ p ∈ S ×ˢ S,
    wardHalfCellWindow (xiRightCenteredZero p.1.1).im u *
      wardHalfCellWindow (xiRightCenteredZero p.2.1).im u *
      (xiWardPairRealCrossEnergyAtLine (51 / 100) p.1 p.2 -
        xiWardPairRealCrossEnergyAtLine (1051 / 100) p.1 p.2)

/-- Literal finite packet selected by one translated half-cell. -/
def xiWardHalfCellPacket
    (S : Finset XiRightUpperZeroCopy) (u : ℝ) :
    Finset XiRightUpperZeroCopy :=
  S.filter fun q =>
    u ∈ Set.Icc (-(xiRightCenteredZero q.1).im)
      (1 / 2 - (xiRightCenteredZero q.1).im)

/-- Filtering the packet and weighting its full ordered-pair sum by the
half-cell indicators are exactly the same operation. -/
theorem xiWardHalfCellPacket_pair_sum_eq_sliding
    (S : Finset XiRightUpperZeroCopy) (u : ℝ) :
    (∑ q ∈ xiWardHalfCellPacket S u,
      ∑ r ∈ xiWardHalfCellPacket S u,
        (xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
          xiWardPairRealCrossEnergyAtLine (1051 / 100) q r)) =
      xiWardSlidingHalfCellAnnulusEnergy S u := by
  classical
  unfold xiWardHalfCellPacket xiWardSlidingHalfCellAnnulusEnergy
  rw [Finset.sum_product]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqwin : u ∈ Set.Icc (-(xiRightCenteredZero q.1).im)
      (1 / 2 - (xiRightCenteredZero q.1).im)
  · have hwq : wardHalfCellWindow (xiRightCenteredZero q.1).im u = 1 := by
      unfold wardHalfCellWindow
      exact Set.indicator_of_mem hqwin (fun _ => (1 : ℝ))
    rw [if_pos hqwin]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hrwin : u ∈ Set.Icc (-(xiRightCenteredZero r.1).im)
        (1 / 2 - (xiRightCenteredZero r.1).im)
    · have hwr : wardHalfCellWindow (xiRightCenteredZero r.1).im u = 1 := by
        unfold wardHalfCellWindow
        exact Set.indicator_of_mem hrwin (fun _ => (1 : ℝ))
      rw [if_pos hrwin, hwq, hwr]
      ring
    · have hwr : wardHalfCellWindow (xiRightCenteredZero r.1).im u = 0 := by
        unfold wardHalfCellWindow
        exact Set.indicator_of_notMem hrwin (fun _ => (1 : ℝ))
      rw [if_neg hrwin, hwq, hwr]
      ring
  · have hwq : wardHalfCellWindow (xiRightCenteredZero q.1).im u = 0 := by
      unfold wardHalfCellWindow
      exact Set.indicator_of_notMem hqwin (fun _ => (1 : ℝ))
    rw [if_neg hqwin]
    simp only [hwq, zero_mul, Finset.sum_const_zero]

/-- One localized pair is exactly twice the translation average of its two
fixed half-window indicators. -/
theorem two_mul_integral_windowed_xiWardPairAnnulus_eq_localizedPair
    (q r : XiRightUpperZeroCopy) :
    2 * ∫ u : ℝ,
      wardHalfCellWindow (xiRightCenteredZero q.1).im u *
        wardHalfCellWindow (xiRightCenteredZero r.1).im u *
        (xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
          xiWardPairRealCrossEnergyAtLine (1051 / 100) q r) =
      xiWardTriangularLocalizedAnnulusPair q r := by
  let A := xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
    xiWardPairRealCrossEnergyAtLine (1051 / 100) q r
  have hInt := integrable_wardHalfCellWindow_mul
    (xiRightCenteredZero q.1).im (xiRightCenteredZero r.1).im
  have hcorr := two_mul_integral_wardHalfCellWindow_mul
    (xiRightCenteredZero q.1).im (xiRightCenteredZero r.1).im
  rw [show (fun u : ℝ =>
      wardHalfCellWindow (xiRightCenteredZero q.1).im u *
        wardHalfCellWindow (xiRightCenteredZero r.1).im u * A) =
      (fun u : ℝ => A *
        (wardHalfCellWindow (xiRightCenteredZero q.1).im u *
          wardHalfCellWindow (xiRightCenteredZero r.1).im u)) by
    funext u
    ring]
  rw [MeasureTheory.integral_const_mul]
  unfold xiWardTriangularLocalizedAnnulusPair
  dsimp only [A]
  calc
    2 * ((xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
        xiWardPairRealCrossEnergyAtLine (1051 / 100) q r) *
      ∫ u : ℝ,
        wardHalfCellWindow (xiRightCenteredZero q.1).im u *
          wardHalfCellWindow (xiRightCenteredZero r.1).im u) =
        (2 * ∫ u : ℝ,
          wardHalfCellWindow (xiRightCenteredZero q.1).im u *
            wardHalfCellWindow (xiRightCenteredZero r.1).im u) *
          (xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
            xiWardPairRealCrossEnergyAtLine (1051 / 100) q r) := by ring
    _ = _ := by rw [hcorr]

/-- **Exact triangular averaging identity.**  Averaging the fixed half-unit
window over all translations gives exactly the deterministic triangular Ward
annulus, including every off-diagonal term with its autocorrelation weight. -/
theorem two_mul_integral_xiWardSlidingHalfCellAnnulusEnergy_eq_triangular
    (S : Finset XiRightUpperZeroCopy) :
    2 * ∫ u : ℝ, xiWardSlidingHalfCellAnnulusEnergy S u =
      xiWardTriangularLocalizedAnnulusEnergy S := by
  have hterm : ∀ p ∈ S ×ˢ S,
      MeasureTheory.Integrable (fun u : ℝ =>
        wardHalfCellWindow (xiRightCenteredZero p.1.1).im u *
          wardHalfCellWindow (xiRightCenteredZero p.2.1).im u *
          (xiWardPairRealCrossEnergyAtLine (51 / 100) p.1 p.2 -
            xiWardPairRealCrossEnergyAtLine (1051 / 100) p.1 p.2)) := by
    intro p hp
    exact (integrable_wardHalfCellWindow_mul
      (xiRightCenteredZero p.1.1).im
      (xiRightCenteredZero p.2.1).im).mul_const _
  unfold xiWardSlidingHalfCellAnnulusEnergy
  rw [MeasureTheory.integral_finsetSum _ hterm, Finset.mul_sum]
  unfold xiWardTriangularLocalizedAnnulusEnergy
  rw [show (∑ q ∈ S, ∑ r ∈ S,
      xiWardTriangularLocalizedAnnulusPair q r) =
      ∑ p ∈ S ×ˢ S,
        xiWardTriangularLocalizedAnnulusPair p.1 p.2 from
    (Finset.sum_product S S (fun p =>
      xiWardTriangularLocalizedAnnulusPair p.1 p.2)).symm]
  apply Finset.sum_congr rfl
  intro p hp
  exact two_mul_integral_windowed_xiWardPairAnnulus_eq_localizedPair p.1 p.2

/-- Translation average of paired source rectangles.  This quantity is
zero-independent by definition: only the continued prime--archimedean trace
appears inside the rectangle responses. -/
def xiWardSlidingSourceRectangleAnnulusEnergy
    (z₁ z₂ z₁' z₂' : ℝ → ℂ) : ℝ :=
  2 * ∫ u : ℝ,
    xiWardPairedSourceRectangleAnnulusEnergy
      (z₁ u) (z₂ u) (z₁' u) (z₂' u)

/-- **Source-only triangular weld.**  Once each translated pair of source
rectangles renders its literal half-cell packet, its integrated annulus is
the fixed triangular receiver exactly. -/
theorem xiWardSlidingSourceRectangleAnnulusEnergy_eq_triangular
    (S : Finset XiRightUpperZeroCopy)
    (z₁ z₂ z₁' z₂' : ℝ → ℂ)
    (hsource : ∀ u : ℝ,
      xiWardPairedSourceRectangleAnnulusEnergy
          (z₁ u) (z₂ u) (z₁' u) (z₂' u) =
        xiWardSlidingHalfCellAnnulusEnergy S u) :
    xiWardSlidingSourceRectangleAnnulusEnergy z₁ z₂ z₁' z₂' =
      xiWardTriangularLocalizedAnnulusEnergy S := by
  unfold xiWardSlidingSourceRectangleAnnulusEnergy
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall hsource)]
  exact two_mul_integral_xiWardSlidingHalfCellAnnulusEnergy_eq_triangular S

/-- Almost-everywhere form needed by literal moving rectangles: translations
whose horizontal edge passes through a zero form the harmless exceptional set. -/
theorem xiWardSlidingSourceRectangleAnnulusEnergy_eq_triangular_ae
    (S : Finset XiRightUpperZeroCopy)
    (z₁ z₂ z₁' z₂' : ℝ → ℂ)
    (hsource : ∀ᵐ u : ℝ ∂MeasureTheory.volume,
      xiWardPairedSourceRectangleAnnulusEnergy
          (z₁ u) (z₂ u) (z₁' u) (z₂' u) =
        xiWardSlidingHalfCellAnnulusEnergy S u) :
    xiWardSlidingSourceRectangleAnnulusEnergy z₁ z₂ z₁' z₂' =
      xiWardTriangularLocalizedAnnulusEnergy S := by
  unfold xiWardSlidingSourceRectangleAnnulusEnergy
  rw [MeasureTheory.integral_congr_ae hsource]
  exact two_mul_integral_xiWardSlidingHalfCellAnnulusEnergy_eq_triangular S

/-- At one translation, rendering the literal filtered packet on both Ward
lines identifies the paired source annulus with the weighted sliding annulus. -/
theorem xiWardPairedSourceRectangleAnnulusEnergy_eq_sliding
    (S : Finset XiRightUpperZeroCopy) (u : ℝ)
    (z₁ z₂ z₁' z₂' : ℂ)
    (hnarrow : ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ)) z₁ z₂ z₁' z₂' =
        ∑ q ∈ xiWardHalfCellPacket S u,
          xiAntiCausalWardSchwarzPairResponse q
            (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ)))
    (hwide : ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ)) z₁ z₂ z₁' z₂' =
        ∑ q ∈ xiWardHalfCellPacket S u,
          xiAntiCausalWardSchwarzPairResponse q
            (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ))) :
    xiWardPairedSourceRectangleAnnulusEnergy z₁ z₂ z₁' z₂' =
      xiWardSlidingHalfCellAnnulusEnergy S u := by
  exact (xiWardPairedSourceRectangleAnnulusEnergy_eq_pair_sum
    (xiWardHalfCellPacket S u) z₁ z₂ z₁' z₂' hnarrow hwide).trans
      (xiWardHalfCellPacket_pair_sum_eq_sliding S u)

/-- **Completed source-only receiver.**  Almost every translated rectangle
need only satisfy the two linear Guinand--Weil response identities.  Their
quadratic source energy then charges every strict-right copy by `3π`. -/
theorem card_mul_three_pi_le_xiWardSlidingSourceRectangleAnnulusEnergy
    (S : Finset XiRightUpperZeroCopy)
    (z₁ z₂ z₁' z₂' : ℝ → ℂ)
    (hnarrow : ∀ᵐ u : ℝ ∂MeasureTheory.volume, ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ))
            (z₁ u) (z₂ u) (z₁' u) (z₂' u) =
        ∑ q ∈ xiWardHalfCellPacket S u,
          xiAntiCausalWardSchwarzPairResponse q
            (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ)))
    (hwide : ∀ᵐ u : ℝ ∂MeasureTheory.volume, ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ))
            (z₁ u) (z₂ u) (z₁' u) (z₂' u) =
        ∑ q ∈ xiWardHalfCellPacket S u,
          xiAntiCausalWardSchwarzPairResponse q
            (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ))) :
    (S.card : ℝ) * (3 * Real.pi) ≤
      xiWardSlidingSourceRectangleAnnulusEnergy z₁ z₂ z₁' z₂' := by
  have hsource : ∀ᵐ u : ℝ ∂MeasureTheory.volume,
      xiWardPairedSourceRectangleAnnulusEnergy
          (z₁ u) (z₂ u) (z₁' u) (z₂' u) =
        xiWardSlidingHalfCellAnnulusEnergy S u := by
    filter_upwards [hnarrow, hwide] with u hnu hwu
    exact xiWardPairedSourceRectangleAnnulusEnergy_eq_sliding
      S u (z₁ u) (z₂ u) (z₁' u) (z₂' u) hnu hwu
  rw [xiWardSlidingSourceRectangleAnnulusEnergy_eq_triangular_ae
    S z₁ z₂ z₁' z₂' hsource]
  exact card_mul_three_pi_le_xiWardTriangularLocalizedAnnulusEnergy S

end

end RHTower

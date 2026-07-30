import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyTransport

/-!
# Infinite Schwarz-paired contractivity of the Xi Ward transport

Pairing every strict-right Xi divisor copy with its Schwarz conjugate and dividing by the
canonical boundary phase cancels the genus-one contacts exactly.  The normalized phase is the
unconditional infinite product of two-factor right-half-plane Cayley contractions.

Consequently actual source transport `V` is exactly `1 - phase` and is bounded by four-unit
source amplitude `2` at every positive aperture.
-/

open Complex Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Right-half-plane Cayley aperture factor attached to a centered divisor point. -/
def xiWardHalfPlaneCayleyFactor (lam w : ℂ) (alpha : ℝ) : ℂ :=
  (w + lam - alpha) / (w + lam + alpha)

theorem norm_xiWardHalfPlaneCayleyFactor_le_one
    {lam w : ℂ} {alpha : ℝ}
    (hlam : 0 < lam.re) (hw : 0 < w.re) (ha : 0 ≤ alpha) :
    ‖xiWardHalfPlaneCayleyFactor lam w alpha‖ ≤ 1 := by
  have hx : 0 < (w + lam).re := by
    simp only [Complex.add_re]
    linarith
  have hden : w + lam + (alpha : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith
  rw [xiWardHalfPlaneCayleyFactor, norm_div,
    div_le_one (norm_pos_iff.mpr hden)]
  have hsquare :
      ‖w + lam - (alpha : ℂ)‖ ^ 2 ≤
        ‖w + lam + (alpha : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith
  nlinarith [norm_nonneg (w + lam - (alpha : ℂ)),
    norm_nonneg (w + lam + (alpha : ℂ))]

theorem weierstrassE1_shift_ratio_eq_cayley_exp
    {lam w : ℂ} {alpha : ℝ}
    (hlam : lam ≠ 0) (hden : w + lam + (alpha : ℂ) ≠ 0) :
    weierstrassE1 (-(w - (alpha : ℂ)) / lam) /
        weierstrassE1 (-(w + (alpha : ℂ)) / lam) =
      xiWardHalfPlaneCayleyFactor lam w alpha *
        Complex.exp (2 * (alpha : ℂ) / lam) := by
  have hbase :
      1 - (-(w + (alpha : ℂ)) / lam) ≠ 0 := by
    intro h
    apply hden
    have h' : -(w + (alpha : ℂ)) / lam = 1 :=
      (sub_eq_zero.mp h).symm
    field_simp [hlam] at h'
    linear_combination -h'
  rw [weierstrassE1, weierstrassE1, xiWardHalfPlaneCayleyFactor,
    div_eq_iff (mul_ne_zero hbase (Complex.exp_ne_zero _))]
  have hexp :
      2 * (alpha : ℂ) / lam +
          (-(w + (alpha : ℂ)) / lam) =
        -(w - (alpha : ℂ)) / lam := by
    field_simp [hlam]
    ring
  calc
    (1 - -(w - (alpha : ℂ)) / lam) *
          Complex.exp (-(w - (alpha : ℂ)) / lam) =
        ((w + lam - (alpha : ℂ)) /
            (w + lam + (alpha : ℂ))) *
          (1 - -(w + (alpha : ℂ)) / lam) *
          Complex.exp (-(w - (alpha : ℂ)) / lam) := by
      field_simp [hlam, hden, hbase, Complex.exp_ne_zero]
      ring
    _ = ((w + lam - (alpha : ℂ)) /
            (w + lam + (alpha : ℂ))) *
          (Complex.exp (2 * (alpha : ℂ) / lam) *
            ((1 - -(w + (alpha : ℂ)) / lam) *
              Complex.exp (-(w + (alpha : ℂ)) / lam))) := by
      have he :
          Complex.exp (2 * (alpha : ℂ) / lam) *
              Complex.exp (-(w + (alpha : ℂ)) / lam) =
            Complex.exp (-(w - (alpha : ℂ)) / lam) := by
        rw [← Complex.exp_add, hexp]
      rw [← he]
      ring
    _ = ((w + lam - (alpha : ℂ)) /
            (w + lam + (alpha : ℂ)) *
          Complex.exp (2 * (alpha : ℂ) / lam)) *
            ((1 - -(w + (alpha : ℂ)) / lam) *
              Complex.exp (-(w + (alpha : ℂ)) / lam)) := by
      ring

def xiWardCayleyFactor
    (q : XiRightZeroCopy) (w : ℂ) (alpha : ℝ) : ℂ :=
  xiWardHalfPlaneCayleyFactor (xiRightCenteredZero q) w alpha

def xiWardSchwarzPairCayleyFactor
    (q : XiRightUpperZeroCopy) (w : ℂ) (alpha : ℝ) : ℂ :=
  xiWardCayleyFactor q.1 w alpha *
    xiWardCayleyFactor (xiRightZeroCopyConjEquiv q.1) w alpha

theorem norm_xiWardCayleyFactor_le_one
    (q : XiRightZeroCopy) {w : ℂ} {alpha : ℝ}
    (hw : 0 < w.re) (ha : 0 ≤ alpha) :
    ‖xiWardCayleyFactor q w alpha‖ ≤ 1 := by
  exact norm_xiWardHalfPlaneCayleyFactor_le_one q.2 hw ha

theorem norm_xiWardSchwarzPairCayleyFactor_le_one
    (q : XiRightUpperZeroCopy) {w : ℂ} {alpha : ℝ}
    (hw : 0 < w.re) (ha : 0 ≤ alpha) :
    ‖xiWardSchwarzPairCayleyFactor q w alpha‖ ≤ 1 := by
  rw [xiWardSchwarzPairCayleyFactor, norm_mul]
  exact mul_le_one₀
    (norm_xiWardCayleyFactor_le_one q.1 hw ha)
    (norm_nonneg _)
    (norm_xiWardCayleyFactor_le_one
      (xiRightZeroCopyConjEquiv q.1) hw ha)

theorem xiWardCanonicalArgument_sub
    (q : XiRightZeroCopy) (w : ℂ) (alpha : ℝ) :
    (I * w - (alpha : ℂ) * I) / xiRightSpectralPoint q =
      -(w - (alpha : ℂ)) / xiRightCenteredZero q := by
  rw [xiRightCenteredZero, xiRightSpectralPoint]
  field_simp [I_ne_zero, xiSpectralPoint_ne_zero q.1]
  rw [pow_two, I_mul_I]
  ring

theorem xiWardCanonicalArgument_add
    (q : XiRightZeroCopy) (w : ℂ) (alpha : ℝ) :
    (I * w + (alpha : ℂ) * I) / xiRightSpectralPoint q =
      -(w + (alpha : ℂ)) / xiRightCenteredZero q := by
  rw [xiRightCenteredZero, xiRightSpectralPoint]
  field_simp [I_ne_zero, xiSpectralPoint_ne_zero q.1]
  rw [pow_two, I_mul_I]
  ring

theorem xiWardE1_shift_ratio_eq_cayley_exp
    (q : XiRightZeroCopy) {w : ℂ} {alpha : ℝ}
    (hw : 0 < w.re) (ha : 0 ≤ alpha) :
    weierstrassE1
          ((I * w - (alpha : ℂ) * I) / xiRightSpectralPoint q) /
        weierstrassE1
          ((I * w + (alpha : ℂ) * I) / xiRightSpectralPoint q) =
      xiWardCayleyFactor q w alpha *
        Complex.exp
          (2 * (alpha : ℂ) / xiRightCenteredZero q) := by
  rw [xiWardCanonicalArgument_sub, xiWardCanonicalArgument_add,
    xiWardCayleyFactor]
  apply weierstrassE1_shift_ratio_eq_cayley_exp
  · exact xiRightCenteredZero_ne_zero q
  · intro hzero
    have hre := congrArg Complex.re hzero
    have hq := q.2
    change 0 < (xiRightCenteredZero q).re at hq
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith

theorem xiWardE1_schwarzPair_ratio_eq_cayley_exp
    (q : XiRightUpperZeroCopy) {w : ℂ} {alpha : ℝ}
    (hw : 0 < w.re) (ha : 0 ≤ alpha) :
    (weierstrassE1
          ((I * w - (alpha : ℂ) * I) / xiRightSpectralPoint q.1) *
        weierstrassE1
          ((I * w - (alpha : ℂ) * I) /
            xiRightSpectralPoint (xiRightZeroCopyConjEquiv q.1))) /
      (weierstrassE1
          ((I * w + (alpha : ℂ) * I) / xiRightSpectralPoint q.1) *
        weierstrassE1
          ((I * w + (alpha : ℂ) * I) /
            xiRightSpectralPoint (xiRightZeroCopyConjEquiv q.1))) =
      xiWardSchwarzPairCayleyFactor q w alpha *
        Complex.exp
          ((alpha : ℂ) * xiAntiCausalWardBoundaryPairTerm q) := by
  have hq :=
    xiWardE1_shift_ratio_eq_cayley_exp q.1 hw ha
  have hqc :=
    xiWardE1_shift_ratio_eq_cayley_exp
      (xiRightZeroCopyConjEquiv q.1) hw ha
  rw [xiWardSchwarzPairCayleyFactor,
    xiAntiCausalWardBoundaryPairTerm_eq_pair]
  have hden1 :
      weierstrassE1
        ((I * w + (alpha : ℂ) * I) /
          xiRightSpectralPoint q.1) ≠ 0 := by
    rw [xiWardCanonicalArgument_add, weierstrassE1]
    apply mul_ne_zero
    · intro hzero
      have h' : -(w + (alpha : ℂ)) /
          xiRightCenteredZero q.1 = 1 :=
        (sub_eq_zero.mp hzero).symm
      have hlam := xiRightCenteredZero_ne_zero q.1
      field_simp [hlam] at h'
      have hre := congrArg Complex.re h'
      have hright := q.1.2
      change 0 < (xiRightCenteredZero q.1).re at hright
      simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re,
        ] at hre
      linarith
    · exact Complex.exp_ne_zero _
  have hden2 :
      weierstrassE1
        ((I * w + (alpha : ℂ) * I) /
          xiRightSpectralPoint (xiRightZeroCopyConjEquiv q.1)) ≠ 0 := by
    rw [xiWardCanonicalArgument_add, weierstrassE1]
    apply mul_ne_zero
    · intro hzero
      have h' : -(w + (alpha : ℂ)) /
          xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1) = 1 :=
        (sub_eq_zero.mp hzero).symm
      have hlam :=
        xiRightCenteredZero_ne_zero (xiRightZeroCopyConjEquiv q.1)
      field_simp [hlam] at h'
      have hre := congrArg Complex.re h'
      have hright := (xiRightZeroCopyConjEquiv q.1).2
      change 0 <
        (xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1)).re at hright
      simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re,
        ] at hre
      linarith
    · exact Complex.exp_ne_zero _
  rw [show
    (weierstrassE1
          ((I * w - (alpha : ℂ) * I) / xiRightSpectralPoint q.1) *
        weierstrassE1
          ((I * w - (alpha : ℂ) * I) /
            xiRightSpectralPoint (xiRightZeroCopyConjEquiv q.1))) /
      (weierstrassE1
          ((I * w + (alpha : ℂ) * I) / xiRightSpectralPoint q.1) *
        weierstrassE1
          ((I * w + (alpha : ℂ) * I) /
            xiRightSpectralPoint (xiRightZeroCopyConjEquiv q.1))) =
      (weierstrassE1
          ((I * w - (alpha : ℂ) * I) / xiRightSpectralPoint q.1) /
        weierstrassE1
          ((I * w + (alpha : ℂ) * I) / xiRightSpectralPoint q.1)) *
      (weierstrassE1
          ((I * w - (alpha : ℂ) * I) /
            xiRightSpectralPoint (xiRightZeroCopyConjEquiv q.1)) /
        weierstrassE1
          ((I * w + (alpha : ℂ) * I) /
            xiRightSpectralPoint (xiRightZeroCopyConjEquiv q.1))) by
      field_simp [hden1, hden2]]
  rw [hq, hqc]
  calc
    xiWardCayleyFactor q.1 w alpha *
          Complex.exp (2 * (alpha : ℂ) / xiRightCenteredZero q.1) *
        (xiWardCayleyFactor (xiRightZeroCopyConjEquiv q.1) w alpha *
          Complex.exp
            (2 * (alpha : ℂ) /
              xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1))) =
      xiWardCayleyFactor q.1 w alpha *
        xiWardCayleyFactor (xiRightZeroCopyConjEquiv q.1) w alpha *
          (Complex.exp (2 * (alpha : ℂ) / xiRightCenteredZero q.1) *
            Complex.exp
              (2 * (alpha : ℂ) /
                xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1))) := by
      ring
    _ = xiWardCayleyFactor q.1 w alpha *
        xiWardCayleyFactor (xiRightZeroCopyConjEquiv q.1) w alpha *
          Complex.exp
            ((alpha : ℂ) *
              (2 * ((xiRightCenteredZero q.1)⁻¹ +
                (xiRightCenteredZero
                  (xiRightZeroCopyConjEquiv q.1))⁻¹))) := by
      rw [← Complex.exp_add]
      congr 2
      field_simp [xiRightCenteredZero_ne_zero q.1,
        xiRightCenteredZero_ne_zero (xiRightZeroCopyConjEquiv q.1)]

set_option maxHeartbeats 2000000 in
theorem xiRightCanonicalProduct_hasProd_schwarzPairs (z : ℂ) :
    HasProd
      (fun q : XiRightUpperZeroCopy =>
        weierstrassE1 (z / xiRightSpectralPoint q.1) *
          weierstrassE1
            (z / xiRightSpectralPoint
              (xiRightZeroCopyConjEquiv q.1)))
      (xiRightCanonicalProduct z) := by
  let f : XiRightZeroCopy → ℂ :=
    fun q => weierstrassE1 (z / xiRightSpectralPoint q)
  have hfull : HasProd f (xiRightCanonicalProduct z) := by
    simpa only [f] using
      xiRightCanonicalProduct_hasProdLocallyUniformlyOn.hasProd
        (show z ∈ Set.univ by simp)
  have hupperSum : Summable
      (fun q : XiRightUpperZeroCopy =>
        1 / ‖xiRightSpectralPoint q.1‖ ^ 2) :=
    xiRightSpectralPoint_inv_sq_summable.subtype
      (fun q : XiRightZeroCopy => 0 < (xiRightCenteredZero q).im)
  have hl : Multipliable
      (fun q : XiRightUpperZeroCopy =>
        f (xiRightSchwarzPairEquiv (Sum.inl q))) := by
    simpa only [f, xiRightSchwarzPairEquiv_inl] using
      (canonicalProductE1Indexed_hasProdLocallyUniformlyOn
        (fun q : XiRightUpperZeroCopy => xiRightSpectralPoint q.1)
        (fun q => xiRightSpectralPoint_ne_zero q.1)
        hupperSum).hasProd (show z ∈ Set.univ by simp) |>.multipliable
  have hlowerSum : Summable
      (fun q : XiRightUpperZeroCopy =>
        1 / ‖xiRightSpectralPoint
          (xiRightZeroCopyConjEquiv q.1)‖ ^ 2) := by
    apply hupperSum.congr
    intro q
    have hnorm :
        ‖xiRightSpectralPoint
            (xiRightZeroCopyConjEquiv q.1)‖ =
          ‖xiRightSpectralPoint q.1‖ := by
      have h := congrArg norm (xiRightCenteredZero_conj q.1)
      simpa only [xiRightCenteredZero, xiRightSpectralPoint,
        norm_mul, norm_I, one_mul, map_zero, Complex.norm_conj] using h
    rw [hnorm]
  have hr : Multipliable
      (fun q : XiRightUpperZeroCopy =>
        f (xiRightSchwarzPairEquiv (Sum.inr q))) := by
    simpa only [f, xiRightSchwarzPairEquiv_inr] using
      (canonicalProductE1Indexed_hasProdLocallyUniformlyOn
        (fun q : XiRightUpperZeroCopy =>
          xiRightSpectralPoint (xiRightZeroCopyConjEquiv q.1))
        (fun q => xiRightSpectralPoint_ne_zero
          (xiRightZeroCopyConjEquiv q.1))
        hlowerSum).hasProd (show z ∈ Set.univ by simp) |>.multipliable
  have hpair := hl.hasProd.mul hr.hasProd
  have hsum :
      HasProd (f ∘ xiRightSchwarzPairEquiv)
        (xiRightCanonicalProduct z) :=
    xiRightSchwarzPairEquiv.hasProd_iff.mpr hfull
  have hsplit :
      HasProd (f ∘ xiRightSchwarzPairEquiv)
        ((∏' q : XiRightUpperZeroCopy,
            f (xiRightSchwarzPairEquiv (Sum.inl q))) *
          ∏' q : XiRightUpperZeroCopy,
            f (xiRightSchwarzPairEquiv (Sum.inr q))) := by
    exact hl.hasProd.sum hr.hasProd
  have heq :
      (∏' q : XiRightUpperZeroCopy,
          f (xiRightSchwarzPairEquiv (Sum.inl q))) *
        ∏' q : XiRightUpperZeroCopy,
          f (xiRightSchwarzPairEquiv (Sum.inr q)) =
        xiRightCanonicalProduct z :=
    hsplit.unique hsum
  rw [heq] at hpair
  simpa only [f, xiRightSchwarzPairEquiv_inl,
    xiRightSchwarzPairEquiv_inr] using hpair

theorem HasProd.div_of_limit_ne_zero
    {ι : Type*} {f g : ι → ℂ} {a b : ℂ}
    (hf : HasProd f a) (hg : HasProd g b) (hb : b ≠ 0) :
    HasProd (fun i => f i / g i) (a / b) := by
  rw [HasProd] at hf hg ⊢
  convert hf.div hg hb using 1
  ext s
  exact Finset.prod_div_distrib f g

theorem xiRightCanonicalProduct_boundary_shift_ne_zero
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 ≤ alpha) :
    xiRightCanonicalProduct
      (I * w + (alpha : ℂ) * I) ≠ 0 := by
  intro hzero
  obtain ⟨q, hq⟩ :=
    (xiRightCanonicalProduct_eq_zero_iff_exists
      (I * w + (alpha : ℂ) * I)).mp hzero
  have hright := q.2
  change 0 < (I * xiRightSpectralPoint q).re at hright
  rw [hq] at hright
  have hcoord :
      I * (I * w + (alpha : ℂ) * I) =
        -(w + (alpha : ℂ)) := by
    calc
      _ = (I * I) * w + (alpha : ℂ) * (I * I) := by ring
      _ = -(w + (alpha : ℂ)) := by rw [I_mul_I]; ring
  rw [hcoord] at hright
  simp only [neg_re, add_re, ofReal_re] at hright
  linarith

set_option maxHeartbeats 800000 in
theorem xiRightWardBoundarySourcePhaseCrossRatio_hasProd_cayley
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 ≤ alpha) :
    HasProd (fun q : XiRightUpperZeroCopy =>
      xiWardSchwarzPairCayleyFactor q w alpha)
      (xiRightWardBoundarySourcePhaseCrossRatio
        (I * w) (alpha : ℂ)) := by
  let zminus : ℂ := I * w - (alpha : ℂ) * I
  let zplus : ℂ := I * w + (alpha : ℂ) * I
  let e1minus : XiRightUpperZeroCopy → ℂ :=
    fun q =>
      weierstrassE1 (zminus / xiRightSpectralPoint q.1) *
        weierstrassE1
          (zminus / xiRightSpectralPoint
            (xiRightZeroCopyConjEquiv q.1))
  let e1plus : XiRightUpperZeroCopy → ℂ :=
    fun q =>
      weierstrassE1 (zplus / xiRightSpectralPoint q.1) *
        weierstrassE1
          (zplus / xiRightSpectralPoint
            (xiRightZeroCopyConjEquiv q.1))
  have hminus : HasProd e1minus (xiRightCanonicalProduct zminus) := by
    simpa only [e1minus] using
      xiRightCanonicalProduct_hasProd_schwarzPairs zminus
  have hplus : HasProd e1plus (xiRightCanonicalProduct zplus) := by
    simpa only [e1plus] using
      xiRightCanonicalProduct_hasProd_schwarzPairs zplus
  have hzplus : xiRightCanonicalProduct zplus ≠ 0 := by
    simpa only [zplus] using
      xiRightCanonicalProduct_boundary_shift_ne_zero hw ha
  have hratio : HasProd (fun q => e1minus q / e1plus q)
      (xiRightCanonicalProduct zminus /
        xiRightCanonicalProduct zplus) :=
    HasProd.div_of_limit_ne_zero hminus hplus hzplus
  have hsum :
      HasSum
        (fun q : XiRightUpperZeroCopy =>
          (alpha : ℂ) * xiAntiCausalWardBoundaryPairTerm q)
        ((alpha : ℂ) * xiAntiCausalWardBoundarySelfSymbol) := by
    simpa only [xiAntiCausalWardBoundarySelfSymbol] using
      summable_xiAntiCausalWardBoundaryPairTerm.hasSum.mul_left
        (alpha : ℂ)
  have hexp :
      HasProd
        (fun q : XiRightUpperZeroCopy =>
          Complex.exp
            ((alpha : ℂ) * xiAntiCausalWardBoundaryPairTerm q))
        (Complex.exp
          ((alpha : ℂ) * xiAntiCausalWardBoundarySelfSymbol)) := by
    simpa only [Function.comp_apply, ← Complex.exp_eq_exp_ℂ] using!
      hsum.exp
  have hexp_ne :
      Complex.exp
        ((alpha : ℂ) * xiAntiCausalWardBoundarySelfSymbol) ≠ 0 :=
    Complex.exp_ne_zero _
  have hquot :=
    HasProd.div_of_limit_ne_zero hratio hexp hexp_ne
  have hfactor :
      (fun q : XiRightUpperZeroCopy =>
        (e1minus q / e1plus q) /
          Complex.exp
            ((alpha : ℂ) * xiAntiCausalWardBoundaryPairTerm q)) =
        fun q => xiWardSchwarzPairCayleyFactor q w alpha := by
    funext q
    rw [xiWardE1_schwarzPair_ratio_eq_cayley_exp q hw ha]
    field_simp [Complex.exp_ne_zero]
  rw [hfactor] at hquot
  simpa only [zminus, zplus, xiRightWardBoundarySourcePhaseCrossRatio,
    xiRightWardSourcePhase, xiAntiCausalWardBoundarySourcePhase] using
    hquot

theorem norm_xiRightWardBoundarySourcePhaseCrossRatio_le_one
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 ≤ alpha) :
    ‖xiRightWardBoundarySourcePhaseCrossRatio
      (I * w) (alpha : ℂ)‖ ≤ 1 := by
  have hprod :=
    xiRightWardBoundarySourcePhaseCrossRatio_hasProd_cayley hw ha
  have hnorm := hprod.norm
  rw [HasProd] at hnorm
  refine le_of_tendsto' hnorm (fun s => ?_)
  exact Finset.prod_le_one
    (fun q _ => norm_nonneg _)
    (fun q _ =>
      norm_xiWardSchwarzPairCayleyFactor_le_one q hw ha)

theorem mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase
    {w : ℂ} (hw : 0 < w.re) (alpha : ℂ) :
    mobiusGammaXiAntiCausalWardTransportV w alpha =
      1 - xiRightWardBoundarySourcePhaseCrossRatio (I * w) alpha := by
  have hw0 : w ≠ 0 := by
    intro hzero
    rw [hzero] at hw
    simp at hw
  simp only [mobiusGammaXiAntiCausalWardTransportV,
    xiRightWardBoundaryAnchoredSourceTransportV,
    xiRightWardBoundaryJuliaCrossDefect]
  field_simp [I_ne_zero, hw0]
  ring

theorem norm_mobiusGammaXiAntiCausalWardTransportV_le_two
    {w : ℂ} {alpha : ℝ} (hw : 0 < w.re) (ha : 0 ≤ alpha) :
    ‖mobiusGammaXiAntiCausalWardTransportV w (alpha : ℂ)‖ ≤ 2 := by
  rw [mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase hw]
  calc
    ‖1 - xiRightWardBoundarySourcePhaseCrossRatio
        (I * w) (alpha : ℂ)‖ ≤
        ‖(1 : ℂ)‖ +
          ‖xiRightWardBoundarySourcePhaseCrossRatio
            (I * w) (alpha : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ 2 := by
      have hphase :=
        norm_xiRightWardBoundarySourcePhaseCrossRatio_le_one hw ha
      norm_num
      linarith

/-- Every entry in distinguished boundary column of non-scalar matrix transport obeys same
four-unit amplitude bound.  This connects infinite Cayley contraction to augmented `V`, rather
than defining separate coordinatewise transport. -/
theorem norm_mobiusGammaXiAntiCausalWardMatrixTransportV_boundaryColumn_le_two
    {n : ℕ} {node : Fin n → ℂ} (hnode : ∀ i, 0 < (node i).re)
    {alpha : ℝ} (ha : 0 ≤ alpha) (i : Fin n) :
    ‖mobiusGammaXiAntiCausalWardMatrixTransportV node (alpha : ℂ)
      (Sum.inl i) (Sum.inr ())‖ ≤ 2 := by
  rw [mobiusGammaXiAntiCausalWardMatrixTransportV_boundaryColumn]
  exact norm_mobiusGammaXiAntiCausalWardTransportV_le_two
    (hnode i) ha

end

end RHTower

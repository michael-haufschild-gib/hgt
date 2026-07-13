import GaloisForLFunctions.Hurwitz.AnchorTransversality
import GaloisForLFunctions.RHTower.OrbitwiseSourceDivisorSeam
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# The Hurwitz anchor tail and the prime flux have the same first-prime seam

The exact canonical-anchor formula identifies the normalized `r`th Hurwitz shift jet with
`zeta(s+r)`.  First-coefficient extraction for Dirichlet series then gives

`2^r * (zeta(s+r)-1) -> 2^(-s)`.

Applied to the functional-equation and Schwarz endpoints `1-rho` and `conj rho`, this proves that
the normalized Hurwitz anchor-tail difference converges to the same first-prime seam charge as the
far-right difference of the actual von Mangoldt source `-zeta'/zeta`.  Their difference therefore
tends to zero unconditionally for every point in the open critical strip.

This is a value relation between two source coordinates, not an RH proof.  Vanishing of their
common limit is exactly the additional orientation condition selecting the critical line.
-/

open Complex Filter Real LSeries
open scoped LSeries.notation

namespace RHTower

noncomputable section

/-- Coefficient twist which translates the zeta Dirichlet series by `a`. -/
def anchorShiftedZetaCoeff (a : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (n : ℂ) ^ (-a)

@[simp] theorem anchorShiftedZetaCoeff_zero (a : ℂ) :
    anchorShiftedZetaCoeff a 0 = 0 := by
  simp [anchorShiftedZetaCoeff]

@[simp] theorem anchorShiftedZetaCoeff_one (a : ℂ) :
    anchorShiftedZetaCoeff a 1 = 1 := by
  simp [anchorShiftedZetaCoeff]

theorem anchorShiftedZetaCoeff_two (a : ℂ) :
    anchorShiftedZetaCoeff a 2 = (2 : ℂ) ^ (-a) := by
  simp [anchorShiftedZetaCoeff]

/-- Translating the zeta argument is coefficient twisting. -/
theorem LSeries_anchorShiftedZetaCoeff (a s : ℂ) :
    LSeries (anchorShiftedZetaCoeff a) s =
      LSeries (1 : ℕ → ℂ) (a + s) := by
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [anchorShiftedZetaCoeff, if_neg hn,
      Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    simp only [Pi.one_apply, one_div, Complex.cpow_neg]
    field_simp

/-- Every translated zeta coefficient sequence has a finite absolute-convergence abscissa. -/
theorem anchorShiftedZetaCoeff_abscissa_lt_top (a : ℂ) :
    abscissaOfAbsConv (anchorShiftedZetaCoeff a) < ⊤ := by
  let x : ℝ := max 2 (2 - a.re)
  have hx : 1 < (a + (x : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, x]
    have h := le_max_right 2 (2 - a.re)
    linarith
  have hs : LSeriesSummable (1 : ℕ → ℂ) (a + (x : ℂ)) :=
    LSeriesSummable_one_iff.mpr hx
  have hshift : LSeriesSummable (anchorShiftedZetaCoeff a) (x : ℂ) := by
    rw [LSeriesSummable] at hs ⊢
    apply hs.congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      rw [anchorShiftedZetaCoeff, if_neg hn,
        Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
      simp only [Pi.one_apply, one_div, Complex.cpow_neg]
      field_simp
  exact hshift.abscissaOfAbsConv_le.trans_lt (by simp)

/-- Delete the unit coefficient so that the first surviving Dirichlet atom is `n=2`. -/
def anchorShiftedZetaTailCoeff (a : ℂ) : ℕ → ℂ :=
  anchorShiftedZetaCoeff a - LSeries.delta

@[simp] theorem anchorShiftedZetaTailCoeff_zero (a : ℂ) :
    anchorShiftedZetaTailCoeff a 0 = 0 := by
  simp [anchorShiftedZetaTailCoeff, LSeries.delta]

@[simp] theorem anchorShiftedZetaTailCoeff_one (a : ℂ) :
    anchorShiftedZetaTailCoeff a 1 = 0 := by
  simp [anchorShiftedZetaTailCoeff, LSeries.delta]

theorem anchorShiftedZetaTailCoeff_two (a : ℂ) :
    anchorShiftedZetaTailCoeff a 2 = (2 : ℂ) ^ (-a) := by
  simp [anchorShiftedZetaTailCoeff, LSeries.delta, anchorShiftedZetaCoeff_two]

theorem anchorShiftedZetaTailCoeff_abscissa_lt_top (a : ℂ) :
    abscissaOfAbsConv (anchorShiftedZetaTailCoeff a) < ⊤ := by
  have hdelta : abscissaOfAbsConv LSeries.delta < ⊤ := by
    have hs : LSeriesSummable LSeries.delta 0 := by
      rw [LSeriesSummable]
      apply (summable_congr (fun n => LSeries.term_delta 0 n)).mpr
      exact (hasSum_ite_eq 1 (1 : ℂ)).summable
    exact hs.abscissaOfAbsConv_le.trans_lt (by simp)
  exact (LSeries.abscissaOfAbsConv_sub_le
    (anchorShiftedZetaCoeff a) LSeries.delta).trans_lt
      (max_lt (anchorShiftedZetaCoeff_abscissa_lt_top a) hdelta)

/-- On the convergence half-plane, the shifted tail L-series is exactly `zeta(a+x)-1`. -/
theorem LSeries_anchorShiftedZetaTailCoeff_eq (a : ℂ) {x : ℝ}
    (hx : 1 < (a + (x : ℂ)).re) :
    LSeries (anchorShiftedZetaTailCoeff a) (x : ℂ) =
      riemannZeta (a + (x : ℂ)) - 1 := by
  have hshift : LSeriesSummable (anchorShiftedZetaCoeff a) (x : ℂ) := by
    rw [LSeriesSummable]
    have hs : LSeriesSummable (1 : ℕ → ℂ) (a + (x : ℂ)) :=
      LSeriesSummable_one_iff.mpr hx
    rw [LSeriesSummable] at hs
    apply hs.congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      rw [anchorShiftedZetaCoeff, if_neg hn,
        Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
      simp only [Pi.one_apply, one_div, Complex.cpow_neg]
      field_simp
  have hdelta : LSeriesSummable LSeries.delta (x : ℂ) := by
    rw [LSeriesSummable]
    apply (summable_congr (fun n => LSeries.term_delta (x : ℂ) n)).mpr
    exact (hasSum_ite_eq 1 (1 : ℂ)).summable
  rw [anchorShiftedZetaTailCoeff, LSeries_sub hshift hdelta,
    LSeries_anchorShiftedZetaCoeff, LSeries_delta,
    LSeries_one_eq_riemannZeta hx]
  rfl

/-- **First-prime extraction for translated zeta.** -/
theorem tendsto_two_cpow_mul_riemannZeta_shift_sub_one (a : ℂ) :
    Tendsto (fun x : ℝ => (2 : ℂ) ^ (x : ℂ) *
      (riemannZeta (a + (x : ℂ)) - 1)) atTop
      (nhds ((2 : ℂ) ^ (-a))) := by
  have h := LSeries.tendsto_cpow_mul_atTop
    (f := anchorShiftedZetaTailCoeff a) (n := 1)
    (fun m hm => by interval_cases m <;> simp)
    (anchorShiftedZetaTailCoeff_abscissa_lt_top a)
  norm_num at h
  rw [anchorShiftedZetaTailCoeff_two] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 - a.re)] with x hx
  rw [LSeries_anchorShiftedZetaTailCoeff_eq a (by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith)]

/-- Remove the explicit signed Pochhammer coefficient from the canonical Hurwitz anchor jet and
subtract the unit Dirichlet atom. -/
def normalizedHurwitzAnchorTail (s : ℂ) (r : ℕ) : ℂ :=
  iteratedDeriv r (HurwitzZetaContinuation.continuedHzeta s) 1 /
      ((-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s) - 1

/-- The normalized anchor tail is exactly the translated zeta tail. -/
theorem normalizedHurwitzAnchorTail_eq (r : ℕ) {s : ℂ} (hs : 0 < s.re) :
    normalizedHurwitzAnchorTail s r = riemannZeta (s + r) - 1 := by
  rw [normalizedHurwitzAnchorTail,
    HurwitzZetaContinuation.continuedHzeta_iteratedDeriv_at_one r hs]
  have hsign : (-1 : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  have hp : (ascPochhammer ℂ r).eval s ≠ 0 :=
    HurwitzZetaContinuation.ascPochhammer_eval_ne_zero_of_pos_re r hs
  field_simp [hsign, hp]

/-- The normalized Hurwitz anchor tail recovers the first prime character `2^(-s)`. -/
theorem tendsto_two_cpow_mul_normalizedHurwitzAnchorTail
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun r : ℕ => (2 : ℂ) ^ (r : ℂ) *
      normalizedHurwitzAnchorTail s r) atTop
      (nhds ((2 : ℂ) ^ (-s))) := by
  have h := (tendsto_two_cpow_mul_riemannZeta_shift_sub_one s).comp
    tendsto_natCast_atTop_atTop
  convert h using 1
  funext r
  rw [normalizedHurwitzAnchorTail_eq r hs]
  norm_num

/-- Difference of the FE and Schwarz normalized anchor tails, scaled to its first-prime limit. -/
def xiHurwitzAnchorPrimeTwoSeam (rho : ℂ) (r : ℕ) : ℂ :=
  (Real.log 2 : ℂ) * (2 : ℂ) ^ (r : ℂ) *
    (normalizedHurwitzAnchorTail ((starRingEnd ℂ) rho) r -
      normalizedHurwitzAnchorTail (1 - rho) r)

/-- **Hurwitz-anchor value relation.**  The anchor-tail difference converges to the canonical
orbitwise first-prime seam charge. -/
theorem tendsto_xiHurwitzAnchorPrimeTwoSeam
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Tendsto (xiHurwitzAnchorPrimeTwoSeam rho) atTop
      (nhds (orbitwiseFirstPrimeSeamCharge rho)) := by
  have hconj := tendsto_two_cpow_mul_normalizedHurwitzAnchorTail
    ((starRingEnd ℂ) rho) (by simpa using hstrip.1)
  have href := tendsto_two_cpow_mul_normalizedHurwitzAnchorTail
    (1 - rho) (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith)
  have h := (hconj.sub href).const_mul (Real.log 2 : ℂ)
  convert h using 1
  · funext r
    simp only [xiHurwitzAnchorPrimeTwoSeam]
    ring

/-- The corresponding first-prime-scaled difference of the actual continued prime flux. -/
def xiPrimeFluxPrimeTwoSeam (rho : ℂ) (r : ℕ) : ℂ :=
  (2 : ℂ) ^ (r : ℂ) *
    (infinitePrimeFlux ((starRingEnd ℂ) rho + (r : ℂ)) -
      infinitePrimeFlux ((1 - rho) + (r : ℂ)))

theorem tendsto_xiPrimeFluxPrimeTwoSeam (rho : ℂ) :
    Tendsto (xiPrimeFluxPrimeTwoSeam rho) atTop
      (nhds (orbitwiseFirstPrimeSeamCharge rho)) := by
  have h := (tendsto_orbitwiseFirstPrimeSeamCharge_infinitePrimeFlux rho).comp
    tendsto_natCast_atTop_atTop
  convert h using 1

/-- **Common-seam theorem.**  The local Hurwitz anchor coefficient channel and the far-right
all-prime flux channel agree asymptotically after first-prime normalization. -/
theorem tendsto_anchorPrimeTwoSeam_sub_primeFluxPrimeTwoSeam_zero
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Tendsto (fun r => xiHurwitzAnchorPrimeTwoSeam rho r -
      xiPrimeFluxPrimeTwoSeam rho r) atTop (nhds 0) := by
  simpa using (tendsto_xiHurwitzAnchorPrimeTwoSeam hstrip).sub
    (tendsto_xiPrimeFluxPrimeTwoSeam rho)

/-- Vanishing of the Hurwitz anchor first-prime seam forces the critical-line equation. -/
theorem re_eq_half_of_xiHurwitzAnchorPrimeTwoSeam_tendsto_zero
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hzero : Tendsto (xiHurwitzAnchorPrimeTwoSeam rho) atTop (nhds 0)) :
    rho.re = 1 / 2 := by
  have hcharge := tendsto_xiHurwitzAnchorPrimeTwoSeam hstrip
  have heq : orbitwiseFirstPrimeSeamCharge rho = 0 :=
    tendsto_nhds_unique hcharge hzero
  exact (orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).mp heq

/-- Global vanishing hypothesis for the Xi-indexed Hurwitz anchor first-prime seams. -/
def XiHurwitzAnchorPrimeTwoSeamsVanish : Prop :=
  ∀ rho : XiDivisorSupport,
    Tendsto (xiHurwitzAnchorPrimeTwoSeam (rho : ℂ)) atTop (nhds 0)

/-- **Anchor-tail first-prime chain to RH.** -/
theorem riemannHypothesis_of_xiHurwitzAnchorPrimeTwoSeamsVanish
    (h : XiHurwitzAnchorPrimeTwoSeamsVanish) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hstrip := xi_divisor_support_re_mem_open_unit support
  have hre := re_eq_half_of_xiHurwitzAnchorPrimeTwoSeam_tendsto_zero
    hstrip (h support)
  exact (not_lt_of_ge hre.le) (mem_rightHalf.mp hrho)

end

end RHTower

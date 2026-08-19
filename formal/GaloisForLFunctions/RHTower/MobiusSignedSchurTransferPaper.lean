import GaloisForLFunctions.RHTower.MobiusCausalSourceLimit
import GaloisForLFunctions.RHTower.MobiusSignedSchurComplexMultiplier

/-!
# Paper certificate: the signed Möbius coisometry is an exact Schur transfer

Formal certificate for
`docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius/`
`mobius-signed-coisometry-schur-transfer-law.md`.

```text
(9)--(13)  tau_omega(z) = zeta(2sigma)/(zeta(sigma) zeta(sigma+z)), |tau_omega| <= 1 on Re z >= 0,
           tau_omega(0) = zeta(2sigma)/zeta(sigma)^2 ;
(17)       L a_omega(z) = zeta(1+z)/(1+omega+z) ;
(23a)      K_omega(z)   = zeta(1+z)/(1+omega+z) - c_omega/z ;
(18)       L B_{omega,d}(z) = d^{-z} zeta(1+z)/(1+omega+z) - c_omega/z ;
(21)       sum_d mu(d) d^{-sigma} L B_{omega,d}(z) = M_omega(z) ;
(23b)      M_omega/Z_omega = tau_omega K_omega + c_omega (tau_omega(z)-tau_omega(0))/z ;
(23e)      L g_omega(z) = (tau_omega(z) - tau_omega(0))/z ;
(23f)/(23g) |g_omega|^2 <= P{log d > t} and ||g_omega||^2 <= E[log d] ;
(23i)      Z_omega ~ 1/(2 omega zeta(2)) and E[log d] ~ 1/(2 omega).
```
-/

open Complex MeasureTheory Set Filter ArithmeticFunction LSeries
open scoped BigOperators Topology LSeries.notation Moebius

noncomputable section
namespace RHTower

/-! ### The Hardy floor-remainder transform -/

/-- Card `(23a)`: the `H²` floor-remainder transform `K_omega`. -/
def floorRemainderTransform (ω : ℝ) (z : ℂ) : ℂ :=
  riemannZeta (1 + z) / (1 + (ω : ℂ) + z) - (1 / ((1 : ℂ) + (ω : ℂ))) / z

/-- Card `(18)`: the transform of the coupled channel feature. -/
def channelFeatureTransform (ω : ℝ) (d : ℕ) (z : ℂ) : ℂ :=
  ((d : ℂ)) ^ (-z) * (riemannZeta (1 + z) / (1 + (ω : ℂ) + z)) -
    (1 / ((1 : ℂ) + (ω : ℂ))) / z

theorem channelFeatureTransform_one (ω : ℝ) (z : ℂ) :
    channelFeatureTransform ω 1 z = floorRemainderTransform ω z := by
  rw [channelFeatureTransform, floorRemainderTransform]
  norm_num

/-! ### Card `(21)`: the complete coupled causal transform -/

theorem tsum_channelFeatureTransform {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    (∑' d : ℕ, mobiusRealWeight (1 + 2 * ω) d * channelFeatureTransform ω d z)
      = mobiusCausalMultiplier ω z := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  have hre : 1 < (((1 + 2 * ω : ℝ) : ℂ)).re := by simpa using ha
  have hshiftre : 1 < ((((1 + 2 * ω : ℝ) : ℂ)) + z).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hsum1 : Summable (mobiusRealWeight (1 + 2 * ω)) := summable_mobiusRealWeight ha
  have hterm : ∀ d : ℕ,
      mobiusRealWeight (1 + 2 * ω) d * ((d : ℂ)) ^ (-z)
        = LSeries.term (↗μ) (((1 + 2 * ω : ℝ) : ℂ) + z) d := by
    intro d
    by_cases hd : d = 0
    · subst d
      simp [mobiusRealWeight]
    · have hne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
      rw [mobiusRealWeight_eq_term, LSeries.term_of_ne_zero hd, LSeries.term_of_ne_zero hd,
        Complex.cpow_add _ _ hne, Complex.cpow_neg]
      field_simp
  have hsum2 : Summable (fun d : ℕ => mobiusRealWeight (1 + 2 * ω) d * ((d : ℂ)) ^ (-z)) :=
    Summable.congr (LSeriesSummable_moebius_iff.mpr hshiftre) fun d => (hterm d).symm
  have hsplit : (∑' d : ℕ, mobiusRealWeight (1 + 2 * ω) d * channelFeatureTransform ω d z)
      = (riemannZeta (1 + z) / (1 + (ω : ℂ) + z)) *
          (∑' d : ℕ, mobiusRealWeight (1 + 2 * ω) d * ((d : ℂ)) ^ (-z)) -
        ((1 / ((1 : ℂ) + (ω : ℂ))) / z) * ∑' d : ℕ, mobiusRealWeight (1 + 2 * ω) d := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub (hsum2.mul_left _)
      (hsum1.mul_left _)]
    refine tsum_congr fun d => ?_
    rw [channelFeatureTransform]
    ring
  rw [hsplit, tsum_mobiusRealWeight ha]
  rw [show (∑' d : ℕ, mobiusRealWeight (1 + 2 * ω) d * ((d : ℂ)) ^ (-z))
      = (riemannZeta (((1 + 2 * ω : ℝ) : ℂ) + z))⁻¹ from by
    rw [tsum_congr hterm]
    exact LSeries_moebius_eq_inv_riemannZeta hshiftre]
  have hcast : ((1 + 2 * ω : ℝ) : ℂ) = 1 + 2 * (ω : ℂ) := by push_cast; ring
  rw [hcast, mobiusCausalMultiplier]
  have hζ := riemannZeta_one_add_two_mul_add_ne_zero hω hz
  have hζ0 := riemannZeta_one_add_two_mul_ne_zero hω
  have hlin := one_add_ofReal_add_ne_zero hω hz
  have hω0 := one_add_ofReal_ne_zero hω
  field_simp

/-! ### Card `(23b)`: the exact centered Hardy decomposition -/

private theorem schur_decomposition_algebra {A B C D E F z : ℂ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hE : E ≠ 0) (hF : F ≠ 0) (hz : z ≠ 0) :
    (D / (E * B) - 1 / (F * z * A)) / (A / C)
      = (C / (A * B)) * (D / E - (1 / F) / z) + (1 / F) * ((C / (A * B) - C / (A * A)) / z) := by
  field_simp
  ring

theorem mobiusCausalMultiplier_div_total {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re)
    (hz0 : z ≠ 0) :
    mobiusCausalMultiplier ω z / ((squarefreeMobiusTotal (1 + 2 * ω) : ℝ) : ℂ)
      = mobiusSchurTransfer (1 + 2 * ω) z * floorRemainderTransform ω z +
        (1 / ((1 : ℂ) + (ω : ℂ))) *
          ((mobiusSchurTransfer (1 + 2 * ω) z - mobiusSchurTransfer (1 + 2 * ω) 0) / z) := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  have hcast : ((1 + 2 * ω : ℝ) : ℂ) = 1 + 2 * (ω : ℂ) := by push_cast; ring
  have hτ := mobiusSchurTransfer_eq_zetaRatio ha hz
  have hτ0 := mobiusSchurTransfer_eq_zetaRatio ha (by simp : (0 : ℝ) ≤ (0 : ℂ).re)
  have hZ := ofReal_squarefreeMobiusTotal_eq_zetaRatio ha
  have hζs : riemannZeta (((1 + 2 * ω : ℝ) : ℂ)) ≠ 0 := by
    rw [hcast]; exact riemannZeta_one_add_two_mul_ne_zero hω
  have hζsz : riemannZeta ((((1 + 2 * ω : ℝ) : ℂ)) + z) ≠ 0 := by
    rw [hcast]
    exact riemannZeta_one_add_two_mul_add_ne_zero hω hz
  have hζ2 : riemannZeta (2 * ((1 + 2 * ω : ℝ) : ℂ)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    linarith
  have hlin := one_add_ofReal_add_ne_zero hω hz
  have hω0 := one_add_ofReal_ne_zero hω
  rw [hcast] at hτ hτ0 hZ hζs hζsz hζ2
  rw [add_zero] at hτ0
  rw [hτ, hτ0, hZ, mobiusCausalMultiplier, floorRemainderTransform]
  exact schur_decomposition_algebra hζs hζsz hζ2 hlin hω0 hz0


/-! ### Cards `(23d)`--`(23g)`: the centered boundary difference quotient -/

private theorem gap_algebra {A B C w F : ℂ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hw : w ≠ 0) (hF : F ≠ 0) :
    (F * (A / C)⁻¹) * ((1 / F) * ((B⁻¹ - A⁻¹) / w))
      = (C / (A * B) - C / (A * A)) / w := by
  field_simp

/-- Card `(23d)`: the signed channel gap `g_omega`. -/
def signedChannelGap (ω : ℝ) (t : ℝ) : ℂ :=
  Set.indicator (Set.Ioi (0 : ℝ))
    (fun s : ℝ => -((((squarefreeMobiusTotal (1 + 2 * ω) : ℝ) : ℂ))⁻¹ *
      mobiusWeightedTail (1 + 2 * ω) s)) t

theorem signedChannelGap_eq_smul {ω : ℝ} (hω : 0 < ω) (t : ℝ) :
    signedChannelGap ω t =
      ((((1 + ω : ℝ)) : ℂ) * (((squarefreeMobiusTotal (1 + 2 * ω) : ℝ) : ℂ))⁻¹) *
        centeredMertensVector ω t := by
  have hω0 : ((1 : ℂ) + (ω : ℂ)) ≠ 0 := one_add_ofReal_ne_zero hω
  rcases le_or_gt t 0 with ht | ht
  · rw [signedChannelGap, Set.indicator_of_notMem (by simpa using ht),
      centeredMertensVector_of_nonpos ω ht, mul_zero]
  · rw [signedChannelGap, Set.indicator_of_mem (Set.mem_Ioi.mpr ht),
      centeredMertensVector_eq_tail hω ht]
    push_cast
    field_simp

/-- **Card `(23e)`.**  The gap has the centered Schur difference quotient as transform. -/
theorem laplaceBoundary_signedChannelGap {ω : ℝ} (hω : 0 < ω) {y : ℝ} (hy : y ≠ 0) :
    laplaceBoundary (signedChannelGap ω) y
      = (mobiusSchurTransfer (1 + 2 * ω) ((y : ℂ) * Complex.I) -
          mobiusSchurTransfer (1 + 2 * ω) 0) / ((y : ℂ) * Complex.I) := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  have hcast : ((1 + 2 * ω : ℝ) : ℂ) = 1 + 2 * (ω : ℂ) := by push_cast; ring
  have hyre : (0 : ℝ) ≤ ((y : ℂ) * Complex.I).re := by simp
  have hτ := mobiusSchurTransfer_eq_zetaRatio ha hyre
  have hτ0 := mobiusSchurTransfer_eq_zetaRatio ha (by simp : (0 : ℝ) ≤ (0 : ℂ).re)
  have hZ := ofReal_squarefreeMobiusTotal_eq_zetaRatio ha
  have hζs : riemannZeta (((1 + 2 * ω : ℝ) : ℂ)) ≠ 0 := by
    rw [hcast]; exact riemannZeta_one_add_two_mul_ne_zero hω
  have hζsz : riemannZeta ((((1 + 2 * ω : ℝ) : ℂ)) + (y : ℂ) * Complex.I) ≠ 0 := by
    rw [hcast]
    exact riemannZeta_one_add_two_mul_add_ne_zero hω hyre
  have hζ2 : riemannZeta (2 * ((1 + 2 * ω : ℝ) : ℂ)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    linarith
  have hyI : (y : ℂ) * Complex.I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hy
  have hω0 : ((1 : ℂ) + (ω : ℂ)) ≠ 0 := one_add_ofReal_ne_zero hω
  have hZ0 : (((squarefreeMobiusTotal (1 + 2 * ω) : ℝ) : ℂ)) ≠ 0 := by
    have := squarefreeMobiusTotal_pos ha
    exact_mod_cast ne_of_gt this
  have hfun : signedChannelGap ω
      = fun t : ℝ => ((((1 + ω : ℝ)) : ℂ) *
        (((squarefreeMobiusTotal (1 + 2 * ω) : ℝ) : ℂ))⁻¹) * centeredMertensVector ω t := by
    funext t
    exact signedChannelGap_eq_smul hω t
  rw [hfun, laplaceBoundary]
  rw [show (∫ u : ℝ, Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ)) *
      (((((1 + ω : ℝ)) : ℂ) * (((squarefreeMobiusTotal (1 + 2 * ω) : ℝ) : ℂ))⁻¹) *
        centeredMertensVector ω u))
      = ((((1 + ω : ℝ)) : ℂ) * (((squarefreeMobiusTotal (1 + 2 * ω) : ℝ) : ℂ))⁻¹) *
        ∫ u : ℝ, Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ)) * centeredMertensVector ω u from by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [] with u
    ring]
  have hL : (∫ u : ℝ, Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ)) *
      centeredMertensVector ω u) = centeredSchurQuotient ω ((y : ℂ) * Complex.I) :=
    laplaceBoundary_centeredMertensVector hω hy
  rw [hL, centeredSchurQuotient, hτ, hτ0, add_zero, hZ]
  rw [hcast] at hζs hζsz hζ2
  push_cast
  exact gap_algebra hζs hζsz hζ2 hyI hω0


/-- The channel tail probability `P_omega{log d > t}`. -/
def channelTailProbAtom (ω : ℝ) (d : ℕ) (t : ℝ) : ℝ :=
  Set.indicator (Set.Ioo (0 : ℝ) (Real.log d))
    (fun _ : ℝ => squarefreeMobiusProbability (1 + 2 * ω) d) t

def channelTailProb (ω : ℝ) (t : ℝ) : ℝ := ∑' d : ℕ, channelTailProbAtom ω d t

theorem channelTailProbAtom_nonneg {ω : ℝ} (hω : 0 < ω) (d : ℕ) (t : ℝ) :
    0 ≤ channelTailProbAtom ω d t := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  rw [channelTailProbAtom]
  by_cases h : t ∈ Set.Ioo (0 : ℝ) (Real.log d)
  · rw [Set.indicator_of_mem h]
    exact squarefreeMobiusProbability_nonneg ha d
  · rw [Set.indicator_of_notMem h]

theorem channelTailProbAtom_le {ω : ℝ} (hω : 0 < ω) (d : ℕ) (t : ℝ) :
    channelTailProbAtom ω d t ≤ squarefreeMobiusProbability (1 + 2 * ω) d := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  rw [channelTailProbAtom]
  by_cases h : t ∈ Set.Ioo (0 : ℝ) (Real.log d)
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    exact squarefreeMobiusProbability_nonneg ha d

theorem summable_channelTailProbAtom {ω : ℝ} (hω : 0 < ω) (t : ℝ) :
    Summable (fun d : ℕ => channelTailProbAtom ω d t) := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  exact Summable.of_nonneg_of_le (channelTailProbAtom_nonneg hω · t)
    (channelTailProbAtom_le hω · t) (summable_squarefreeMobiusProbability ha)

theorem channelTailProb_le_one {ω : ℝ} (hω : 0 < ω) (t : ℝ) : channelTailProb ω t ≤ 1 := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  calc channelTailProb ω t
      ≤ ∑' d : ℕ, squarefreeMobiusProbability (1 + 2 * ω) d :=
        Summable.tsum_le_tsum (channelTailProbAtom_le hω · t)
          (summable_channelTailProbAtom hω t) (summable_squarefreeMobiusProbability ha)
    _ = 1 := tsum_squarefreeMobiusProbability ha

theorem channelTailProb_nonneg {ω : ℝ} (hω : 0 < ω) (t : ℝ) : 0 ≤ channelTailProb ω t :=
  tsum_nonneg (channelTailProbAtom_nonneg hω · t)

/-- **Card `(23f)`.**  The gap is dominated by the channel tail probability. -/
theorem norm_signedChannelGap_le {ω : ℝ} (hω : 0 < ω) (t : ℝ) :
    ‖signedChannelGap ω t‖ ≤ channelTailProb ω t := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  have hZpos : 0 < squarefreeMobiusTotal (1 + 2 * ω) := squarefreeMobiusTotal_pos ha
  rcases le_or_gt t 0 with ht | ht
  · rw [signedChannelGap, Set.indicator_of_notMem (by simpa using ht), norm_zero]
    exact channelTailProb_nonneg hω t
  · rw [signedChannelGap, Set.indicator_of_mem (Set.mem_Ioi.mpr ht), norm_neg, norm_mul]
    have hZnorm : ‖(((squarefreeMobiusTotal (1 + 2 * ω) : ℝ) : ℂ))⁻¹‖
        = (squarefreeMobiusTotal (1 + 2 * ω))⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZpos]
    have hterm : ∀ d : ℕ,
        ‖(if Real.exp t < (d : ℝ) then mobiusRealWeight (1 + 2 * ω) d else 0)‖
          ≤ squarefreeMobiusTotal (1 + 2 * ω) * channelTailProbAtom ω d t := by
      intro d
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst d
        have hne : ¬ (Real.exp t < ((0 : ℕ) : ℝ)) := by
          simp only [Nat.cast_zero, not_lt]
          exact (Real.exp_pos t).le
        rw [if_neg hne, norm_zero]
        have := channelTailProbAtom_nonneg hω 0 t
        positivity
      · have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
        have hiff : Real.exp t < (d : ℝ) ↔ t ∈ Set.Ioo (0 : ℝ) (Real.log d) := by
          constructor
          · intro h
            exact ⟨ht, (Real.lt_log_iff_exp_lt hdpos).mpr h⟩
          · rintro ⟨-, h2⟩
            exact (Real.lt_log_iff_exp_lt hdpos).mp h2
        by_cases hc : Real.exp t < (d : ℝ)
        · rw [if_pos hc, channelTailProbAtom, Set.indicator_of_mem (hiff.mp hc),
            squarefreeMobiusProbability]
          have hZc : squarefreeMobiusTotal (1 + 2 * ω) *
              (squarefreeMobiusMass (1 + 2 * ω) d / squarefreeMobiusTotal (1 + 2 * ω))
              = squarefreeMobiusMass (1 + 2 * ω) d := by
            field_simp
          rw [hZc, mobiusRealWeight, if_neg hd.ne', norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hdpos.le _),
            squarefreeMobiusMass]
          by_cases hsq : Squarefree d
          · rw [if_pos hsq]
            have hmu : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
              rw [Complex.norm_intCast]
              have := ArithmeticFunction.abs_moebius_le_one (n := d)
              exact_mod_cast this
            nlinarith [Real.rpow_nonneg hdpos.le (-(1 + 2 * ω)),
              norm_nonneg (((ArithmeticFunction.moebius d : ℤ) : ℂ))]
          · rw [if_neg hsq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
            simp
        · rw [if_neg hc, norm_zero, channelTailProbAtom,
            Set.indicator_of_notMem (fun hcon => hc (hiff.mpr hcon))]
          simp
    have hsum := summable_mobiusWeightedTailTerm ha t
    have hbound : ‖mobiusWeightedTail (1 + 2 * ω) t‖
        ≤ squarefreeMobiusTotal (1 + 2 * ω) * channelTailProb ω t := by
      calc ‖mobiusWeightedTail (1 + 2 * ω) t‖
          ≤ ∑' d : ℕ, ‖(if Real.exp t < (d : ℝ) then mobiusRealWeight (1 + 2 * ω) d else 0)‖ :=
            norm_tsum_le_tsum_norm hsum.norm
        _ ≤ ∑' d : ℕ, squarefreeMobiusTotal (1 + 2 * ω) * channelTailProbAtom ω d t :=
            Summable.tsum_le_tsum hterm hsum.norm
              ((summable_channelTailProbAtom hω t).mul_left _)
        _ = squarefreeMobiusTotal (1 + 2 * ω) * channelTailProb ω t := tsum_mul_left
    rw [hZnorm]
    rw [inv_mul_le_iff₀ hZpos]
    exact hbound

/-- **Card `(23f)`, squared form.** -/
theorem norm_sq_signedChannelGap_le {ω : ℝ} (hω : 0 < ω) (t : ℝ) :
    ‖signedChannelGap ω t‖ ^ 2 ≤ channelTailProb ω t := by
  have h1 := norm_signedChannelGap_le hω t
  have h2 := channelTailProb_le_one hω t
  have h3 : (0 : ℝ) ≤ ‖signedChannelGap ω t‖ := norm_nonneg _
  nlinarith


theorem measurable_channelTailProbAtom (ω : ℝ) (d : ℕ) :
    Measurable (channelTailProbAtom ω d) := by
  exact measurable_const.indicator measurableSet_Ioo

theorem integrable_channelTailProbAtom (ω : ℝ) (d : ℕ) :
    Integrable (channelTailProbAtom ω d) := by
  have hdef : channelTailProbAtom ω d
      = Set.indicator (Set.Ioo (0 : ℝ) (Real.log d))
        (fun _ : ℝ => squarefreeMobiusProbability (1 + 2 * ω) d) := rfl
  rw [hdef]
  refine (integrable_indicator_iff measurableSet_Ioo).mpr ?_
  exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)

theorem integral_channelTailProbAtom (ω : ℝ) (d : ℕ) :
    (∫ t : ℝ, channelTailProbAtom ω d t)
      = squarefreeMobiusProbability (1 + 2 * ω) d * Real.log d := by
  have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have hdef : channelTailProbAtom ω d
      = Set.indicator (Set.Ioo (0 : ℝ) (Real.log d))
        (fun _ : ℝ => squarefreeMobiusProbability (1 + 2 * ω) d) := rfl
  rw [hdef, integral_indicator measurableSet_Ioo, setIntegral_const,
    measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hlog, smul_eq_mul]
  ring

theorem measurable_signedChannelGap {ω : ℝ} (hω : 0 < ω) :
    Measurable (signedChannelGap ω) := by
  have hfun : signedChannelGap ω
      = fun t : ℝ => ((((1 + ω : ℝ)) : ℂ) *
        (((squarefreeMobiusTotal (1 + 2 * ω) : ℝ) : ℂ))⁻¹) * centeredMertensVector ω t :=
    funext (signedChannelGap_eq_smul hω)
  rw [hfun]
  exact (measurable_centeredMertensVector ω).const_mul _

/-- **Card `(23g)`.**  The gap energy is at most the logarithmic channel moment. -/
theorem lintegral_norm_sq_signedChannelGap_le {ω : ℝ} (hω : 0 < ω) :
    (∫⁻ t : ℝ, ‖signedChannelGap ω t‖ₑ ^ 2)
      ≤ ENNReal.ofReal (squarefreeMobiusLogMoment 1 (1 + 2 * ω)) := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  have hlog := summable_squarefreeMobiusLogMoment 1 ha
  simp only [pow_one] at hlog
  have hstep1 : (∫⁻ t : ℝ, ‖signedChannelGap ω t‖ₑ ^ 2)
      ≤ ∫⁻ t : ℝ, ∑' d : ℕ, ENNReal.ofReal (channelTailProbAtom ω d t) := by
    refine lintegral_mono fun t => ?_
    have h1 : ‖signedChannelGap ω t‖ₑ ^ 2 = ENNReal.ofReal (‖signedChannelGap ω t‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have h2 : ENNReal.ofReal (channelTailProb ω t)
        = ∑' d : ℕ, ENNReal.ofReal (channelTailProbAtom ω d t) :=
      ENNReal.ofReal_tsum_of_nonneg (channelTailProbAtom_nonneg hω · t)
        (summable_channelTailProbAtom hω t)
    rw [h1, ← h2]
    exact ENNReal.ofReal_le_ofReal (norm_sq_signedChannelGap_le hω t)
  have hstep2 : (∫⁻ t : ℝ, ∑' d : ℕ, ENNReal.ofReal (channelTailProbAtom ω d t))
      = ∑' d : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal (channelTailProbAtom ω d t) :=
    lintegral_tsum fun d =>
      (ENNReal.measurable_ofReal.comp (measurable_channelTailProbAtom ω d)).aemeasurable
  have hstep3 : ∀ d : ℕ, (∫⁻ t : ℝ, ENNReal.ofReal (channelTailProbAtom ω d t))
      = ENNReal.ofReal (squarefreeMobiusProbability (1 + 2 * ω) d * Real.log d) := by
    intro d
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_channelTailProbAtom ω d)
      (Filter.Eventually.of_forall (channelTailProbAtom_nonneg hω d)),
      integral_channelTailProbAtom ω d]
  have hstep4 : (∑' d : ℕ,
      ENNReal.ofReal (squarefreeMobiusProbability (1 + 2 * ω) d * Real.log d))
      = ENNReal.ofReal (squarefreeMobiusLogMoment 1 (1 + 2 * ω)) := by
    rw [squarefreeMobiusLogMoment]
    rw [show (∑' n : ℕ, squarefreeMobiusProbability (1 + 2 * ω) n * Real.log n ^ 1)
        = ∑' n : ℕ, squarefreeMobiusProbability (1 + 2 * ω) n * Real.log n from
      tsum_congr fun n : ℕ => by rw [pow_one]]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun d => by
      have h1 := squarefreeMobiusProbability_nonneg ha d
      have h2 := Real.log_natCast_nonneg d
      positivity) hlog).symm
  calc (∫⁻ t : ℝ, ‖signedChannelGap ω t‖ₑ ^ 2)
      ≤ ∫⁻ t : ℝ, ∑' d : ℕ, ENNReal.ofReal (channelTailProbAtom ω d t) := hstep1
    _ = ∑' d : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal (channelTailProbAtom ω d t) := hstep2
    _ = ∑' d : ℕ,
          ENNReal.ofReal (squarefreeMobiusProbability (1 + 2 * ω) d * Real.log d) :=
        tsum_congr hstep3
    _ = ENNReal.ofReal (squarefreeMobiusLogMoment 1 (1 + 2 * ω)) := hstep4

/-- **Card `(23g)`, real form.** -/
theorem integral_norm_sq_signedChannelGap_le {ω : ℝ} (hω : 0 < ω) :
    (∫ t : ℝ, ‖signedChannelGap ω t‖ ^ 2) ≤ squarefreeMobiusLogMoment 1 (1 + 2 * ω) := by
  have ha : (1 : ℝ) < 1 + 2 * ω := by linarith
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ‖signedChannelGap ω t‖ ^ 2) volume :=
    ((measurable_signedChannelGap hω).norm.pow_const 2).aestronglyMeasurable
  have hmem : MemLp (signedChannelGap ω) 2 volume :=
    memLp_two_of_lintegral_lt_top (measurable_signedChannelGap hω).aestronglyMeasurable
      (lt_of_le_of_lt (lintegral_norm_sq_signedChannelGap_le hω) ENNReal.ofReal_lt_top)
  have hint : Integrable (fun t : ℝ => ‖signedChannelGap ω t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      (measurable_signedChannelGap hω).aestronglyMeasurable).mp hmem
  have hlt := lintegral_norm_sq_signedChannelGap_le hω
  rw [lintegral_enorm_sq_eq_ofReal hint] at hlt
  have hmoment_nonneg : 0 ≤ squarefreeMobiusLogMoment 1 (1 + 2 * ω) := by
    rw [squarefreeMobiusLogMoment]
    refine tsum_nonneg fun n => ?_
    have h1 := squarefreeMobiusProbability_nonneg ha n
    have h2 := Real.log_natCast_nonneg n
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hmoment_nonneg).mp hlt


/-! ### Card `(18)`: the transform of the shifted channel feature -/

/-- Card `(16)`: the coupled channel feature `B_{omega,d} = V_{log d} a_omega - c_omega`. -/
def shiftedChannelFeature (ω : ℝ) (d : ℕ) (t : ℝ) : ℂ :=
  Set.indicator (Set.Ici (Real.log d))
      (fun s : ℝ => ((powerSumBoundary ω (s - Real.log d) : ℝ) : ℂ)) t -
    (1 / ((1 : ℂ) + (ω : ℂ)))

theorem integral_Ioi_cexp_neg_mul' {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Set.Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ))) = z⁻¹ := by
  rw [← GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul hz]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring_nf

theorem integrableOn_cexp_neg_mul' {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ))) (Set.Ioi (0 : ℝ)) volume := by
  have h := GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul hz
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  ring_nf

/-- **Card `(18)`.**  The transform of the coupled channel feature. -/
theorem causalLaplace_shiftedChannelFeature {ω : ℝ} (homega : 0 ≤ ω) {z : ℂ} (hz : 0 < z.re)
    {d : ℕ} (hd : 0 < d) :
    (∫ t in Set.Ioi (0 : ℝ), shiftedChannelFeature ω d t * Complex.exp (-z * (t : ℂ)))
      = channelFeatureTransform ω d z := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hintA : IntegrableOn (fun t : ℝ => ((powerSumBoundary ω t : ℝ) : ℂ) *
      Complex.exp (-z * (t : ℂ))) (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_powerSumBoundary_damped homega hz
  have hshiftInt : IntegrableOn (fun t : ℝ =>
      Set.indicator (Set.Ici (Real.log d))
        (fun s : ℝ => ((powerSumBoundary ω (s - Real.log d) : ℝ) : ℂ)) t *
        Complex.exp (-z * (t : ℂ))) (Set.Ioi (0 : ℝ)) volume := by
    refine Integrable.mono' (integrableOn_cexp_neg_mul' hz).norm ?_ ?_
    · refine (Measurable.mul ?_ (by fun_prop)).aestronglyMeasurable
      refine Measurable.indicator ?_ measurableSet_Ici
      exact Complex.measurable_ofReal.comp
        ((measurable_powerSumBoundary ω).comp (measurable_id.sub_const _))
    · filter_upwards [] with t
      rw [norm_mul]
      by_cases hmem : t ∈ Set.Ici (Real.log d)
      · rw [Set.indicator_of_mem hmem, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (powerSumBoundary_nonneg ω _)]
        have h1 := powerSumBoundary_le_one homega (t - Real.log d)
        have h2 : (0 : ℝ) ≤ ‖Complex.exp (-z * (t : ℂ))‖ := norm_nonneg _
        nlinarith [powerSumBoundary_nonneg ω (t - Real.log d)]
      · rw [Set.indicator_of_notMem hmem, norm_zero, zero_mul]
        exact norm_nonneg _
  have hconstInt : IntegrableOn (fun t : ℝ => (1 / ((1 : ℂ) + (ω : ℂ))) *
      Complex.exp (-z * (t : ℂ))) (Set.Ioi (0 : ℝ)) volume :=
    (integrableOn_cexp_neg_mul' hz).const_mul _
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), shiftedChannelFeature ω d t * Complex.exp (-z * (t : ℂ)))
      = (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator (Set.Ici (Real.log d))
            (fun s : ℝ => ((powerSumBoundary ω (s - Real.log d) : ℝ) : ℂ)) t *
            Complex.exp (-z * (t : ℂ))) -
        ∫ t in Set.Ioi (0 : ℝ), (1 / ((1 : ℂ) + (ω : ℂ))) * Complex.exp (-z * (t : ℂ)) := by
    rw [← integral_sub hshiftInt hconstInt]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [shiftedChannelFeature]
    ring
  rw [hsplit, causalLaplace_indicator_shift hlog hintA, integral_const_mul,
    integral_Ioi_cexp_neg_mul' hz]
  have hA : (∫ s in Set.Ioi (0 : ℝ), ((powerSumBoundary ω s : ℝ) : ℂ) *
      Complex.exp (-z * (s : ℂ))) = riemannZeta (1 + z) / (1 + (ω : ℂ) + z) := by
    have h := causalLaplace_powerSumBoundary (omega := ω) (z := z) homega hz
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [hA]
  have hcpow : Complex.exp (-z * ((Real.log d : ℝ) : ℂ)) = ((d : ℂ)) ^ (-z) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hd.ne' : (d : ℂ) ≠ 0)]
    congr 1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (le_of_lt hdpos)]
    ring
  rw [hcpow, channelFeatureTransform]
  ring

end RHTower


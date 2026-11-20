import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.AUniformVarianceBoundForTranslatedMoebiusSections
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The squarefree finite part at almost every prime twist

Summability of the window variances makes the squared errors summable
for almost every twist. On dyadic windows this holds simultaneously for
all integer length exponents, even with prescribed moving starting heights.
Every positive length exponent has the same squarefree finite part.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
open Filter Topology Finset Complex MeasureTheory
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open _root_.RHTower _root_.RHTower.Sieve
noncomputable section

/-- Excess over the squarefree diagonal per unit length in a sharp window. -/
def meanSquareError (N : ℕ) (A L : ℝ) (x : GaugeTorus) :=
  centeredMoment (volume.restrict (Set.Ioc A (A+L))) N x/L

private theorem integrated_error_sq {L : ℝ} (hL : 0 < L) (A : ℝ) (N : ℕ) :
    ∫ x, (meanSquareError N A L x)^2 ∂gaugeHaar ≤ 6*(1+Real.log ((N:ℝ)+1))^4/L := by
  let ν := volume.restrict (Set.Ioc A (A+L))
  have he := sharp_interval_moebius_variance N (A:=A) (B:=A+L) (le_add_of_nonneg_right hL.le)
  rw [add_sub_cancel_left] at he
  simp only [meanSquareError,div_pow,integral_div]
  exact (div_le_div_of_nonneg_right he (sq_nonneg L)).trans_eq (by field_simp [hL.ne'])

/-- The variance cost controls the entire series of squared errors for
any prescribed sequence of positive length windows and sharp cutoffs. -/
theorem ae_summable_translated_errors (N : ℕ → ℕ) (A L : ℕ → ℝ) (hL : ∀ j, 0 < L j)
    (hs : Summable fun j => (1+Real.log ((N j:ℝ)+1))^4/L j) :
    ∀ᵐ x ∂gaugeHaar, Summable fun j => (meanSquareError (N j) (A j) (L j) x)^2 := by
  let F (j : ℕ) (x : GaugeTorus) := (meanSquareError (N j) (A j) (L j) x)^2
  let B (j : ℕ) := 6*(1+Real.log ((N j:ℝ)+1))^4/L j
  have hc (j : ℕ) : Continuous (F j) :=
    ((continuous_centeredMoment _ (N j)).div_const (L j)).pow 2
  have hi (j : ℕ) : Integrable (F j) gaugeHaar :=
    (hc j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn (j : ℕ) : ∫ x, ‖F j x‖ ∂gaugeHaar ≤ B j := by
    have he (x : GaugeTorus) : ‖F j x‖ = F j x :=
      (Real.norm_eq_abs _).trans (abs_of_nonneg (sq_nonneg _))
    simp_rw [he]
    exact integrated_error_sq (hL j) (A j) (N j)
  have hb : Summable B := (hs.mul_left 6).congr fun j => by dsimp only [B]; ring
  have hsfin : ∫⁻ x, ∑' j, ‖F j x‖ₑ ∂gaugeHaar ≠ ⊤ := by
    rw [lintegral_tsum (fun j => (hi j).aestronglyMeasurable.enorm)]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r:=∑' j, B j)) ?_
    have hB (j : ℕ) : 0 ≤ B j :=
      div_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by
        have := Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg (N j) (α:=ℝ)))
        linarith) 4)) (hL j).le
    rw [ENNReal.ofReal_tsum_of_nonneg hB hb]
    apply ENNReal.tsum_le_tsum
    intro j
    rw [←ofReal_integral_norm_eq_lintegral_enorm (hi j)]
    exact ENNReal.ofReal_le_ofReal (hn j)
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun j => (hi j).aestronglyMeasurable.enorm) hsfin] with x hx
  apply Summable.of_norm
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hx.ne)

private theorem dyadic_cost (r : ℕ) :
    Summable fun j : ℕ => (1+Real.log (((2^(r*j):ℕ):ℝ)+1))^4/(2:ℝ)^j := by
  let f (n : ℕ) : ℝ := (n:ℝ)^4 * (1/2:ℝ)^n
  have hf : Summable f := summable_pow_mul_geometric_of_norm_lt_one 4
    (by norm_num [Real.norm_eq_abs] : ‖(1/2:ℝ)‖ < 1)
  have hbase : Summable (fun n : ℕ => f (n+1)) := (summable_nat_add_iff 1).mpr hf
  have hs : Summable fun j : ℕ => ((j:ℝ)+1)^4/(2:ℝ)^j := (hbase.mul_left 2).congr fun j => by
    change 2 * (((j+1 : ℕ) : ℝ)^4 * (1/2 : ℝ)^(j+1)) = ((j:ℝ)+1)^4/(2:ℝ)^j
    rw [Nat.cast_succ,pow_succ (1/2 : ℝ) j,div_pow,one_pow]
    ring
  let C := (2*((r:ℝ)+1))^4
  apply Summable.of_nonneg_of_le (fun j => div_nonneg (by positivity) (by positivity)) _ (hs.mul_left C)
  intro j
  have htwo : 1 ≤ (2:ℝ)^(r*j) := one_le_pow₀ (by norm_num)
  have harg : (2:ℝ)^(r*j)+1 ≤ 2^(r*j+1) := by rw [pow_succ]; linarith only [htwo]
  have hlog := Real.log_le_log (by positivity) harg
  rw [Real.log_pow] at hlog
  have hl₂ : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hb : 1+Real.log ((2:ℝ)^(r*j)+1) ≤ 2*((r:ℝ)+1)*((j:ℝ)+1) := by
    have h := mul_le_mul_of_nonneg_left hl₂ (Nat.cast_nonneg (r*j+1) (α:=ℝ))
    push_cast at h hlog
    nlinarith only [h,hlog,Nat.cast_nonneg (α:=ℝ) r,Nat.cast_nonneg (α:=ℝ) j,
      mul_nonneg (Nat.cast_nonneg r (α:=ℝ)) (Nat.cast_nonneg j (α:=ℝ))]
  have hpow := pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_nonneg (by linarith only [htwo]))) hb 4
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  exact (div_le_div_of_nonneg_right hpow (by positivity)).trans_eq (by dsimp only [C]; rw [mul_pow]; ring)

/-- Almost surely, every fixed polynomial cutoff has vanishing absolute
error from the diagonal on these dyadic windows. The starting heights may
depend on both the exponent and the window. -/
theorem ae_dyadic_polynomial_diagonal (A : ℕ → ℕ → ℝ) :
    ∀ᵐ x ∂gaugeHaar, ∀ r : ℕ, Tendsto (fun j : ℕ => meanSquareError (2^(r*j)) (A r j) ((2:ℝ)^j) x)
      atTop (𝓝 0) := by
  rw [ae_all_iff]
  intro r
  filter_upwards [ae_summable_translated_errors (fun j => 2^(r*j)) (A r) (fun j => (2:ℝ)^j)
    (fun _ => by positivity) (dyadic_cost r)] with x hx
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hx.tendsto_atTop_zero
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq_eq_abs,sub_zero,Real.norm_eq_abs] using h

/-- At every positive polynomial length the critical-line mean minus its
logarithmic main term converges to the ordinary squarefree harmonic constant. -/
theorem ae_dyadic_moebius_finite_part (A : ℕ → ℕ → ℝ) :
    ∀ᵐ x ∂gaugeHaar, ∀ r : ℕ, 0 < r →
      Tendsto (fun j : ℕ => moment (volume.restrict (Set.Ioc (A r j) (A r j+(2:ℝ)^j)))
        (fun n => (MoebiusGram.coeff n:ℂ)) (Icc 1 (2^(r*j))) x/(2:ℝ)^j -
          squarefreeDensity*Real.log (2^(r*j):ℝ)) atTop (𝓝 squarefreeHarmonicConstant) := by
  filter_upwards [ae_dyadic_polynomial_diagonal A] with x hx r hr
  let M (j : ℕ) := 2^(r*j)
  have hM : Tendsto (fun j : ℕ => ((M j:ℕ):ℝ)) atTop atTop := by
    have hb : (1:ℝ) < 2^r := one_lt_pow₀ (by norm_num) hr.ne'
    have ht := tendsto_pow_atTop_atTop_of_one_lt hb
    exact ht.congr fun j => by simp only [M,Nat.cast_pow,Nat.cast_ofNat,pow_mul]
  have hsmall := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp hM).const_mul 12
  rw [mul_zero] at hsmall
  have hD : Tendsto (fun j => harmonicMoebiusDiagonal (M j)-squarefreeDensity*Real.log (M j)) atTop
      (𝓝 squarefreeHarmonicConstant) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ hsmall
    exact .of_forall fun j => by
      rw [Real.norm_eq_abs]
      exact squarefree_harmonic_finite_part (X:=(M j:ℝ)) (by exact_mod_cast
        (show 1 ≤ M j from Nat.one_le_pow _ _ (by norm_num)))
  have hh := (hx r).add hD
  rw [zero_add] at hh
  apply hh.congr
  intro j
  have hp : 0 < (2:ℝ)^j := by positivity
  simp only [meanSquareError,centeredMoment,measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le
    (le_add_of_nonneg_right hp.le),add_sub_cancel_left,M,Nat.cast_pow,Nat.cast_ofNat]
  field_simp [hp.ne']
  <;> ring

end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments

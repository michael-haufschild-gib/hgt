import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourMomentTail

/-!
# An aperture-free seam split for the eighth section

The aperture weight `r sinh(ar)` compares with `r²` uniformly in the aperture: since
`sinh(ay)/y` is nondecreasing, `r sinh(ar) ≤ c_a r²` below a split radius `r_c` and
`r sinh(ar) ≥ c_a r²` above it, with `c_a = sinh(a r_c)/r_c`. Hence if the odd native fibre
form is nonnegative beyond `r_c`, and the `r²`-weighted bulk beyond `r_c` pays for the
`r²`-weighted negative part of the fibre below `r_c`, the odd block of the eighth section is
nonnegative at every critical aperture, and `I_7(a) ≥ 0` for every `0 < a < 1/2`.
-/

open MeasureTheory Set Matrix
namespace RHTower
noncomputable section

/-- The odd native fibre form at center `r/2`. -/
def thetaCuspOddFourFibreForm (r : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * thetaCuspNativeSignedJet (r/2) (2 * (i.val + j.val) + 2)

/-- The seam-split integrand: the negative part below `r_c`, the full form above. -/
def thetaCuspOddFourSeamSplitIntegrand (rc r : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  r ^ 2 * (if r ≤ rc then min (thetaCuspOddFourFibreForm r v) 0
    else thetaCuspOddFourFibreForm r v)

/-- `sinh(y)/y` is nondecreasing: `Y sinh y ≤ y sinh Y` for `0 ≤ y ≤ Y`. -/
theorem mul_sinh_le_mul_sinh_of_le {y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y) :
    Y * Real.sinh y ≤ y * Real.sinh Y := by
  set d := Y - y with hd
  have hd0 : 0 ≤ d := by linarith
  have hY : Y = y + d := by ring
  rw [hY, Real.sinh_add]
  have h1 : d ≤ Real.sinh d := Real.self_le_sinh_iff.mpr hd0
  have h2 := sinh_le_mul_cosh hy
  have h3 : 1 ≤ Real.cosh d := Real.one_le_cosh d
  have hs : 0 ≤ Real.sinh y := Real.sinh_nonneg_iff.mpr hy
  nlinarith [mul_nonneg hy hs, mul_nonneg (mul_nonneg hy hs) (sub_nonneg.mpr h3),
    mul_le_mul h2 h1 hd0 (by nlinarith [Real.cosh_pos y]), mul_nonneg hs hd0]

/-- The aperture weight against `r²`, below and above the split radius. -/
theorem aperture_weight_le {a r rc : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hrc : r ≤ rc) :
    rc * Real.sinh (a * r) ≤ r * Real.sinh (a * rc) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  have h := mul_sinh_le_mul_sinh_of_le (mul_nonneg ha hr) (mul_le_mul_of_nonneg_left hrc ha)
  nlinarith

theorem continuous_thetaCuspOddFourFibreForm (v : Fin 4 → ℝ) :
    Continuous fun r => thetaCuspOddFourFibreForm r v := by
  unfold thetaCuspOddFourFibreForm
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_thetaCuspNativeSignedJet_half _)

theorem integrableOn_thetaCuspOddFourSeamSplitIntegrand (rc : ℝ) (v : Fin 4 → ℝ) :
    IntegrableOn (fun r => thetaCuspOddFourSeamSplitIntegrand rc r v) (Ioi 0) := by
  set D : ℝ := ∑ i : Fin 4, ∑ j : Fin 4, |v i * v j| *
    thetaCuspNativeJetDecayConstant (2 * (i.val + j.val) + 2)
  have hexp : IntegrableOn (fun r : ℝ => r ^ 2 * Real.exp (-r)) (Ioi 0) := by
    have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2) (b := 1)
      (by norm_num) le_rfl one_pos
    refine hb.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul, one_mul]
    norm_cast
  have hf := continuous_thetaCuspOddFourFibreForm v
  have hmeas : AEStronglyMeasurable (fun r => thetaCuspOddFourSeamSplitIntegrand rc r v)
      (volume.restrict (Ioi 0)) := by
    unfold thetaCuspOddFourSeamSplitIntegrand
    refine ((continuous_pow 2).measurable.mul (Measurable.ite measurableSet_Iic
      (hf.measurable.min measurable_const) hf.measurable)).aestronglyMeasurable
  refine (hexp.const_mul D).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := le_of_lt hr
  have hform : |thetaCuspOddFourFibreForm r v| ≤ D * Real.exp (-r) := by
    unfold thetaCuspOddFourFibreForm
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [D, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_thetaCuspNativeSignedJet_half_le _ hr0) (abs_nonneg _)
  have hpiece : |if r ≤ rc then min (thetaCuspOddFourFibreForm r v) 0
      else thetaCuspOddFourFibreForm r v| ≤ |thetaCuspOddFourFibreForm r v| := by
    split_ifs
    · rw [abs_le]
      constructor
      · exact le_min (neg_abs_le _) (neg_nonpos.mpr (abs_nonneg _))
      · exact (min_le_right _ _).trans (abs_nonneg _)
    · exact le_rfl
  rw [Real.norm_eq_abs, thetaCuspOddFourSeamSplitIntegrand, abs_mul, abs_of_nonneg (by positivity)]
  calc r ^ 2 * |_| ≤ r ^ 2 * (D * Real.exp (-r)) :=
        mul_le_mul_of_nonneg_left (hpiece.trans hform) (by positivity)
    _ = D * (r ^ 2 * Real.exp (-r)) := by ring

/-- **Aperture-free seam split.** If the odd fibre form is nonnegative beyond `r_c` and the
`r²`-weighted bulk pays for the `r²`-weighted negative part below `r_c`, the odd block of the
eighth section is nonnegative at every critical aperture. -/
theorem thetaCuspCenterMixedOddFour_posSemidef_of_seamSplit {rc : ℝ} (hrc : 0 < rc)
    (hbulk : ∀ r : ℝ, rc < r → ∀ v : Fin 4 → ℝ, 0 ≤ thetaCuspOddFourFibreForm r v)
    (hsplit : ∀ v : Fin 4 → ℝ,
      0 ≤ ∫ r in Ioi 0, thetaCuspOddFourSeamSplitIntegrand rc r v)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedOddFour a).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (thetaCuspCenterMixedOddFour_isHermitian a) fun v => ?_
  have hint (i j : Fin 4) := (integrableOn_thetaCuspWeightedNativeSignedJet ha0.le ha
    (2 * (i.val + j.val) + 2)).const_mul (v i * v j)
  -- the odd form as one aperture integral of the fibre form
  have hform : star v ⬝ᵥ (thetaCuspCenterMixedOddFour a *ᵥ v) =
      ∫ r in Ioi 0, r * Real.sinh (a * r) * thetaCuspOddFourFibreForm r v := by
    have hpoint (r : ℝ) : r * Real.sinh (a * r) * thetaCuspOddFourFibreForm r v =
        ∑ i : Fin 4, ∑ j : Fin 4, (v i * v j) *
          (r * Real.sinh (a * r) * thetaCuspNativeSignedJet (r/2) (2 * (i.val + j.val) + 2)) := by
      simp only [thetaCuspOddFourFibreForm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hpoint]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hint i j))]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, thetaCuspCenterMixedOddFour, star_trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet ha0.le ha]
    ring
  rw [hform]
  set c := Real.sinh (a * rc) / rc with hc
  have hc0 : 0 < c := div_pos (Real.sinh_pos_iff.mpr (mul_pos ha0 hrc)) hrc
  have hlhs : IntegrableOn (fun r => r * Real.sinh (a * r) * thetaCuspOddFourFibreForm r v)
      (Ioi 0) := by
    refine (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hint i j))).congr ?_
    filter_upwards with r
    simp only [thetaCuspOddFourFibreForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hrhs := (integrableOn_thetaCuspOddFourSeamSplitIntegrand rc v).const_mul c
  have hmono : ∫ r in Ioi 0, c * thetaCuspOddFourSeamSplitIntegrand rc r v ≤
      ∫ r in Ioi 0, r * Real.sinh (a * r) * thetaCuspOddFourFibreForm r v := by
    refine setIntegral_mono_on hrhs hlhs measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    have hw0 : 0 ≤ r * Real.sinh (a * r) :=
      mul_nonneg hr0.le (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0.le hr0.le))
    unfold thetaCuspOddFourSeamSplitIntegrand
    split_ifs with hle
    · -- below the split radius the weight is at most `c r²`
      have hw : r * Real.sinh (a * r) ≤ c * r ^ 2 := by
        have h := aperture_weight_le ha0.le hr0.le hle
        rw [hc, div_mul_eq_mul_div, le_div_iff₀ hrc]
        nlinarith
      have hm : min (thetaCuspOddFourFibreForm r v) 0 ≤ 0 := min_le_right _ _
      have hf : min (thetaCuspOddFourFibreForm r v) 0 ≤ thetaCuspOddFourFibreForm r v :=
        min_le_left _ _
      calc c * (r ^ 2 * min (thetaCuspOddFourFibreForm r v) 0)
          = (c * r ^ 2) * min (thetaCuspOddFourFibreForm r v) 0 := by ring
        _ ≤ (r * Real.sinh (a * r)) * min (thetaCuspOddFourFibreForm r v) 0 :=
            mul_le_mul_of_nonpos_right hw hm
        _ ≤ r * Real.sinh (a * r) * thetaCuspOddFourFibreForm r v :=
            mul_le_mul_of_nonneg_left hf hw0
    · -- above it the weight is at least `c r²` and the fibre is nonnegative
      push Not at hle
      have hw : c * r ^ 2 ≤ r * Real.sinh (a * r) := by
        have h := aperture_weight_le ha0.le hrc.le hle.le
        rw [hc, div_mul_eq_mul_div, div_le_iff₀ hrc]
        nlinarith
      have hf := hbulk r hle v
      calc c * (r ^ 2 * thetaCuspOddFourFibreForm r v)
          = (c * r ^ 2) * thetaCuspOddFourFibreForm r v := by ring
        _ ≤ r * Real.sinh (a * r) * thetaCuspOddFourFibreForm r v :=
            mul_le_mul_of_nonneg_right hw hf
  rw [integral_const_mul] at hmono
  exact (mul_nonneg hc0.le (hsplit v)).trans hmono

/-- **The eighth section from the seam split.** Under the aperture-free seam split, the
successor integral `I_7(a)` is nonnegative at every critical aperture `0 < a < 1/2`. -/
theorem thetaCuspNativeSuccessorIntegral_seven_nonneg_of_seamSplit {rc : ℝ} (hrc : 0 < rc)
    (hbulk : ∀ r : ℝ, rc < r → ∀ v : Fin 4 → ℝ, 0 ≤ thetaCuspOddFourFibreForm r v)
    (hsplit : ∀ v : Fin 4 → ℝ,
      0 ≤ ∫ r in Ioi 0, thetaCuspOddFourSeamSplitIntegrand rc r v)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    0 ≤ ∫ r : ℝ in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSuccessorSource a 7 (r/2) :=
  (thetaCuspCenterMixedSignedHankel_succ_posSemidef_iff_nativeIntegral_nonneg ha0.le ha
    (thetaCuspCenterMixedSignedHankel_seven_posDef ha0 ha)).mp
    (thetaCuspCenterMixedSignedHankel_eight_posSemidef_of_oddFour ha0 ha
      (thetaCuspCenterMixedOddFour_posSemidef_of_seamSplit hrc hbulk hsplit ha0 ha))


/-! ### The same split at every rank -/

/-- The native signed fibre form of rank `N` at center `r/2`. -/
def thetaCuspNativeFibreForm {N : ℕ} (r : ℝ) (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, v i * v j * thetaCuspNativeSignedJet (r/2) (i.val + j.val)

/-- The rank-`N` seam-split integrand. -/
def thetaCuspNativeSeamSplitIntegrand {N : ℕ} (rc r : ℝ) (v : Fin N → ℝ) : ℝ :=
  r ^ 2 * (if r ≤ rc then min (thetaCuspNativeFibreForm r v) 0 else thetaCuspNativeFibreForm r v)

theorem integrableOn_thetaCuspNativeSeamSplitIntegrand {N : ℕ} (rc : ℝ) (v : Fin N → ℝ) :
    IntegrableOn (fun r => thetaCuspNativeSeamSplitIntegrand rc r v) (Ioi 0) := by
  set D : ℝ := ∑ i : Fin N, ∑ j : Fin N, |v i * v j| *
    thetaCuspNativeJetDecayConstant (i.val + j.val)
  have hexp : IntegrableOn (fun r : ℝ => r ^ 2 * Real.exp (-r)) (Ioi 0) := by
    have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2) (b := 1)
      (by norm_num) le_rfl one_pos
    refine hb.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul, one_mul]
    norm_cast
  have hf : Continuous fun r => thetaCuspNativeFibreForm r v := by
    unfold thetaCuspNativeFibreForm
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_thetaCuspNativeSignedJet_half _)
  have hmeas : AEStronglyMeasurable (fun r => thetaCuspNativeSeamSplitIntegrand rc r v)
      (volume.restrict (Ioi 0)) := by
    unfold thetaCuspNativeSeamSplitIntegrand
    exact ((continuous_pow 2).measurable.mul (Measurable.ite measurableSet_Iic
      (hf.measurable.min measurable_const) hf.measurable)).aestronglyMeasurable
  refine (hexp.const_mul D).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := le_of_lt hr
  have hform : |thetaCuspNativeFibreForm r v| ≤ D * Real.exp (-r) := by
    unfold thetaCuspNativeFibreForm
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [D, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_thetaCuspNativeSignedJet_half_le _ hr0) (abs_nonneg _)
  have hpiece : |if r ≤ rc then min (thetaCuspNativeFibreForm r v) 0
      else thetaCuspNativeFibreForm r v| ≤ |thetaCuspNativeFibreForm r v| := by
    split_ifs
    · rw [abs_le]
      exact ⟨le_min (neg_abs_le _) (neg_nonpos.mpr (abs_nonneg _)),
        (min_le_right _ _).trans (abs_nonneg _)⟩
    · exact le_rfl
  rw [Real.norm_eq_abs, thetaCuspNativeSeamSplitIntegrand, abs_mul, abs_of_nonneg (by positivity)]
  calc r ^ 2 * |_| ≤ r ^ 2 * (D * Real.exp (-r)) :=
        mul_le_mul_of_nonneg_left (hpiece.trans hform) (by positivity)
    _ = D * (r ^ 2 * Real.exp (-r)) := by ring

/-- **Aperture-free seam split at every rank.** If the rank-`N` native fibre form is
nonnegative beyond `r_c` and its `r²`-weighted bulk beyond `r_c` pays for its `r²`-weighted
negative part below `r_c`, then the rank-`N` signed section is nonnegative at every critical
aperture. -/
theorem thetaCuspCenterMixedSignedHankel_posSemidef_of_seamSplit {N : ℕ} {rc : ℝ} (hrc : 0 < rc)
    (hbulk : ∀ r : ℝ, rc < r → ∀ v : Fin N → ℝ, 0 ≤ thetaCuspNativeFibreForm r v)
    (hsplit : ∀ v : Fin N → ℝ,
      0 ≤ ∫ r in Ioi 0, thetaCuspNativeSeamSplitIntegrand rc r v)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedSignedHankel a N).PosSemidef := by
  have hHerm : (thetaCuspCenterMixedSignedHankel a N).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspCenterMixedSignedHankel, add_comm]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun v => ?_
  have hint (i j : Fin N) := (integrableOn_thetaCuspWeightedNativeSignedJet ha0.le ha
    (i.val + j.val)).const_mul (v i * v j)
  have hform : star v ⬝ᵥ (thetaCuspCenterMixedSignedHankel a N *ᵥ v) =
      ∫ r in Ioi 0, r * Real.sinh (a * r) * thetaCuspNativeFibreForm r v := by
    have hpoint (r : ℝ) : r * Real.sinh (a * r) * thetaCuspNativeFibreForm r v =
        ∑ i : Fin N, ∑ j : Fin N, (v i * v j) *
          (r * Real.sinh (a * r) * thetaCuspNativeSignedJet (r/2) (i.val + j.val)) := by
      simp only [thetaCuspNativeFibreForm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hpoint]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hint i j))]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, thetaCuspCenterMixedSignedHankel,
      star_trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet ha0.le ha]
    ring
  rw [hform]
  set c := Real.sinh (a * rc) / rc with hc
  have hc0 : 0 < c := div_pos (Real.sinh_pos_iff.mpr (mul_pos ha0 hrc)) hrc
  have hlhs : IntegrableOn (fun r => r * Real.sinh (a * r) * thetaCuspNativeFibreForm r v)
      (Ioi 0) := by
    refine (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hint i j))).congr ?_
    filter_upwards with r
    simp only [thetaCuspNativeFibreForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hrhs := (integrableOn_thetaCuspNativeSeamSplitIntegrand rc v).const_mul c
  have hmono : ∫ r in Ioi 0, c * thetaCuspNativeSeamSplitIntegrand rc r v ≤
      ∫ r in Ioi 0, r * Real.sinh (a * r) * thetaCuspNativeFibreForm r v := by
    refine setIntegral_mono_on hrhs hlhs measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    have hw0 : 0 ≤ r * Real.sinh (a * r) :=
      mul_nonneg hr0.le (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0.le hr0.le))
    unfold thetaCuspNativeSeamSplitIntegrand
    split_ifs with hle
    · have hw : r * Real.sinh (a * r) ≤ c * r ^ 2 := by
        have h := aperture_weight_le ha0.le hr0.le hle
        rw [hc, div_mul_eq_mul_div, le_div_iff₀ hrc]
        nlinarith
      calc c * (r ^ 2 * min (thetaCuspNativeFibreForm r v) 0)
          = (c * r ^ 2) * min (thetaCuspNativeFibreForm r v) 0 := by ring
        _ ≤ (r * Real.sinh (a * r)) * min (thetaCuspNativeFibreForm r v) 0 :=
            mul_le_mul_of_nonpos_right hw (min_le_right _ _)
        _ ≤ r * Real.sinh (a * r) * thetaCuspNativeFibreForm r v :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hw0
    · push Not at hle
      have hw : c * r ^ 2 ≤ r * Real.sinh (a * r) := by
        have h := aperture_weight_le ha0.le hrc.le hle.le
        rw [hc, div_mul_eq_mul_div, div_le_iff₀ hrc]
        nlinarith
      calc c * (r ^ 2 * thetaCuspNativeFibreForm r v)
          = (c * r ^ 2) * thetaCuspNativeFibreForm r v := by ring
        _ ≤ r * Real.sinh (a * r) * thetaCuspNativeFibreForm r v :=
            mul_le_mul_of_nonneg_right hw (hbulk r hle v)
  rw [integral_const_mul] at hmono
  exact (mul_nonneg hc0.le (hsplit v)).trans hmono

end
end RHTower

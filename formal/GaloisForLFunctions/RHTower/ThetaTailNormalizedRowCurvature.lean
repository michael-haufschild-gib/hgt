import GaloisForLFunctions.RHTower.ThetaTailCauchyFirstCorrection

/-!
# Opposite curvature signs in the same normalized theta-tail row

At every fixed positive spacing, the literal source-normalized kernel has
a negative centered midpoint gap and a positive right-shifted midpoint gap
on every sufficiently far translated row. Thus neither convexity nor
concavity of individual rows supplies the affine-interpolation exclusion
needed by the higher Schur residual argument.
-/

open Filter Topology Set
noncomputable section
namespace RHTower.ThetaTailRow
open ThetaTailCauchy ThetaTailFirstCorrection

/-- The literal tail kernel normalized by its two endpoint sources. -/
def normalized (x y : ℝ) : ℝ :=
  thetaTailFirstMomentKernel x y / (thetaCuspFullSource x * thetaCuspFullSource y)

/-- Centered midpoint gap in the row based at `r`. -/
def centeredGap (h r : ℝ) : ℝ :=
  normalized r (r-h) + normalized r (r+h) - 2 * normalized r r

/-- Right-shifted midpoint gap in that same row. -/
def rightGap (h r : ℝ) : ℝ :=
  normalized r r + normalized r (r+2*h) - 2 * normalized r (r+h)

private theorem normalized_exp (x y r : ℝ) :
    normalized (x+r) (y+r) / Real.exp (-2*r) =
      thetaTailFirstMomentKernel (x+r) (y+r) / baseNormalizer x y r := by
  simp only [normalized, baseNormalizer, pairProduct, div_div]
  congr 1
  ring

private theorem affine_error_limit (x y : ℝ) :
    Tendsto (fun r : ℝ => normalized (x+r) (y+r) / Real.exp (-2*r) -
      (2*r+x+y)/(2*pairScale x y)) atTop (𝓝 0) := by
  have he : Tendsto (fun r : ℝ => r * Real.exp (-2*r)) atTop (𝓝 0) := by
    simpa [Real.rpow_one, mul_comm, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) 2 (by norm_num)
  have hl := (kernel_first_correction_limit x y).mul he
  simp only [mul_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [normalized_exp]
  exact div_mul_cancel₀ _ (mul_ne_zero hr.ne' (Real.exp_ne_zero _))

private theorem leading_limit (x y : ℝ) :
    Tendsto (fun r : ℝ => normalized (x+r) (y+r) / (r*Real.exp (-2*r)))
      atTop (𝓝 (1/pairScale x y)) := by
  unfold pairScale
  apply (kernel_normalized_limit x y).congr'
  apply Eventually.of_forall
  intro r
  simp only [normalized, normalizer, div_div]
  congr 1
  ring

/-- The clock term survives the exact cancellation of the centered Cauchy terms. -/
theorem centeredGap_limit (h : ℝ) :
    Tendsto (fun r : ℝ => centeredGap h r / Real.exp (-2*r)) atTop
      (𝓝 (h*(1-Real.exp (2*h))/(2*Real.pi*(1+Real.exp (2*h))))) := by
  have hl := ((affine_error_limit 0 (-h)).add (affine_error_limit 0 h)).sub
    ((affine_error_limit 0 0).const_mul 2)
  simp only [zero_add, mul_zero, sub_zero] at hl
  have hc := hl.add_const (h*(1-Real.exp (2*h))/(2*Real.pi*(1+Real.exp (2*h))))
  simp only [zero_add] at hc
  apply hc.congr'
  apply Eventually.of_forall
  intro r
  have he : Real.exp (2*(-h)) = (Real.exp (2*h))⁻¹ := by
    rw [show 2*(-h) = -(2*h) by ring, Real.exp_neg]
  dsimp [centeredGap, pairScale]
  simp only [mul_zero, Real.exp_zero, he, neg_add_eq_sub]
  field_simp [Real.pi_ne_zero, Real.exp_ne_zero,
    show 1 + Real.exp (2*h) ≠ 0 by positivity,
    show 1 + (Real.exp (2*h))⁻¹ ≠ 0 by positivity]
  ring_nf

/-- The adjacent right-hand gap retains a strictly positive leading Cauchy term. -/
theorem rightGap_limit (h : ℝ) :
    Tendsto (fun r : ℝ => rightGap h r / (r*Real.exp (-2*r))) atTop
      (𝓝 ((Real.exp (2*h)-1)^3 /
        (2*Real.pi*(1+Real.exp (2*h))*(1+(Real.exp (2*h))^2)))) := by
  have hl := ((leading_limit 0 0).add (leading_limit 0 (2*h))).sub
    ((leading_limit 0 h).const_mul 2)
  have he : Real.exp (2*(2*h)) = (Real.exp (2*h))^2 := by
    rw [show 2*(2*h) = 2*h+2*h by ring, Real.exp_add, pow_two]
  have hc : 1/pairScale 0 0 + 1/pairScale 0 (2*h) - 2*(1/pairScale 0 h) =
      (Real.exp (2*h)-1)^3 /
        (2*Real.pi*(1+Real.exp (2*h))*(1+(Real.exp (2*h))^2)) := by
    simp only [pairScale, mul_zero, Real.exp_zero, he]
    field_simp [Real.pi_ne_zero,
      show 1 + Real.exp (2*h) ≠ 0 by positivity,
      show 1 + (Real.exp (2*h))^2 ≠ 0 by positivity]
    ring_nf
  rw [hc] at hl
  convert hl using 1
  funext r
  dsimp [rightGap]
  simp only [zero_add]
  rw [show 2*h+r = r+2*h by ring, show h+r = r+h by ring]
  ring

/-- Both strict discrete curvature orientations occur in the same positive tail row. -/
theorem opposite_gaps_eventually {h : ℝ} (hh : 0 < h) :
    ∀ᶠ r : ℝ in atTop, 0 < r-h ∧ centeredGap h r < 0 ∧ 0 < rightGap h r := by
  have hv : 1 < Real.exp (2*h) := Real.one_lt_exp_iff.mpr (by positivity)
  have hc : h*(1-Real.exp (2*h))/(2*Real.pi*(1+Real.exp (2*h))) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hh (sub_neg.mpr hv)) (by positivity)
  have hd : 0 < (Real.exp (2*h)-1)^3 /
      (2*Real.pi*(1+Real.exp (2*h))*(1+(Real.exp (2*h))^2)) := by
    exact div_pos (pow_pos (sub_pos.mpr hv) _) (by positivity)
  filter_upwards [(centeredGap_limit h).eventually (eventually_lt_nhds hc),
    (rightGap_limit h).eventually (eventually_gt_nhds hd),
    eventually_gt_atTop h] with r hr hs hhr
  have hr0 : 0 < r := hh.trans hhr
  refine ⟨sub_pos.mpr hhr, ?_, ?_⟩
  · simpa using (div_lt_iff₀ (Real.exp_pos (-2*r))).mp hr
  · simpa using (lt_div_iff₀ (mul_pos hr0 (Real.exp_pos (-2*r)))).mp hs

/-- Neither uniform row-convexity nor uniform row-concavity survives on positive tails. -/
theorem row_neither_convex_nor_concave_eventually {h : ℝ} (hh : 0 < h) :
    ∀ᶠ r : ℝ in atTop,
      ¬ ConvexOn ℝ (Icc (r-h) (r+2*h)) (normalized r) ∧
      ¬ ConcaveOn ℝ (Icc (r-h) (r+2*h)) (normalized r) := by
  filter_upwards [opposite_gaps_eventually hh] with r hr
  constructor
  · intro hc
    rcases hc with ⟨_, hc⟩
    have hm := hc (x := r-h) (y := r+h)
      (show r-h ∈ Icc (r-h) (r+2*h) by constructor <;> linarith)
      (show r+h ∈ Icc (r-h) (r+2*h) by constructor <;> linarith)
      (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hm
    rw [show (1/2 : ℝ)*(r-h)+(1/2)*(r+h) = r by ring] at hm
    dsimp [centeredGap] at hr
    linarith [hr.2.1]
  · intro hc
    rcases hc with ⟨_, hc⟩
    have hm := hc (x := r) (y := r+2*h)
      (show r ∈ Icc (r-h) (r+2*h) by constructor <;> linarith)
      (show r+2*h ∈ Icc (r-h) (r+2*h) by constructor <;> linarith)
      (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hm
    rw [show (1/2 : ℝ)*r+(1/2)*(r+2*h) = r+h by ring] at hm
    dsimp [rightGap] at hr
    linarith [hr.2.2]

end RHTower.ThetaTailRow

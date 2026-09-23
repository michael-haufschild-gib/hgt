import GaloisForLFunctions.RHTower.XiMassPrimeSemigroupHighPass

/-!
# Pointwise no-go for the canonical Xi mass-semigroup high-pass

The canonical aperture high-pass is an integrated object.  Its kernel is not pointwise small:
on the whole negative-frequency cone `x < -3/4`, the fixed-mass arm grows exponentially with
height while the co-moving arm tends to zero.  Consequently the kernel norm tends to infinity.

The final theorem strengthens this to an almost-everywhere obstruction.  No finite real-valued
function can dominate the kernel simultaneously at every height, even almost everywhere.  In
particular, dominated-convergence or absolute-value arguments cannot prove boundedness of the
integrated prime high-pass.  Any successful argument must exploit cancellation after integration.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The mass root conserves the product of its real and imaginary coordinates. -/
theorem xiMassAnalyticSqrt_re_mul_im (a : ℝ) (z : ℂ) :
    (xiMassAnalyticSqrt a z).re * (xiMassAnalyticSqrt a z).im = z.re * z.im := by
  have him := congrArg Complex.im (xiMassAnalyticSqrt_sq a z)
  rw [xiMassAnalyticArg_im] at him
  simp only [pow_two, Complex.mul_im] at him
  nlinarith

/-- Bottom point at frequency `x` on the common depth `3/4`. -/
def xiMassHighPassBottomPoint (x : ℝ) : ℂ :=
  (x : ℂ) - ((3 / 4 : ℝ) : ℂ) * I

@[simp] theorem xiMassHighPassBottomPoint_re (x : ℝ) :
    (xiMassHighPassBottomPoint x).re = x := by
  norm_num [xiMassHighPassBottomPoint, Complex.mul_re]

@[simp] theorem xiMassHighPassBottomPoint_im (x : ℝ) :
    (xiMassHighPassBottomPoint x).im = -(3 / 4) := by
  norm_num [xiMassHighPassBottomPoint, Complex.mul_im]

theorem xiMassHighPassBottomPoint_mem_strip {a x : ℝ} (ha : 3 / 4 < a) :
    xiMassHighPassBottomPoint x ∈ xiMassStrip a := by
  change |(xiMassHighPassBottomPoint x).im| < a
  norm_num
  exact ha

/-- Conservation law on the depth-`3/4` bottom line. -/
theorem xiMassHighPassBottomRoot_charge (a x : ℝ) :
    (xiMassAnalyticSqrt a (xiMassHighPassBottomPoint x)).re *
        (xiMassAnalyticSqrt a (xiMassHighPassBottomPoint x)).im = -3 * x / 4 := by
  rw [xiMassAnalyticSqrt_re_mul_im]
  norm_num
  ring

/-- On the negative-frequency cone `x < -3/4`, every legal mass root lies strictly above its
mass aperture. -/
theorem xiMassHighPassBottomRoot_re_gt_mass {a x : ℝ}
    (ha : 3 / 4 < a) (hx : x < -(3 / 4)) :
    a < (xiMassAnalyticSqrt a (xiMassHighPassBottomPoint x)).re := by
  have ha0 : 0 < a := by linarith
  have hre : 0 < (xiMassAnalyticSqrt a (xiMassHighPassBottomPoint x)).re :=
    xiMassAnalyticSqrt_re_pos ha0 (xiMassHighPassBottomPoint_mem_strip ha)
  have hsq := xiMassAnalyticSqrt_re_sq a (xiMassHighPassBottomPoint x)
  have hnorm := Complex.re_le_norm (xiMassAnalyticArg a (xiMassHighPassBottomPoint x))
  have harg := xiMassAnalyticArg_re a (xiMassHighPassBottomPoint x)
  rw [xiMassHighPassBottomPoint_re, xiMassHighPassBottomPoint_im] at harg
  have hxabs : (3 / 4 : ℝ) < |x| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hxsq : (3 / 4 : ℝ) ^ (2 : ℕ) < x ^ (2 : ℕ) := by
    rw [sq_lt_sq]
    norm_num
    exact hxabs
  nlinarith

theorem xiMassHighPassBottomRoot_im_pos {a x : ℝ}
    (ha : 3 / 4 < a) (hx : x < -(3 / 4)) :
    0 < (xiMassAnalyticSqrt a (xiMassHighPassBottomPoint x)).im := by
  have hre := xiMassHighPassBottomRoot_re_gt_mass ha hx
  have hcharge := xiMassHighPassBottomRoot_charge a x
  have ha0 : 0 < a := by linarith
  nlinarith

/-- Exact modulus of the bottom mass test at a real frequency. -/
theorem norm_xiMassBottomTest_negative_frequency (a σ u x : ℝ) :
    ‖xiMassBottomTest a (3 / 4) ((σ : ℂ) + u * I) x‖ =
      Real.exp (-σ * (xiMassAnalyticSqrt a (xiMassHighPassBottomPoint x)).re +
        u * (xiMassAnalyticSqrt a (xiMassHighPassBottomPoint x)).im) := by
  rw [xiMassBottomTest, xiMassAnalyticTest, Complex.norm_exp]
  congr 1
  norm_num [xiMassHighPassBottomPoint, Complex.mul_re]

/-- The co-moving arm has an explicit decaying bound throughout the negative-frequency cone. -/
theorem norm_xiMassBottomTest_comoving_negative_frequency_le {σ u x : ℝ}
    (hσ : 0 < σ) (hu : 0 ≤ u) (hx : x < -(3 / 4)) :
    ‖xiMassBottomTest (xiComovingMass u) (3 / 4)
        ((σ : ℂ) + u * I) x‖ ≤
      Real.exp (-σ * (u + 2) - 3 * x / 4) := by
  have hA : xiComovingMass u = u + 2 := by
    rw [xiComovingMass, abs_of_nonneg hu]
  have hAprobe : 3 / 4 < xiComovingMass u := by
    rw [hA]
    linarith
  have hre := xiMassHighPassBottomRoot_re_gt_mass hAprobe hx
  have him := xiMassHighPassBottomRoot_im_pos hAprobe hx
  have hcharge := xiMassHighPassBottomRoot_charge (xiComovingMass u) x
  have hmass :
      u + 2 <
        (xiMassAnalyticSqrt (xiComovingMass u) (xiMassHighPassBottomPoint x)).re := by
    rw [← hA]
    exact hre
  have hcross :
      u * (xiMassAnalyticSqrt (xiComovingMass u) (xiMassHighPassBottomPoint x)).im ≤
        -3 * x / 4 := by
    calc
      u * (xiMassAnalyticSqrt (xiComovingMass u) (xiMassHighPassBottomPoint x)).im ≤
          (xiMassAnalyticSqrt (xiComovingMass u) (xiMassHighPassBottomPoint x)).re *
            (xiMassAnalyticSqrt (xiComovingMass u) (xiMassHighPassBottomPoint x)).im := by
              apply mul_le_mul_of_nonneg_right
              · exact le_of_lt (lt_trans (by linarith) hmass)
              · exact him.le
      _ = -3 * x / 4 := hcharge
  rw [norm_xiMassBottomTest_negative_frequency]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_pos hσ (sub_pos.mpr hmass)]

/-- The co-moving arm vanishes at every fixed frequency in the negative cone. -/
theorem tendsto_norm_xiMassBottomTest_comoving_negative_frequency_zero
    {σ x : ℝ} (hσ : 0 < σ) (hx : x < -(3 / 4)) :
    Tendsto
      (fun u : ℝ => ‖xiMassBottomTest (xiComovingMass u) (3 / 4)
        ((σ : ℂ) + u * I) x‖) atTop (𝓝 0) := by
  have hlinear : Tendsto (fun u : ℝ => -σ * u) atTop atBot := by
    simpa using tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hσ)
  have hshift : Tendsto (fun u : ℝ => -σ * (u + 2) - 3 * x / 4) atTop atBot := by
    convert tendsto_atBot_add_const_right atTop (-2 * σ - 3 * x / 4) hlinear using 1
    funext u
    ring
  have hmajor : Tendsto (fun u : ℝ => Real.exp (-σ * (u + 2) - 3 * x / 4))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hshift
  refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  exact norm_xiMassBottomTest_comoving_negative_frequency_le hσ hu hx

/-- The fixed-mass arm diverges at every fixed frequency in the negative cone. -/
theorem tendsto_norm_xiMassBottomTest_fixed_negative_frequency_atTop
    {σ x : ℝ} (hx : x < -(3 / 4)) :
    Tendsto (fun u : ℝ => ‖xiMassBottomTest 1 (3 / 4) ((σ : ℂ) + u * I) x‖)
      atTop atTop := by
  have him : 0 < (xiMassAnalyticSqrt 1 (xiMassHighPassBottomPoint x)).im :=
    xiMassHighPassBottomRoot_im_pos (by norm_num) hx
  have hlinear : Tendsto
      (fun u : ℝ => u * (xiMassAnalyticSqrt 1 (xiMassHighPassBottomPoint x)).im)
      atTop atTop := by
    simpa [mul_comm] using tendsto_id.const_mul_atTop him
  have hshift : Tendsto
      (fun u : ℝ =>
        -σ * (xiMassAnalyticSqrt 1 (xiMassHighPassBottomPoint x)).re +
          u * (xiMassAnalyticSqrt 1 (xiMassHighPassBottomPoint x)).im)
      atTop atTop := by
    convert tendsto_atTop_add_const_right atTop
      (-σ * (xiMassAnalyticSqrt 1 (xiMassHighPassBottomPoint x)).re) hlinear using 1
    funext u
    ring
  rw [show (fun u : ℝ => ‖xiMassBottomTest 1 (3 / 4) ((σ : ℂ) + u * I) x‖) =
      fun u : ℝ => Real.exp
        (-σ * (xiMassAnalyticSqrt 1 (xiMassHighPassBottomPoint x)).re +
          u * (xiMassAnalyticSqrt 1 (xiMassHighPassBottomPoint x)).im) by
    funext u
    exact norm_xiMassBottomTest_negative_frequency 1 σ u x]
  exact Real.tendsto_exp_atTop.comp hshift

/-- **Negative-frequency no-go.** On every `x < -3/4`, the canonical semigroup high-pass kernel
diverges pointwise. -/
theorem tendsto_norm_xiMassSemigroupHighPassKernel_negative_frequency_atTop
    {σ x : ℝ} (hσ : 0 < σ) (hx : x < -(3 / 4)) :
    Tendsto
      (fun u : ℝ =>
        ‖xiMassBottomTest 1 (3 / 4) ((σ : ℂ) + u * I) x -
          xiMassBottomTest (xiComovingMass u) (3 / 4)
            ((σ : ℂ) + u * I) x‖)
      atTop atTop := by
  have hfixed := tendsto_norm_xiMassBottomTest_fixed_negative_frequency_atTop
    (σ := σ) hx
  have hmoving := tendsto_norm_xiMassBottomTest_comoving_negative_frequency_zero hσ hx
  have hminor : Tendsto
      (fun u : ℝ =>
        ‖xiMassBottomTest 1 (3 / 4) ((σ : ℂ) + u * I) x‖ -
          ‖xiMassBottomTest (xiComovingMass u) (3 / 4)
            ((σ : ℂ) + u * I) x‖)
      atTop atTop := by
    simpa [sub_eq_add_neg] using hfixed.atTop_add hmoving.neg
  refine tendsto_atTop_mono' atTop ?_ hminor
  exact Eventually.of_forall fun u => norm_sub_norm_le _ _

/-- No finite function can dominate the canonical high-pass kernel for every height, even almost
everywhere.  Hence no uniform `L¹` majorant exists. -/
theorem not_exists_ae_uniform_majorant_xiMassSemigroupHighPassKernel
    {σ : ℝ} (hσ : 0 < σ) :
    ¬ ∃ g : ℝ → ℝ, ∀ u : ℝ, ∀ᵐ x : ℝ ∂MeasureTheory.volume,
      ‖xiMassBottomTest 1 (3 / 4) ((σ : ℂ) + u * I) x -
        xiMassBottomTest (xiComovingMass u) (3 / 4)
          ((σ : ℂ) + u * I) x‖ ≤ g x := by
  rintro ⟨g, hg⟩
  have hall : ∀ᵐ x : ℝ ∂MeasureTheory.volume, ∀ n : ℕ,
      ‖xiMassBottomTest 1 (3 / 4) ((σ : ℂ) + (n : ℝ) * I) x -
        xiMassBottomTest (xiComovingMass (n : ℝ)) (3 / 4)
          ((σ : ℂ) + (n : ℝ) * I) x‖ ≤ g x := by
    rw [MeasureTheory.ae_all_iff]
    exact fun n => hg n
  let J : Set ℝ := Set.Icc (-2) (-1)
  have hJmeas : MeasurableSet J := measurableSet_Icc
  have hJvol : MeasureTheory.volume J ≠ 0 := by
    rw [show J = Set.Icc (-2 : ℝ) (-1) by rfl, Real.volume_Icc]
    norm_num
  have hrestrict : MeasureTheory.volume.restrict J ≠ 0 := by
    intro hzero
    have huniv := congrArg (fun μ : MeasureTheory.Measure ℝ => μ Set.univ) hzero
    rw [MeasureTheory.Measure.restrict_apply_univ J] at huniv
    exact hJvol (by simpa using huniv)
  letI : NeZero (MeasureTheory.volume.restrict J) := ⟨hrestrict⟩
  have hboth : ∀ᵐ x : ℝ ∂MeasureTheory.volume.restrict J,
      x ∈ J ∧ ∀ n : ℕ,
        ‖xiMassBottomTest 1 (3 / 4) ((σ : ℂ) + (n : ℝ) * I) x -
          xiMassBottomTest (xiComovingMass (n : ℝ)) (3 / 4)
            ((σ : ℂ) + (n : ℝ) * I) x‖ ≤ g x := by
    filter_upwards [MeasureTheory.ae_restrict_mem hJmeas,
      MeasureTheory.ae_restrict_of_ae hall] with x hxJ hx
    exact ⟨hxJ, hx⟩
  rcases hboth.exists with ⟨x, hxJ, hxall⟩
  have hxneg : x < -(3 / 4) := by
    have hxle : x ≤ -1 := hxJ.2
    linarith
  have hdiv : Tendsto
      (fun n : ℕ =>
        ‖xiMassBottomTest 1 (3 / 4) ((σ : ℂ) + (n : ℝ) * I) x -
          xiMassBottomTest (xiComovingMass (n : ℝ)) (3 / 4)
            ((σ : ℂ) + (n : ℝ) * I) x‖)
      atTop atTop :=
    (tendsto_norm_xiMassSemigroupHighPassKernel_negative_frequency_atTop hσ hxneg).comp
      tendsto_natCast_atTop_atTop
  have hlarge := hdiv.eventually_ge_atTop (g x + 1)
  rcases hlarge.exists with ⟨n, hn⟩
  linarith [hxall n]

end

end RHTower

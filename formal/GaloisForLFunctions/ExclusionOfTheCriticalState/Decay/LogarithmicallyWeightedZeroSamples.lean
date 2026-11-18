import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.TheLeftTraceUpToTheRateOfTheZeros

/-!
# Square summability at the zeros with the zero-density weight

Multiplying the translated Laplace transform by an analytic logarithm transfers
the second and third boundary logarithmic moments to the zero samples. The
resulting square mass pays the logarithmic cost of a Lorentzian row of zeros.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem summable_strip_samples {g : ℂ → ℂ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ g z)
    {B : ℝ} (hB : 0 ≤ B) (hg : ∀ z : ℂ, 0 ≤ z.re → ‖g z‖ ≤ B*(1+‖z‖)^2)
    (ht : Integrable fun t : ℝ => ‖g ((t:ℂ)*I)‖^2)
    (hl : Integrable fun t : ℝ => (xiLineTwoLogDerivConstant + Real.log (|t|+4)) *
      ‖g ((t:ℂ)*I)‖^2) :
    Summable fun q : XiZeroCopy => ‖g (centredZero q + 1)‖^2 := by
  let w := fun q => centredZero q + 1
  let J := fun (q : XiZeroCopy) (t : ℝ) =>
    halfPlanePoisson (w q).re (t-(w q).im) * ‖g ((t:ℂ)*I)‖^2
  have hstrip (q) : 1/2 ≤ (w q).re ∧ (w q).re ≤ 3/2 := by
    have hh := abs_lt.mp (abs_re_centredZero_lt q)
    simp only [w, Complex.add_re, Complex.one_re]
    constructor <;> linarith
  have hpos (q) : 0 < (w q).re := lt_of_lt_of_le (by norm_num) (hstrip q).1
  have hi (q) : Integrable (J q) := integrable_halfPlanePoisson_sub_mul ht (hpos q) _
  have hp (q) : ‖g (w q)‖^2 ≤ ∫ t, J q t := by
    simpa only [Complex.re_add_im, J] using
      norm_sq_le_poisson_of_quadratic_bound hdiff hB hg ht _ (hpos q) (w q).im
  apply summable_of_sum_le (fun _ => sq_nonneg _)
    (c := ∫ t : ℝ, (16/Real.pi)*((xiLineTwoLogDerivConstant + Real.log (|t|+4)) *
      ‖g ((t:ℂ)*I)‖^2))
  intro S
  calc ∑ q ∈ S, ‖g (w q)‖^2 ≤ ∑ q ∈ S, ∫ t, J q t := Finset.sum_le_sum fun q _ => hp q
    _ = ∫ t, ∑ q ∈ S, J q t := (integral_finsetSum S fun q _ => hi q).symm
    _ ≤ _ := by
      apply integral_mono (integrable_finsetSum S fun q _ => hi q) (hl.const_mul _)
      intro t
      have hk (q) : halfPlanePoisson (w q).re (t-(w q).im) ≤
          (2/Real.pi) * lorentzMassTerm t q := by
        simpa [w, im_centredZero, lorentzMassTerm, one_div] using
          halfPlanePoisson_le_lorentz (hstrip q).1 (hstrip q).2 (t-(w q).im)
      have hrow := ((summable_lorentzMassTerm t).sum_le_tsum S
        fun q _ => lorentzMassTerm_nonneg _ q).trans (lorentzMass_le_log t)
      simp only [J, ← Finset.sum_mul]
      calc _ ≤ ((2/Real.pi) * ∑ q ∈ S, lorentzMassTerm t q) * ‖g ((t:ℂ)*I)‖^2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              rw [Finset.mul_sum]
              exact Finset.sum_le_sum fun q _ => hk q
        _ ≤ ((2/Real.pi) * (8*(xiLineTwoLogDerivConstant+Real.log (|t|+4)))) * ‖g ((t:ℂ)*I)‖^2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrow (by positivity)) (sq_nonneg _)
        _ = _ := by ring

/-- The squared logarithm of the ordinate is summable against the squared
actual state samples at all centred zeros, counted with multiplicity. -/
theorem summable_log_sq_mul_norm_sq_laplace_centredZero {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Summable fun q : XiZeroCopy => Real.log (|(centredZero q).im|+4)^2 *
      ‖negativeHalfLineLaplace (cx F) (centredZero q)‖^2 := by
  let L := negativeHalfLineLaplace (cx F)
  let g := fun w : ℂ => lineLogWeight 0 w * L (w-1)
  let l := fun t : ℝ => Real.log (|t|+4)
  let f := fun t : ℝ => L (((-1:ℝ):ℂ)+(t:ℂ)*I)
  let M := transformMass F (-1)
  have hM : 0 ≤ M := transformMass_nonneg _ _
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hdif (w : ℂ) (hw : 0 ≤ w.re) : DifferentiableAt ℂ g w := by
    have hp : -4 < (w-1).re := by simp; linarith
    have hL : DifferentiableAt ℂ L (w-1) := differentiableAt_laplace hd hp
    have hsub : DifferentiableAt ℂ (fun v : ℂ => v-1) w := by fun_prop
    have hcomp := hL.comp w hsub
    exact (differentiableAt_lineLogWeight hw).mul hcomp
  have hgc : Continuous fun t : ℝ => g ((t:ℂ)*I) :=
    continuous_iff_continuousAt.mpr fun t => (hdif _ (by simp)).continuousAt.comp (by fun_prop)
  have hlc : Continuous l := (continuous_abs.add_const 4).log fun t => by positivity
  have hl0 (t) : 0 ≤ l t := Real.log_nonneg (by linarith only [abs_nonneg t])
  have hmom (n : ℕ) : Integrable fun t : ℝ => l t ^ n * ‖f t‖^2 :=
    integrable_log_pow_mul_norm_sq_reflected_laplace hW ht hF (c := 1) (by norm_num) le_rfl n
  have he (t : ℝ) : g ((t:ℂ)*I) = lineLogWeight 0 ((t:ℂ)*I)*f t := by
    have e : (t:ℂ)*I-1 = ((-1:ℝ):ℂ)+(t:ℂ)*I := by push_cast; ring
    exact congrArg (fun w => lineLogWeight 0 ((t:ℂ)*I)*L w) e
  have hbound (t : ℝ) : ‖g ((t:ℂ)*I)‖^2 ≤ 5 * (l t^2 * ‖f t‖^2) := by
    have hr := re_lineLogWeight_line_le 0 t
    simp only [Complex.ofReal_zero, zero_add] at hr
    have h1 := one_le_re_lineLogWeight (σ := 0) (p := (t:ℂ)*I) (by simp)
    have hh := normSq_lineLogWeight_le (σ := 0) (p := (t:ℂ)*I) (by simp)
    have h2 := pow_le_pow_left₀ (zero_le_one.trans h1) hr 2
    rw [he, norm_mul, mul_pow, Complex.sq_norm]
    exact (mul_le_mul_of_nonneg_right (hh.trans (mul_le_mul_of_nonneg_left h2 (by norm_num)))
      (sq_nonneg _)).trans_eq (mul_assoc _ _ _)
  have hgi : Integrable fun t : ℝ => ‖g ((t:ℂ)*I)‖^2 :=
    ((hmom 2).const_mul 5).mono' (hgc.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun t => by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hbound t)
  have hgli : Integrable fun t : ℝ => l t * ‖g ((t:ℂ)*I)‖^2 := by
    apply ((hmom 3).const_mul 5).mono' (hlc.mul (hgc.norm.pow 2)).aestronglyMeasurable
    apply Eventually.of_forall
    intro t
    change ‖l t * ‖g ((t:ℂ)*I)‖^2‖ ≤ 5*(l t^3*‖f t‖^2)
    rw [Real.norm_of_nonneg (mul_nonneg (hl0 t) (sq_nonneg _))]
    calc _ ≤ l t * (5*(l t^2*‖f t‖^2)) := mul_le_mul_of_nonneg_left (hbound t) (hl0 t)
      _ = _ := by ring
  have hgrow (w : ℂ) (hw : 0 ≤ w.re) : ‖g w‖ ≤ (8*M)*(1+‖w‖)^2 := by
    have h4 := four_le_re_sub_add (σ := 0) hw
    have hn := h4.trans (Complex.re_le_norm _)
    have hlog := Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num : (0:ℝ)<4) hn)
    have hre : (lineLogWeight 0 w).re ≤ ‖w‖ + 3 := by
      rw [lineLogWeight, Complex.log_re]
      simp only [Complex.ofReal_zero, sub_zero] at hlog ⊢
      have h := norm_add_le w (4:ℂ)
      simp only [Complex.norm_ofNat] at h
      linarith
    have h1 := one_le_re_lineLogWeight hw
    have him := abs_im_lineLogWeight_le hw
    have hsum := Complex.norm_le_abs_re_add_abs_im (lineLogWeight 0 w)
    rw [abs_of_nonneg (zero_le_one.trans h1)] at hsum
    have hw' : (-1:ℝ) ≤ (w-1).re := by simp; linarith
    change ‖lineLogWeight 0 w * L (w-1)‖ ≤ _
    rw [norm_mul]
    apply (mul_le_mul (show ‖lineLogWeight 0 w‖ ≤ ‖w‖+5 by linarith)
      (norm_laplace_le_transformMass hd (by norm_num : (-4:ℝ)< -1) hw') (norm_nonneg _) (by positivity)).trans
    have h : ‖w‖+5 ≤ 8*(1+‖w‖)^2 := by nlinarith only [norm_nonneg w, sq_nonneg ‖w‖]
    exact (mul_le_mul_of_nonneg_right h hM).trans_eq (by ring)
  have hh := summable_strip_samples (g := g) hdif (B := 8*M) (by positivity) hgrow
    hgi (((hgi.const_mul xiLineTwoLogDerivConstant).add hgli).congr
      (Eventually.of_forall fun t => (add_mul _ _ _).symm))
  apply Summable.of_nonneg_of_le (fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _ (hh.mul_left 4)
  intro q
  let w := centredZero q + 1
  have hw : 0 ≤ w.re := by
    have h := abs_lt.mp (abs_re_centredZero_lt q)
    simp only [w, Complex.add_re, Complex.one_re]; linarith
  have h4 := (four_le_re_sub_add (σ := 0) hw).trans (Complex.re_le_norm _)
  have hi := Complex.abs_im_le_norm (w - ((0:ℝ):ℂ) + 4)
  have hi' : |(centredZero q).im| ≤ ‖w - ((0:ℝ):ℂ) + 4‖ := by simpa [w] using hi
  have hlog := Real.log_le_log (by positivity : 0 < |(centredZero q).im|+4)
    (show |(centredZero q).im|+4 ≤ 2*‖w-((0:ℝ):ℂ)+4‖ by linarith only [h4, hi'])
  rw [Real.log_mul (by norm_num) (by linarith only [h4] : ‖w-((0:ℝ):ℂ)+4‖ ≠ 0)] at hlog
  have hr : Real.log (|(centredZero q).im|+4) ≤ 2*‖lineLogWeight 0 w‖ := by
    have h1 := one_le_re_lineLogWeight hw
    have h2 := Complex.re_le_norm (lineLogWeight 0 w)
    have heq : Real.log ‖w-((0:ℝ):ℂ)+4‖ = (lineLogWeight 0 w).re := by rw [lineLogWeight, Complex.log_re]
    linarith only [h1,h2,hlog,heq,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hs := pow_le_pow_left₀ (hl0 _) hr 2
  change _ ≤ 4*‖lineLogWeight 0 w * L (centredZero q + 1 - 1)‖^2
  rw [add_sub_cancel_right, norm_mul, mul_pow]
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans_eq (by ring)

/-- The state coefficients absorb the full Lorentzian zero-counting weight. -/
theorem criticalState_summable_zero_density_mass {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Summable fun q : XiZeroCopy => (xiLineTwoLogDerivConstant + Real.log (|(centredZero q).im|+4)) *
      ‖negativeHalfLineLaplace (cx F) (centredZero q)‖^2 := by
  have h0 := criticalState_summable_norm_sq_zeroValues hW ht hF
  have h2 := summable_log_sq_mul_norm_sq_laplace_centredZero hW ht hF
  apply Summable.of_nonneg_of_le _ _ ((h0.mul_left (xiLineTwoLogDerivConstant+1)).add h2)
  · intro q
    apply mul_nonneg _ (sq_nonneg _)
    exact add_nonneg xiLineTwoLogDerivConstant_nonneg (Real.log_nonneg (by linarith only [abs_nonneg (centredZero q).im]))
  · intro q
    let l := Real.log (|(centredZero q).im|+4)
    have h : xiLineTwoLogDerivConstant+l ≤ (xiLineTwoLogDerivConstant+1)+l^2 := by
      nlinarith only [sq_nonneg (l-1/2)]
    exact (mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans_eq (add_mul _ _ _)

#print axioms criticalState_summable_zero_density_mass
#print axioms summable_log_sq_mul_norm_sq_laplace_centredZero

end GaloisForLFunctions.ExclusionOfTheCriticalState

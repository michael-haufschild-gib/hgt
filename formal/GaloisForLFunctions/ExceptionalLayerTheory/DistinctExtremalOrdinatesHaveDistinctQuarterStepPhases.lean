import GaloisForLFunctions.ExceptionalLayerTheory.TheBoundaryTraceOfTheTwoIntervalPrimeRadius
import GaloisForLFunctions.ZeroConfigurationGeometry.TheBoundaryTraceDeterminesTheTopZeros
import GaloisForLFunctions.HTGeometry.ExponentialSeriesFiberwise

/-!
# Equal step phases have one extremal ordinate

For a positive frequency difference fixed by the step, every pair of boundary
zeros contributing to the squared-increment coefficient has negative imaginary
part. The circle identity forces this coefficient to vanish.
-/

noncomputable section
open Complex Filter Topology RHTower
open scoped ComplexConjugate
open GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.ExceptionalLayerTheory

private def stepMultiplier (β h ω : ℝ) : ℂ :=
  (Real.exp (β*h) : ℂ) * expChar ω h - 1

/-- The contribution of one zero copy to a translated boundary increment. -/
def stepAmplitude (β h : ℝ) (q : XiZeroCopy) : ℂ :=
  stepMultiplier β h (xiCopyOrdinate q) * primeErrorBoundaryAmplitude β q

private theorem char_add_time (ω t h : ℝ) :
    expChar ω (t+h) = expChar ω t * expChar ω h := by
  rw [expChar, expChar, expChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem char_neg_freq (ω t : ℝ) : expChar (-ω) t = conj (expChar ω t) := by
  rw [expChar, expChar, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem stepAmplitude_summable {β : ℝ} (hβ : 1/2 < β) (h : ℝ) :
    Summable fun q => ‖stepAmplitude β h q‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    ((summable_primeErrorBoundaryAmplitude hβ).mul_left (Real.exp (β*h)+1))
  rw [stepAmplitude, norm_mul]
  unfold stepMultiplier
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_expChar, mul_one, norm_one] using norm_sub_le ((Real.exp (β*h):ℂ)*expChar (xiCopyOrdinate q) h) 1

/-- The translated increment retains the absolutely convergent boundary expansion. -/
theorem stepAmplitude_carrier {β : ℝ} (hβ : 1/2 < β) (h t : ℝ) :
    (boundaryStep β h (primeErrorBoundaryTrace β) t : ℂ) =
      expSeriesCarrier (stepAmplitude β h) xiCopyOrdinate t := by
  simp only [boundaryStep, Complex.ofReal_sub, Complex.ofReal_mul, ofReal_primeErrorBoundaryTrace,
    expSeriesCarrier]
  rw [← tsum_mul_left, ← ((summable_expSeries (summable_primeErrorBoundaryAmplitude hβ)
    xiCopyOrdinate (t+h)).mul_left (Real.exp (β*h) : ℂ)).tsum_sub
      (summable_expSeries (summable_primeErrorBoundaryAmplitude hβ) xiCopyOrdinate t)]
  apply tsum_congr
  intro q
  rw [char_add_time, stepAmplitude, stepMultiplier]
  ring

private def pairAmplitude (β h : ℝ) (p : XiZeroCopy × XiZeroCopy) : ℂ :=
  stepAmplitude β h p.1 * conj (stepAmplitude β h p.2)

private def pairFrequency (p : XiZeroCopy × XiZeroCopy) : ℝ :=
  xiCopyOrdinate p.1 - xiCopyOrdinate p.2

private theorem summable_norm_pairAmplitude {β : ℝ} (hβ : 1/2 < β) (h : ℝ) :
    Summable fun p => ‖pairAmplitude β h p‖ := by
  let a := stepAmplitude β h
  have ha : Summable fun q => ‖a q‖ := stepAmplitude_summable hβ h
  have hconj : Summable fun q => ‖conj (a q)‖ := by simpa only [Complex.norm_conj] using ha
  change Summable (fun r : XiZeroCopy × XiZeroCopy => ‖a r.1 * conj (a r.2)‖)
  exact GaloisForLFunctions.summable_norm_mul (b := a) (c := fun q => conj (a q)) ha hconj

private theorem squareStep_carrier {β : ℝ} (hβ : 1/2 < β) (h t : ℝ) :
    ((boundaryStep β h (primeErrorBoundaryTrace β) t ^ 2 : ℝ) : ℂ) =
      expSeriesCarrier (pairAmplitude β h) pairFrequency t := by
  let a := stepAmplitude β h
  let ω := xiCopyOrdinate
  have hc : conj (expSeriesCarrier a ω t) =
      expSeriesCarrier (fun q => conj (a q)) (fun q => -(ω q)) t := by
    simp only [expSeriesCarrier, Complex.conj_tsum, map_mul, ← char_neg_freq]
  have he := stepAmplitude_carrier hβ h t
  rw [Complex.ofReal_pow, sq]
  calc _ = expSeriesCarrier a ω t * conj (expSeriesCarrier a ω t) := by
             rw [← he, Complex.conj_ofReal]
    _ = _ := by
      rw [hc, expSeriesCarrier_mul ω (fun q => -ω q) (stepAmplitude_summable hβ h)
        (by simpa only [Complex.norm_conj] using stepAmplitude_summable hβ h)]
      have hf : (fun r : XiZeroCopy × XiZeroCopy => ω r.1 + -ω r.2) = pairFrequency :=
        funext fun r => (sub_eq_add_neg _ _).symm
      exact congrArg (fun f => expSeriesCarrier (pairAmplitude β h) f t) hf

/-- The sign is strict for every occupied pair because the common step multiplier
has nonzero modulus. -/
private theorem pairAmplitude_im_neg {β h : ℝ} (hβ : 0 < β) (hh : 0 < h)
    {p q : XiZeroCopy} (hp : (p.1 : ℂ).re = β) (hq : (q.1 : ℂ).re = β)
    (hlt : xiCopyOrdinate q < xiCopyOrdinate p)
    (he : expChar (xiCopyOrdinate p) h = expChar (xiCopyOrdinate q) h) :
    (pairAmplitude β h (p,q)).im < 0 := by
  let z := stepMultiplier β h (xiCopyOrdinate q)
  have hz : z ≠ 0 := by
    intro hz
    change (Real.exp (β*h) : ℂ) * expChar (xiCopyOrdinate q) h - 1 = 0 at hz
    have hu := congrArg (fun w : ℂ => ‖w‖) (sub_eq_zero.mp hz)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_expChar, mul_one, norm_one] at hu
    exact (Real.one_lt_exp_iff.mpr (mul_pos hβ hh)).ne' hu
  have hmul : stepMultiplier β h (xiCopyOrdinate p) = z := by
    simp only [z, stepMultiplier, he]
  have hpair : pairAmplitude β h (p,q) =
      (Complex.normSq z : ℂ) * (((p.1 : ℂ) * conj (q.1 : ℂ))⁻¹) := by
    simp only [pairAmplitude, stepAmplitude, primeErrorBoundaryAmplitude, hp, hq, if_true, hmul,
      map_mul, map_neg, map_inv₀, mul_inv_rev, ← Complex.mul_conj]
    ring
  rw [hpair, Complex.im_ofReal_mul, Complex.inv_im]
  apply mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hz)
  have hden : (p.1 : ℂ) * conj (q.1 : ℂ) ≠ 0 := mul_ne_zero (xiZeroCopy_ne_zero p)
    ((map_ne_zero _).mpr (xiZeroCopy_ne_zero q))
  have him : 0 < ((p.1 : ℂ)*conj (q.1 : ℂ)).im := by
    rw [Complex.mul_im, Complex.conj_im, Complex.conj_re, hp, hq]
    change 0 < β * -xiCopyOrdinate q + xiCopyOrdinate p * β
    nlinarith only [mul_pos hβ (sub_pos.mpr hlt)]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr him) (Complex.normSq_pos.mpr hden)

private theorem step_square_coeff_zero {β h C : ℝ}
    (hβ : 1/2 < β) (d : ℝ) (hd : d ≠ 0) (he : expChar d h = 1)
    (hcirc : ∀ t, boundaryStep β h (primeErrorBoundaryTrace β) t ^ 2 +
      boundaryStep β h (primeErrorBoundaryTrace β) (t+h) ^ 2 = C) :
    fiberAmplitude (pairAmplitude β h) pairFrequency d = 0 := by
  let G := expSeriesCarrier (pairAmplitude β h) pairFrequency
  have hs := summable_norm_pairAmplitude hβ h
  have hc : Continuous G := continuous_expSeriesCarrier hs _
  have ha : _root_.HTGeometry.IsBohrAlmostPeriodic G := isBohrAlmostPeriodic_expSeriesCarrier hs _
  have hsc := hc.comp (continuous_id.add continuous_const : Continuous (fun t : ℝ => t+h))
  have hsa := isBohrAlmostPeriodic_comp_add_const ha h
  have hconst : (fun t => G t + G (t+h)) = fun _ => (C:ℂ) := by
    funext t
    dsimp only [G]
    rw [← squareStep_carrier hβ h t, ← squareStep_carrier hβ h (t+h), ← Complex.ofReal_add, hcirc]
  have hcoef : bohrCoefficient (fun t => G t + G (t+h)) d =
      bohrCoefficient G d + bohrCoefficient (fun t => G (t+h)) d := by
    simp only [bohrCoefficient, add_mul]
    exact bohrMean_add (hc.mul (continuous_bohrChar _)) (isBohrAlmostPeriodic_mul_bohrChar hc ha _)
      (hsc.mul (continuous_bohrChar _)) (isBohrAlmostPeriodic_mul_bohrChar hsc hsa _)
  have hz : bohrCoefficient (fun _ : ℝ => (C:ℂ)) d = 0 := by
    unfold bohrCoefficient
    rw [bohrMean_const_mul _ (continuous_bohrChar _) (isBohrAlmostPeriodic_bohrChar _),
      bohrMean_bohrChar, if_neg hd, mul_zero]
  rw [hconst, hz, bohrCoefficient_comp_add_const hc ha, he, one_mul,
    ← two_mul] at hcoef
  rw [← bohrCoefficient_expSeriesCarrier_fiber _ _ hs]
  exact (mul_eq_zero.mp hcoef.symm).resolve_left (by norm_num)

private theorem char_eq_of_difference {u v h d : ℝ} (hd : u-v = d) (he : expChar d h = 1) :
    expChar u h = expChar v h := by
  rw [show u = d+v by linarith only [hd], ← expChar_add, he, one_mul]

/-- Distinct extremal ordinates cannot have the same trial step phase when
the ordinary-prime discrepancy is bounded. -/
theorem top_step_phase_separates_ordinates {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hγ : γ ≠ 0)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m))
    (p q : XiZeroCopy) (hp : (p.1 : ℂ).re = zetaZeroAbscissa)
    (hq : (q.1 : ℂ).re = zetaZeroAbscissa) :
    expChar (xiCopyOrdinate p) (quarterPeriodStep γ) =
      expChar (xiCopyOrdinate q) (quarterPeriodStep γ) → xiCopyOrdinate p = xiCopyOrdinate q := by
  classical
  let β := zetaZeroAbscissa
  let h := quarterPeriodStep γ
  have hh : 0 < h := quarterPeriodStep_pos hγ
  have hβ : 0 < β := lt_trans (by norm_num : (0 : ℝ) < 1/2) hΘ
  suffices noPair : ∀ (u v : XiZeroCopy), (u.1 : ℂ).re = β → (v.1 : ℂ).re = β →
      xiCopyOrdinate v < xiCopyOrdinate u → expChar (xiCopyOrdinate u) h ≠ expChar (xiCopyOrdinate v) h by
    intro he
    apply le_antisymm
    · exact le_of_not_gt fun hlt => noPair p q hp hq hlt he
    · exact le_of_not_gt fun hlt => noPair q p hq hp hlt he.symm
  intro u v hu hv hlt he
  let d := xiCopyOrdinate u - xiCopyOrdinate v
  have hd : 0 < d := sub_pos.mpr hlt
  have hd1 : expChar d h = 1 := by
    apply mul_right_cancel₀ (show expChar (xiCopyOrdinate v) h ≠ 0 from Complex.exp_ne_zero _)
    rw [expChar_add, show d + xiCopyOrdinate v = xiCopyOrdinate u from sub_add_cancel _ _, one_mul, he]
  have hz := step_square_coeff_zero hΘ d hd.ne' hd1 (boundaryStep_circle_of_bounded_thetaRadial hΘ hb)
  let S := {w : XiZeroCopy × XiZeroCopy // pairFrequency w = d}
  let a := fun w : S => -(pairAmplitude β h w.val).im
  have hs : Summable (fun w : S => pairAmplitude β h w.val) :=
    (Summable.of_norm (summable_norm_pairAmplitude hΘ h)).subtype _
  have ha : Summable a := (Complex.hasSum_im hs.hasSum).summable.neg
  have ha0 (w : S) : 0 ≤ a w := by
    obtain ⟨⟨s,r⟩,hw⟩ := w
    change 0 ≤ -(pairAmplitude β h (s,r)).im
    by_cases hs : (s.1 : ℂ).re = β
    · by_cases hr : (r.1 : ℂ).re = β
      · change xiCopyOrdinate s - xiCopyOrdinate r = d at hw
        exact (neg_pos.mpr (pairAmplitude_im_neg hβ hh hs hr (by linarith only [hw,hd])
          (char_eq_of_difference hw hd1))).le
      · simp [pairAmplitude, stepAmplitude, primeErrorBoundaryAmplitude, hr]
    · simp [pairAmplitude, stepAmplitude, primeErrorBoundaryAmplitude, hs]
  let w : S := ⟨(u,v),rfl⟩
  have hpw : 0 < a w := neg_pos.mpr (pairAmplitude_im_neg hβ hh hu hv hlt he)
  have hle : a w ≤ ∑' r, a r := by
    simpa only [Finset.sum_singleton] using ha.sum_le_tsum {w} (fun r _ => ha0 r)
  have hzero : ∑' r, a r = 0 := by
    change (∑' r : S, -(pairAmplitude β h r.val).im) = 0
    rw [tsum_neg, ← Complex.im_tsum hs]
    change -(fiberAmplitude (pairAmplitude β h) pairFrequency d).im = 0
    rw [hz, Complex.zero_im, neg_zero]
  exact (hpw.trans_le hle).ne' hzero

/-- Multiplicities included, each phase for the doubled step contains finitely
many extremal zeros. Its two possible square roots each determine at most one ordinate. -/
theorem finite_top_double_step_fiber {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hγ : γ ≠ 0)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)) (z : ℂ) :
    {q : XiZeroCopy | (q.1 : ℂ).re = zetaZeroAbscissa ∧
      expChar (xiCopyOrdinate q) (2*quarterPeriodStep γ) = z}.Finite := by
  classical
  let h := quarterPeriodStep γ
  let S := fun w : ℂ => {q : XiZeroCopy | (q.1 : ℂ).re = zetaZeroAbscissa ∧
    expChar (xiCopyOrdinate q) h = w}
  have hS (w : ℂ) : (S w).Finite := by
    by_cases hp : (S w).Nonempty
    · obtain ⟨p,hp⟩ := hp
      refine (finite_xiOrdinateWindow |xiCopyOrdinate p| 0).subset fun q hq => ?_
      have he := top_step_phase_separates_ordinates hΘ hγ hb q p hq.1 hp.1 (hq.2.trans hp.2.symm)
      rw [mem_xiOrdinateWindow_iff, sub_zero]
      change |xiCopyOrdinate q| ≤ |xiCopyOrdinate p|
      exact (congrArg abs he).le
    · exact Set.finite_empty.subset fun _ hq => (hp ⟨_,hq⟩).elim
  let T := {q : XiZeroCopy | (q.1 : ℂ).re = zetaZeroAbscissa ∧ expChar (xiCopyOrdinate q) (2*h) = z}
  change T.Finite
  by_cases ht : T.Nonempty
  · obtain ⟨p,hp⟩ := ht
    let w := expChar (xiCopyOrdinate p) h
    refine ((hS w).union (hS (-w))).subset fun q hq => ?_
    have hs (r : XiZeroCopy) : expChar (xiCopyOrdinate r) h ^ 2 =
        expChar (xiCopyOrdinate r) (2*h) := by rw [two_mul, char_add_time, sq]
    have he := (hs q).trans ((hq.2.trans hp.2.symm).trans (hs p).symm)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with H | H
    · exact Or.inl ⟨hq.1,H⟩
    · exact Or.inr ⟨hq.1,H⟩
  · exact Set.finite_empty.subset fun _ hq => (ht ⟨_,hq⟩).elim

#print axioms top_step_phase_separates_ordinates
#print axioms finite_top_double_step_fiber

end GaloisForLFunctions.ExceptionalLayerTheory

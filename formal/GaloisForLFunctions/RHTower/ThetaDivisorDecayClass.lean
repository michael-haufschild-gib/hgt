import GaloisForLFunctions.RHTower.ThetaZeroDivisionLipschitz
import GaloisForLFunctions.RHTower.WeilPrimeBlindZeroSideIdentity

/-!
# Finite theta divisors satisfy the full zero-sum decay class

Admissibility cancels every reflection seam. Weighted outgoing tails give
exponential decay of the first derivative as well as the source itself.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- A fixed decay rate shared by all finite divisor sources and their first jets. -/
def ExponentialFirstJet (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ 2 f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
    ‖f x‖ ≤ C * Real.exp (-|x|) ∧ ‖deriv f x‖ ≤ C * Real.exp (-|x|)

theorem ExponentialFirstJet.const_mul {f : ℝ → ℂ} (hf : ExponentialFirstJet f) (a : ℂ) :
    ExponentialFirstJet (fun x => a * f x) := by
  obtain ⟨hs, C, hC, hb⟩ := hf
  refine ⟨contDiff_const.mul hs, ‖a‖ * C, by positivity, fun x => ?_⟩
  have hd := ((hs.differentiable (by norm_num) x).hasDerivAt.const_mul a).deriv
  rw [hd, norm_mul, norm_mul]
  constructor <;> nlinarith [norm_nonneg a, (hb x).1, (hb x).2]

theorem ExponentialFirstJet.sub {f g : ℝ → ℂ}
    (hf : ExponentialFirstJet f) (hg : ExponentialFirstJet g) :
    ExponentialFirstJet (fun x => f x - g x) := by
  obtain ⟨hs, C, hC, hb⟩ := hf
  obtain ⟨ht, D, hD, hc⟩ := hg
  refine ⟨hs.sub ht, C + D, by positivity, fun x => ?_⟩
  have hd := ((hs.differentiable (by norm_num) x).hasDerivAt.sub
    (ht.differentiable (by norm_num) x).hasDerivAt).deriv
  change deriv (fun y => f y - g y) x = deriv f x - deriv g x at hd
  rw [hd]
  constructor
  · exact (norm_sub_le _ _).trans (by nlinarith [(hb x).1, (hc x).1])
  · exact (norm_sub_le _ _).trans (by nlinarith [(hb x).2, (hc x).2])

theorem exponentialFirstJet_thetaSourceC : ExponentialFirstJet thetaSourceC := by
  obtain ⟨C, hC, hb⟩ := exists_abs_thetaCuspFullSource_le 1
  obtain ⟨D, hD, hc⟩ := exists_abs_deriv_thetaCuspFullSource_le 1
  refine ⟨contDiff_thetaSourceC.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)),
    C + D, by positivity, fun x => ?_⟩
  have hd := (differentiable_thetaCuspFullSource x).hasDerivAt.ofReal_comp.deriv
  change ‖(thetaCuspFullSource x : ℂ)‖ ≤ _ ∧
    ‖deriv (fun y => (thetaCuspFullSource y : ℂ)) x‖ ≤ _
  rw [hd, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  simp only [one_mul] at hb hc
  constructor <;> nlinarith [hb x, hc x, Real.exp_pos (-|x|)]

theorem ExpMomentSource.joinedDivisionDeriv_decay {f : ℝ → ℂ}
    (hf : ExpMomentSource f) (α : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖joinedDivisionDeriv α f x‖ ≤
      (2 * ‖α‖ ^ 2 * (∫ t, Real.exp ((2 * (|α.im| + 1)) * |t|) * ‖f t‖)) *
        Real.exp (-x) := by
  have ha : 0 ≤ |α.im| + 1 := by positivity
  have hex (t : ℝ) : Real.exp (|α.im| * |t|) ≤ Real.exp ((|α.im| + 1) * |t|) := by
    gcongr
    linarith
  have hs := hf.norm_weighted_tail_le ha (hf.integrable_sin α)
    (fun t => (norm_csin_mul_ofReal_le α t).trans (hex t)) hx
  have hc := hf.norm_weighted_tail_le ha (hf.integrable_cos α)
    (fun t => (norm_ccos_mul_ofReal_le α t).trans (hex t)) hx
  have he : Real.exp (|α.im| * x) = Real.exp (-x) * Real.exp ((|α.im| + 1) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsin : ‖Complex.sin (α * x) * sineTail α f x‖ ≤
      Real.exp (-x) * (∫ t, Real.exp ((2 * (|α.im| + 1)) * |t|) * ‖f t‖) := by
    rw [norm_mul]
    calc
      _ ≤ Real.exp (|α.im| * x) * ‖sineTail α f x‖ := by
        gcongr
        simpa only [abs_of_nonneg hx] using norm_csin_mul_ofReal_le α x
      _ = Real.exp (-x) * (Real.exp ((|α.im| + 1) * x) * ‖sineTail α f x‖) := by rw [he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
  have hcos : ‖Complex.cos (α * x) * cosineTail α f x‖ ≤
      Real.exp (-x) * (∫ t, Real.exp ((2 * (|α.im| + 1)) * |t|) * ‖f t‖) := by
    rw [norm_mul]
    calc
      _ ≤ Real.exp (|α.im| * x) * ‖cosineTail α f x‖ := by
        gcongr
        simpa only [abs_of_nonneg hx] using norm_ccos_mul_ofReal_le α x
      _ = Real.exp (-x) * (Real.exp ((|α.im| + 1) * x) * ‖cosineTail α f x‖) := by rw [he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
  rw [joinedDivisionDeriv, norm_neg, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (sq_nonneg _)).trans
    (by nlinarith [sq_nonneg ‖α‖])

theorem norm_deriv_neg_of_even {f : ℝ → ℂ} (hf : Differentiable ℝ f)
    (he : ∀ x, f (-x) = f x) (x : ℝ) : ‖deriv f (-x)‖ = ‖deriv f x‖ := by
  have hd := (hf (-x)).hasDerivAt.scomp x (hasDerivAt_neg x)
  have heq : f ∘ Neg.neg = f := funext he
  rw [heq] at hd
  have hu := hd.unique (hf x).hasDerivAt
  simpa only [neg_smul, one_smul, norm_neg] using congrArg norm hu

theorem exponentialFirstJet_zeroDivision {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (heven : ∀ x, f (-x) = f x) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    {α : ℂ} (hzero : sourceTransform f α = 0) :
    ExponentialFirstJet (zeroDivision α f) := by
  have hd := (zeroDivision_smooth_green hf heven hs hzero).1
  let C := ‖α‖ * (∫ t, Real.exp ((1 + |α.im|) * |t|) * ‖f t‖)
  let D := 2 * ‖α‖ ^ 2 * (∫ t, Real.exp ((2 * (|α.im| + 1)) * |t|) * ‖f t‖)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (integral_nonneg fun t => by positivity)
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg fun t => by positivity)
  have hv (x : ℝ) : ‖zeroDivision α f x‖ ≤ C * Real.exp (-|x|) := by
    simpa only [C, one_mul, mul_assoc] using hf.norm_zeroDivision_le α (by norm_num : (0:ℝ) ≤ 1) x
  have hder (x : ℝ) (hx : 0 ≤ x) : ‖deriv (zeroDivision α f) x‖ ≤ D * Real.exp (-x) := by
    rw [zeroDivision_eq_joinedDivision hf heven hzero, (hasDerivAt_joinedDivision hf α x).deriv]
    exact hf.joinedDivisionDeriv_decay α hx
  have hda (x : ℝ) : ‖deriv (zeroDivision α f) x‖ ≤ D * Real.exp (-|x|) := by
    by_cases hx : 0 ≤ x
    · simpa only [abs_of_nonneg hx] using hder x hx
    · have hneg := norm_deriv_neg_of_even (hd.differentiable (by simp)) (zeroDivision_neg α f) x
      rw [← hneg, abs_of_neg (lt_of_not_ge hx)]
      exact hder (-x) (by linarith)
  refine ⟨hd.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)),
    C + D, by positivity, fun x => ?_⟩
  constructor <;> nlinarith [hv x, hda x, Real.exp_pos (-|x|)]

theorem exponentialFirstJet_thetaListDivision {L : List ℂ} (hL : ThetaDivisionList L) :
    ExponentialFirstJet (thetaListDivision L) := by
  cases L with
  | nil => exact exponentialFirstJet_thetaSourceC
  | cons α L =>
    exact exponentialFirstJet_zeroDivision (expMomentSource_thetaListDivision L)
      (thetaListDivision_neg L) (contDiff_thetaListDivision hL.tail)
      (sourceTransform_thetaListDivision_eq_zero hL)

theorem exponentialFirstJet_listComb {L : List ℂ} (hL : ThetaDivisionList L)
    (e : Polynomial ℂ) : ExponentialFirstJet (listComb thetaListDivision L e) := by
  induction L generalizing e with
  | nil => exact exponentialFirstJet_thetaSourceC.const_mul (e.coeff 0)
  | cons α L ih =>
    exact ((exponentialFirstJet_thetaListDivision hL).const_mul _).sub
      ((ih hL.tail _).const_mul _)

theorem ExponentialFirstJet.re {f : ℝ → ℂ} (hf : ExponentialFirstJet f) :
    WeilSpectral.ExpDecayTest (fun x => (f x).re) := by
  obtain ⟨hs, C, hC, hb⟩ := hf
  refine ⟨Complex.reCLM.contDiff.comp hs, 1/2, C, by norm_num, hC, fun x => ?_⟩
  have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hs.differentiable (by norm_num) x).hasDerivAt).deriv
  change deriv (fun y => (f y).re) x = (deriv f x).re at hd
  rw [hd]
  norm_num only [show (1:ℝ)/2+1/2=1 by norm_num, one_mul]
  exact ⟨(Complex.abs_re_le_norm _).trans (hb x).1,
    (Complex.abs_re_le_norm _).trans (hb x).2⟩

theorem ExponentialFirstJet.im {f : ℝ → ℂ} (hf : ExponentialFirstJet f) :
    WeilSpectral.ExpDecayTest (fun x => (f x).im) := by
  obtain ⟨hs, C, hC, hb⟩ := hf
  refine ⟨Complex.imCLM.contDiff.comp hs, 1/2, C, by norm_num, hC, fun x => ?_⟩
  have hd := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x
    (hs.differentiable (by norm_num) x).hasDerivAt).deriv
  change deriv (fun y => (f y).im) x = (deriv f x).im at hd
  rw [hd]
  norm_num only [show (1:ℝ)/2+1/2=1 by norm_num, one_mul]
  exact ⟨(Complex.abs_im_le_norm _).trans (hb x).1,
    (Complex.abs_im_le_norm _).trans (hb x).2⟩

end RHTower

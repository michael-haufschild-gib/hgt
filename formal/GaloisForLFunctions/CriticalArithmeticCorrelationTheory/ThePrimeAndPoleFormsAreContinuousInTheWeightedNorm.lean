import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ExponentialSourceMassControlsTheFullPrimeSum
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.RHTower.EulerMaclaurinCountertermQuadratureAndOneSidedPBAP

/-!
# The prime and pole forms are continuous in the weighted norm

On measurable functions with finite `exponentialSourceMass` (the norm `∫ e^{2|t|} f²`) the prime
sum and the pole moments are well defined, with no continuity or compact support:

* `abs_integral_mul_shift_le`: a correlation at lag `s` costs `e^{−|s|}` times the two norms;
* `abs_primeSum_sub_le`: `|P(f) − P(g)| ≤ 2 V √D (√F + √G)`, `V = Σ Λ(n) n^{−3/2}`;
* `abs_integral_mul_kernel_le`: a kernel of size `e^{|u|/2}` pairs with the norm.

So these parts of Weil's form pass to strong limits in the weighted norm, and that norm is
controlled by the plain `L²` norm together with the eighth exponential mass
(`exponentialSourceMass_le_of_support`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter RHTower
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticCastelnuovoSeveri

/-- Finite weighted mass: measurable, with `e^{|t|} f` square integrable. -/
structure WeightedTwo (f : ℝ → ℝ) : Prop where
  meas : AEStronglyMeasurable f volume
  sq : Integrable (fun t => (Real.exp |t| * f t) ^ 2)

private theorem WeightedTwo.weightedMeas {f : ℝ → ℝ} (hf : WeightedTwo f) :
    AEStronglyMeasurable (fun t => Real.exp |t| * f t) volume :=
  (Real.continuous_exp.comp continuous_abs).aestronglyMeasurable.mul hf.meas

theorem WeightedTwo.sub {f g : ℝ → ℝ} (hf : WeightedTwo f) (hg : WeightedTwo g) :
    WeightedTwo (fun t => f t - g t) := by
  refine ⟨hf.meas.sub hg.meas, ?_⟩
  refine Integrable.mono' ((hf.sq.const_mul 2).add (hg.sq.const_mul 2)) ?_ ?_
  · exact ((hf.weightedMeas.sub hg.weightedMeas).pow 2).congr
      (Eventually.of_forall fun t => by simp only [Pi.sub_apply, Pi.pow_apply]; ring)
  · refine Eventually.of_forall fun t => ?_
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [sq_nonneg (Real.exp |t| * f t + Real.exp |t| * g t)]

/-- Translated weighted bound: the product of two shifted weighted sources is integrable. -/
theorem integrable_mul_shift {a b : ℝ → ℝ} (ha : WeightedTwo a) (hb : WeightedTwo b) (s : ℝ) :
    Integrable (fun t => a t * b (t - s)) := by
  let A : ℝ → ℝ := fun t => Real.exp |t| * a t
  let B : ℝ → ℝ := fun t => Real.exp |t - s| * b (t - s)
  have hBm : AEStronglyMeasurable B volume :=
    hb.weightedMeas.comp_quasiMeasurePreserving (measurePreserving_sub_right volume s).quasiMeasurePreserving
  have hB2 : Integrable (fun t => B t ^ 2) := hb.sq.comp_sub_right s
  have hAB := HTGeometry.integrable_mul_of_sq_integrable ha.weightedMeas hBm ha.sq hB2
  have hbm : AEStronglyMeasurable (fun t => b (t - s)) volume :=
    hb.meas.comp_quasiMeasurePreserving (measurePreserving_sub_right volume s).quasiMeasurePreserving
  refine hAB.mono (ha.meas.mul hbm) (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp, B]
  have h1 := Real.one_le_exp (abs_nonneg t)
  have h2 := Real.one_le_exp (abs_nonneg (t - s))
  have hx : 0 ≤ |a t| * |b (t - s)| := by positivity
  have hprod : 1 ≤ Real.exp |t| * Real.exp |t - s| := by nlinarith only [h1, h2]
  nlinarith only [mul_le_mul_of_nonneg_right hprod hx]

/-- **A correlation at lag `s` costs `e^{−|s|}` times the weighted norms.** -/
theorem abs_integral_mul_shift_le {a b : ℝ → ℝ} (ha : WeightedTwo a) (hb : WeightedTwo b) (s : ℝ) :
    |∫ t, a t * b (t - s)| ≤ Real.exp (-|s|) *
      (Real.sqrt (exponentialSourceMass a) * Real.sqrt (exponentialSourceMass b)) := by
  let A : ℝ → ℝ := fun t => Real.exp |t| * a t
  let B : ℝ → ℝ := fun t => Real.exp |t - s| * b (t - s)
  have hBm : AEStronglyMeasurable B volume :=
    hb.weightedMeas.comp_quasiMeasurePreserving (measurePreserving_sub_right volume s).quasiMeasurePreserving
  have hB2 : Integrable (fun t => B t ^ 2) := hb.sq.comp_sub_right s
  have hA2' : (∫ t, A t ^ 2) = exponentialSourceMass a := rfl
  have hB2' : (∫ t, B t ^ 2) = exponentialSourceMass b := by
    simpa only [exponentialSourceMass] using
      integral_sub_right_eq_self (fun t => (Real.exp |t| * b t) ^ 2) s
  have hA0 : 0 ≤ exponentialSourceMass a := exponentialSourceMass_nonneg a
  have hB0 : 0 ≤ exponentialSourceMass b := exponentialSourceMass_nonneg b
  -- absolute values of the weighted pieces
  have hAa : Integrable (fun t => |A t| ^ 2) := by simpa only [sq_abs] using ha.sq
  have hBa : Integrable (fun t => |B t| ^ 2) := by simpa only [sq_abs] using hB2
  have hAm : AEStronglyMeasurable (fun t => |A t|) volume := by
    simpa only [Real.norm_eq_abs] using ha.weightedMeas.norm
  have hBm' : AEStronglyMeasurable (fun t => |B t|) volume := by
    simpa only [Real.norm_eq_abs] using hBm.norm
  have hcs := HTGeometry.sq_integral_mul_le hAm hBm' hAa hBa
  simp only [sq_abs] at hcs
  rw [hA2', hB2'] at hcs
  have hAB := HTGeometry.integrable_mul_of_sq_integrable hAm hBm' hAa hBa
  have hle : ∫ t, |A t| * |B t| ≤
      Real.sqrt (exponentialSourceMass a) * Real.sqrt (exponentialSourceMass b) := by
    rw [← Real.sqrt_mul hA0]
    exact Real.le_sqrt_of_sq_le hcs
  have hint := integrable_mul_shift ha hb s
  have hpt (t : ℝ) : |a t * b (t - s)| ≤ Real.exp (-|s|) * (|A t| * |B t|) := by
    have hs : |s| ≤ |t| + |t - s| := by
      have h := abs_sub_le t 0 (t - s)
      simpa only [sub_sub_cancel, sub_zero, zero_sub, abs_neg] using h
    have hexp : Real.exp |s| ≤ Real.exp |t| * Real.exp |t - s| := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hs
    have hne : Real.exp (-|s|) * Real.exp |s| = 1 := by
      rw [← Real.exp_add]; simp
    simp only [A, B, abs_mul, Real.abs_exp]
    have hx : 0 ≤ |a t| * |b (t - s)| := by positivity
    have h1 := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-|s|)).le
    rw [hne] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 hx
    calc |a t| * |b (t - s)| = 1 * (|a t| * |b (t - s)|) := (one_mul _).symm
      _ ≤ _ := h2
      _ = _ := by ring
  calc |∫ t, a t * b (t - s)| ≤ ∫ t, |a t * b (t - s)| := abs_integral_le_integral_abs
    _ ≤ ∫ t, Real.exp (-|s|) * (|A t| * |B t|) :=
        integral_mono hint.abs (hAB.const_mul _) hpt
    _ = Real.exp (-|s|) * ∫ t, |A t| * |B t| := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

private theorem atom_div_nat_eq (n : ℕ) :
    vonMangoldtAtom n / (n : ℝ) =
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  by_cases hn : 2 ≤ n
  · have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hp : Real.sqrt (n : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
      calc
        _ = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_one]
        _ = (n : ℝ) ^ ((1 / 2 : ℝ) + 1) := (Real.rpow_add hn' _ _).symm
        _ = (n : ℝ) ^ (3 / 2 : ℝ) := by congr 1; ring
    rw [vonMangoldtAtom, if_pos hn, div_div, hp]
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> norm_num [vonMangoldtAtom]

/-- One prime term of the mixed correlation. -/
def primePairTerm (a b : ℝ → ℝ) (n : ℕ) : ℝ :=
  vonMangoldtAtom n * ((∫ t, a t * b (t - Real.log n)) + ∫ t, a t * b (t + Real.log n))

/-- A prime term decays as `Λ(n) n^{−3/2}`. -/
theorem abs_primePairTerm_le {a b : ℝ → ℝ} (ha : WeightedTwo a) (hb : WeightedTwo b) (n : ℕ) :
    |primePairTerm a b n| ≤ (2 * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ))) *
      (Real.sqrt (exponentialSourceMass a) * Real.sqrt (exponentialSourceMass b)) := by
  rw [← atom_div_nat_eq]
  by_cases hn : 2 ≤ n
  · have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have he : Real.exp (-|Real.log (n : ℝ)|) = 1 / (n : ℝ) := by
      rw [abs_of_nonneg (Real.log_nonneg hn1), Real.exp_neg, Real.exp_log hn', one_div]
    have hminus := abs_integral_mul_shift_le ha hb (Real.log n)
    have hplus := abs_integral_mul_shift_le ha hb (-Real.log n)
    rw [he] at hminus
    simp only [sub_neg_eq_add, abs_neg, he] at hplus
    have hatom : 0 ≤ vonMangoldtAtom n := by
      rw [vonMangoldtAtom, if_pos hn]
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    unfold primePairTerm
    rw [abs_mul, abs_of_nonneg hatom]
    have hsum := (abs_add_le _ _).trans (add_le_add hminus hplus)
    have h := mul_le_mul_of_nonneg_left hsum hatom
    refine h.trans_eq ?_
    ring
  · simp only [primePairTerm, vonMangoldtAtom, if_neg hn, zero_mul, zero_div, mul_zero, abs_zero,
      le_refl]

/-- The prime terms of a weighted source are summable. -/
theorem summable_primePairTerm {a b : ℝ → ℝ} (ha : WeightedTwo a) (hb : WeightedTwo b) :
    Summable (primePairTerm a b) :=
  Summable.of_norm_bounded
    ((summable_vonMangoldt_div_threeHalves.mul_left 2).mul_right _)
    fun n => by simpa only [Real.norm_eq_abs] using abs_primePairTerm_le ha hb n

/-- **The prime sum moves by weighted amounts.** -/
theorem abs_primeSum_sub_le {f g : ℝ → ℝ} (hf : WeightedTwo f) (hg : WeightedTwo g) :
    |primeSum f - primeSum g| ≤ 2 * vonMangoldtThreeHalvesMass *
      (Real.sqrt (exponentialSourceMass fun t => f t - g t) *
        (Real.sqrt (exponentialSourceMass f) + Real.sqrt (exponentialSourceMass g))) := by
  have hd := hf.sub hg
  have hsf := summable_primePairTerm hf hf
  have hsg := summable_primePairTerm hg hg
  have heq (n : ℕ) : primePairTerm f f n - primePairTerm g g n =
      primePairTerm (fun t => f t - g t) f n + primePairTerm g (fun t => f t - g t) n := by
    have hlag (s : ℝ) : (∫ t, f t * f (t - s)) - ∫ t, g t * g (t - s) =
        (∫ t, (f t - g t) * f (t - s)) + ∫ t, g t * (f (t - s) - g (t - s)) := by
      have i1 := integrable_mul_shift hf hf s
      have i2 := integrable_mul_shift hg hf s
      have i3 := integrable_mul_shift hg hg s
      rw [show (fun t => (f t - g t) * f (t - s)) =
            fun t => f t * f (t - s) - g t * f (t - s) from funext fun t => by ring,
        show (fun t => g t * (f (t - s) - g (t - s))) =
            fun t => g t * f (t - s) - g t * g (t - s) from funext fun t => by ring,
        integral_sub i1 i2, integral_sub i2 i3]
      ring
    have hp := hlag (Real.log n)
    have hm := hlag (-Real.log n)
    simp only [sub_neg_eq_add] at hm
    simp only [primePairTerm]
    linear_combination vonMangoldtAtom n * hp + vonMangoldtAtom n * hm
  have hle (n : ℕ) : |primePairTerm f f n - primePairTerm g g n| ≤
      (2 * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ))) *
        (Real.sqrt (exponentialSourceMass fun t => f t - g t) *
          (Real.sqrt (exponentialSourceMass f) + Real.sqrt (exponentialSourceMass g))) := by
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    have h1 := abs_primePairTerm_le hd hf n
    have h2 := abs_primePairTerm_le hg hd n
    calc _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
  have hsumB := (summable_vonMangoldt_div_threeHalves.mul_left 2).mul_right
    (Real.sqrt (exponentialSourceMass fun t => f t - g t) *
      (Real.sqrt (exponentialSourceMass f) + Real.sqrt (exponentialSourceMass g)))
  have hP (h : ℝ → ℝ) : primeSum h = ∑' n, primePairTerm h h n := rfl
  rw [hP f, hP g, ← hsf.tsum_sub hsg]
  have hnorm := norm_tsum_le_tsum_norm (hsf.sub hsg).norm
  simp only [Real.norm_eq_abs] at hnorm
  refine hnorm.trans ?_
  refine ((hsf.sub hsg).abs.tsum_le_tsum hle hsumB).trans_eq ?_
  rw [tsum_mul_right, tsum_mul_left]
  rfl

/-- The mass of the kernel weight `e^{−|u|}`. -/
theorem integrable_exp_neg_abs' : Integrable (fun u : ℝ => Real.exp (-|u|)) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic (a := 1) (by norm_num) 0).congr_fun ?_ measurableSet_Iic
    intro u hu
    simp only [one_mul, abs_of_nonpos (Set.mem_Iic.mp hu), neg_neg]
  · refine (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).congr_fun ?_ measurableSet_Ioi
    intro u hu
    simp only [abs_of_pos (Set.mem_Ioi.mp hu), neg_mul, one_mul]

/-- A kernel of size `e^{|u|/2}` pairs with the weighted norm, with no support hypothesis. -/
theorem abs_integral_mul_kernel_le {d k : ℝ → ℝ} (hd : WeightedTwo d) (hk : Continuous k)
    (hb : ∀ u, |k u| ≤ Real.exp (|u| / 2)) :
    Integrable (fun u => d u * k u) ∧
      |∫ u, d u * k u| ≤ Real.sqrt (exponentialSourceMass d) *
        Real.sqrt (∫ u, Real.exp (-|u|)) := by
  let K : ℝ → ℝ := fun u => k u * Real.exp (-|u|)
  have hKc : Continuous K := hk.mul (by fun_prop)
  have hKsq (u : ℝ) : K u ^ 2 ≤ Real.exp (-|u|) := by
    have h1 : k u ^ 2 ≤ Real.exp |u| := by
      rw [← sq_abs]
      calc |k u| ^ 2 ≤ Real.exp (|u| / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb u) 2
        _ = Real.exp |u| := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have he : Real.exp (-|u|) ^ 2 = Real.exp (-|u|) * Real.exp (-|u|) := sq _
    have hne : Real.exp |u| * Real.exp (-|u|) = 1 := by rw [← Real.exp_add]; simp
    simp only [K, mul_pow, he]
    have hp := Real.exp_pos (-|u|)
    calc k u ^ 2 * (Real.exp (-|u|) * Real.exp (-|u|))
        ≤ Real.exp |u| * (Real.exp (-|u|) * Real.exp (-|u|)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (Real.exp |u| * Real.exp (-|u|)) * Real.exp (-|u|) := by ring
      _ = _ := by rw [hne, one_mul]
  have hK2 : Integrable (fun u => K u ^ 2) := by
    refine integrable_exp_neg_abs'.mono' (hKc.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hKsq u
  have hmul := HTGeometry.integrable_mul_of_sq_integrable hd.weightedMeas
    hKc.aestronglyMeasurable hd.sq hK2
  have heq : (fun u => (Real.exp |u| * d u) * K u) = fun u => d u * k u := by
    funext u
    have hne : Real.exp |u| * Real.exp (-|u|) = 1 := by rw [← Real.exp_add]; simp
    simp only [K]
    calc _ = (Real.exp |u| * Real.exp (-|u|)) * (d u * k u) := by ring
      _ = _ := by rw [hne, one_mul]
  rw [heq] at hmul
  refine ⟨hmul, ?_⟩
  have hcs := HTGeometry.sq_integral_mul_le hd.weightedMeas hKc.aestronglyMeasurable hd.sq hK2
  rw [heq] at hcs
  have hbound : (∫ u, K u ^ 2) ≤ ∫ u, Real.exp (-|u|) :=
    integral_mono hK2 integrable_exp_neg_abs' hKsq
  have hmass : (∫ u, (Real.exp |u| * d u) ^ 2) = exponentialSourceMass d := rfl
  rw [hmass] at hcs
  have hA := exponentialSourceMass_nonneg d
  rw [← Real.sqrt_mul hA]
  exact Real.abs_le_sqrt (hcs.trans (mul_le_mul_of_nonneg_left hbound hA))

/-- The cosh kernel has size `e^{|u|/2}`. -/
theorem abs_cosh_half_le_exp (u : ℝ) : |Real.cosh (u / 2)| ≤ Real.exp (|u| / 2) := by
  rw [abs_of_pos (Real.cosh_pos _), ← Real.cosh_abs, Real.cosh_eq]
  have h : |u / 2| = |u| / 2 := by rw [abs_div, abs_two]
  rw [h]
  have h1 : Real.exp (-(|u| / 2)) ≤ Real.exp (|u| / 2) :=
    Real.exp_le_exp.mpr (by linarith only [abs_nonneg u])
  linarith only [h1]

/-- The sinh kernel has size `e^{|u|/2}`. -/
theorem abs_sinh_half_le_exp (u : ℝ) : |Real.sinh (u / 2)| ≤ Real.exp (|u| / 2) := by
  have hc := abs_cosh_half_le_exp u
  rw [abs_of_pos (Real.cosh_pos _)] at hc
  have h1 := Real.sinh_lt_cosh (u / 2)
  have h2 := Real.sinh_lt_cosh (-(u / 2))
  rw [Real.sinh_neg, Real.cosh_neg] at h2
  rw [abs_le]
  constructor <;> linarith only [hc, h1, h2]

/-- The cosh moment moves by weighted amounts. -/
theorem abs_coshHalfMoment_sub_le {f g : ℝ → ℝ} (hf : WeightedTwo f) (hg : WeightedTwo g) :
    |coshHalfMoment f - coshHalfMoment g| ≤
      Real.sqrt (exponentialSourceMass fun t => f t - g t) * Real.sqrt (∫ u, Real.exp (-|u|)) := by
  have hc : Continuous fun u : ℝ => Real.cosh (u / 2) :=
    Real.continuous_cosh.comp (continuous_id.div_const 2)
  obtain ⟨-, h⟩ := abs_integral_mul_kernel_le (hf.sub hg) hc abs_cosh_half_le_exp
  obtain ⟨i1, -⟩ := abs_integral_mul_kernel_le hf hc abs_cosh_half_le_exp
  obtain ⟨i2, -⟩ := abs_integral_mul_kernel_le hg hc abs_cosh_half_le_exp
  have e : (∫ u, (f u - g u) * Real.cosh (u / 2)) = coshHalfMoment f - coshHalfMoment g := by
    unfold coshHalfMoment
    rw [← integral_sub i1 i2]
    congr 1; funext u; ring
  rwa [e] at h

/-- The sinh moment moves by weighted amounts. -/
theorem abs_sinhHalfMoment_sub_le {f g : ℝ → ℝ} (hf : WeightedTwo f) (hg : WeightedTwo g) :
    |sinhHalfMoment f - sinhHalfMoment g| ≤
      Real.sqrt (exponentialSourceMass fun t => f t - g t) * Real.sqrt (∫ u, Real.exp (-|u|)) := by
  have hc : Continuous fun u : ℝ => Real.sinh (u / 2) :=
    Real.continuous_sinh.comp (continuous_id.div_const 2)
  obtain ⟨-, h⟩ := abs_integral_mul_kernel_le (hf.sub hg) hc abs_sinh_half_le_exp
  obtain ⟨i1, -⟩ := abs_integral_mul_kernel_le hf hc abs_sinh_half_le_exp
  obtain ⟨i2, -⟩ := abs_integral_mul_kernel_le hg hc abs_sinh_half_le_exp
  have e : (∫ u, (f u - g u) * Real.sinh (u / 2)) = sinhHalfMoment f - sinhHalfMoment g := by
    unfold sinhHalfMoment
    rw [← integral_sub i1 i2]
    congr 1; funext u; ring
  rwa [e] at h

/-- On `y ≤ Y`, the weight `e^{2|y|}` is at most `e^{2Y}` plus a small multiple of `e^{−8y}`. -/
theorem exp_two_abs_le_add {Y y : ℝ} (hY : 0 ≤ Y) (hy : y ≤ Y) :
    Real.exp |y| ^ 2 ≤ Real.exp (2 * Y) + Real.exp (-(6 * Y)) * Real.exp (-(8 * y)) := by
  have hp1 := Real.exp_pos (2 * Y)
  have hp2 := mul_pos (Real.exp_pos (-(6 * Y))) (Real.exp_pos (-(8 * y)))
  have hsq : Real.exp |y| ^ 2 = Real.exp (2 * |y|) := by
    rw [← Real.exp_nat_mul]; congr 1
  rw [hsq]
  by_cases hlow : -Y ≤ y
  · have h : Real.exp (2 * |y|) ≤ Real.exp (2 * Y) :=
      Real.exp_le_exp.mpr (by linarith only [abs_le.mpr ⟨hlow, hy⟩])
    linarith only [h, hp2]
  · have hyn : y < -Y := not_le.mp hlow
    have habs : |y| = -y := abs_of_nonpos (by linarith only [hyn, hY])
    rw [habs, ← Real.exp_add]
    have h : Real.exp (2 * -y) ≤ Real.exp (-(6 * Y) + -(8 * y)) :=
      Real.exp_le_exp.mpr (by linarith only [hyn])
    linarith only [h, hp1]

/-- **The weighted norm is controlled by `L²` and the eighth exponential mass.** A function
vanishing above `Y` has finite weighted mass, at most `e^{2Y}‖d‖² + e^{−6Y} W₈(d)`. -/
theorem exponentialSourceMass_le_of_support {d : ℝ → ℝ} {Y : ℝ} (hY : 0 ≤ Y)
    (hm : AEStronglyMeasurable d volume) (hd2 : Integrable (fun y => d y ^ 2))
    (hd8 : Integrable (fun y => d y ^ 2 * Real.exp (-(8 * y))))
    (hs : ∀ᵐ y, Y < y → d y = 0) :
    WeightedTwo d ∧ exponentialSourceMass d ≤ Real.exp (2 * Y) * (∫ y, d y ^ 2) +
      Real.exp (-(6 * Y)) * ∫ y, d y ^ 2 * Real.exp (-(8 * y)) := by
  have hdom : Integrable (fun y => Real.exp (2 * Y) * d y ^ 2 +
      Real.exp (-(6 * Y)) * (d y ^ 2 * Real.exp (-(8 * y)))) :=
    (hd2.const_mul _).add (hd8.const_mul _)
  have hpt : ∀ᵐ y, (Real.exp |y| * d y) ^ 2 ≤ Real.exp (2 * Y) * d y ^ 2 +
      Real.exp (-(6 * Y)) * (d y ^ 2 * Real.exp (-(8 * y))) := by
    filter_upwards [hs] with y hy
    by_cases hyY : y ≤ Y
    · have h := mul_le_mul_of_nonneg_right (exp_two_abs_le_add hY hyY) (sq_nonneg (d y))
      calc (Real.exp |y| * d y) ^ 2 = Real.exp |y| ^ 2 * d y ^ 2 := mul_pow _ _ _
        _ ≤ _ := h
        _ = _ := by ring
    · rw [hy (not_le.mp hyY)]
      simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        add_zero, le_refl]
  have hmw : AEStronglyMeasurable (fun y => (Real.exp |y| * d y) ^ 2) volume :=
    ((Real.continuous_exp.comp continuous_abs).aestronglyMeasurable.mul hm).pow 2
  have hsq : Integrable (fun y => (Real.exp |y| * d y) ^ 2) := by
    refine hdom.mono' hmw ?_
    filter_upwards [hpt] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hy
  refine ⟨⟨hm, hsq⟩, ?_⟩
  have h := integral_mono_ae hsq hdom hpt
  rw [integral_add (hd2.const_mul _) (hd8.const_mul _), integral_const_mul, integral_const_mul] at h
  exact h

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

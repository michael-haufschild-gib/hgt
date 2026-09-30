import GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineSource
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Imaginary exponential envelope for the complete reciprocal sine trace

A real-segment mean-value estimate retains the necessary factor
`t * ‖w‖²`, so complementary packets need only reciprocal-square
summability. Both signs of the imaginary part have the same envelope.
A strict imaginary-frequency gap makes the full complementary sum
vanish after exponential normalization.

The actual-source corollaries zero only the selected packet; they retain
every other analytic multiplicity copy and require no RH premise.
-/

open Complex Set Filter Topology
open scoped Classical
namespace RHTower
noncomputable section


/-- The complex cosine is bounded by the exponential of the absolute imaginary part. -/
theorem liClock_norm_cos_le_imaginary_exp (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have hp : ‖Complex.exp (z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  have hm : ‖Complex.exp (-z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, mul_zero, mul_one, zero_sub, neg_neg]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  calc
    ‖Complex.cos z‖ = ‖Complex.exp (z*I)+Complex.exp (-z*I)‖/2 := by
      rw [Complex.cos, norm_div]
      norm_num
    _ ≤ (Real.exp |z.im|+Real.exp |z.im|)/2 :=
      div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add hp hm)) (by norm_num)
    _ = _ := by ring

/-- The sine contribution has an imaginary exponential envelope with the full square factor. -/
theorem liClock_norm_mul_sin_le_imaginary_exp {t : ℝ} (ht : 0 ≤ t) (w : ℂ) :
    ‖w*Complex.sin ((t:ℂ)*w)‖ ≤ t*‖w‖^2*Real.exp (t*|w.im|) := by
  have hd (u : ℝ) : HasDerivAt (fun x : ℝ => Complex.sin ((x:ℂ)*w))
      (Complex.cos ((u:ℂ)*w)*w) u := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (u:ℂ)).mul_const w).csin.comp_ofReal
  have hb (u : ℝ) (hu : u ∈ Icc 0 t) :
      ‖Complex.cos ((u:ℂ)*w)*w‖ ≤ ‖w‖*Real.exp (t*|w.im|) := by
    rw [norm_mul]
    have him : |((u:ℂ)*w).im| = u*|w.im| := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, abs_mul, abs_of_nonneg hu.1]
    have hc := liClock_norm_cos_le_imaginary_exp ((u:ℂ)*w)
    rw [him] at hc
    have he : Real.exp (u*|w.im|) ≤ Real.exp (t*|w.im|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hu.2 (abs_nonneg _))
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hc.trans he) (norm_nonneg w)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_hu : u ∈ Icc 0 t) => (hd u).hasDerivWithinAt)
    hb (convex_Icc (0:ℝ) t) (show (0:ℝ) ∈ Icc 0 t from ⟨le_rfl,ht⟩)
    (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩)
  have hs : ‖Complex.sin ((t:ℂ)*w)‖ ≤ (‖w‖*Real.exp (t*|w.im|))*t := by
    simpa only [Complex.ofReal_zero, zero_mul, Complex.sin_zero, sub_zero,
      Real.norm_eq_abs, abs_of_nonneg ht] using h
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left hs (norm_nonneg w)).trans_eq (by ring)

/-- An upper imaginary-frequency bound gives a separated reciprocal-square majorant. -/
theorem liClock_norm_mul_sin_le_of_imaginary_bound {t β : ℝ} (ht : 0 ≤ t)
    (w : ℂ) (hβ : |w.im| ≤ β) :
    ‖w*Complex.sin ((t:ℂ)*w)‖ ≤ ‖w‖^2*(t*Real.exp (β*t)) := by
  have he : Real.exp (t*|w.im|) ≤ Real.exp (β*t) := by
    apply Real.exp_le_exp.mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hβ ht
  exact (liClock_norm_mul_sin_le_imaginary_exp ht w).trans
    ((mul_le_mul_of_nonneg_left he (mul_nonneg ht (sq_nonneg _))).trans_eq (by ring))

/-- Square summability and a uniform imaginary bound give absolute summability of the sine trace. -/
theorem liClock_summable_norm_sine_of_imaginary_bound {ι : Type*} (w : ι → ℂ)
    (hs : Summable (fun q => ‖w q‖^2)) {t β : ℝ}
    (hβ : ∀ q, |(w q).im| ≤ β) (ht : 0 ≤ t) :
    Summable (fun q => ‖w q*Complex.sin ((t:ℂ)*w q)‖) := by
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _
    (hs.mul_right (t*Real.exp (β*t)))
  intro q
  exact liClock_norm_mul_sin_le_of_imaginary_bound ht (w q) (hβ q)

/-- The full sine sum is bounded by its reciprocal-square mass and imaginary exponential rate. -/
theorem liClock_norm_tsum_sine_le_of_imaginary_bound {ι : Type*} (w : ι → ℂ)
    (hs : Summable (fun q => ‖w q‖^2)) {t β : ℝ}
    (hβ : ∀ q, |(w q).im| ≤ β) (ht : 0 ≤ t) :
    ‖∑' q, w q*Complex.sin ((t:ℂ)*w q)‖ ≤
      (∑' q, ‖w q‖^2)*t*Real.exp (β*t) := by
  have hn := liClock_summable_norm_sine_of_imaginary_bound w hs hβ ht
  calc
    _ ≤ ∑' q, ‖w q*Complex.sin ((t:ℂ)*w q)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' q, ‖w q‖^2*(t*Real.exp (β*t)) :=
      Summable.tsum_le_tsum (fun q =>
        liClock_norm_mul_sin_le_of_imaginary_bound ht (w q) (hβ q)) hn
        (hs.mul_right (t*Real.exp (β*t)))
    _ = _ := by rw [tsum_mul_right]; ring

private theorem linear_exp_gap_tendsto_zero {β b : ℝ} (hgap : β < b) (W : ℝ) :
    Tendsto (fun t : ℝ => W*t*Real.exp (-(b-β)*t)) atTop (𝓝 0) := by
  have hδ : 0 < b-β := sub_pos.mpr hgap
  have hbase : Tendsto (fun t : ℝ => ((b-β)*t)*Real.exp (-((b-β)*t)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, id_eq] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop hδ)
  have heq : (fun t : ℝ => (W/(b-β))*(((b-β)*t)*Real.exp (-((b-β)*t)))) =
      (fun t : ℝ => W*t*Real.exp (-(b-β)*t)) := by
    funext t
    rw [neg_mul]
    field_simp [hδ.ne']
  simpa only [heq, mul_zero] using hbase.const_mul (W/(b-β))

/-- A strict imaginary-frequency gap makes the exponentially normalized full sine sum tend to zero. -/
theorem liClock_tendsto_normalized_sine_tsum_zero_of_imaginary_gap {ι : Type*}
    (w : ι → ℂ) (hs : Summable (fun q => ‖w q‖^2)) {β b : ℝ}
    (hβ : ∀ q, |(w q).im| ≤ β) (hgap : β < b) :
    Tendsto (fun t : ℝ => (Real.exp (-b*t):ℂ)*
      ∑' q, w q*Complex.sin ((t:ℂ)*w q)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (linear_exp_gap_tendsto_zero hgap (∑' q, ‖w q‖^2))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (mul_le_mul_of_nonneg_left
    (liClock_norm_tsum_sine_le_of_imaginary_bound w hs hβ ht) (Real.exp_nonneg _)).trans_eq ?_
  rw [show Real.exp (-b*t)*((∑' q, ‖w q‖^2)*t*Real.exp (β*t)) =
    ((∑' q, ‖w q‖^2)*t)*(Real.exp (-b*t)*Real.exp (β*t)) by ring,
    ← Real.exp_add]
  congr 2
  ring

private theorem actual_reciprocal_norm_sq_summable :
    Summable (fun q : XiZeroCopy => ‖(xiSpectralPoint q)⁻¹‖^2) := by
  simpa only [norm_inv, one_div, inv_pow] using xiSpectralPoint_inv_sq_summable

private theorem summable_zeroed_reciprocal_sq (Q : Set XiZeroCopy) :
    Summable (fun q : XiZeroCopy => ‖if q ∈ Q then (0:ℂ) else (xiSpectralPoint q)⁻¹‖^2) := by
  classical
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ actual_reciprocal_norm_sq_summable
  intro q
  by_cases hq : q ∈ Q <;> simp [hq]

/-- The actual complementary trace retains all copies and is bounded by the full reciprocal-square mass. -/
theorem liEvenCrossActualClock_norm_complement_le (Q : Set XiZeroCopy) {t β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : ∀ q, q ∉ Q → |((xiSpectralPoint q)⁻¹).im| ≤ β)
    (ht : 0 ≤ t) :
    ‖∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockSineAtom t q‖ ≤
      (∑' q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖^2)*t*Real.exp (β*t) := by
  classical
  let w : XiZeroCopy → ℂ := fun q => if q ∈ Q then 0 else (xiSpectralPoint q)⁻¹
  have hs : Summable (fun q => ‖w q‖^2) := summable_zeroed_reciprocal_sq Q
  have hb (q : XiZeroCopy) : |(w q).im| ≤ β := by
    by_cases hq : q ∈ Q
    · simpa [w,hq] using hβ0
    · simpa [w,hq] using hβ q hq
  have heq : (fun q : XiZeroCopy => if q ∈ Q then 0 else liEvenCrossActualClockSineAtom t q) =
      (fun q => w q*Complex.sin ((t:ℂ)*w q)) := by
    funext q
    by_cases hq : q ∈ Q <;> simp [w,hq,liEvenCrossActualClockSineAtom]
  rw [heq]
  have hmass : (∑' q, ‖w q‖^2) ≤ ∑' q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖^2 := by
    apply Summable.tsum_le_tsum _ hs actual_reciprocal_norm_sq_summable
    intro q
    by_cases hq : q ∈ Q <;> simp [w,hq]
  exact (liClock_norm_tsum_sine_le_of_imaginary_bound w hs hb ht).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmass ht) (Real.exp_nonneg _))

/-- The actual complementary trace vanishes under a strict exponential gap, without an RH premise. -/
theorem liEvenCrossActualClock_tendsto_normalized_complement_zero (Q : Set XiZeroCopy)
    {β b : ℝ} (hβ0 : 0 ≤ β)
    (hβ : ∀ q, q ∉ Q → |((xiSpectralPoint q)⁻¹).im| ≤ β) (hgap : β < b) :
    Tendsto (fun t : ℝ => (Real.exp (-b*t):ℂ)*
      ∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockSineAtom t q)
      atTop (𝓝 0) := by
  classical
  let w : XiZeroCopy → ℂ := fun q => if q ∈ Q then 0 else (xiSpectralPoint q)⁻¹
  have hs : Summable (fun q => ‖w q‖^2) := summable_zeroed_reciprocal_sq Q
  have hb (q : XiZeroCopy) : |(w q).im| ≤ β := by
    by_cases hq : q ∈ Q
    · simpa [w,hq] using hβ0
    · simpa [w,hq] using hβ q hq
  have heq : (fun t : ℝ => (Real.exp (-b*t):ℂ)*
      ∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockSineAtom t q) =
      (fun t : ℝ => (Real.exp (-b*t):ℂ)*∑' q, w q*Complex.sin ((t:ℂ)*w q)) := by
    funext t
    congr 1
    apply tsum_congr
    intro q
    by_cases hq : q ∈ Q <;> simp [w,hq,liEvenCrossActualClockSineAtom]
  rw [heq]
  exact liClock_tendsto_normalized_sine_tsum_zero_of_imaginary_gap w hs hb hgap

end
end RHTower

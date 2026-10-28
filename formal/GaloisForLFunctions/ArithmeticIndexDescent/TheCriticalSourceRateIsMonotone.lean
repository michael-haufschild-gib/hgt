import Mathlib.Analysis.Convex.Deriv
import GaloisForLFunctions.ArithmeticIndexDescent.TheQuadraticScaleWorkDetectsEveryException

/-!
# Inverse-scale curvature makes the critical source rate monotone

Rational damping is convex in its inverse-square scale after reflection.
The zero-free height gap controls the second derivative's mixed term.
Convex secants therefore make each critically normalized pair increment
increase. Absolute convergence transfers this order to the completed
arithmetic source, without differentiating an infinite sum.
-/

open Set Filter RHTower
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open scoped Topology
noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

private theorem inverseScale_secant_antitone {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) f) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (f (b / 4) - f b) / b ≤ (f (a / 4) - f a) / a := by
  have hb : 0 < b := ha.trans_le hab
  have h1 := hf.monotoneOn_slope_gt (show a / 4 ∈ Ici 0 from (by positivity : 0 ≤ a / 4))
    (show a ∈ {y ∈ Ici 0 | a / 4 < y} from ⟨ha.le, by linarith only [ha]⟩)
    (show b ∈ {y ∈ Ici 0 | a / 4 < y} from ⟨hb.le, by linarith only [ha, hab]⟩) hab
  have h2 := hf.monotoneOn_slope_lt (show b ∈ Ici 0 from hb.le)
    (show a / 4 ∈ {y ∈ Ici 0 | y < b} from
      ⟨(by positivity : 0 ≤ a / 4), by linarith only [ha, hab]⟩)
    (show b / 4 ∈ {y ∈ Ici 0 | y < b} from
      ⟨(by positivity : 0 ≤ b / 4), by linarith only [hb]⟩)
    (show a / 4 ≤ b / 4 by linarith only [hab])
  rw [slope_comm f b (a / 4), slope_comm f b (b / 4)] at h2
  have h := h1.trans h2
  simp only [slope_def_field] at h
  rw [div_le_div_iff₀ (by linarith only [ha] : 0 < a - a / 4)
    (by linarith only [hb] : 0 < b - b / 4)] at h
  rw [div_le_div_iff₀ hb ha]
  nlinarith only [h]

private def curvatureHeightWeight (r t : ℝ) : ℝ := (t ^ 2) ^ 2 / (1 + r * t ^ 2) ^ 4

private theorem curvatureWeight_nonneg (r t : ℝ) : 0 ≤ curvatureHeightWeight r t := by
  unfold curvatureHeightWeight
  positivity

/-- Fourth-power ratio bounds absorb changes of the curvature profile. -/
private theorem curvatureWeight_relative_ordered (r a b : ℝ) (hr : 0 ≤ r)
    (ha : 4 ≤ a) (hab : a ≤ b) :
    2 * |curvatureHeightWeight r a - curvatureHeightWeight r b| ≤
      (b - a) * (curvatureHeightWeight r a + curvatureHeightWeight r b) := by
  have hb : 4 ≤ b := ha.trans hab
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 : 0 < b := ha0.trans_le hab
  have hA : 0 < 1 + r * a ^ 2 := by positivity
  have hB : 0 < 1 + r * b ^ 2 := by positivity
  have hsq : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha0.le hb0.le).mpr hab
  have hratio : a ^ 2 / (1 + r * a ^ 2) ≤ b ^ 2 / (1 + r * b ^ 2) := by
    rw [div_le_div_iff₀ hA hB]
    nlinarith only [hsq]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ a ^ 2 / (1 + r * a ^ 2)) hratio 4
  have hpower (t : ℝ) : t ^ 4 * curvatureHeightWeight r t =
      (t ^ 2 / (1 + r * t ^ 2)) ^ 4 := by
    simp only [curvatureHeightWeight, div_pow]
    ring
  have hleft : a ^ 4 * curvatureHeightWeight r a ≤ b ^ 4 * curvatureHeightWeight r b := by
    rw [hpower, hpower]
    exact hp
  have hinv : 1 / (1 + r * b ^ 2) ≤ 1 / (1 + r * a ^ 2) := by
    rw [div_le_div_iff₀ hB hA]
    nlinarith only [mul_le_mul_of_nonneg_left hsq hr]
  have hi := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (1 + r * b ^ 2)) hinv 4
  have hmul := mul_le_mul_of_nonneg_left hi (show 0 ≤ a ^ 4 * b ^ 4 by positivity)
  have hright : a ^ 4 * curvatureHeightWeight r b ≤ b ^ 4 * curvatureHeightWeight r a := by
    calc
      _ = (a ^ 4 * b ^ 4) * (1 / (1 + r * b ^ 2)) ^ 4 := by
        simp only [curvatureHeightWeight, div_pow, one_pow]
        ring
      _ ≤ (a ^ 4 * b ^ 4) * (1 / (1 + r * a ^ 2)) ^ 4 := hmul
      _ = _ := by
        simp only [curvatureHeightWeight, div_pow, one_pow]
        ring
  have hbase : 4 * (a + b) ≤ a ^ 2 + b ^ 2 := by
    nlinarith only [mul_nonneg ha0.le (sub_nonneg.mpr ha),
      mul_nonneg hb0.le (sub_nonneg.mpr hb)]
  have hfourth : 2 * (a + b) * (a ^ 2 + b ^ 2) ≤ a ^ 4 + b ^ 4 := by
    have hm := mul_le_mul_of_nonneg_right hbase (add_nonneg (sq_nonneg a) (sq_nonneg b))
    nlinarith only [hm, sq_nonneg (a ^ 2 - b ^ 2)]
  have hpoly : 2 * (b ^ 4 - a ^ 4) ≤ (b - a) * (a ^ 4 + b ^ 4) := by
    have hm := mul_le_mul_of_nonneg_left hfourth (sub_nonneg.mpr hab)
    nlinarith only [hm]
  have hcross : (a ^ 4 + b ^ 4) *
      |curvatureHeightWeight r a - curvatureHeightWeight r b| ≤
      (b ^ 4 - a ^ 4) * (curvatureHeightWeight r a + curvatureHeightWeight r b) := by
    by_cases h : 0 ≤ curvatureHeightWeight r a - curvatureHeightWeight r b
    · rw [abs_of_nonneg h]
      nlinarith only [hleft]
    · rw [abs_of_nonpos (le_of_not_ge h)]
      nlinarith only [hright]
  have hpaid := mul_le_mul_of_nonneg_right hpoly
    (add_nonneg (curvatureWeight_nonneg r a) (curvatureWeight_nonneg r b))
  by_contra! hfail
  have hstrict := mul_pos (show 0 < a ^ 4 + b ^ 4 by positivity) (sub_pos.mpr hfail)
  nlinarith only [hcross, hpaid, hstrict]

private theorem curvatureWeight_relative (r t u : ℝ) (hr : 0 ≤ r)
    (ht : 4 ≤ |t|) (hu : 4 ≤ |u|) :
    2 * |curvatureHeightWeight r t - curvatureHeightWeight r u| ≤
      |t - u| * (curvatureHeightWeight r t + curvatureHeightWeight r u) := by
  have hbase : 2 * |curvatureHeightWeight r (abs t) - curvatureHeightWeight r (abs u)| ≤
      |abs t - abs u| * (curvatureHeightWeight r (abs t) + curvatureHeightWeight r (abs u)) := by
    rcases le_total |t| |u| with htu | hut
    · simpa only [abs_of_nonpos (sub_nonpos.mpr htu), neg_sub] using
        curvatureWeight_relative_ordered r |t| |u| hr ht htu
    · have h := curvatureWeight_relative_ordered r |u| |t| hr hu hut
      calc
        _ = 2 * |curvatureHeightWeight r (abs u) - curvatureHeightWeight r (abs t)| := by
          rw [abs_sub_comm]
        _ ≤ (|t| - |u|) * (curvatureHeightWeight r (abs u) + curvatureHeightWeight r (abs t)) := h
        _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hut)]; ring
  simp only [curvatureHeightWeight, sq_abs] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le_abs_sub t u)
    (add_nonneg (curvatureWeight_nonneg r t) (curvatureWeight_nonneg r u)))

/-- Rational damping in the inverse-square scale coordinate. -/
def inverseScaleDamping (r t : ℝ) : ℝ := 1 / (1 + r * t ^ 2) ^ 2

private theorem inverseScaleDamping_hasDerivAt (r t : ℝ) (hr : 0 ≤ r) :
    HasDerivAt (fun a => inverseScaleDamping a t)
      (-2 * t ^ 2 / (1 + r * t ^ 2) ^ 3) r := by
  have hd : 1 + r * t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hbase := ((hasDerivAt_id r).mul_const (t ^ 2)).const_add 1
  convert (hasDerivAt_const r (1 : ℝ)).div (hbase.pow 2) (pow_ne_zero 2 hd) using 1 <;>
    try rfl
  dsimp only [Pi.pow_apply, id_eq]
  field_simp
  ring

private theorem inverseScaleVelocity_hasDerivAt (r t : ℝ) (hr : 0 ≤ r) :
    HasDerivAt (fun a => -2 * t ^ 2 / (1 + a * t ^ 2) ^ 3)
      (6 * curvatureHeightWeight r t) r := by
  have hd : 1 + r * t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hbase := ((hasDerivAt_id r).mul_const (t ^ 2)).const_add 1
  convert (hasDerivAt_const r (-2 * t ^ 2)).div (hbase.pow 3) (pow_ne_zero 3 hd) using 1 <;>
    try rfl
  dsimp only [curvatureHeightWeight, Pi.pow_apply, id_eq]
  field_simp
  ring

private theorem curvatureWork_nonneg (r x y t u : ℝ) (hr : 0 ≤ r)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) (ht : 4 ≤ |t|) (hu : 4 ≤ |u|) :
    0 ≤ reflectedWork x y (t - u) (curvatureHeightWeight r t) (curvatureHeightWeight r u) := by
  apply (reflectedWork_bounds x y (t - u) _ _ ?_).1
  have hv := curvatureWeight_nonneg r t
  have hw := curvatureWeight_nonneg r u
  by_cases hd : (t - u) ^ 2 ≤ 1
  · have h1 := mul_le_mul_of_nonneg_right (curvatureWeight_relative r t u hr ht hu)
      (abs_nonneg (reflectedCross x y (t - u)))
    have h2 := mul_le_mul_of_nonneg_left (reflectedCross_near x y (t - u) hxy hd)
      (add_nonneg hv hw)
    rw [abs_mul] at h2 ⊢
    nlinarith only [h1, h2]
  · have hdiff : |curvatureHeightWeight r t - curvatureHeightWeight r u| ≤
        curvatureHeightWeight r t + curvatureHeightWeight r u :=
      abs_le.mpr ⟨by linarith only [hv, hw], by linarith only [hv, hw]⟩
    rw [abs_mul]
    exact mul_le_mul hdiff (reflectedCross_far x y (t - u) hxy (le_of_not_ge hd))
      (abs_nonneg _) (add_nonneg hv hw)

/-- Reflected work is convex in inverse-square scale above the zero-free height gap. -/
theorem inverseScale_reflectedWork_convex (x y t u : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) (ht : 4 ≤ |t|) (hu : 4 ≤ |u|) :
    ConvexOn ℝ (Ici 0) (fun r => reflectedWork x y (t - u)
      (inverseScaleDamping r t) (inverseScaleDamping r u)) := by
  let f' : ℝ → ℝ := fun r => reflectedWork x y (t - u)
    (-2 * t ^ 2 / (1 + r * t ^ 2) ^ 3) (-2 * u ^ 2 / (1 + r * u ^ 2) ^ 3)
  let f'' : ℝ → ℝ := fun r => 6 * reflectedWork x y (t - u)
    (curvatureHeightWeight r t) (curvatureHeightWeight r u)
  have hd (r : ℝ) (hr : 0 ≤ r) : HasDerivAt
      (fun a => reflectedWork x y (t - u) (inverseScaleDamping a t) (inverseScaleDamping a u))
      (f' r) r := by
    have h1 := inverseScaleDamping_hasDerivAt r t hr
    have h2 := inverseScaleDamping_hasDerivAt r u hr
    exact (((h1.add h2).mul_const (reflectedEnergy x y (t - u))).add
      ((h1.sub h2).mul_const (reflectedCross x y (t - u)))).div_const 2
  have hdd (r : ℝ) (hr : 0 ≤ r) : HasDerivAt f' (f'' r) r := by
    have h1 := inverseScaleVelocity_hasDerivAt r t hr
    have h2 := inverseScaleVelocity_hasDerivAt r u hr
    have h := (((h1.add h2).mul_const (reflectedEnergy x y (t - u))).add
      ((h1.sub h2).mul_const (reflectedCross x y (t - u)))).div_const 2
    convert h using 1 <;> try rfl
    dsimp only [f'', reflectedWork]
    ring
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'') (convex_Ici 0)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt) ?_ ?_ ?_
  · intro r hr
    rw [interior_Ici] at hr
    exact (hd r (show 0 < r from hr).le).hasDerivWithinAt
  · intro r hr
    rw [interior_Ici] at hr
    exact (hdd r (show 0 < r from hr).le).hasDerivWithinAt
  · intro r hr
    rw [interior_Ici] at hr
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
      (curvatureWork_nonneg r x y t u (show 0 < r from hr).le hxy ht hu)

private theorem heightDamping_as_inverseScaleDamping (t : ℝ) {R : ℝ} (hR : 0 < R) :
    heightDamping R t = inverseScaleDamping (1 / R ^ 2) t := by
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  have hsum : R ^ 2 + t ^ 2 ≠ 0 := by positivity
  have hnorm : 1 + 1 / R ^ 2 * t ^ 2 ≠ 0 := by positivity
  unfold heightDamping inverseScaleDamping
  field_simp [hR2, hsum, hnorm]

private theorem normalized_pair_eq_secant (x y t u R : ℝ) (hR : 0 < R) :
    let f : ℝ → ℝ := fun a => reflectedWork x y (t - u)
      (inverseScaleDamping a t) (inverseScaleDamping a u)
    R ^ 2 * (reflectedWork x y (t - u) (heightDamping (2 * R) t) (heightDamping (2 * R) u) -
      reflectedWork x y (t - u) (heightDamping R t) (heightDamping R u)) =
      (f ((1 / R ^ 2) / 4) - f (1 / R ^ 2)) / (1 / R ^ 2) := by
  have h2R : 0 < 2 * R := by positivity
  have htwo : 1 / (2 * R) ^ 2 = (1 / R ^ 2) / 4 := by
    field_simp
    ring
  dsimp only
  rw [heightDamping_as_inverseScaleDamping t h2R, heightDamping_as_inverseScaleDamping u h2R,
    heightDamping_as_inverseScaleDamping t hR, heightDamping_as_inverseScaleDamping u hR, htwo]
  simp only [div_eq_mul_inv, one_mul, inv_inv]
  ring

private theorem normalized_pair_monotone (x y t u : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) (ht : 4 ≤ |t|) (hu : 4 ≤ |u|) :
    MonotoneOn (fun R => R ^ 2 *
      (reflectedWork x y (t - u) (heightDamping (2 * R) t) (heightDamping (2 * R) u) -
        reflectedWork x y (t - u) (heightDamping R t) (heightDamping R u))) (Ioi 0) := by
  intro R hR S hS hRS
  change 0 < R at hR
  change 0 < S at hS
  dsimp only
  rw [normalized_pair_eq_secant x y t u R hR, normalized_pair_eq_secant x y t u S hS]
  exact inverseScale_secant_antitone (inverseScale_reflectedWork_convex x y t u hxy ht hu)
    (by positivity : 0 < 1 / S ^ 2)
    (one_div_le_one_div_of_le (sq_pos_of_pos hR) ((sq_le_sq₀ hR.le hS.le).mpr hRS))

/-- The critical normalization of one reflected pair increment. -/
def xiQuadraticPairWork (R : ℝ) (p q : XiZeroCopy) : ℝ :=
  R ^ 2 * (xiDampedPairWork (2 * R) p q - xiDampedPairWork R p q)

/-- Convexity in inverse-square scale makes every critically normalized pair increase. -/
theorem xiQuadraticPairWork_monotoneOn (p q : XiZeroCopy) :
    MonotoneOn (fun R => xiQuadraticPairWork R p q) (Ioi 0) :=
  normalized_pair_monotone _ _ _ _ (xiSignedDepth_pair_bound p q)
    (four_le_abs_xiZeroHeight p) (four_le_abs_xiZeroHeight q)

theorem xiQuadraticPairWork_nonneg {R : ℝ} (hR : 4 ≤ R) (p q : XiZeroCopy) :
    0 ≤ xiQuadraticPairWork R p q := by
  apply mul_nonneg (sq_nonneg R)
  apply sub_nonneg.mpr
  exact xiDampedPairWork_monotoneOn p q
    (show 0 ≤ R by linarith only [hR]) (show 0 ≤ 2 * R by linarith only [hR])
    (show R ≤ 2 * R by linarith only [hR])

theorem xiQuadraticPairWork_summable {R : ℝ} (hR : 4 ≤ R) :
    Summable (fun pq : XiZeroCopy × XiZeroCopy => xiQuadraticPairWork R pq.1 pq.2) :=
  ((xiDampedPairWork_summable (show 4 ≤ 2 * R by linarith only [hR])).sub
    (xiDampedPairWork_summable hR)).mul_left (R ^ 2)

/-- The critical arithmetic source rate is an absolutely convergent sum of pair increments. -/
theorem quadraticWorkIncrement_eq_tsum {R : ℝ} (hR : 4 ≤ R) :
    quadraticWorkIncrement R =
      (∑' pq : XiZeroCopy × XiZeroCopy, xiQuadraticPairWork R pq.1 pq.2) / 4 := by
  unfold quadraticWorkIncrement doubledSourceWorkIncrement xiDampedSourceWork xiQuadraticPairWork
  rw [tsum_mul_left,
    (xiDampedPairWork_summable (show 4 ≤ 2 * R by linarith only [hR])).tsum_sub
      (xiDampedPairWork_summable hR)]
  ring

/-- The completed source rate is monotone; no derivative is interchanged with an infinite sum. -/
theorem quadraticWorkIncrement_monotoneOn : MonotoneOn quadraticWorkIncrement (Ici 4) := by
  intro R hR S hS hRS
  change 4 ≤ R at hR
  change 4 ≤ S at hS
  rw [quadraticWorkIncrement_eq_tsum hR, quadraticWorkIncrement_eq_tsum hS]
  apply div_le_div_of_nonneg_right ?_ (by norm_num : (0 : ℝ) ≤ 4)
  exact Summable.tsum_le_tsum
    (fun pq => xiQuadraticPairWork_monotoneOn pq.1 pq.2
      (show 0 < R by linarith only [hR]) (show 0 < S by linarith only [hS]) hRS)
    (xiQuadraticPairWork_summable hR) (xiQuadraticPairWork_summable hS)

/-- The limiting pair retains both height-square weights and their reflected mixed term. -/
theorem xiQuadraticPairWork_tendsto (p q : XiZeroCopy) :
    Tendsto (fun R : ℝ => xiQuadraticPairWork R p q) atTop
      (𝓝 ((3 / 2 : ℝ) * reflectedWork
        (xiSignedDepth p - xiSignedDepth q) (xiSignedDepth p + xiSignedDepth q)
        (xiZeroHeight p - xiZeroHeight q) (xiZeroHeight p ^ 2) (xiZeroHeight q ^ 2))) := by
  have hp := heightDamping_quadraticGap_tendsto (xiZeroHeight p)
  have hq := heightDamping_quadraticGap_tendsto (xiZeroHeight q)
  have h := (((hp.add hq).mul_const
      (reflectedEnergy (xiSignedDepth p - xiSignedDepth q) (xiSignedDepth p + xiSignedDepth q)
        (xiZeroHeight p - xiZeroHeight q))).add
    ((hp.sub hq).mul_const
      (reflectedCross (xiSignedDepth p - xiSignedDepth q) (xiSignedDepth p + xiSignedDepth q)
        (xiZeroHeight p - xiZeroHeight q)))).div_const 2
  convert h using 1
  · funext R
    unfold xiQuadraticPairWork xiDampedPairWork reflectedWork
    ring
  · congr 1
    unfold reflectedWork
    ring

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.inverseScale_reflectedWork_convex
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.xiQuadraticPairWork_monotoneOn
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.quadraticWorkIncrement_monotoneOn
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.xiQuadraticPairWork_tendsto

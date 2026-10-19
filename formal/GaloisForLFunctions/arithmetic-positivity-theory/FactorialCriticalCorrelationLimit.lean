import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialAffineClockResonance
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialPhaseHarmonicLayers
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialPhaseBohrCoercivityAndTailIndependence
import GaloisForLFunctions.HTGeometry.SoninCosineRiemannLebesgue
import Mathlib.Analysis.Normed.Group.Tannery

/-! Complete critical correlations of the actual factorial phases. Cosine decay
separates the fast arithmetic slopes from the slow collar detuning; absolute
harmonic summability retains every exact dilation resonance. -/

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

private theorem limit_weight_integrable :
    IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one

private theorem limit_weight_mass : (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ)) = 1 := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
  norm_num

private theorem limit_integrable {f : ℝ → ℝ} {B : ℝ}
    (hf : Continuous f) (hB : ∀ v, |f v| ≤ B) :
    IntegrableOn (fun v => v ^ (-2 : ℝ) * f v) (Ioi (1 : ℝ)) := by
  refine Integrable.mono' (limit_weight_integrable.const_mul B)
    (limit_weight_integrable.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hw : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hv)) _
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw, Real.norm_eq_abs]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hB v) hw

private theorem limit_integral_bound {f : ℝ → ℝ} {B : ℝ}
    (hf : Continuous f) (hB : ∀ v, |f v| ≤ B) :
    |∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * f v| ≤ B := by
  have hi := limit_integrable hf hB
  calc |∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * f v|
      ≤ ∫ v in Ioi (1 : ℝ), ‖v ^ (-2 : ℝ) * f v‖ :=
        by simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := volume.restrict (Ioi (1 : ℝ)))
            (fun v : ℝ => v ^ (-2 : ℝ) * f v))
    _ ≤ ∫ v in Ioi (1 : ℝ), B * v ^ (-2 : ℝ) := by
      refine setIntegral_mono_on hi.norm (limit_weight_integrable.const_mul B)
        measurableSet_Ioi fun v hv => ?_
      have hw : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hv)) _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw, Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hB v) hw
    _ = B := by rw [integral_const_mul, limit_weight_mass, mul_one]

private def limitCosine (a : ℝ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * v)

private theorem limit_cosine_integrable (a : ℝ) :
    IntegrableOn (fun v => v ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * v))
      (Ioi (1 : ℝ)) :=
  limit_integrable (by fun_prop) (fun v => Real.abs_cos_le_one _)

private theorem limit_cosine_bound (a : ℝ) : |limitCosine a| ≤ 1 :=
  limit_integral_bound (by fun_prop) (fun v => Real.abs_cos_le_one _)

private theorem limit_cosine_zero : limitCosine 0 = 1 := by
  simpa [limitCosine] using limit_weight_mass

private theorem limit_cosine_neg (a : ℝ) : limitCosine (-a) = limitCosine a := by
  unfold limitCosine
  apply integral_congr_ae
  filter_upwards [] with v
  rw [show 2 * Real.pi * (-a) * v = -(2 * Real.pi * a * v) by ring, Real.cos_neg]

private theorem limit_cosine_tendsto {a : ℕ → ℝ} {b : ℝ}
    (ha : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun n => limitCosine (a n)) atTop (𝓝 (limitCosine b)) := by
  apply tendsto_integral_of_dominated_convergence (fun v : ℝ => v ^ (-2 : ℝ))
  · intro n
    exact (limit_cosine_integrable (a n)).aestronglyMeasurable
  · exact limit_weight_integrable
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hw : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hv)) _
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw, Real.norm_eq_abs]
    exact mul_le_of_le_one_right hw (Real.abs_cos_le_one _)
  · filter_upwards [] with v
    exact ((Real.continuous_cos.tendsto _).comp
      ((ha.const_mul (2 * Real.pi)).mul_const v)).const_mul _

private theorem limit_cosine_atTop : Tendsto limitCosine atTop (𝓝 0) := by
  let w : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (fun v => v ^ (-2 : ℝ))
  have hi : Integrable w := limit_weight_integrable.integrable_indicator measurableSet_Ioi
  have h := RHTower.tendsto_integral_mul_cos_atTop hi
  apply h.congr
  intro a
  unfold limitCosine
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with v
  by_cases hv : v ∈ Ioi (1 : ℝ)
  · simp only [w, indicator_of_mem hv]
    congr 2
    ring
  · simp [w, indicator_of_notMem hv]

private theorem limit_cosine_affine {a b : ℝ} {z : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 b)) :
    Tendsto (fun n => limitCosine (a * ((n + 1 : ℕ) : ℝ) + z n)) atTop
      (𝓝 (if a = 0 then limitCosine b else 0)) := by
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  by_cases ha : a = 0
  · simpa [ha] using limit_cosine_tendsto hz
  · rw [if_neg ha]
    rcases lt_or_gt_of_ne ha with ha | ha
    · have hpos : 0 < -a := by linarith
      have hfreq := (Filter.Tendsto.const_mul_atTop hpos hN).atTop_add hz.neg
      have h := limit_cosine_atTop.comp hfreq
      apply h.congr
      intro n
      dsimp only [Function.comp_def]
      rw [show -a * ((n+1 : ℕ) : ℝ) + -z n =
        -(a * ((n+1 : ℕ) : ℝ) + z n) by ring, limit_cosine_neg]
    · exact limit_cosine_atTop.comp
        ((Filter.Tendsto.const_mul_atTop ha hN).atTop_add hz)

private def limitCosProduct (a b : ℝ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
    Real.cos (2 * Real.pi * a * v) * Real.cos (2 * Real.pi * b * v)

private theorem limit_cos_product_integrable (a b : ℝ) :
    IntegrableOn (fun v => v ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * v) *
      Real.cos (2 * Real.pi * b * v)) (Ioi (1 : ℝ)) := by
  have h := limit_integrable (f := fun v =>
    Real.cos (2 * Real.pi * a * v) * Real.cos (2 * Real.pi * b * v))
    (B := 1) (by fun_prop) (fun v => by
      rw [abs_mul]
      exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
  simpa only [mul_assoc] using h

private theorem limit_cos_product_eq (a b : ℝ) :
    limitCosProduct a b = (limitCosine (a-b) + limitCosine (a+b)) / 2 := by
  have hp (v : ℝ) :
      v ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * v) * Real.cos (2 * Real.pi * b * v) =
      (1 / 2 : ℝ) * (v ^ (-2 : ℝ) * Real.cos (2 * Real.pi * (a-b) * v) +
        v ^ (-2 : ℝ) * Real.cos (2 * Real.pi * (a+b) * v)) := by
    rw [show 2 * Real.pi * (a-b) * v =
      2 * Real.pi * a * v - 2 * Real.pi * b * v by ring,
      show 2 * Real.pi * (a+b) * v =
      2 * Real.pi * a * v + 2 * Real.pi * b * v by ring,
      Real.cos_sub, Real.cos_add]
    ring
  unfold limitCosProduct
  simp_rw [hp]
  rw [integral_const_mul, integral_add (limit_cosine_integrable _) (limit_cosine_integrable _)]
  unfold limitCosine
  ring

private theorem limit_cos_product_tendsto {a b u v : ℝ} {s t : ℕ → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : Tendsto s atTop (𝓝 u))
    (ht : Tendsto t atTop (𝓝 v)) :
    Tendsto (fun n => limitCosProduct (a * ((n+1 : ℕ) : ℝ) + s n)
      (b * ((n+1 : ℕ) : ℝ) + t n)) atTop
      (𝓝 (if a = b then limitCosine (u-v) / 2 else 0)) := by
  have hminus := limit_cosine_affine (a := a-b) (hs.sub ht)
  have hplus := limit_cosine_affine (a := a+b) (hs.add ht)
  have hab : a+b ≠ 0 := by linarith
  simp only [if_neg hab] at hplus
  have h := (hminus.add hplus).div_const 2
  have he (n : ℕ) :
      limitCosProduct (a * ((n+1 : ℕ) : ℝ) + s n) (b * ((n+1 : ℕ) : ℝ) + t n) =
      (limitCosine ((a-b) * ((n+1 : ℕ) : ℝ) + (s n-t n)) +
        limitCosine ((a+b) * ((n+1 : ℕ) : ℝ) + (s n+t n))) / 2 := by
    rw [limit_cos_product_eq]
    congr 2 <;> congr 1 <;> ring
  simpa only [sub_eq_zero, add_zero, ite_div, zero_div] using h.congr (fun n => (he n).symm)

/-- The critical physical cosine product retains exactly the resonant slow difference. -/
theorem factorialCriticalCosineProduct_tendsto {a b u v : ℝ} {s t : ℕ → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : Tendsto s atTop (𝓝 u))
    (ht : Tendsto t atTop (𝓝 v)) :
    Tendsto (fun n => ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) *
      Real.cos (2 * Real.pi * (a * ((n+1 : ℕ) : ℝ) + s n) * x) *
      Real.cos (2 * Real.pi * (b * ((n+1 : ℕ) : ℝ) + t n) * x)) atTop
      (𝓝 (if a = b then
        (∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) * Real.cos (2 * Real.pi * (u-v) * x)) / 2
        else 0)) :=
  limit_cos_product_tendsto ha hb hs ht

private theorem limit_affine_defect_zero :
    Tendsto (fun n : ℕ => factorialAffineDefect (n+1)) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun n : ℕ => 1 / (140 * (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, div_div] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 / 140 : ℝ)).comp (tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun n => (by positivity : 0 ≤ 1 / (225 * (n + 1 : ℝ))).trans
    (factorialAffineDefect_bounds n).1) (fun n => (factorialAffineDefect_bounds n).2) hmaj

private theorem limit_collar_shift :
    Tendsto (fun n : ℕ => (1 / 12 : ℝ) - factorialAffineDefect (n+1))
      atTop (𝓝 (1 / 12 : ℝ)) := by
  simpa using tendsto_const_nhds.sub limit_affine_defect_zero

/-- Translating a factorial source by a fixed offset retains that offset and the exact collar shift. -/
theorem factorialShiftedFreq_translated_sub_tendsto (j : ℕ) :
    Tendsto (fun n : ℕ => factorialShiftedFreq (n+j+1) - ((n+1 : ℕ) : ℝ))
      atTop (𝓝 ((j : ℝ) + 1/12)) := by
  have h := (tendsto_const_nhds (x := (j : ℝ))).add
    (limit_collar_shift.comp (tendsto_add_atTop_nat j))
  refine h.congr (fun n => ?_)
  dsimp only [Function.comp_def]
  unfold factorialAffineDefect
  push_cast
  ring

private def limitLayer (n k : ℕ) (v : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * (k : ℝ) * factorialShiftedFreq (n+1) * v) -
    Real.cos (2 * Real.pi * (k : ℝ) * ((n+1 : ℕ) : ℝ) * v)

private theorem limit_layer_bound (n k : ℕ) (v : ℝ) : |limitLayer n k v| ≤ 2 := by
  have ha := abs_le.mp (Real.abs_cos_le_one
    (2 * Real.pi * (k : ℝ) * factorialShiftedFreq (n+1) * v))
  have hb := abs_le.mp (Real.abs_cos_le_one
    (2 * Real.pi * (k : ℝ) * ((n+1 : ℕ) : ℝ) * v))
  unfold limitLayer
  rw [abs_le]
  constructor <;> linarith

private def limitLayerCorr (n k l r : ℕ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * limitLayer n k v * limitLayer n l ((r : ℝ) * v)

private theorem limit_layer_corr_eq (n k l r : ℕ) :
    limitLayerCorr n k l r =
      limitCosProduct ((k : ℝ) * factorialShiftedFreq (n+1))
        ((r : ℝ) * l * factorialShiftedFreq (n+1)) -
      limitCosProduct ((k : ℝ) * factorialShiftedFreq (n+1))
        ((r : ℝ) * l * ((n+1 : ℕ) : ℝ)) -
      limitCosProduct ((k : ℝ) * ((n+1 : ℕ) : ℝ))
        ((r : ℝ) * l * factorialShiftedFreq (n+1)) +
      limitCosProduct ((k : ℝ) * ((n+1 : ℕ) : ℝ))
        ((r : ℝ) * l * ((n+1 : ℕ) : ℝ)) := by
  let a := (k : ℝ) * factorialShiftedFreq (n+1)
  let b := (k : ℝ) * ((n+1 : ℕ) : ℝ)
  let c := (r : ℝ) * l * factorialShiftedFreq (n+1)
  let d := (r : ℝ) * l * ((n+1 : ℕ) : ℝ)
  let F (x y v : ℝ) := v ^ (-2 : ℝ) *
    Real.cos (2 * Real.pi * x * v) * Real.cos (2 * Real.pi * y * v)
  have hp (v : ℝ) : v ^ (-2 : ℝ) * limitLayer n k v * limitLayer n l ((r : ℝ) * v) =
      F a c v - F a d v - F b c v + F b d v := by
    dsimp only [limitLayer, F, a, b, c, d]
    ring_nf
  unfold limitLayerCorr
  simp_rw [hp]
  have hac : IntegrableOn (F a c) (Ioi (1 : ℝ)) := limit_cos_product_integrable a c
  have had : IntegrableOn (F a d) (Ioi (1 : ℝ)) := limit_cos_product_integrable a d
  have hbc : IntegrableOn (F b c) (Ioi (1 : ℝ)) := limit_cos_product_integrable b c
  have hbd : IntegrableOn (F b d) (Ioi (1 : ℝ)) := limit_cos_product_integrable b d
  have h1 := integral_sub hac had
  have h2 := integral_sub (hac.sub had) hbc
  have h3 := integral_add ((hac.sub had).sub hbc) hbd
  simp only [Pi.sub_apply] at h1 h2 h3
  rw [h2, h1] at h3
  exact h3

/-- The slow phase retained by the critical physical weight in harmonic `k`. -/
def factorialCriticalHarmonicDefect (k : ℕ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
    (1 - Real.cos (2 * Real.pi * ((k : ℝ) / 12) * v))

private theorem limit_defect_eq (k : ℕ) :
    factorialCriticalHarmonicDefect k = 1 - limitCosine ((k : ℝ) / 12) := by
  unfold factorialCriticalHarmonicDefect
  simp_rw [mul_sub, mul_one]
  rw [integral_sub limit_weight_integrable (limit_cosine_integrable _), limit_weight_mass]
  rfl

/-- The slow-phase mass lies between zero and twice the physical measure mass. -/
theorem factorialCriticalHarmonicDefect_bounds (k : ℕ) :
    0 ≤ factorialCriticalHarmonicDefect k ∧ factorialCriticalHarmonicDefect k ≤ 2 := by
  rw [limit_defect_eq]
  have h := abs_le.mp (limit_cosine_bound ((k : ℝ) / 12))
  constructor <;> linarith

private theorem limit_layer_corr_tendsto {k l r : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hr : 0 < r) :
    Tendsto (fun n => limitLayerCorr n k l r) atTop
      (𝓝 (if k = r*l then factorialCriticalHarmonicDefect k else 0)) := by
  let a : ℝ := k
  let b : ℝ := (r : ℝ) * l
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast hk
  have hb : 0 < b := mul_pos (by exact_mod_cast hr) (by exact_mod_cast hl)
  have hs := limit_collar_shift.const_mul a
  have ht := limit_collar_shift.const_mul b
  have hss := limit_cos_product_tendsto ha hb hs ht
  have hsi := limit_cos_product_tendsto ha hb hs
    (tendsto_const_nhds (x := (0 : ℝ)))
  have his := limit_cos_product_tendsto ha hb
    (tendsto_const_nhds (x := (0 : ℝ))) ht
  have hii := limit_cos_product_tendsto ha hb
    (tendsto_const_nhds (x := (0 : ℝ))) (tendsto_const_nhds (x := (0 : ℝ)))
  have h := ((hss.sub hsi).sub his).add hii
  have hval :
      ((if a=b then limitCosine (a*(1/12)-b*(1/12))/2 else 0) -
        (if a=b then limitCosine (a*(1/12)-0)/2 else 0) -
        (if a=b then limitCosine (0-b*(1/12))/2 else 0) +
        (if a=b then limitCosine (0-0)/2 else 0)) =
      if a=b then 1-limitCosine (a/12) else 0 := by
    by_cases hab : a=b
    · simp only [hab, ite_true, sub_self, sub_zero, zero_sub,
        limit_cosine_zero, limit_cosine_neg]
      rw [show b * (1/12) = b/12 by ring]
      ring
    · simp only [if_neg hab]
      ring
  rw [hval] at h
  have heq (n : ℕ) : limitLayerCorr n k l r =
      limitCosProduct (a * ((n+1 : ℕ) : ℝ) + a * ((1/12) - factorialAffineDefect (n+1)))
        (b * ((n+1 : ℕ) : ℝ) + b * ((1/12) - factorialAffineDefect (n+1))) -
      limitCosProduct (a * ((n+1 : ℕ) : ℝ) + a * ((1/12) - factorialAffineDefect (n+1)))
        (b * ((n+1 : ℕ) : ℝ) + 0) -
      limitCosProduct (a * ((n+1 : ℕ) : ℝ) + 0)
        (b * ((n+1 : ℕ) : ℝ) + b * ((1/12) - factorialAffineDefect (n+1))) +
      limitCosProduct (a * ((n+1 : ℕ) : ℝ) + 0) (b * ((n+1 : ℕ) : ℝ) + 0) := by
    rw [limit_layer_corr_eq]
    dsimp only [a, b]
    have hf (x : ℝ) : x * factorialShiftedFreq (n+1) =
        x * ((n+1 : ℕ) : ℝ) + x * ((1/12) - factorialAffineDefect (n+1)) := by
      unfold factorialAffineDefect
      ring
    simp only [hf, add_zero]
  have hres := h.congr (fun n => (heq n).symm)
  simpa only [a, b, ← Nat.cast_mul, Nat.cast_inj, ← limit_defect_eq] using hres

private theorem limit_layer_continuous (n k : ℕ) : Continuous (limitLayer n k) := by
  unfold limitLayer
  fun_prop

private theorem limit_layer_product_bound (n k l r : ℕ) (v : ℝ) :
    |limitLayer n k v * limitLayer n l ((r : ℝ) * v)| ≤ 4 := by
  rw [abs_mul]
  exact (mul_le_mul (limit_layer_bound n k v) (limit_layer_bound n l _)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)

private theorem limit_layer_corr_bound (n k l r : ℕ) : |limitLayerCorr n k l r| ≤ 4 := by
  have h := limit_integral_bound
    (f := fun v => limitLayer n k v * limitLayer n l ((r : ℝ) * v))
    (by unfold limitLayer; fun_prop) (limit_layer_product_bound n k l r)
  simpa only [limitLayerCorr, mul_assoc] using h

private theorem limit_layer_hasSum (n : ℕ) (v : ℝ) :
    HasSum (fun k => dyadicHarmonicWeight k * limitLayer n k v)
      (-(Real.pi ^ 2 / 2) * factorialPhaseProfile (n+1) v) := by
  refine (factorialPhaseProfile_hasSum (n+1) v).congr_fun (fun k => ?_)
  dsimp only [dyadicHarmonicWeight, limitLayer]
  ring_nf

private theorem limit_pair_summable :
    Summable (fun p : ℕ × ℕ =>
      (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) * 4) :=
  (summable_abs_dyadicHarmonicWeight.mul_of_nonneg summable_abs_dyadicHarmonicWeight
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)).mul_right 4

private theorem limit_pair_bound (n r : ℕ) (p : ℕ × ℕ) (v : ℝ) :
    |(dyadicHarmonicWeight p.1 * limitLayer n p.1 v) *
      (dyadicHarmonicWeight p.2 * limitLayer n p.2 ((r : ℝ) * v))| ≤
      (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) * 4 := by
  calc _ = (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) *
      |limitLayer n p.1 v * limitLayer n p.2 ((r : ℝ) * v)| := by
        simp only [abs_mul]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (limit_layer_product_bound n p.1 p.2 r v)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The complete actual phase at source scale `n+1`, tested at integer dilation `r`. -/
def factorialCriticalCorrelation (n r : ℕ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * factorialPhaseProfile (n+1) v *
    factorialPhaseProfile (n+1) ((r : ℝ) * v)

/-- Every full-profile physical correlation is a genuine Lebesgue integral. -/
theorem integrable_factorialCriticalCorrelation (n r : ℕ) :
    IntegrableOn (fun v => v ^ (-2 : ℝ) * factorialPhaseProfile (n+1) v *
      factorialPhaseProfile (n+1) ((r : ℝ) * v)) (Ioi (1 : ℝ)) := by
  have hf : Continuous (fun v => factorialPhaseProfile (n+1) v *
      factorialPhaseProfile (n+1) ((r : ℝ) * v)) :=
    (continuous_factorialPhaseProfile _).mul
      ((continuous_factorialPhaseProfile _).comp (continuous_const.mul continuous_id))
  have hB (v : ℝ) : |factorialPhaseProfile (n+1) v *
      factorialPhaseProfile (n+1) ((r : ℝ) * v)| ≤ 4 := by
    rw [abs_mul]
    exact (mul_le_mul (abs_factorialPhaseProfile_le _ _) (abs_factorialPhaseProfile_le _ _)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)
  simpa only [mul_assoc] using limit_integrable hf hB

private theorem limit_correlation_hasSum (n r : ℕ) :
    HasSum (fun p : ℕ × ℕ => dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      limitLayerCorr n p.1 p.2 r) ((Real.pi ^ 4 / 4) * factorialCriticalCorrelation n r) := by
  let F (p : ℕ × ℕ) (v : ℝ) := v ^ (-2 : ℝ) *
    ((dyadicHarmonicWeight p.1 * limitLayer n p.1 v) *
      (dyadicHarmonicWeight p.2 * limitLayer n p.2 ((r : ℝ) * v)))
  let B (p : ℕ × ℕ) := (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) * 4
  let f (v : ℝ) := v ^ (-2 : ℝ) *
    ((-(Real.pi ^ 2 / 2) * factorialPhaseProfile (n+1) v) *
      (-(Real.pi ^ 2 / 2) * factorialPhaseProfile (n+1) ((r : ℝ) * v)))
  have hs (v : ℝ) : Summable (fun p : ℕ × ℕ =>
      (dyadicHarmonicWeight p.1 * limitLayer n p.1 v) *
        (dyadicHarmonicWeight p.2 * limitLayer n p.2 ((r : ℝ) * v))) :=
    limit_pair_summable.of_norm_bounded (fun p => by
      rw [Real.norm_eq_abs]
      exact limit_pair_bound n r p v)
  have h := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (1 : ℝ))) (F := F) (f := f)
    (fun p v => B p * v ^ (-2 : ℝ))
    (fun p => limit_weight_integrable.aestronglyMeasurable.mul
      (show Continuous (fun v => (dyadicHarmonicWeight p.1 * limitLayer n p.1 v) *
        (dyadicHarmonicWeight p.2 * limitLayer n p.2 ((r : ℝ) * v))) by
          unfold limitLayer
          fun_prop).aestronglyMeasurable)
    (by
      intro p
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hw : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hv)) _
      dsimp only [F, B]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw, Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (limit_pair_bound n r p v) hw)
    (Eventually.of_forall fun v => limit_pair_summable.mul_right (v ^ (-2 : ℝ)))
    (by
      have hi := limit_weight_integrable.const_mul (∑' p, B p)
      simpa only [tsum_mul_right] using hi)
    (Eventually.of_forall fun v =>
      ((limit_layer_hasSum n v).mul (limit_layer_hasSum n ((r : ℝ) * v)) (hs v)).mul_left
        (v ^ (-2 : ℝ)))
  have hfun : HasSum (fun p : ℕ × ℕ => dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      limitLayerCorr n p.1 p.2 r) (∫ v in Ioi (1 : ℝ), f v) := by
    refine h.congr_fun (fun p => ?_)
    unfold limitLayerCorr
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp only [F]
    ring
  have hval : (∫ v in Ioi (1 : ℝ), f v) =
      (Real.pi ^ 4 / 4) * factorialCriticalCorrelation n r := by
    unfold factorialCriticalCorrelation
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp only [f]
    ring
  rwa [hval] at hfun

private theorem limit_weighted_layer_tendsto (k l r : ℕ) (hr : 0 < r) :
    Tendsto (fun n => dyadicHarmonicWeight k * dyadicHarmonicWeight l *
      limitLayerCorr n k l r) atTop
      (𝓝 (if k=r*l then dyadicHarmonicWeight k * dyadicHarmonicWeight l *
        factorialCriticalHarmonicDefect k else 0)) := by
  by_cases hk : k=0
  · simp only [hk, dyadicHarmonicWeight_zero, zero_mul, ite_self]
    exact tendsto_const_nhds
  by_cases hl : l=0
  · simp only [hl, dyadicHarmonicWeight_zero, mul_zero, zero_mul, ite_self]
    exact tendsto_const_nhds
  have h := (limit_layer_corr_tendsto (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hl) hr).const_mul
    (dyadicHarmonicWeight k * dyadicHarmonicWeight l)
  simpa only [mul_ite, mul_zero] using h

private theorem limit_weighted_layer_bound (n k l r : ℕ) :
    ‖dyadicHarmonicWeight k * dyadicHarmonicWeight l * limitLayerCorr n k l r‖ ≤
      (|dyadicHarmonicWeight k| * |dyadicHarmonicWeight l|) * 4 := by
  simp only [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (limit_layer_corr_bound n k l r)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- All harmonic coincidences of the critical factorial phase, with the physical slow phase retained. -/
def factorialCriticalCorrelationLimit (r : ℕ) : ℝ :=
  (4 / Real.pi ^ 4) * ∑' l : ℕ,
    dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l * factorialCriticalHarmonicDefect (r*l)

/-- The full harmonic series converges to its exact resonant physical correlation. -/
theorem factorialCriticalCorrelation_tendsto (r : ℕ) (hr : 0 < r) :
    Tendsto (fun n => factorialCriticalCorrelation n r) atTop
      (𝓝 (factorialCriticalCorrelationLimit r)) := by
  let g (p : ℕ × ℕ) := if p.1=r*p.2 then
    dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 * factorialCriticalHarmonicDefect p.1 else 0
  have hpair (p : ℕ × ℕ) := limit_weighted_layer_tendsto p.1 p.2 r hr
  have hg : Summable g := limit_pair_summable.of_norm_bounded fun p =>
    le_of_tendsto (hpair p).norm
      (Eventually.of_forall fun n => limit_weighted_layer_bound n p.1 p.2 r)
  have h := tendsto_tsum_of_dominated_convergence limit_pair_summable hpair
    (Eventually.of_forall fun n p => limit_weighted_layer_bound n p.1 p.2 r)
  have hsum : (∑' p, g p) = ∑' l : ℕ,
      dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l * factorialCriticalHarmonicDefect (r*l) := by
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq g]
    change (∑' p : ℕ × ℕ, g p.swap) = _
    rw [hg.prod_symm.tsum_prod]
    apply tsum_congr
    intro l
    dsimp only [g, Prod.swap]
    rw [tsum_eq_single (r*l)]
    · simp only [ite_true]
    · intro k hk
      simp only [if_neg hk]
  change Tendsto _ atTop (𝓝 (∑' p, g p)) at h
  rw [hsum] at h
  have hscaled := h.const_mul (4 / Real.pi ^ 4)
  apply hscaled.congr
  intro n
  rw [(limit_correlation_hasSum n r).tsum_eq]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- Every nonzero harmonic retains positive slow-phase mass on the physical half-line. -/
theorem factorialCriticalHarmonicDefect_pos (k : ℕ) (hk : 0 < k) :
    0 < factorialCriticalHarmonicDefect k := by
  let g (v : ℝ) := 1 - Real.cos (2 * Real.pi * ((k : ℝ) / 12) * v)
  let f (v : ℝ) := v ^ (-2 : ℝ) * g v
  have hg : Continuous g := by dsimp only [g]; fun_prop
  have hgnn (v : ℝ) : 0 ≤ g v := sub_nonneg.mpr (Real.cos_le_one _)
  have hgb (v : ℝ) : |g v| ≤ 2 := by
    have hc := abs_le.mp (Real.abs_cos_le_one (2 * Real.pi * ((k : ℝ) / 12) * v))
    dsimp only [g]
    rw [abs_le]
    constructor <;> linarith
  have hi : IntegrableOn f (Ioi (1 : ℝ)) := limit_integrable hg hgb
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hv)) _) (hgnn v)
  let v0 : ℝ := 12 + 6 / (k : ℝ)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hv0 : 1 < v0 := by
    have hp : 0 < 6 / (k : ℝ) := by positivity
    dsimp only [v0]
    linarith
  have harg : 2 * Real.pi * ((k : ℝ) / 12) * v0 = (k : ℝ) * (2 * Real.pi) + Real.pi := by
    dsimp only [v0]
    field_simp [ne_of_gt hkR]
    ring
  have hgv0 : 0 < g v0 := by
    dsimp only [g]
    rw [harg, Real.cos_nat_mul_two_pi_add_pi]
    norm_num
  let U : Set ℝ := {v | 0 < g v} ∩ Ioi 1
  have hU : IsOpen U := (isOpen_lt continuous_const hg).inter isOpen_Ioi
  have hUne : U.Nonempty := ⟨v0, hgv0, hv0⟩
  have hsub : U ⊆ Function.support f ∩ Ioi 1 := by
    intro v hv
    refine ⟨?_, hv.2⟩
    change f v ≠ 0
    exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one hv.2) _) hv.1)
  change 0 < ∫ v in Ioi (1 : ℝ), f v
  exact (setIntegral_pos_iff_support_of_nonneg_ae hnn hi).2
    (lt_of_lt_of_le (hU.measure_pos volume hUne) (measure_mono hsub))

end
end GaloisForLFunctions.ArithmeticPositivityTheory

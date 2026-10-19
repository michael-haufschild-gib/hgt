import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalCorrelationLimit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Quantified critical harmonic tails

Two integrations by parts retain the boundary phase of the complete harmonic
defect. The resulting bounds control its infinite tail and the finite phases
needed for the signed prime budget.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private theorem weighted_tail_integrable {p : ℝ} (hp : p < -1)
    (f : ℝ → ℝ) (hf : Continuous f) (hb : ∀ v, |f v| ≤ 1) :
    IntegrableOn (fun v : ℝ => v^p * f v) (Ioi (1 : ℝ)) := by
  apply (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).mul_bdd
    (c := 1) hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs] using hb v

private theorem weighted_tail_bound {p : ℝ} (hp : p < -1)
    (f : ℝ → ℝ) (hb : ∀ v, |f v| ≤ 1) :
    |∫ v in Ioi (1 : ℝ), v^p * f v| ≤ -1 / (p + 1) := by
  have h := norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt hp zero_lt_one)
    (f := fun v : ℝ => v^p * f v) ?_
  · simpa only [Real.norm_eq_abs, integral_Ioi_rpow_of_lt hp zero_lt_one,
      Real.one_rpow] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hv).le p),
      Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hb v) (Real.rpow_nonneg (zero_lt_one.trans hv).le p)).trans_eq
      (mul_one _)

private theorem weighted_tail_vanish {p : ℝ} (hp : p < 0)
    (f : ℝ → ℝ) (hb : ∀ v, |f v| ≤ 1) :
    Tendsto (fun v : ℝ => v^p * f v) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun v : ℝ => v^p)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) p),
      Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hb v) (Real.rpow_nonneg (by linarith) p)).trans_eq
      (mul_one _)
  · simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -p)

private theorem weighted_cos_ibp {p : ℝ} (hp : p < -1) (θ φ : ℝ) :
    θ * (∫ v in Ioi (1 : ℝ), v^p * Real.cos (θ*v+φ)) =
      -Real.sin (θ+φ) - p * (∫ v in Ioi (1 : ℝ), v^(p-1) * Real.sin (θ*v+φ)) := by
  have hc : Continuous (fun v : ℝ => Real.cos (θ*v+φ)) := by fun_prop
  have hs : Continuous (fun v : ℝ => Real.sin (θ*v+φ)) := by fun_prop
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun v : ℝ => v^p) (u' := fun v => p * v^(p-1))
    (v := fun v : ℝ => Real.sin (θ*v+φ)) (v' := fun v => θ * Real.cos (θ*v+φ))
    (a := 1) (a' := Real.sin (θ+φ)) (b' := 0)
    (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (zero_lt_one.trans hx).ne'))
    (fun x _ => by
      simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using
        ((Real.hasDerivAt_sin (θ*x+φ)).comp x
          (((hasDerivAt_id x).const_mul θ).add_const φ)))
    ?_ ?_ ?_ ?_
  · have hleft : (fun v : ℝ => v^p * (θ * Real.cos (θ*v+φ))) =
        (fun v : ℝ => θ * (v^p * Real.cos (θ*v+φ))) := by funext v; ring
    have hright : (fun v : ℝ => p * v^(p-1) * Real.sin (θ*v+φ)) =
        (fun v : ℝ => p * (v^(p-1) * Real.sin (θ*v+φ))) := by funext v; ring
    rw [hleft, hright, integral_const_mul, integral_const_mul] at h
    simpa only [zero_sub] using h
  · simpa only [IntegrableOn, Pi.mul_def, mul_left_comm] using
      (weighted_tail_integrable hp _ hc (fun v => Real.abs_cos_le_one _)).const_mul θ
  · simpa only [IntegrableOn, Pi.mul_def, mul_assoc] using
      (weighted_tail_integrable (by linarith : p-1 < -1) _ hs
        (fun v => Real.abs_sin_le_one _)).const_mul p
  · have hcont : ContinuousAt (fun v : ℝ => v^p * Real.sin (θ*v+φ)) 1 :=
      (continuousAt_id.rpow_const (Or.inl one_ne_zero)).mul hs.continuousAt
    simpa only [Pi.mul_def, Real.one_rpow, mul_one, one_mul] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  · simpa only [Pi.mul_def] using
      weighted_tail_vanish (by linarith : p < 0) _ (fun v => Real.abs_sin_le_one (θ*v+φ))

private theorem defect_eq_cosine_tail (m : ℕ) :
    factorialCriticalHarmonicDefect m = 1 -
      ∫ v in Ioi (1 : ℝ), v^(-2 : ℝ) * Real.cos (Real.pi * m / 6 * v) := by
  unfold factorialCriticalHarmonicDefect
  simp_rw [show 2 * Real.pi * ((m : ℝ) / 12) = Real.pi * m / 6 by ring,
    mul_sub, mul_one]
  rw [integral_sub (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one)
    (weighted_tail_integrable (by norm_num) _ (by fun_prop)
      (fun v => Real.abs_cos_le_one _)), integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num

private theorem cosine_tail_recurrences (θ : ℝ) :
    θ * (∫ v in Ioi (1 : ℝ), v^(-2 : ℝ) * Real.cos (θ*v)) =
      -Real.sin θ + 2 * (∫ v in Ioi (1 : ℝ), v^(-3 : ℝ) * Real.sin (θ*v)) ∧
    θ * (∫ v in Ioi (1 : ℝ), v^(-3 : ℝ) * Real.sin (θ*v)) =
      Real.cos θ - 3 * (∫ v in Ioi (1 : ℝ), v^(-4 : ℝ) * Real.cos (θ*v)) := by
  constructor
  · simpa only [add_zero, show (-2 : ℝ)-1 = -3 by norm_num, sub_neg_eq_add,
      neg_mul] using weighted_cos_ibp (by norm_num : (-2 : ℝ) < -1) θ 0
  · have h := weighted_cos_ibp (by norm_num : (-3 : ℝ) < -1) θ (Real.pi / 2)
    simp only [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, mul_neg,
      integral_neg, show (-3 : ℝ)-1 = -4 by norm_num, neg_mul] at h
    linarith

/-- The complete harmonic mass approaches one with a quantified inverse-frequency error. -/
theorem factorialCriticalHarmonicDefect_tail_bound (m : ℕ) :
    |factorialCriticalHarmonicDefect (m+1) - 1| ≤
      12 / (Real.pi * ((m+1 : ℕ) : ℝ)) := by
  let θ := Real.pi * ((m+1 : ℕ) : ℝ) / 6
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hrec := (cosine_tail_recurrences θ).1
  have hb : |∫ v in Ioi (1 : ℝ), v^(-3 : ℝ) * Real.sin (θ*v)| ≤ 1/2 := by
    convert weighted_tail_bound (by norm_num : (-3 : ℝ) < -1)
      (fun v : ℝ => Real.sin (θ*v)) (fun v => Real.abs_sin_le_one _) using 1
    norm_num
  have hsin := Real.abs_sin_le_one θ
  have habs : θ * |∫ v in Ioi (1 : ℝ), v^(-2 : ℝ) * Real.cos (θ*v)| ≤ 2 := by
    calc
      _ = |θ * (∫ v in Ioi (1 : ℝ), v^(-2 : ℝ) * Real.cos (θ*v))| := by
        rw [abs_mul, abs_of_pos hθ]
      _ = _ := congrArg abs hrec
      _ ≤ |Real.sin θ| + 2 * |∫ v in Ioi (1 : ℝ), v^(-3 : ℝ) * Real.sin (θ*v)| := by
        simpa only [abs_neg, abs_mul, show |(2 : ℝ)| = 2 by norm_num] using abs_add_le
          (-Real.sin θ) (2 * (∫ v in Ioi (1 : ℝ), v^(-3 : ℝ) * Real.sin (θ*v)))
      _ ≤ 2 := by linarith
  have hle : |∫ v in Ioi (1 : ℝ), v^(-2 : ℝ) * Real.cos (θ*v)| ≤ 2 / θ :=
    (le_div_iff₀ hθ).mpr (by rw [mul_comm]; exact habs)
  rw [defect_eq_cosine_tail]
  rw [show (1 : ℝ) - (∫ v in Ioi (1 : ℝ), v^(-2 : ℝ) * Real.cos
    (Real.pi * ((m+1 : ℕ) : ℝ) / 6 * v)) - 1 =
    -(∫ v in Ioi (1 : ℝ), v^(-2 : ℝ) * Real.cos (θ*v)) by dsimp [θ]; ring]
  rw [abs_neg]
  convert hle using 1
  dsimp [θ]
  ring

/-- A scaled upper bound retains both boundary phases. -/
theorem factorialCriticalHarmonicDefect_phase_upper_scaled (m : ℕ) :
    let θ := Real.pi * ((m+1 : ℕ) : ℝ) / 6
    factorialCriticalHarmonicDefect (m+1) * θ^2 ≤
      θ^2 + θ * Real.sin θ + 2 * (1 - Real.cos θ) := by
  dsimp only
  let θ := Real.pi * ((m+1 : ℕ) : ℝ) / 6
  change factorialCriticalHarmonicDefect (m+1) * θ^2 ≤
    θ^2 + θ * Real.sin θ + 2 * (1 - Real.cos θ)
  have hrec := cosine_tail_recurrences θ
  have hb : |∫ v in Ioi (1 : ℝ), v^(-4 : ℝ) * Real.cos (θ*v)| ≤ 1/3 := by
    convert weighted_tail_bound (by norm_num : (-4 : ℝ) < -1)
      (fun v : ℝ => Real.cos (θ*v)) (fun v => Real.abs_cos_le_one _) using 1
    norm_num
  have hJ := defect_eq_cosine_tail (m+1)
  change factorialCriticalHarmonicDefect (m+1) = 1 -
    ∫ v in Ioi (1 : ℝ), v^(-2 : ℝ) * Real.cos (θ*v) at hJ
  have hscaled := congrArg (fun x : ℝ => θ * x) hrec.1
  have hJscaled := congrArg (fun x : ℝ => θ^2 * x) hJ
  nlinarith only [hJscaled, hrec.2, hscaled,
    le_abs_self (∫ v in Ioi (1 : ℝ), v^(-4 : ℝ) * Real.cos (θ*v)), hb]

/-- The phase-sensitive bound in unscaled form. -/
theorem factorialCriticalHarmonicDefect_phase_upper (m : ℕ) :
    let θ := Real.pi * ((m+1 : ℕ) : ℝ) / 6
    factorialCriticalHarmonicDefect (m+1) ≤
      1 + Real.sin θ / θ + 2 * (1 - Real.cos θ) / θ^2 := by
  dsimp only
  let θ := Real.pi * ((m+1 : ℕ) : ℝ) / 6
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hle := (le_div_iff₀ (sq_pos_of_pos hθ)).mpr
    (factorialCriticalHarmonicDefect_phase_upper_scaled m)
  convert hle using 1 <;> first | rfl | (field_simp [hθ.ne'] <;> ring)

/-- A uniform rational tail budget, valid without a cutoff premise. -/
theorem factorialCriticalHarmonicDefect_add_twenty_le (m : ℕ) :
    factorialCriticalHarmonicDefect (m+20) ≤ 6/5 := by
  have h := factorialCriticalHarmonicDefect_tail_bound (m+19)
  have hm : (20 : ℝ) ≤ ((m+20 : ℕ) : ℝ) := by
    exact_mod_cast (show 20 ≤ m+20 by omega)
  have hden : (60 : ℝ) ≤ Real.pi * ((m+20 : ℕ) : ℝ) := by
    calc
      60 ≤ 3 * ((m+20 : ℕ) : ℝ) := by linarith
      _ ≤ Real.pi * ((m+20 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by positivity)
  have herror : 12 / (Real.pi * ((m+20 : ℕ) : ℝ)) ≤ 1/5 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  norm_num only [Nat.add_assoc, Nat.reduceAdd] at h
  linarith [le_abs_self (factorialCriticalHarmonicDefect (m+20) - 1)]

/-- Beyond harmonic nineteen, the phase bound has a uniform `7/6` budget. -/
theorem factorialCriticalHarmonicDefect_add_nineteen_le (m : ℕ) :
    factorialCriticalHarmonicDefect (m+19) ≤ 7/6 := by
  let θ := Real.pi * ((m+19 : ℕ) : ℝ) / 6
  have hm : (19 : ℝ) ≤ ((m+19 : ℕ) : ℝ) := by
    exact_mod_cast (show 19 ≤ m+19 by omega)
  have hθ : (19/2 : ℝ) ≤ θ := by
    dsimp [θ]
    have hprod := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
      (show 0 ≤ ((m+19 : ℕ) : ℝ) by positivity)
    linarith
  have hθpos : 0 < θ := by linarith
  have h := factorialCriticalHarmonicDefect_phase_upper_scaled (m+18)
  norm_num only [Nat.add_assoc, Nat.reduceAdd] at h
  change factorialCriticalHarmonicDefect (m+19) * θ^2 ≤
    θ^2 + θ * Real.sin θ + 2 * (1 - Real.cos θ) at h
  have hs := mul_le_mul_of_nonneg_left (Real.sin_le_one θ) hθpos.le
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hθpos)).mp
  nlinarith only [h, hs, Real.neg_one_le_cos θ, sq_nonneg (θ-19/2), hθ]

end GaloisForLFunctions.ArithmeticPositivityTheory

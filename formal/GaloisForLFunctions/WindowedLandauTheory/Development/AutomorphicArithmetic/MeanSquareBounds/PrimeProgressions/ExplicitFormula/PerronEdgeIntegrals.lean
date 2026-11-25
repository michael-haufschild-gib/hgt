import GaloisForLFunctions.RHTower.Sieve.PerronVerticalLogBound
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronBoundaryBounds
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronResidues

/-! Integrating the pointwise logarithmic-derivative estimates along the Perron boundary. -/

open Complex DirichletCharacter Filter MeasureTheory Set

noncomputable section

namespace QH.PrimeProgressions

def primitivePerronAbscissa (u : ℝ) : ℝ := 1 + 1 / Real.log u

theorem primitivePerronAbscissa_bounds {u : ℝ} (hu : 2 ≤ u) :
    1 < primitivePerronAbscissa u ∧ primitivePerronAbscissa u ≤ 5 / 2 ∧
      u ^ primitivePerronAbscissa u ≤ 3 * u := by
  have hu₁ : 1 < u := by linarith only [hu]
  have hlog : 0 < Real.log u := Real.log_pos hu₁
  have hlog' : (2 / 3 : ℝ) ≤ Real.log u :=
    (by linarith only [Real.log_two_gt_d9] : (2 / 3 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hu)
  have hrec : 1 / Real.log u ≤ (3 / 2 : ℝ) := by
    rw [div_le_iff₀ hlog]
    linarith only [hlog']
  unfold primitivePerronAbscissa
  refine ⟨lt_add_of_pos_right _ (one_div_pos.mpr hlog), by linarith only [hrec], ?_⟩
  rw [Real.rpow_add (by linarith only [hu]), Real.rpow_one,
    Real.rpow_def_of_pos (by linarith only [hu]), mul_one_div_cancel hlog.ne']
  calc
    _ ≤ u * 3 := mul_le_mul_of_nonneg_left (by linarith only [Real.exp_one_lt_d9]) (by linarith only [hu])
    _ = _ := mul_comm _ _

theorem norm_primitivePerronIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu : 0 < u) (s : ℂ) :
    ‖primitivePerronIntegrand χ u s‖ = ‖logDeriv χ.LFunction s‖ * u ^ s.re / ‖s‖ := by
  rw [primitivePerronIntegrand, norm_div, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu]

theorem norm_primitivePerron_horizontal {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {u T t D : ℝ} (hu : 2 ≤ u) (hT : 0 < T) (ht : T ≤ |t|) (hD : 0 ≤ D)
    (h : ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ primitivePerronAbscissa u → s.im = t →
      ‖logDeriv χ.LFunction s‖ ≤ D) :
    ‖∫ x : ℝ in (-(1 / 2 : ℝ))..primitivePerronAbscissa u,
        primitivePerronIntegrand χ u ((x : ℂ) + t * I)‖ ≤ 9 * D * u / T := by
  obtain ⟨hc₁, hc₂, hcu⟩ := primitivePerronAbscissa_bounds hu
  have hu₀ : 0 < u := by linarith only [hu]
  have hc : -(1 / 2 : ℝ) ≤ primitivePerronAbscissa u := by linarith only [hc₁]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := D * (3 * u) / T)
    (fun x hx => ?_)).trans ?_
  · rw [uIoc_of_le hc] at hx
    let s : ℂ := x + t * I
    have hr : s.re = x := by simp [s]
    have hi : s.im = t := by simp [s]
    have hn : T ≤ ‖s‖ := ht.trans (by rw [← hi]; exact abs_im_le_norm s)
    have hb := h s (by simpa only [hr] using hx.1.le) (by simpa only [hr] using hx.2) hi
    have hxpow := (Real.rpow_le_rpow_of_exponent_le (by linarith only [hu]) hx.2).trans hcu
    change ‖primitivePerronIntegrand χ u s‖ ≤ _
    rw [norm_primitivePerronIntegrand _ hu₀, hr]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul hb hxpow (Real.rpow_nonneg hu₀.le _) hD) (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) hT hn)
  · rw [abs_of_nonneg (sub_nonneg.mpr hc)]
    calc
      _ ≤ D * (3 * u) / T * 3 := mul_le_mul_of_nonneg_left (by linarith only [hc₂]) (by positivity)
      _ = _ := by ring

/-- The left edge costs two logarithmic factors, uniformly in the character and the Perron height. -/
theorem norm_primitivePerron_left :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ u U : ℝ, 1 ≤ u → 0 ≤ U →
        ‖∫ t : ℝ in -U..U, primitivePerronIntegrand χ u (((-(1 / 2 : ℝ)) : ℂ) + t * I)‖ ≤
          C * Real.log ((N : ℝ) * (U + 2)) * (1 + Real.log (1 + 2 * U)) := by
  obtain ⟨C, hC, H⟩ := primitive_logDeriv_left_edge
  refine ⟨2 * C, by positivity, ?_⟩
  intro N _ χ hχ u U hu hU
  let D := C * Real.log ((N : ℝ) * (U + 2))
  let v (t : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hD : 0 ≤ D := mul_nonneg hC.le (Real.log_nonneg
    ((by linarith only [hU] : (1 : ℝ) ≤ U + 2).trans (le_mul_of_one_le_left (by positivity) hN)))
  have hcont : Continuous (fun t : ℝ => D * (1 / ‖v t‖)) := by
    refine continuous_const.mul (continuous_const.div (by unfold v; fun_prop) fun t => ?_)
    refine norm_ne_zero_iff.mpr fun e => ?_
    have he := congrArg Complex.re e
    norm_num [v] at he
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith only [hU])
    (Filter.Eventually.of_forall fun t ht => ?_) (hcont.intervalIntegrable _ _)).trans ?_
  · have htu : |t| ≤ U := abs_le.mpr ⟨ht.1.le, ht.2⟩
    let s : ℂ := ((-(1 / 2 : ℝ)) : ℂ) + t * I
    have hr : s.re = -(1 / 2 : ℝ) := by simp [s]
    have hi : s.im = t := by simp [s]
    have hd : ‖s‖ = ‖v t‖ := by
      dsimp only [s, v]
      simp only [← ofReal_neg, Complex.norm_add_mul_I, neg_sq]
    have hb : ‖logDeriv χ.LFunction s‖ ≤ D :=
      (H N χ hχ s hr).2.trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left
          (by simpa only [hi] using add_le_add htu (le_refl (2 : ℝ))) (Nat.cast_nonneg _))) hC.le)
    have hu₀ : 0 < u := zero_lt_one.trans_le hu
    have hpow : u ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
    change ‖primitivePerronIntegrand χ u s‖ ≤ _
    rw [norm_primitivePerronIntegrand _ hu₀, hr, hd]
    change _ ≤ D * (1 / ‖v t‖)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right ((mul_le_mul hb hpow (by positivity) hD).trans_eq (mul_one _))
      (norm_nonneg _)
  · rw [intervalIntegral.integral_const_mul]
    have h := RHTower.Sieve.integral_symm_inv_norm_line_le (by norm_num : (0 : ℝ) < 1 / 2) hU
    change (∫ t in -U..U, 1 / ‖v t‖) ≤ 2 * (1 + Real.log (1 + U / (1 / 2))) at h
    rw [show U / (1 / 2 : ℝ) = 2 * U by ring] at h
    exact (mul_le_mul_of_nonneg_left h hD).trans_eq (by dsimp only [D]; ring)

end QH.PrimeProgressions

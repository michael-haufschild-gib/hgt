import GaloisForLFunctions.RHTower.Sieve.GuthMaynardDirichletPolynomialLocalAverage
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSumL2
import GaloisForLFunctions.RHTower.Sieve.SeparatedCount

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 11.7: `|R(v)|` is locally constant at scale `1/T`

For a finite `W ⊆ [T₀, T₀ + T]` and `v ≍ 1` (Guth–Maynard, arXiv 2405.20552, Lemma 11.7):

`|R(v)| ≪ T ∫_{|v' − v| ⪅ 1/T} |R(v')| dv' + O(T^{−A})`,   `R(v) = Σ_{t ∈ W} v^{it}`.

Proof. In logarithmic coordinates `R(e^u) = Σ_{t ∈ W} e(u · t/2π)` has its frequencies within `T`
of `T₀/2π`, so the band kernel at scale `L = T` reproduces it (`GuthMaynardBandKernel`):
`|R(e^u)| ≤ T ‖K‖_∞ ∫_{−δ}^{δ} |R(e^{u+η})| dη + |W| ∫_{|ξ| > Tδ} |K|`, and the same with cubes
and the factor `‖K‖₁²`. With `δ = T^ε/T` the tail is `O_A(T^{−A−1})` and `|W| ≤ T + 1` by
separation. The substitution `v' = v e^η` turns the `η`-window into `|v' − v| ≤ 4δ`.

The cube form in logarithmic coordinates (`norm_lagSum_exp_cube_le_local`) is the input of
Lemma 11.8.
-/

open MeasureTheory Set Finset

namespace RHTower.GuthMaynard

noncomputable section

/-- `|W| ≤ T + 1` for a `1`-separated `W ⊆ [T₀, T₀ + T]`. -/
theorem card_le_of_isSeparated_of_mem {W : Finset ℝ} {T₀ T : ℝ} (hT : 0 ≤ T)
    (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) (hsep : IsSeparated 1 W) : (W.card : ℝ) ≤ T + 1 := by
  have h := Sieve.card_le_of_separated (s := W) (u := id) (g := 1) (L := T) (c := T₀) one_pos hT
    (fun t ht t' ht' hne => hsep t ht t' ht' hne) hW
  simpa using h

/-- The frequencies `t/2π`, `t ∈ [T₀, T₀ + T]`, lie within `T` of `T₀/2π`. -/
theorem abs_div_two_pi_sub_le {T₀ T t : ℝ} (hT : 0 ≤ T) (ht : T₀ ≤ t ∧ t ≤ T₀ + T) :
    |t / (2 * Real.pi) - T₀ / (2 * Real.pi)| ≤ T := by
  rw [← sub_div, abs_div, abs_of_nonneg (by linarith [ht.1]), abs_of_pos Real.two_pi_pos,
    div_le_iff₀ Real.two_pi_pos]
  nlinarith [Real.pi_gt_three]

theorem sum_norm_one (W : Finset ℝ) : ∑ _t ∈ W, ‖(1 : ℂ)‖ = W.card := by simp

/-- **Lemma 11.7, logarithmic form.** For `W ⊆ [T₀, T₀ + T]`, `T > 0`, `δ ≥ 0`:
`|R(e^u)| ≤ T ‖K‖_∞ ∫_{−δ}^{δ} |R(e^{u+η})| dη + |W| ∫_{|ξ|>Tδ} |K|`. -/
theorem norm_lagSum_exp_le_local {W : Finset ℝ} {T₀ T δ : ℝ} (hT : 0 < T) (hδ : 0 ≤ δ)
    (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) (u : ℝ) :
    ‖lagSum W (Real.exp u)‖ ≤
      T * bandSup * (∫ η in -δ..δ, ‖lagSum W (Real.exp (u + η))‖) + W.card * bandTail (T * δ) := by
  have h := norm_finiteFrequencyPoly_le_local (fun _ => (1 : ℂ)) W (fun t => t / (2 * Real.pi))
    (a := T₀ / (2 * Real.pi)) hT hδ (fun t ht => abs_div_two_pi_sub_le hT.le (hW t ht)) u
  simp_rw [← lagSum_exp_eq_finiteFrequencyPoly, sum_norm_one] at h
  exact h

/-- **Lemma 11.7, logarithmic cube form.**
`|R(e^u)|³ ≤ ‖K‖₁² (T ‖K‖_∞ ∫_{−δ}^{δ} |R(e^{u+η})|³ dη + |W|³ ∫_{|ξ|>Tδ} |K|)`. -/
theorem norm_lagSum_exp_cube_le_local {W : Finset ℝ} {T₀ T δ : ℝ} (hT : 0 < T) (hδ : 0 ≤ δ)
    (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) (u : ℝ) :
    ‖lagSum W (Real.exp u)‖ ^ 3 ≤
      bandMass ^ 2 * (T * bandSup * (∫ η in -δ..δ, ‖lagSum W (Real.exp (u + η))‖ ^ 3) +
        (W.card : ℝ) ^ 3 * bandTail (T * δ)) := by
  have h := norm_finiteFrequencyPoly_cube_le_local (fun _ => (1 : ℂ)) W (fun t => t / (2 * Real.pi))
    (a := T₀ / (2 * Real.pi)) hT hδ (fun t ht => abs_div_two_pi_sub_le hT.le (hW t ht)) u
  simp_rw [← lagSum_exp_eq_finiteFrequencyPoly, sum_norm_one] at h
  exact h

/-! ### Back to the variable `v` -/

/-- `‖R‖` is continuous on `(0, ∞)`. -/
theorem continuousOn_norm_lagSum (W : Finset ℝ) :
    ContinuousOn (fun v => ‖lagSum W v‖) (Ioi 0) := by
  unfold lagSum
  refine ContinuousOn.norm (continuousOn_finsetSum _ fun t _ => ?_)
  exact (Complex.continuous_exp.comp_continuousOn
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun x hx => ne_of_gt hx))))

/-- `‖R‖` is interval integrable on every interval (bounded and measurable). -/
theorem intervalIntegrable_norm_lagSum (W : Finset ℝ) (a b : ℝ) :
    IntervalIntegrable (fun v => ‖lagSum W v‖) volume a b := by
  refine (intervalIntegrable_const (c := (W.card : ℝ))).mono_fun ?_
    (Filter.Eventually.of_forall fun y => ?_)
  · unfold lagSum
    exact (Finset.measurable_sum _ fun t _ => by fun_prop).norm.aestronglyMeasurable
  · simp only [norm_norm, Real.norm_natCast]
    exact norm_lagSum_le W y

/-- **Change of variables.** For `v ∈ [1/2, 2]` and `0 ≤ δ ≤ 1`:
`∫_{−δ}^{δ} |R(v e^η)| dη ≤ 6 ∫_{v−4δ}^{v+4δ} |R(v')| dv'`. -/
theorem integral_norm_lagSum_exp_le {W : Finset ℝ} {v δ : ℝ} (hv : v ∈ Icc (1 / 2 : ℝ) 2)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∫ η in -δ..δ, ‖lagSum W (Real.exp (Real.log v + η))‖ ≤
      6 * ∫ v' in (v - 4 * δ)..(v + 4 * δ), ‖lagSum W v'‖ := by
  have hv0 : 0 < v := by linarith [hv.1]
  set g : ℝ → ℝ := fun y => ‖lagSum W y‖
  set f : ℝ → ℝ := fun η => v * Real.exp η
  have hf : ∀ η, Real.exp (Real.log v + η) = f η := fun η => by
    simp only [f]; rw [Real.exp_add, Real.exp_log hv0]
  simp_rw [hf]
  have hderiv : ∀ η ∈ uIcc (-δ) δ, HasDerivAt f (v * Real.exp η) η :=
    fun η _ => (Real.hasDerivAt_exp η).const_mul v
  have himage : f '' uIcc (-δ) δ ⊆ Ioi 0 := by
    rintro _ ⟨η, -, rfl⟩
    exact mul_pos hv0 (Real.exp_pos η)
  have hsub := intervalIntegral.integral_comp_mul_deriv' (g := g) hderiv
    (by fun_prop) ((continuousOn_norm_lagSum W).mono himage)
  -- the Jacobian `v e^η` is at least `1/6` on `[-δ, δ]`
  have hjac : ∀ η ∈ Icc (-δ) δ, (1 : ℝ) ≤ 6 * (v * Real.exp η) := by
    intro η hη
    have he : Real.exp (-1) ≤ Real.exp η := Real.exp_le_exp.mpr (by linarith [hη.1])
    have he1 : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, one_div, inv_le_inv₀ (by norm_num) (Real.exp_pos 1)]
      linarith [Real.exp_one_lt_d9]
    nlinarith [hv.1]
  have hcont : ContinuousOn (fun η => g (f η)) (Icc (-δ) δ) :=
    (continuousOn_norm_lagSum W).comp (by fun_prop) fun η _ => mul_pos hv0 (Real.exp_pos η)
  have h1 : ∫ η in -δ..δ, g (f η) ≤ ∫ η in -δ..δ, 6 * ((g ∘ f) η * (v * Real.exp η)) := by
    refine intervalIntegral.integral_mono_on (by linarith)
      (hcont.intervalIntegrable_of_Icc (by linarith))
      ((((hcont.mul (by fun_prop : ContinuousOn (fun η => v * Real.exp η) (Icc (-δ) δ)))).const_smul
        (6 : ℝ)).intervalIntegrable_of_Icc (by linarith)) fun η hη => ?_
    simp only [Function.comp]
    have hg0 : 0 ≤ g (f η) := norm_nonneg _
    nlinarith [hjac η hη]
  rw [intervalIntegral.integral_const_mul, hsub] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  -- enlarge `[v e^{−δ}, v e^{δ}]` to `[v − 4δ, v + 4δ]`
  have hexp : |Real.exp δ - 1| ≤ 2 * δ := by
    have := Real.abs_exp_sub_one_le (x := δ) (by rw [abs_of_nonneg hδ]; exact hδ1)
    rwa [abs_of_nonneg hδ] at this
  have hexp' : |Real.exp (-δ) - 1| ≤ 2 * δ := by
    have := Real.abs_exp_sub_one_le (x := -δ) (by rw [abs_neg, abs_of_nonneg hδ]; exact hδ1)
    rwa [abs_neg, abs_of_nonneg hδ] at this
  have hlo : v - 4 * δ ≤ f (-δ) := by
    simp only [f]
    have := (abs_le.mp hexp').1
    nlinarith [hv.2]
  have hhi : f δ ≤ v + 4 * δ := by
    simp only [f]
    have := (abs_le.mp hexp).2
    nlinarith [hv.2]
  have hmid : f (-δ) ≤ f δ := by
    simp only [f]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hv0.le
  exact intervalIntegral.integral_mono_interval hlo hmid hhi
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) (intervalIntegrable_norm_lagSum W _ _)

/-- **Guth–Maynard Lemma 11.7** (`|R(v)| ≪ T ∫_{|v'−v| ⪅ 1/T} |R(v')| dv' + O(T^{−A})` for
`v ≍ 1`): for every `ε > 0` and `A` there is `C ≥ 0` such that for every `1`-separated
`W ⊆ [T₀, T₀ + T]`, `T ≥ 2`, and `v ∈ [1/2, 2]`,
`|R(v)| ≤ C T ∫_{v − 4T^ε/T}^{v + 4T^ε/T} |R(v')| dv' + C T^{−A}`. -/
theorem guthMaynard_lemma117 {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (W : Finset ℝ) (T T₀ v : ℝ), 2 ≤ T → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      IsSeparated 1 W → v ∈ Icc (1 / 2 : ℝ) 2 →
      ‖lagSum W v‖ ≤
        C * T * (∫ v' in (v - 4 * T ^ ε / T)..(v + 4 * T ^ ε / T), ‖lagSum W v'‖) +
          C * T ^ (-A) := by
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  obtain ⟨C₁, hC₁, htail⟩ := exists_bandTail_rpow_le hε'0 (A + 1)
  refine ⟨max (6 * bandSup) (2 * C₁), le_trans (by positivity) (le_max_right _ _),
    fun W T T₀ v hT hW hsep hv => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hv0 : 0 < v := by linarith [hv.1]
  set δ := T ^ ε' / T with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hTε' : T ^ ε' ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT1 (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hT0]
    calc T ^ ε' ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (min_le_right _ _)
      _ = T := Real.rpow_one T
  have hTδ : T * δ = T ^ ε' := by rw [hδdef]; field_simp
  have h := norm_lagSum_exp_le_local hT0 hδ0 hW (Real.log v)
  rw [Real.exp_log hv0, hTδ] at h
  have hcv := integral_norm_lagSum_exp_le (W := W) hv hδ0 hδ1
  -- enlarge the window from `4δ` to `4T^ε/T`
  have hwin : ∫ v' in (v - 4 * δ)..(v + 4 * δ), ‖lagSum W v'‖ ≤
      ∫ v' in (v - 4 * T ^ ε / T)..(v + 4 * T ^ ε / T), ‖lagSum W v'‖ := by
    have hδε : 4 * δ ≤ 4 * T ^ ε / T := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hTε' hT0.le) (by norm_num)
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) (intervalIntegrable_norm_lagSum W _ _)
  have hcard := card_le_of_isSeparated_of_mem hT0.le hW hsep
  have herr : (W.card : ℝ) * bandTail (T ^ ε') ≤ 2 * C₁ * T ^ (-A) := by
    calc (W.card : ℝ) * bandTail (T ^ ε') ≤ (2 * T) * (C₁ * T ^ (-(A + 1))) :=
          mul_le_mul (by linarith) (htail T hT1) (bandTail_nonneg _) (by positivity)
      _ = 2 * C₁ * T ^ (-A) := by
          rw [show -(A + 1) = -A + (-1) by ring, Real.rpow_add hT0, Real.rpow_neg_one]
          field_simp
  set I := ∫ v' in (v - 4 * T ^ ε / T)..(v + 4 * T ^ ε / T), ‖lagSum W v'‖
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg (by
      have : 0 ≤ 4 * T ^ ε / T := by positivity
      linarith) fun _ _ => norm_nonneg _
  have hmain : T * bandSup * (∫ η in -δ..δ, ‖lagSum W (Real.exp (Real.log v + η))‖) ≤
      max (6 * bandSup) (2 * C₁) * T * I := by
    calc T * bandSup * (∫ η in -δ..δ, ‖lagSum W (Real.exp (Real.log v + η))‖)
        ≤ T * bandSup * (6 * I) :=
          mul_le_mul_of_nonneg_left (hcv.trans (mul_le_mul_of_nonneg_left hwin (by norm_num)))
            (mul_nonneg hT0.le bandSup_nonneg)
      _ = 6 * bandSup * T * I := by ring
      _ ≤ max (6 * bandSup) (2 * C₁) * T * I := by
          gcongr
          exact le_max_left _ _
  have herr' : 2 * C₁ * T ^ (-A) ≤ max (6 * bandSup) (2 * C₁) * T ^ (-A) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  linarith

end

end RHTower.GuthMaynard

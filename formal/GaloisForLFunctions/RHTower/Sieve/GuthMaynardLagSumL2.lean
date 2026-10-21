import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSum
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueBasic

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 8.2: the `L²` bound for the lag sum

For a `1`-separated finite set `W ⊂ ℝ` and the window `v ∈ [A⁻¹, A]` (`A ≥ 1`),

`∫_{A⁻¹}^{A} |R(v)|² dv ≤ (5π/2) · A · max(1, log A) · |W|`.

This is Lemma 8.2 of Guth–Maynard (arXiv 2405.20552): `∫_{v ≍ 1} |R(v)|² dv ≪_ε |W|` for
`T^ε`-separated `W`, here with an explicit constant and only `1`-separation.

Proof. The substitution `v = e^u` turns `R(v)` into the exponential sum `Σ_{t ∈ W} e^{itu}` on
`|u| ≤ log A`, with Jacobian `e^u ≤ A`. The corpus Fejér-majorant mean value inequality
`integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight` bounds the mean square of a
unit-coefficient exponential sum by its count of frequency pairs at distance `< 1/max(1, log A)`;
for a `1`-separated set only the diagonal survives. The same window inequality, applied to `R²`,
gives the fourth moment (`GuthMaynardLagSumL4`).
-/

open MeasureTheory Set Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The lag sum in logarithmic coordinates -/

/-- `R(e^u) = Σ_{t ∈ W} e^{itu}`. -/
theorem lagSum_exp (W : Finset ℝ) (u : ℝ) :
    lagSum W (Real.exp u) = ∑ t ∈ W, Complex.exp (Complex.I * t * u) := by
  simp [lagSum, Real.log_exp]

theorem continuous_lagSum_exp (W : Finset ℝ) : Continuous fun u => lagSum W (Real.exp u) := by
  simp_rw [lagSum_exp]
  fun_prop

/-- `R(e^u)` is the corpus exponential sum with unit coefficients and frequencies `t/2π`. -/
theorem lagSum_exp_eq_finiteFrequencyPoly (W : Finset ℝ) (u : ℝ) :
    lagSum W (Real.exp u) =
      Sieve.finiteFrequencyPoly (fun _ => 1) W (fun t => t / (2 * Real.pi)) u := by
  rw [lagSum_exp, Sieve.finiteFrequencyPoly]
  refine sum_congr rfl fun t _ => ?_
  have h : 2 * Real.pi * (u * (t / (2 * Real.pi))) = t * u := by
    field_simp
  rw [one_mul, h]
  push_cast
  ring_nf

/-- **Logarithmic substitution on the window `[A⁻¹, A]`.** For nonnegative `F`,
`∫_{A⁻¹}^{A} F(v) dv = ∫_{|u| ≤ log A} e^u F(e^u) du ≤ A ∫_{|u| ≤ log A} F(e^u) du`. -/
theorem setIntegral_Icc_inv_le {A : ℝ} (hA : 1 ≤ A) {F : ℝ → ℝ} (hF : ∀ v, 0 ≤ F v)
    (hFi : IntegrableOn (fun u => F (Real.exp u)) (Icc (-Real.log A) (Real.log A))) :
    ∫ v in Icc A⁻¹ A, F v ≤ A * ∫ u in Icc (-Real.log A) (Real.log A), F (Real.exp u) := by
  have hA0 : 0 < A := by linarith
  have himage : Real.exp '' Icc (-Real.log A) (Real.log A) = Icc A⁻¹ A := by
    rw [Real.image_exp_Icc, Real.exp_neg, Real.exp_log hA0]
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
    (s := Icc (-Real.log A) (Real.log A))
    measurableSet_Icc (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn F
  rw [himage] at hcov
  rw [hcov, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ (hFi.const_mul A) ?_
  · exact Filter.Eventually.of_forall fun u => smul_nonneg (abs_nonneg _) (hF _)
  · refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    show |Real.exp u| • F (Real.exp u) ≤ A * F (Real.exp u)
    rw [smul_eq_mul, abs_of_pos (Real.exp_pos u)]
    have hu' : Real.exp u ≤ A := by
      calc Real.exp u ≤ Real.exp (Real.log A) := Real.exp_le_exp.mpr hu.2
        _ = A := Real.exp_log hA0
    exact mul_le_mul_of_nonneg_right hu' (hF _)

/-! ### The window mean value inequality with unit coefficients -/

/-- The collision scale `δ_A = 1/(2π max(1, log A))` attached to the window `|u| ≤ log A`. -/
def windowScale (A : ℝ) : ℝ := 1 / (2 * Real.pi * max 1 (Real.log A))

theorem windowScale_pos (A : ℝ) : 0 < windowScale A := by
  unfold windowScale
  have : (0 : ℝ) < max 1 (Real.log A) := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

/-- `2π δ_A ≤ 1`: collisions at scale `δ_A` are frequency pairs at distance `< 1`. -/
theorem two_pi_mul_windowScale_le (A : ℝ) : 2 * Real.pi * windowScale A ≤ 1 := by
  unfold windowScale
  have hL : (1 : ℝ) ≤ max 1 (Real.log A) := le_max_left _ _
  rw [mul_one_div, div_le_one (by positivity)]
  exact le_mul_of_one_le_right (by positivity) hL

/-- **Window mean value with unit coefficients.** For any finite frequency family,
`∫_{|u| ≤ log A} |Σ_i e(u x_i)|² du ≤ (5π/2) max(1, log A) · #{(i, j) : |x_i − x_j| < δ_A}`. -/
theorem setIntegral_Icc_normSq_unitPoly_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (A : ℝ) :
    ∫ u in Icc (-Real.log A) (Real.log A),
        ‖Sieve.finiteFrequencyPoly (fun _ => 1) s x u‖ ^ 2
      ≤ 5 * Real.pi / 2 * max 1 (Real.log A)
          * Sieve.finiteFrequencyCollisionWeight (fun _ => 1) s x (windowScale A) := by
  have hL : (1 : ℝ) ≤ max 1 (Real.log A) := le_max_left _ _
  have hcond : 2 * Real.pi * windowScale A * Real.log A ≤ 1 := by
    unfold windowScale
    rw [mul_one_div, div_mul_eq_mul_div, div_le_one (by positivity)]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hmv := Sieve.integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight
    (fun _ => (1 : ℂ)) s x (windowScale_pos A) hcond
  have hconst : 5 / (4 * windowScale A) = 5 * Real.pi / 2 * max 1 (Real.log A) := by
    unfold windowScale
    field_simp
    ring
  rwa [hconst] at hmv

/-! ### Lemma 8.2 -/

/-- For a `1`-separated set the collisions of the frequencies `t/2π` at a scale `δ` with
`2πδ ≤ 1` are diagonal, so the collision count is at most `|W|`. -/
theorem collisionWeight_le_card {W : Finset ℝ} (hW : IsSeparated 1 W) {δ : ℝ}
    (hδ1 : 2 * Real.pi * δ ≤ 1) :
    Sieve.finiteFrequencyCollisionWeight (fun _ => (1 : ℂ)) W (fun t => t / (2 * Real.pi)) δ
      ≤ W.card := by
  rw [Sieve.finiteFrequencyCollisionWeight]
  have hrow : ∀ t ∈ W, (∑ t' ∈ W,
      if |t / (2 * Real.pi) - t' / (2 * Real.pi)| < δ then ‖(1 : ℂ)‖ * ‖(1 : ℂ)‖ else 0)
        ≤ 1 := by
    intro t ht
    rw [sum_eq_single_of_mem t ht]
    · split_ifs <;> simp
    · intro t' ht' hne
      have hsep : 1 ≤ |t - t'| := hW t ht t' ht' (Ne.symm hne)
      have hfar : δ ≤ |t / (2 * Real.pi) - t' / (2 * Real.pi)| := by
        rw [← sub_div, abs_div, abs_of_pos Real.two_pi_pos, le_div_iff₀ Real.two_pi_pos]
        calc δ * (2 * Real.pi) = 2 * Real.pi * δ := by ring
          _ ≤ 1 := hδ1
          _ ≤ |t - t'| := hsep
      rw [if_neg (not_lt.mpr hfar)]
  calc _ ≤ ∑ _t ∈ W, (1 : ℝ) := sum_le_sum hrow
    _ = W.card := by simp

/-- **Guth–Maynard Lemma 8.2 (`L²` bound), explicit form.** For a `1`-separated finite set `W`
and `A ≥ 1`: `∫_{A⁻¹}^{A} |R(v)|² dv ≤ (5π/2) · A · max(1, log A) · |W|`. -/
theorem setIntegral_Icc_inv_normSq_lagSum_le {A : ℝ} (hA : 1 ≤ A) {W : Finset ℝ}
    (hW : IsSeparated 1 W) :
    ∫ v in Icc A⁻¹ A, ‖lagSum W v‖ ^ 2
      ≤ 5 * Real.pi / 2 * A * max 1 (Real.log A) * W.card := by
  have hcont : Continuous fun u => ‖lagSum W (Real.exp u)‖ ^ 2 :=
    (continuous_lagSum_exp W).norm.pow 2
  have hweight := collisionWeight_le_card hW (two_pi_mul_windowScale_le A)
  have hL : (0 : ℝ) ≤ 5 * Real.pi / 2 * max 1 (Real.log A) :=
    mul_nonneg (by positivity) (le_trans zero_le_one (le_max_left _ _))
  calc ∫ v in Icc A⁻¹ A, ‖lagSum W v‖ ^ 2
      ≤ A * ∫ u in Icc (-Real.log A) (Real.log A), ‖lagSum W (Real.exp u)‖ ^ 2 :=
        setIntegral_Icc_inv_le hA (fun v => by positivity) hcont.integrableOn_Icc
    _ = A * ∫ u in Icc (-Real.log A) (Real.log A),
          ‖Sieve.finiteFrequencyPoly (fun _ => 1) W (fun t => t / (2 * Real.pi)) u‖ ^ 2 := by
        simp_rw [lagSum_exp_eq_finiteFrequencyPoly]
    _ ≤ A * (5 * Real.pi / 2 * max 1 (Real.log A) * W.card) :=
        mul_le_mul_of_nonneg_left ((setIntegral_Icc_normSq_unitPoly_le W _ A).trans
          (mul_le_mul_of_nonneg_left hweight hL)) (by linarith)
    _ = 5 * Real.pi / 2 * A * max 1 (Real.log A) * W.card := by ring

/-- Separation is monotone in the scale. -/
theorem IsSeparated.mono {δ δ' : ℝ} {W : Finset ℝ} (h : δ ≤ δ') (hW : IsSeparated δ' W) :
    IsSeparated δ W :=
  fun t ht t' ht' hne => h.trans (hW t ht t' ht' hne)

/-- **Guth–Maynard Lemma 8.2** in the paper's setting: for every window `[A⁻¹, A]` there is an
absolute constant `C` with `∫_{A⁻¹}^{A} |R(v)|² dv ≤ C |W|` for every `T^ε`-separated set `W`,
`T ≥ 1`, `ε ≥ 0`. -/
theorem guthMaynard_lemma82 {A : ℝ} (hA : 1 ≤ A) :
    ∃ C ≥ 0, ∀ (ε T : ℝ) (W : Finset ℝ), 0 ≤ ε → 1 ≤ T → IsSeparated (T ^ ε) W →
      ∫ v in Icc A⁻¹ A, ‖lagSum W v‖ ^ 2 ≤ C * W.card := by
  refine ⟨5 * Real.pi / 2 * A * max 1 (Real.log A), ?_, fun ε T W hε hT hW => ?_⟩
  · exact mul_nonneg (mul_nonneg (by positivity) (by linarith))
      (le_trans zero_le_one (le_max_left _ _))
  · exact setIntegral_Icc_inv_normSq_lagSum_le hA (hW.mono (Real.one_le_rpow hT hε))

end

end RHTower.GuthMaynard

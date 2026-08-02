import GaloisForLFunctions.RHTower.BurnolCoPoissonCorrectionConstant
import GaloisForLFunctions.HTGeometry.SchwartzDilateSummability

/-!
# Pairing a co-Poisson sum against a test function

Pairing the co-Poisson sum of a window seed with a Schwartz function and exchanging the sum with
the integral turns the multiplicative sum over the seed into a sum of dilates of the test function:

`integral_0^infinity (sum_{n>=1} g(t/n)/n) w(t) dt = integral_0^infinity g(u) (sum_{n>=1} w(n u)) du`.

Both exchanges are absolutely convergent.  The seed is integrable and supported above the aperture,
so the reciprocal of the scale is bounded there, and the quadratic decay of a Schwartz function
makes the dilated sum converge like `1/n^2` uniformly on the support.  The right-hand side is the
shape that Poisson summation acts on.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- A Schwartz function is bounded. -/
theorem exists_norm_bound_schwartz (w : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖w x‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := w.decay 0 0
  exact ⟨C, hCpos.le, fun x => by simpa using hC x⟩

/-- Rescaling the positive ray in an integral. -/
theorem integral_Ioi_dilate_cancel {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ℝ → F) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), h t = c • ∫ x in Ioi (0 : ℝ), h (c * x) := by
  have hcv := integral_comp_mul_left_Ioi h 0 hc
  rw [mul_zero] at hcv
  rw [hcv, smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]

theorem integrableOn_seed_mul_schwartzDilate {g : ℝ → ℂ} (hg : Integrable g)
    (w : SchwartzMap ℝ ℂ) (c : ℝ) :
    IntegrableOn (fun u : ℝ => g u * w (c * u)) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := exists_norm_bound_schwartz w
  have hb : Integrable (fun u : ℝ => w (c * u) * g u) (volume.restrict (Ioi 0)) := by
    refine (hg.restrict (s := Ioi 0)).bdd_mul ?_
      (Filter.Eventually.of_forall fun x => hC (c * x))
    exact (w.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  exact hb.congr (Filter.Eventually.of_forall fun u => mul_comm _ _)

/-- **The pairing of one co-Poisson term with a test function is a dilated pairing.** -/
theorem integral_coPoissonTerm_eq {g : ℝ → ℂ} (w : SchwartzMap ℝ ℂ) {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), ((c : ℝ) : ℂ)⁻¹ * g (t / c) * w t) =
      ∫ u in Ioi (0 : ℝ), g u * w (c * u) := by
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  rw [integral_Ioi_dilate_cancel (fun t : ℝ => ((c : ℝ) : ℂ)⁻¹ * g (t / c) * w t) hc]
  have hpt : ∀ x : ℝ, ((c : ℝ) : ℂ)⁻¹ * g (c * x / c) * w (c * x) =
      ((c : ℝ) : ℂ)⁻¹ * (g x * w (c * x)) := by
    intro x
    rw [mul_div_cancel_left₀ _ (ne_of_gt hc), mul_assoc]
  simp only [hpt]
  rw [integral_const_mul, Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]

/-- The same change of variables at the level of norms. -/
theorem integral_norm_coPoissonTerm_eq {g : ℝ → ℂ} (w : SchwartzMap ℝ ℂ) {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), ‖((c : ℝ) : ℂ)⁻¹ * g (t / c) * w t‖) =
      ∫ u in Ioi (0 : ℝ), ‖g u * w (c * u)‖ := by
  rw [integral_Ioi_dilate_cancel (fun t : ℝ => ‖((c : ℝ) : ℂ)⁻¹ * g (t / c) * w t‖) hc]
  have hpt : ∀ x : ℝ, ‖((c : ℝ) : ℂ)⁻¹ * g (c * x / c) * w (c * x)‖ =
      c⁻¹ * ‖g x * w (c * x)‖ := by
    intro x
    rw [mul_div_cancel_left₀ _ (ne_of_gt hc), mul_assoc, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  simp only [hpt]
  rw [integral_const_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]

/-- Integrability of one co-Poisson term against a test function. -/
theorem integrableOn_coPoissonTerm {g : ℝ → ℂ} (hg : Integrable g)
    (w : SchwartzMap ℝ ℂ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => ((c : ℝ) : ℂ)⁻¹ * g (t / c) * w t) (Ioi 0) := by
  have hmain := integrableOn_seed_mul_schwartzDilate hg w c
  have hiff := integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => ((c : ℝ) : ℂ)⁻¹ * g (t / c) * w t) 0 hc
  rw [mul_zero] at hiff
  refine hiff.mp ?_
  have hpt : ∀ x : ℝ, ((c : ℝ) : ℂ)⁻¹ * g (c * x / c) * w (c * x) =
      ((c : ℝ) : ℂ)⁻¹ • (g x * w (c * x)) := by
    intro x
    rw [mul_div_cancel_left₀ _ (ne_of_gt hc), mul_assoc, smul_eq_mul]
  refine (hmain.smul (((c : ℝ) : ℂ))⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply]
  exact (hpt x).symm

/-- **Uniform bound on the dilated pairing.**  A window seed is supported above the aperture, so the
quadratic decay of the test function gives a bound decaying like `1/c^2`. -/
theorem integral_norm_seed_mul_schwartzDilate_le {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) (w : SchwartzMap ℝ ℂ)
    {C : ℝ} (hC : ∀ x : ℝ, x ^ 2 * ‖w x‖ ≤ C) {c : ℝ} (hc : 0 < c) :
    (∫ u in Ioi (0 : ℝ), ‖g u * w (c * u)‖) ≤
      C / (c ^ 2 * b ^ 2) * ∫ u in Ioi (0 : ℝ), ‖g u‖ := by
  have hC0 : 0 ≤ C := by
    have h1 := hC 1
    have h2 : (0 : ℝ) ≤ 1 ^ 2 * ‖w 1‖ := by positivity
    linarith
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ‖g u * w (c * u)‖ ≤ C / (c ^ 2 * b ^ 2) * ‖g u‖ := by
    intro u hu
    by_cases hz : g u = 0
    · simp [hz]
    · have hmem : u ∈ Icc b b⁻¹ := hsupp (Function.mem_support.mpr hz)
      have hub : b ≤ u := hmem.1
      have hwb : ‖w (c * u)‖ ≤ C / (c ^ 2 * b ^ 2) := by
        have h := hC (c * u)
        have hden : (0 : ℝ) < c ^ 2 * b ^ 2 := by positivity
        have hle : c ^ 2 * b ^ 2 * ‖w (c * u)‖ ≤ (c * u) ^ 2 * ‖w (c * u)‖ := by
          have hsq : c ^ 2 * b ^ 2 ≤ (c * u) ^ 2 := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
          exact mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
        rw [le_div_iff₀ hden, mul_comm]
        linarith
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hwb (norm_nonneg _) |>.trans_eq (mul_comm _ _)
  have hint1 : IntegrableOn (fun u : ℝ => ‖g u * w (c * u)‖) (Ioi 0) :=
    (integrableOn_seed_mul_schwartzDilate hg w c).norm
  have hint2 : IntegrableOn (fun u : ℝ => C / (c ^ 2 * b ^ 2) * ‖g u‖) (Ioi 0) :=
    ((hg.norm).restrict (s := Ioi 0)).const_mul _
  rw [← integral_const_mul]
  exact setIntegral_mono_on hint1 hint2 measurableSet_Ioi hpt



/-! ## Exchanging the sum with the integral -/

theorem summable_integral_norm_seed_mul_schwartzDilate {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) (w : SchwartzMap ℝ ℂ) :
    Summable fun k : ℕ =>
      ∫ u in Ioi (0 : ℝ), ‖g u * w (((k + 1 : ℕ) : ℝ) * u)‖ := by
  obtain ⟨C, hC0, hC⟩ := HTGeometry.exists_sq_norm_bound w
  have hmass : 0 ≤ ∫ u in Ioi (0 : ℝ), ‖g u‖ :=
    integral_nonneg fun u => norm_nonneg _
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun u => norm_nonneg _)
    (fun k => ?_)
    (HTGeometry.summable_inv_natSucc_sq.mul_left
      (C / b ^ 2 * ∫ u in Ioi (0 : ℝ), ‖g u‖))
  have hcpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hbound := integral_norm_seed_mul_schwartzDilate_le hb hg hsupp w hC hcpos
  refine hbound.trans_eq ?_
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hne : ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  field_simp

theorem hasSum_integral_coPoissonTerm {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) (w : SchwartzMap ℝ ℂ) :
    HasSum (fun k : ℕ => ∫ t in Ioi (0 : ℝ),
        (((k + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((k + 1 : ℕ) : ℝ)) * w t)
      (∫ t in Ioi (0 : ℝ),
        ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((k + 1 : ℕ) : ℝ)) * w t) := by
  refine hasSum_integral_of_summable_integral_norm
    (fun k => integrableOn_coPoissonTerm hg w (by positivity)) ?_
  refine (summable_integral_norm_seed_mul_schwartzDilate hb hg hsupp w).congr fun k => ?_
  exact (integral_norm_coPoissonTerm_eq w (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))).symm

theorem hasSum_integral_seed_mul_schwartzDilate {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) (w : SchwartzMap ℝ ℂ) :
    HasSum (fun k : ℕ => ∫ u in Ioi (0 : ℝ), g u * w (((k + 1 : ℕ) : ℝ) * u))
      (∫ u in Ioi (0 : ℝ), ∑' k : ℕ, g u * w (((k + 1 : ℕ) : ℝ) * u)) :=
  hasSum_integral_of_summable_integral_norm
    (fun _ => integrableOn_seed_mul_schwartzDilate hg w _)
    (summable_integral_norm_seed_mul_schwartzDilate hb hg hsupp w)

/-- **The pairing identity.**  Pairing the multiplicative sum of a window seed with a Schwartz
function turns it into the pairing of the seed with the sum of the dilates of that function. -/
theorem integral_coPoissonSum_mul_eq {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) (w : SchwartzMap ℝ ℂ) :
    (∫ t in Ioi (0 : ℝ),
        (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((k + 1 : ℕ) : ℝ))) * w t) =
      ∫ u in Ioi (0 : ℝ), g u * ∑' k : ℕ, w (((k + 1 : ℕ) : ℝ) * u) := by
  have hleft : (∫ t in Ioi (0 : ℝ),
      (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((k + 1 : ℕ) : ℝ))) * w t) =
      ∫ t in Ioi (0 : ℝ),
        ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((k + 1 : ℕ) : ℝ)) * w t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact (tsum_mul_right).symm
  have hright : (∫ u in Ioi (0 : ℝ), ∑' k : ℕ, g u * w (((k + 1 : ℕ) : ℝ) * u)) =
      ∫ u in Ioi (0 : ℝ), g u * ∑' k : ℕ, w (((k + 1 : ℕ) : ℝ) * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    exact tsum_mul_left
  rw [hleft, ← hright]
  have hfun : (fun k : ℕ => ∫ u in Ioi (0 : ℝ), g u * w (((k + 1 : ℕ) : ℝ) * u)) =
      fun k : ℕ => ∫ t in Ioi (0 : ℝ),
        (((k + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((k + 1 : ℕ) : ℝ)) * w t := by
    funext k
    exact (integral_coPoissonTerm_eq w (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))).symm
  have hsum2 := hasSum_integral_seed_mul_schwartzDilate hb hg hsupp w
  rw [hfun] at hsum2
  exact HasSum.unique (hasSum_integral_coPoissonTerm hb hg hsupp w) hsum2

end RHTower


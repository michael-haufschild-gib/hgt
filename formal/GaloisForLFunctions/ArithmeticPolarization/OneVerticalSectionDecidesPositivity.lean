import GaloisForLFunctions.ArithmeticPolarization.PositivePolarConfigurationsAreNonnegativeExponentialPolynomials
import GaloisForLFunctions.HTGeometry.PositiveDefiniteLaplaceWeights

/-!
# One vertical section decides positivity

For a finite polar configuration `G(s) = Σ_{z ∈ S} c(z)/(s − z)` with real weights and points in
`Re z ≤ σ₀`, every vertical section `u ↦ Re G(σ + iu)` with `σ > σ₀` is the cosine transform of
`e^{−σt} w(t)`, where `w(t) = Σ_z c(z) e^{Re z · t} cos(Im z · t)` is the scale weight
(`quadForm_polarSum_eq_integral`).

* **One section decides** (`posDef_section_iff_scaleWeight_nonneg`): a single vertical section at
  one abscissa `σ > σ₀` is positive definite iff `w ≥ 0` on `(0, ∞)`. The forward half is the
  uniqueness half of Bochner's theorem (`HTGeometry.LaplaceWeights.nonneg_of_laplace_posDef`); no conjugation
  symmetry and no family of abscissae is used.
* **Rigidity** (`posDef_section_of_posDef_section`): positivity of one vertical section propagates
  to every vertical section right of the configuration, on both sides of the given one.

ACP's Post–Widder law derives `w ≥ 0` from positivity on a half-line of abscissae for
conjugation-symmetric configurations; here one abscissa and no symmetry suffice. The positive cone
of polar configurations is therefore a cone of single kernels: whether a completion is positive is
a property of any one of its vertical sections.
-/

open Complex Finset Filter Topology Real MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry HTGeometry.LaplaceWeights

theorem continuous_polarScaleWeight (S : Finset ℂ) (c : ℂ → ℝ) :
    Continuous (polarScaleWeight S c) := by
  unfold polarScaleWeight
  exact continuous_finsetSum _ fun z _ =>
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))

/-- The scale weight grows at most like `e^{σ₀ t}`. -/
theorem abs_polarScaleWeight_le {S : Finset ℂ} {c : ℂ → ℝ} {σ₀ : ℝ} (hS : ∀ z ∈ S, z.re ≤ σ₀)
    {t : ℝ} (ht : 0 ≤ t) :
    |polarScaleWeight S c t| ≤ (∑ z ∈ S, |c z|) * Real.exp (σ₀ * t) := by
  unfold polarScaleWeight
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z hz => ?_)
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hcos := Real.abs_cos_le_one (z.im * t)
  have hexp : Real.exp (z.re * t) ≤ Real.exp (σ₀ * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hS z hz) ht)
  calc |c z| * Real.exp (z.re * t) * |Real.cos (z.im * t)| ≤ |c z| * Real.exp (z.re * t) * 1 :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
    _ ≤ |c z| * Real.exp (σ₀ * t) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left hexp (abs_nonneg _)

/-- **One vertical section decides positivity.** -/
theorem posDef_section_iff_scaleWeight_nonneg {S : Finset ℂ} {c : ℂ → ℝ} {σ₀ σ : ℝ}
    (hS : ∀ z ∈ S, z.re ≤ σ₀) (hσ : σ₀ < σ) :
    (IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re) ↔
      ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t := by
  constructor
  · intro hpd t ht
    set g : ℝ → ℝ := fun t => Real.exp (-(σ * t)) * polarScaleWeight S c t with hg
    have hgc : Continuous g :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (continuous_polarScaleWeight S c)
    have hgC : ∀ t, 0 ≤ t → |g t| ≤ (∑ z ∈ S, |c z|) * Real.exp (-((σ - σ₀) * t)) := by
      intro t ht
      rw [hg, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(σ * t)) * |polarScaleWeight S c t|
          ≤ Real.exp (-(σ * t)) * ((∑ z ∈ S, |c z|) * Real.exp (σ₀ * t)) :=
            mul_le_mul_of_nonneg_left (abs_polarScaleWeight_le hS ht) (Real.exp_pos _).le
        _ = (∑ z ∈ S, |c z|) * Real.exp (-((σ - σ₀) * t)) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    have hlap : ∀ (n : ℕ) (x w : Fin n → ℝ), 0 ≤ ∫ t in Ioi (0 : ℝ),
        g t * Complex.normSq (∑ i, (w i : ℂ) * Complex.exp (-((x i * t : ℝ) : ℂ) * I)) := by
      intro n x w
      have h := hpd n x w
      have hq := quadForm_polarSum_eq_integral (c := c) (fun z hz => (hS z hz).trans_lt hσ) x w
      simp only [Complex.ofReal_sub] at h hq
      rw [hq] at h
      refine h.trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)))
      simp only [hg]; ring
    have h0 := nonneg_of_laplace_posDef hgc (sub_pos.mpr hσ) hgC hlap ht
    simp only [hg] at h0
    exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp h0
  · intro hw
    exact posDef_polarSum_of_scaleWeight_nonneg (fun z hz => (hS z hz).trans_lt hσ) hw

/-- **Rigidity.** Positivity of one vertical section right of the configuration gives positivity of
every vertical section right of it. -/
theorem posDef_section_of_posDef_section {S : Finset ℂ} {c : ℂ → ℝ} {σ₀ σ σ' : ℝ}
    (hS : ∀ z ∈ S, z.re ≤ σ₀) (hσ : σ₀ < σ) (hσ' : σ₀ < σ')
    (hpd : IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re) :
    IsPosDef fun u : ℝ => (polarSum S c ((σ' : ℂ) + (u : ℂ) * I)).re :=
  (posDef_section_iff_scaleWeight_nonneg hS hσ').mpr
    ((posDef_section_iff_scaleWeight_nonneg hS hσ).mp hpd)

end GaloisForLFunctions.ArithmeticPolarization

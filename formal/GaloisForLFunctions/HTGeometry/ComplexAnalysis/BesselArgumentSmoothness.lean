import GaloisForLFunctions.HTGeometry.BesselArgumentDerivative

/-!
# Smoothness and exponential decay in the Bessel argument

The adjacent-order derivative formula closes the family `K_ν(exp u)` under differentiation.
Induction gives infinite real smoothness for every complex order. Comparison of the Schläfli
integrands at arguments `δ` and `x≥δ` gives exponential decay on every positive ray.
-/

open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The Bessel family in logarithmic argument is closed under differentiation. -/
theorem modifiedBesselKOrder_exp_hasDerivAt (ν : ℂ) (u : ℝ) :
    HasDerivAt (fun t : ℝ => modifiedBesselKOrder (Real.exp t) ν)
      (-(1 / 2 : ℂ) * (Real.exp u : ℂ) *
        (modifiedBesselKOrder (Real.exp u) (ν + 1) +
          modifiedBesselKOrder (Real.exp u) (ν - 1))) u := by
  have h := (RHTower.d4BM_hasDerivAt_modifiedBesselKOrder_argument
    (Real.exp_pos u) ν).scomp u (Real.hasDerivAt_exp u)
  simpa only [Function.comp_def, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using h

/-- Every complex order has a smooth Bessel kernel in logarithmic argument. -/
theorem contDiff_modifiedBesselKOrder_exp (ν : ℂ) :
    ContDiff ℝ ∞ (fun u : ℝ => modifiedBesselKOrder (Real.exp u) ν) := by
  have hall : ∀ n : ℕ, ∀ μ : ℂ,
      ContDiff ℝ n (fun u : ℝ => modifiedBesselKOrder (Real.exp u) μ) := by
    intro n
    induction n with
    | zero =>
        intro μ
        exact contDiff_zero.2 (continuous_iff_continuousAt.2
          (fun u => (modifiedBesselKOrder_exp_hasDerivAt μ u).continuousAt))
    | succ n ih =>
        intro μ
        rw [show (↑(n + 1) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp, contDiff_succ_iff_deriv]
        refine ⟨fun u => (modifiedBesselKOrder_exp_hasDerivAt μ u).differentiableAt, ?_, ?_⟩
        · intro h
          exact absurd h (by simp)
        · have heq : deriv (fun u : ℝ => modifiedBesselKOrder (Real.exp u) μ) =
              fun u => -(1 / 2 : ℂ) * (Real.exp u : ℂ) *
                (modifiedBesselKOrder (Real.exp u) (μ + 1) +
                  modifiedBesselKOrder (Real.exp u) (μ - 1)) :=
            funext fun u => (modifiedBesselKOrder_exp_hasDerivAt μ u).deriv
          rw [heq]
          exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp)).mul
            ((ih (μ + 1)).add (ih (μ - 1)))
  exact contDiff_infty.2 (fun n => hall n ν)

/-- The positive-real Bessel argument is smooth to every order. -/
theorem contDiffOn_modifiedBesselKOrder_argument (ν : ℂ) :
    ContDiffOn ℝ ∞ (fun x : ℝ => modifiedBesselKOrder x ν) (Ioi 0) := by
  intro x hx
  have hs : ContDiffAt ℝ ∞ (fun y : ℝ =>
      modifiedBesselKOrder (Real.exp (Real.log y)) ν) x :=
    (contDiff_modifiedBesselKOrder_exp ν).contDiffAt.comp x
      (Real.contDiffAt_log.2 (ne_of_gt hx))
  apply (hs.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [Real.exp_log hy]

/-- Exponential decay is uniform beyond any fixed positive argument. -/
theorem exists_modifiedBesselKOrder_exp_bound (ν : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, δ ≤ x →
      ‖modifiedBesselKOrder x ν‖ ≤ C * Real.exp (-x) := by
  refine ⟨Real.exp δ * ∫ t in Ioi (0 : ℝ), ‖besselOrderKernel δ ν t‖,
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _), ?_⟩
  intro x hx
  have hnorm (a t : ℝ) : ‖Complex.exp (-(a : ℂ) * Complex.cosh (t : ℂ))‖ =
      Real.exp (-a * Real.cosh t) := by
    rw [Complex.norm_exp, ← Complex.ofReal_cosh]
    simp
  have hb (t : ℝ) : ‖besselOrderKernel x ν t‖ ≤
      Real.exp (δ - x) * ‖besselOrderKernel δ ν t‖ := by
    simp only [besselOrderKernel, norm_mul, hnorm]
    rw [← mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hc := Real.one_le_cosh t
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hc)]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖besselOrderKernel x ν t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (δ - x) * ‖besselOrderKernel δ ν t‖ :=
      setIntegral_mono_on (integrableOn_besselOrderKernel (hδ.trans_le hx) ν).norm
        ((integrableOn_besselOrderKernel hδ ν).norm.const_mul _) measurableSet_Ioi
        (fun t _ => hb t)
    _ = _ := by rw [integral_const_mul, sub_eq_add_neg, Real.exp_add]; ring

end
end GaloisForLFunctions.HTGeometry

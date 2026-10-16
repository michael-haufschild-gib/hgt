import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Strong spatial differentiation of entire parameter jets

A uniform bound for the actual spatial derivative on one parameter circle
pays differentiation of every Cauchy coefficient. No joint differentiability
of the original two-variable function is assumed.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A locally uniform circle bound transfers the actual spatial derivative to
every entire parameter jet. The conclusion is a strong scalar derivative. -/
theorem hasDerivAt_entireParameterJet
    (f g : ℂ → ℝ → ℂ) (a : ℝ) (c : ℂ) (n : ℕ)
    (hf : ∀ x, Differentiable ℂ (fun w => f w x))
    (hg : Differentiable ℂ (fun w => g w a))
    (hd : ∀ w ∈ Metric.sphere c 1, ∀ x ∈ Metric.ball a 1,
      HasDerivAt (f w) (g w x) x)
    (hb : ∃ C : ℝ, ∀ w ∈ Metric.sphere c 1, ∀ x ∈ Metric.ball a 1, ‖g w x‖ ≤ C) :
    HasDerivAt (fun x => iteratedDeriv n (fun w => f w x) c)
      (iteratedDeriv n (fun w => g w a) c) a := by
  obtain ⟨C, hC⟩ := hb
  let μ := volume.restrict (Icc (0 : ℝ) (2*Real.pi))
  let α : ℂ := 2*Real.pi*I/(n.factorial : ℂ)
  let W : ℝ → ℂ := fun θ =>
    deriv (circleMap c 1) θ * (1/(circleMap c 1 θ-c)^(n+1))
  have hmem (θ : ℝ) : circleMap c 1 θ ∈ Metric.sphere c 1 :=
    circleMap_mem_sphere c zero_le_one θ
  have hne (θ : ℝ) : circleMap c 1 θ-c ≠ 0 :=
    sub_ne_zero.mpr (circleMap_ne_mem_ball (Metric.mem_ball_self one_pos) θ)
  have hW : Continuous W := by
    have he : Continuous (fun θ : ℝ => deriv (circleMap c 1) θ) := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 1).mul continuous_const
    exact he.mul (continuous_const.div
      (((continuous_circleMap c 1).sub continuous_const).pow (n+1))
      (fun θ => pow_ne_zero _ (hne θ)))
  have hWnorm (θ : ℝ) : ‖W θ‖ = 1 := by
    simp [W, deriv_circleMap, norm_circleMap_zero]
  let F : ℝ → ℝ → ℂ := fun x θ => W θ * f (circleMap c 1 θ) x
  let G : ℝ → ℝ → ℂ := fun x θ => W θ * g (circleMap c 1 θ) x
  have hFcont (x : ℝ) : Continuous (F x) :=
    hW.mul ((hf x).continuous.comp (continuous_circleMap c 1))
  have hGcont : Continuous (G a) := hW.mul (hg.continuous.comp (continuous_circleMap c 1))
  have hbound : ∀ᵐ θ ∂μ, ∀ x ∈ Metric.ball a 1, ‖G x θ‖ ≤ C := by
    filter_upwards [] with θ
    intro x hx
    change ‖W θ * g (circleMap c 1 θ) x‖ ≤ C
    rw [norm_mul, hWnorm, one_mul]
    exact hC _ (hmem θ) x hx
  have hdiff : ∀ᵐ θ ∂μ, ∀ x ∈ Metric.ball a 1, HasDerivAt (fun x => F x θ) (G x θ) x := by
    filter_upwards [] with θ
    intro x hx
    exact (hd _ (hmem θ) x hx).const_mul (W θ)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := G) (μ := μ) (bound := fun _ => C)
    (Metric.ball_mem_nhds a one_pos)
    (Eventually.of_forall fun x => (hFcont x).aestronglyMeasurable)
    ((hFcont a).integrableOn_Icc) hGcont.aestronglyMeasurable hbound
    ((continuous_const : Continuous (fun _ : ℝ => C)).integrableOn_Icc) hdiff
  have hFjet (x : ℝ) : (∫ θ, F x θ ∂μ) = α * iteratedDeriv n (fun w => f w x) c := by
    have hc := DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul
      (c := c) (R := 1) one_pos n (hf x).diffContOnCl
    rw [circleIntegral_def_Icc] at hc
    simpa only [F, W, μ, α, smul_eq_mul, mul_assoc] using hc
  have hGjet : (∫ θ, G a θ ∂μ) = α * iteratedDeriv n (fun w => g w a) c := by
    have hc := DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul
      (c := c) (R := 1) one_pos n hg.diffContOnCl
    rw [circleIntegral_def_Icc] at hc
    simpa only [G, W, μ, α, smul_eq_mul, mul_assoc] using hc
  have hα : α ≠ 0 := div_ne_zero Complex.two_pi_I_ne_zero
    (by exact_mod_cast Nat.factorial_ne_zero n)
  have hjet : HasDerivAt (fun x => α * iteratedDeriv n (fun w => f w x) c)
      (α * iteratedDeriv n (fun w => g w a) c) a := by
    simpa only [hFjet, hGjet] using h.2
  simpa only [← mul_assoc, inv_mul_cancel₀ hα, one_mul] using hjet.const_mul α⁻¹

/-- The coordinate factor retains the complete predecessor term at every jet order. -/
theorem entire_iteratedDeriv_id_mul {h : ℂ → ℂ} (hh : Differentiable ℂ h) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z : ℂ => z * h z) =
      fun z => ((n : ℂ) + 1) * iteratedDeriv n h z + z * iteratedDeriv (n + 1) h z := by
  induction n with
  | zero =>
      rw [iteratedDeriv_one]
      funext z
      have hd : HasDerivAt (fun z : ℂ => z * h z) (1 * h z + z * deriv h z) z :=
        (hasDerivAt_id z).mul (hh z).hasDerivAt
      rw [hd.deriv]
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      have hdiff : ∀ k, Differentiable ℂ (iteratedDeriv k h) := by
        intro k
        induction k with
        | zero => simpa using hh
        | succ k hk => rw [iteratedDeriv_succ]; exact hk.deriv
      have hd : HasDerivAt (fun z : ℂ => ((n : ℂ) + 1) * iteratedDeriv n h z
            + z * iteratedDeriv (n + 1) h z)
          (((n : ℂ) + 1) * deriv (iteratedDeriv n h) z
            + (1 * iteratedDeriv (n + 1) h z + z * deriv (iteratedDeriv (n + 1) h) z)) z :=
        (((hdiff n z).hasDerivAt).const_mul _).add
          ((hasDerivAt_id z).mul ((hdiff (n + 1) z).hasDerivAt))
      rw [hd.deriv, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
      push_cast
      ring

end GaloisForLFunctions.HTGeometry

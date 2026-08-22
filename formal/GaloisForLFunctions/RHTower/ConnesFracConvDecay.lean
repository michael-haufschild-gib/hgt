import GaloisForLFunctions.RHTower.ConnesFracConvSwap

/-!
# The fractional convolution of a Schwartz function decays faster than every power

Supporting §VII (48) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`ConnesFracConvSwap` bounded the first difference of a Schwartz function using the *quadratic*
weight, which is all that Fubini needed.  For (48) — `‖ε_Λ (C_{α,v} * η)‖₁ = O(Λ^{-N})` for
*every* `N` — the same argument is needed at every order, because the logarithmic factor
`ε_Λ(x) = (log|x| − L)^+` has to be paid for by an arbitrarily large power of `|x|`.

The order-`k` statements are proved here, and combined into the pointwise decay

  `‖(C_{α,v} * η)(x)‖ ≤ A_k (1 + |x|)^{-k}`,

which is what (48) consumes.
-/

open MeasureTheory Real Set
open scoped SchwartzMap Real

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem connes_one_add_abs_pow_le (k : ℕ) (z : ℝ) :
    (1 + |z|) ^ k ≤ 2 ^ k * (1 + |z| ^ k) := by
  rcases le_or_gt |z| 1 with hz | hz
  · have h1 : (1 + |z|) ^ k ≤ 2 ^ k := by
      refine pow_le_pow_left₀ (by positivity) (by linarith) k
    have h2 : (0 : ℝ) ≤ |z| ^ k := by positivity
    nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) k]
  · have hz0 : (0 : ℝ) < |z| := lt_trans zero_lt_one hz
    have h1 : (1 + |z|) ^ k ≤ (2 * |z|) ^ k := by
      refine pow_le_pow_left₀ (by positivity) (by linarith) k
    have h2 : (2 * |z|) ^ k = 2 ^ k * |z| ^ k := by rw [mul_pow]
    have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    nlinarith

/-- **The Schwartz derivative decays at every order.** -/
theorem connes_schwartz_deriv_weight_order (η : 𝓢(ℝ, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ,
      ‖deriv ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z‖ ≤ C * (1 + |z|) ^ (-(k : ℝ)) := by
  set g : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ η with hg
  set σ₀ : ℝ := SchwartzMap.seminorm ℂ 0 0 g with hσ₀
  set σₖ : ℝ := SchwartzMap.seminorm ℂ k 0 g with hσₖ
  have hσ₀0 : (0 : ℝ) ≤ σ₀ := apply_nonneg _ g
  have hσₖ0 : (0 : ℝ) ≤ σₖ := apply_nonneg _ g
  refine ⟨2 ^ k * (σ₀ + σₖ), by positivity, fun z => ?_⟩
  have hcoe : deriv ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z = g z := by
    rw [hg, SchwartzMap.derivCLM_apply]
  have h0 := SchwartzMap.norm_pow_mul_le_seminorm ℂ g 0 z
  have hk := SchwartzMap.norm_pow_mul_le_seminorm ℂ g k z
  rw [Real.norm_eq_abs] at h0 hk
  simp only [pow_zero, one_mul] at h0
  have hpos : (0 : ℝ) < (1 + |z|) ^ k := by positivity
  have hexp : (1 + |z|) ^ (-(k : ℝ)) = ((1 + |z|) ^ k)⁻¹ := by
    rw [← Real.rpow_natCast (1 + |z|) k, ← Real.rpow_neg (by positivity)]
  rw [hcoe, hexp, le_mul_inv_iff₀ hpos]
  have hgnn : (0 : ℝ) ≤ ‖g z‖ := norm_nonneg _
  have hbase := connes_one_add_abs_pow_le k z
  calc ‖g z‖ * (1 + |z|) ^ k
      ≤ ‖g z‖ * (2 ^ k * (1 + |z| ^ k)) := mul_le_mul_of_nonneg_left hbase hgnn
    _ = 2 ^ k * (‖g z‖ + |z| ^ k * ‖g z‖) := by ring
    _ ≤ 2 ^ k * (σ₀ + σₖ) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **The order-`k` first-difference bound.** -/
theorem connes_schwartz_diff_bound_order (η : 𝓢(ℝ, ℂ)) (k : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z : ℝ, ‖deriv ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z‖ ≤ C * (1 + |z|) ^ (-(k : ℝ)))
    {y ε : ℝ} (hε : |ε| ≤ 1) :
    ‖η (y + ε) - η y‖ ≤ (2 ^ k * C * (1 + |y|) ^ (-(k : ℝ))) * |ε| := by
  have hball : ∀ z ∈ Metric.closedBall y 1,
      ‖deriv ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z‖ ≤ 2 ^ k * C * (1 + |y|) ^ (-(k : ℝ)) := by
    intro z hz
    have hzy : |z - y| ≤ 1 := by
      have := Metric.mem_closedBall.mp hz
      rwa [Real.dist_eq] at this
    have hlow : (1 + |y|) / 2 ≤ 1 + |z| := by
      have h1 : |y| - 1 ≤ |z| := by
        have := abs_sub_abs_le_abs_sub y z
        rw [abs_sub_comm y z] at this
        linarith
      rcases le_or_gt 1 |y| with hy | hy
      · linarith
      · have : (0 : ℝ) ≤ |z| := abs_nonneg z
        linarith
    have hyp : (0 : ℝ) < (1 + |y|) / 2 := by positivity
    have hsq : ((1 + |y|) / 2) ^ k ≤ (1 + |z|) ^ k := pow_le_pow_left₀ hyp.le hlow k
    have hzpos : (0 : ℝ) < (1 + |z|) ^ k := by positivity
    have hz2 : (1 + |z|) ^ (-(k : ℝ)) = ((1 + |z|) ^ k)⁻¹ := by
      rw [← Real.rpow_natCast (1 + |z|) k, ← Real.rpow_neg (by positivity)]
    have hy2 : (1 + |y|) ^ (-(k : ℝ)) = ((1 + |y|) ^ k)⁻¹ := by
      rw [← Real.rpow_natCast (1 + |y|) k, ← Real.rpow_neg (by positivity)]
    have hkey : ((1 + |z|) ^ k)⁻¹ ≤ 2 ^ k * ((1 + |y|) ^ k)⁻¹ := by
      have hexp : ((1 + |y|) / 2) ^ k = (1 + |y|) ^ k / 2 ^ k := by
        rw [div_pow]
      rw [hexp] at hsq
      have h4 : (0 : ℝ) < (1 + |y|) ^ k / 2 ^ k := by positivity
      have hm : ((1 + |z|) ^ k)⁻¹ * ((1 + |y|) ^ k / 2 ^ k)
          ≤ ((1 + |z|) ^ k)⁻¹ * ((1 + |z|) ^ k) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      rw [inv_mul_cancel₀ (ne_of_gt hzpos)] at hm
      have hstep : ((1 + |z|) ^ k)⁻¹ ≤ ((1 + |y|) ^ k / 2 ^ k)⁻¹ := by
        calc ((1 + |z|) ^ k)⁻¹
            = ((1 + |z|) ^ k)⁻¹ * ((1 + |y|) ^ k / 2 ^ k) * ((1 + |y|) ^ k / 2 ^ k)⁻¹ := by
              field_simp
          _ ≤ 1 * ((1 + |y|) ^ k / 2 ^ k)⁻¹ :=
              mul_le_mul_of_nonneg_right hm (by positivity)
          _ = ((1 + |y|) ^ k / 2 ^ k)⁻¹ := one_mul _
      have hrw : ((1 + |y|) ^ k / 2 ^ k)⁻¹ = 2 ^ k * ((1 + |y|) ^ k)⁻¹ := by
        field_simp
      rwa [hrw] at hstep
    calc ‖deriv ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z‖
        ≤ C * (1 + |z|) ^ (-(k : ℝ)) := hC z
      _ = C * ((1 + |z|) ^ k)⁻¹ := by rw [hz2]
      _ ≤ C * (2 ^ k * ((1 + |y|) ^ k)⁻¹) := mul_le_mul_of_nonneg_left hkey hC0
      _ = 2 ^ k * C * (1 + |y|) ^ (-(k : ℝ)) := by rw [hy2]; ring
  have hdiff : ∀ z ∈ Metric.closedBall y 1,
      DifferentiableAt ℝ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z := fun z _ => η.differentiable z
  have hconv : Convex ℝ (Metric.closedBall y 1) := convex_closedBall y 1
  have hys : y ∈ Metric.closedBall y 1 := Metric.mem_closedBall_self (by norm_num)
  have hxs : y + ε ∈ Metric.closedBall y 1 := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    simpa using hε
  have hmvt := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hball hys hxs
  simpa [Real.norm_eq_abs] using hmvt

/-- **The fractional convolution inherits Schwartz decay at every order.** -/
theorem connes_fracConv_decay {α : ℝ} (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0) (η : 𝓢(ℝ, ℂ)) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ,
      ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ≤ A * (1 + |x|) ^ (-(k : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := connes_schwartz_deriv_weight_order η k
  set J : ℝ := ∫ ε : ℝ, Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε with hJ
  have hJint : Integrable (Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α))) volume :=
    connes_fracEps_integrable hα1
  have hJ0 : 0 ≤ J := integral_nonneg fun ε => connes_fracEps_nonneg ε
  refine ⟨2 ^ k * C * J, by positivity, fun x => ?_⟩
  have hbd : ∀ ε : ℝ, ‖((connesFracWeight α ψ ε : ℝ) : ℂ) * (η (x + ε) - η x)‖
      ≤ (2 ^ k * C * (1 + |x|) ^ (-(k : ℝ))) *
        Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε := by
    intro ε
    have hDnn : (0 : ℝ) ≤ 2 ^ k * C * (1 + |x|) ^ (-(k : ℝ)) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
    by_cases hmem : ε ∈ Icc (-1 : ℝ) 1
    · have hεle : |ε| ≤ 1 := abs_le.mpr ⟨hmem.1, hmem.2⟩
      have hind : Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε = |ε| ^ (-α) :=
        Set.indicator_of_mem hmem (fun ε : ℝ => |ε| ^ (-α))
      rw [hind, norm_mul]
      have hwabs : ‖(((connesFracWeight α ψ ε : ℝ)) : ℂ)‖ ≤ |ε| ^ (-1 - α) := by
        rw [Complex.norm_real, Real.norm_eq_abs, connesFracWeight,
          abs_of_nonneg (mul_nonneg (hψ0 _) (Real.rpow_nonneg (abs_nonneg ε) _))]
        calc ψ |ε| * |ε| ^ (-1 - α) ≤ 1 * |ε| ^ (-1 - α) :=
              mul_le_mul_of_nonneg_right (hψ1 _) (Real.rpow_nonneg (abs_nonneg ε) _)
          _ = |ε| ^ (-1 - α) := one_mul _
      have hdiff := connes_schwartz_diff_bound_order η k hC0 hC (y := x) (ε := ε) hεle
      rcases eq_or_ne ε 0 with hε0 | hε0
      · subst hε0
        have hrhs : (0 : ℝ) ≤ 2 ^ k * C * (1 + |x|) ^ (-(k : ℝ)) * |(0 : ℝ)| ^ (-α) :=
          mul_nonneg hDnn (Real.rpow_nonneg (abs_nonneg _) _)
        simpa using hrhs
      · have hεpos : (0 : ℝ) < |ε| := abs_pos.mpr hε0
        have hcomb : |ε| ^ (-1 - α) * |ε| = |ε| ^ (-α) := by
          rw [show (-1 - α : ℝ) = -α + -1 by ring, Real.rpow_add hεpos,
            Real.rpow_neg_one, inv_mul_cancel_right₀ (ne_of_gt hεpos)]
        calc ‖(((connesFracWeight α ψ ε : ℝ)) : ℂ)‖ * ‖η (x + ε) - η x‖
            ≤ (|ε| ^ (-1 - α)) * ((2 ^ k * C * (1 + |x|) ^ (-(k : ℝ))) * |ε|) :=
              mul_le_mul hwabs hdiff (norm_nonneg _) (Real.rpow_nonneg (abs_nonneg ε) _)
          _ = (2 ^ k * C * (1 + |x|) ^ (-(k : ℝ))) * (|ε| ^ (-1 - α) * |ε|) := by ring
          _ = (2 ^ k * C * (1 + |x|) ^ (-(k : ℝ))) * |ε| ^ (-α) := by rw [hcomb]
    · have hgt : 1 < |ε| := by
        by_contra hcon
        exact hmem (Set.mem_Icc.mpr (abs_le.mp (not_lt.mp hcon)))
      have hw0 : connesFracWeight α ψ ε = 0 := connesFracWeight_eq_zero hψsupp hgt
      rw [hw0, Set.indicator_of_notMem hmem]
      simp
  have hstep : ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      ≤ ∫ ε : ℝ, (2 ^ k * C * (1 + |x|) ^ (-(k : ℝ))) *
          Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ε => norm_nonneg _)
      (hJint.const_mul _) (Filter.Eventually.of_forall hbd)
  rw [MeasureTheory.integral_const_mul, ← hJ] at hstep
  calc ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      ≤ (2 ^ k * C * (1 + |x|) ^ (-(k : ℝ))) * J := hstep
    _ = 2 ^ k * C * J * (1 + |x|) ^ (-(k : ℝ)) := by ring

end

end GaloisForLFunctions.RHTower

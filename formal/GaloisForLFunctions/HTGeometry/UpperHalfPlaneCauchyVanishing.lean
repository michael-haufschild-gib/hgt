import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Cauchy vanishing on the upper half-plane

If `u` is holomorphic at every point of the closed upper half-plane and satisfies the decay
bound `‖u z‖ ≤ C / (1 + ‖z‖ ^ 2)` there, then `∫_ℝ u = 0`.

The proof integrates `u` over the boundary of the square `[-R, R] × [0, R]`.  Cauchy's theorem
for a rectangle makes that boundary integral vanish, while the quadratic decay bounds the top
side by `2 C / R` and each vertical side by `C / R`.  Letting `R → ∞` and using integrability
of `u` on the real line identifies the remaining bottom side with `∫_ℝ u`.
-/

open Complex Filter Topology MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_sq_ofReal_add_mul_I (x y : ℝ) : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  ring

/-- Quadratic decay on the real axis makes the boundary restriction integrable. -/
theorem integrable_ofReal_of_decay {u : ℂ → ℂ} {C : ℝ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ u z)
    (hbd : ∀ z : ℂ, 0 ≤ z.im → ‖u z‖ ≤ C / (1 + ‖z‖ ^ 2)) :
    Integrable (fun x : ℝ => u ((x : ℝ) : ℂ)) := by
  have hbdline : ∀ x : ℝ, ‖u ((x : ℝ) : ℂ)‖ ≤ C * (1 + x ^ 2)⁻¹ := by
    intro x
    have h := hbd ((x : ℝ) : ℂ) (by simp)
    have hx : ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hx] at h
    calc ‖u ((x : ℝ) : ℂ)‖ ≤ C / (1 + x ^ 2) := h
      _ = C * (1 + x ^ 2)⁻¹ := by rw [div_eq_mul_inv]
  have hcont : Continuous fun x : ℝ => u ((x : ℝ) : ℂ) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hd : DifferentiableAt ℂ u ((x : ℝ) : ℂ) := hdiff _ (by simp)
    exact hd.continuousAt.comp Complex.continuous_ofReal.continuousAt
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hcont.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall hbdline

/-- **Cauchy vanishing on the upper half-plane.**  A function holomorphic on the closed upper
half-plane and decaying like `‖z‖^{-2}` there integrates to zero over the real line. -/
theorem integral_eq_zero_of_upperHalfPlane_decay {u : ℂ → ℂ} {C : ℝ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ u z)
    (hbd : ∀ z : ℂ, 0 ≤ z.im → ‖u z‖ ≤ C / (1 + ‖z‖ ^ 2)) :
    (∫ x : ℝ, u (x : ℂ)) = 0 := by
  have hC : 0 ≤ C := by
    have h := hbd I (by simp)
    have h2 : (0 : ℝ) ≤ C / (1 + ‖(I : ℂ)‖ ^ 2) := le_trans (norm_nonneg _) h
    rw [Complex.norm_I] at h2
    norm_num at h2
    linarith
  have hint : Integrable (fun x : ℝ => u ((x : ℝ) : ℂ)) :=
    integrable_ofReal_of_decay hdiff hbd
  have hsq : ∀ (a b : ℝ), 0 ≤ b → ‖u ((a : ℂ) + (b : ℂ) * I)‖ ≤ C / (1 + a ^ 2 + b ^ 2) := by
    intro a b hb
    have him : ((a : ℂ) + (b : ℂ) * I).im = b := by simp
    have h := hbd _ (by rw [him]; exact hb)
    rwa [norm_sq_ofReal_add_mul_I, ← add_assoc] at h
  -- the rectangle identity
  have hrect : ∀ R : ℝ, 0 < R →
      (((∫ x in (-R)..R, u ((x : ℂ) + ((0:ℝ) : ℂ) * I))
        - ∫ x in (-R)..R, u ((x : ℂ) + ((R : ℝ) : ℂ) * I))
        + I • ∫ y in (0:ℝ)..R, u (((R : ℝ) : ℂ) + (y : ℂ) * I))
        - I • ∫ y in (0:ℝ)..R, u (((-R : ℝ) : ℂ) + (y : ℂ) * I) = 0 := by
    intro R hR
    have hz : ((-R : ℝ) : ℂ).re = -R := by simp
    have hz2 : ((-R : ℝ) : ℂ).im = 0 := by simp
    have hw : (((R : ℝ) : ℂ) + ((R : ℝ) : ℂ) * I).re = R := by simp
    have hw2 : (((R : ℝ) : ℂ) + ((R : ℝ) : ℂ) * I).im = R := by simp
    have hkey := Complex.integral_boundary_rect_eq_zero_of_differentiableOn u
      ((-R : ℝ) : ℂ) (((R : ℝ) : ℂ) + ((R : ℝ) : ℂ) * I) ?_
    · rw [hz, hz2, hw, hw2] at hkey
      exact hkey
    · rw [hz, hz2, hw, hw2]
      intro z hz3
      refine ((hdiff z ?_).differentiableWithinAt)
      have := hz3.2
      simp only [Set.mem_preimage, Set.uIcc_of_le hR.le] at this
      exact this.1
  -- the three vanishing sides
  have hdecay : ∀ (a b R : ℝ), 0 < R → R ≤ |a| ∨ R ≤ |b| → 0 ≤ b →
      ‖u ((a : ℂ) + (b : ℂ) * I)‖ ≤ C / R ^ 2 := by
    intro a b R hR hor hb
    refine le_trans (hsq a b hb) ?_
    refine div_le_div_of_nonneg_left hC (by positivity) ?_
    rcases hor with h | h
    · nlinarith [sq_abs a, sq_nonneg b, abs_nonneg a]
    · nlinarith [sq_abs b, sq_nonneg a, abs_nonneg b]
  have hmain : ∀ R : ℝ, 0 < R → ‖∫ x in (-R)..R, u ((x : ℝ) : ℂ)‖ ≤ 4 * C / R := by
    intro R hR
    have htop : ‖∫ x in (-R)..R, u ((x : ℂ) + ((R : ℝ) : ℂ) * I)‖ ≤ (C / R ^ 2) * |R - -R| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
      exact hdecay x R R hR (Or.inr (by rw [abs_of_pos hR])) hR.le
    have hright : ‖∫ y in (0:ℝ)..R, u (((R : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ (C / R ^ 2) * |R - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      have hy0 : 0 ≤ y := by
        rcases le_or_gt 0 y with h | h
        · exact h
        · exfalso
          rw [Set.uIoc_of_le hR.le] at hy
          exact absurd hy.1 (by linarith)
      exact hdecay R y R hR (Or.inl (by rw [abs_of_pos hR])) hy0
    have hleft : ‖∫ y in (0:ℝ)..R, u (((-R : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ (C / R ^ 2) * |R - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      have hy0 : 0 ≤ y := by
        rcases le_or_gt 0 y with h | h
        · exact h
        · exfalso
          rw [Set.uIoc_of_le hR.le] at hy
          exact absurd hy.1 (by linarith)
      exact hdecay (-R) y R hR (Or.inl (by rw [abs_neg, abs_of_pos hR])) hy0
    have hzeroI : ∀ x : ℝ, ((x : ℂ) + ((0:ℝ) : ℂ) * I) = ((x : ℝ) : ℂ) := by
      intro x; push_cast; ring
    have heq := hrect R hR
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => u ((x : ℝ) : ℂ))
      (fun x _ => by rw [hzeroI x])] at heq
    have hsol : (∫ x in (-R)..R, u ((x : ℝ) : ℂ))
        = (∫ x in (-R)..R, u ((x : ℂ) + ((R : ℝ) : ℂ) * I))
          - I • (∫ y in (0:ℝ)..R, u (((R : ℝ) : ℂ) + (y : ℂ) * I))
          + I • (∫ y in (0:ℝ)..R, u (((-R : ℝ) : ℂ) + (y : ℂ) * I)) := by
      linear_combination heq
    have habsR : |R - -R| = 2 * R := by rw [abs_of_nonneg (by linarith)]; ring
    have habs0 : |R - (0:ℝ)| = R := by rw [sub_zero, abs_of_pos hR]
    rw [habsR] at htop
    rw [habs0] at hright hleft
    have hnI : ‖(I : ℂ)‖ = 1 := Complex.norm_I
    calc ‖∫ x in (-R)..R, u ((x : ℝ) : ℂ)‖
        ≤ ‖∫ x in (-R)..R, u ((x : ℂ) + ((R : ℝ) : ℂ) * I)‖
            + ‖I • (∫ y in (0:ℝ)..R, u (((R : ℝ) : ℂ) + (y : ℂ) * I))‖
            + ‖I • (∫ y in (0:ℝ)..R, u (((-R : ℝ) : ℂ) + (y : ℂ) * I))‖ := by
          rw [hsol]
          exact le_trans (norm_add_le _ _) (by
            gcongr
            exact norm_sub_le _ _)
      _ ≤ (C / R ^ 2) * (2 * R) + (C / R ^ 2) * R + (C / R ^ 2) * R := by
          rw [norm_smul, norm_smul, hnI, one_mul, one_mul]
          gcongr
      _ = 4 * C / R := by field_simp; ring
  -- pass to the limit
  have hlim : Tendsto (fun R : ℝ => ∫ x in (-R)..R, u ((x : ℝ) : ℂ)) atTop
      (𝓝 (∫ x : ℝ, u ((x : ℝ) : ℂ))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hnormlim : Tendsto (fun R : ℝ => ‖∫ x in (-R)..R, u ((x : ℝ) : ℂ)‖) atTop
      (𝓝 ‖∫ x : ℝ, u ((x : ℝ) : ℂ)‖) := hlim.norm
  have hzerolim : Tendsto (fun R : ℝ => 4 * C / R) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hle : ‖∫ x : ℝ, u ((x : ℝ) : ℂ)‖ ≤ 0 := by
    refine le_of_tendsto_of_tendsto hnormlim hzerolim ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    exact hmain R hR
  exact norm_le_zero_iff.mp hle


/-- **Far-field decay upgrades to a global decay bound.**  Continuity on the compact part of the
closed half-plane bounds `u` there, and the two bounds combine into a single `‖z‖^{-2}` law. -/
theorem exists_global_decay_bound_of_farDecay {u : ℂ → ℂ} {M R : ℝ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ u z) (hR : 0 < R)
    (hfar : ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖u z‖ ≤ M / ‖z‖ ^ 2) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → ‖u z‖ ≤ C / (1 + ‖z‖ ^ 2) := by
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hM : 0 ≤ M := by
    have hz : ((R : ℂ) * I).im = R := by simp
    have hn : ‖(R : ℂ) * I‖ = R := by
      rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, mul_one]
    have h := hfar ((R : ℂ) * I) (by rw [hz]; exact hR.le) (by rw [hn])
    rw [hn] at h
    have h0 : (0 : ℝ) ≤ M / R ^ 2 := le_trans (norm_nonneg _) h
    rcases div_nonneg_iff.mp h0 with ⟨hm, _⟩ | ⟨_, hbad⟩
    · exact hm
    · linarith
  set K : Set ℂ := {z : ℂ | 0 ≤ z.im} ∩ Metric.closedBall 0 R with hKdef
  have hKcomp : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const Complex.continuous_im).inter Metric.isClosed_closedBall
    · exact Metric.isBounded_closedBall.subset Set.inter_subset_right
  have hcont : ContinuousOn u K := fun z hz => (hdiff z hz.1).continuousAt.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := hKcomp.exists_bound_of_continuousOn hcont
  have hM₀nonneg : 0 ≤ M₀ :=
    le_trans (norm_nonneg (u 0)) (hM₀ 0 ⟨by simp, by simp [hR.le]⟩)
  refine ⟨max (M * (1 + 1 / R ^ 2)) (M₀ * (1 + R ^ 2)), fun z hz => ?_⟩
  rcases le_or_gt ‖z‖ R with hle | hgt
  · have hmem : z ∈ K := ⟨hz, by simpa [Metric.mem_closedBall] using hle⟩
    refine le_trans (hM₀ z hmem) ?_
    rw [le_div_iff₀ (by positivity)]
    have hC : M₀ * (1 + R ^ 2) ≤ max (M * (1 + 1 / R ^ 2)) (M₀ * (1 + R ^ 2)) := le_max_right _ _
    have hsq : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z, hle]
    nlinarith [hC, mul_nonneg hM₀nonneg (sub_nonneg.mpr hsq)]
  · have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le hR hgt.le
    refine le_trans (hfar z hz hgt.le) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hRz : R ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [hR.le, hgt.le]
    have hratio : (1 : ℝ) ≤ ‖z‖ ^ 2 / R ^ 2 := (one_le_div hR2).mpr hRz
    have key : M ≤ M * (1 / R ^ 2) * ‖z‖ ^ 2 := by
      have hrw : M * (1 / R ^ 2) * ‖z‖ ^ 2 = M * (‖z‖ ^ 2 / R ^ 2) := by ring
      rw [hrw]
      nlinarith [hM, hratio]
    have hCle : M * (1 + 1 / R ^ 2) ≤ max (M * (1 + 1 / R ^ 2)) (M₀ * (1 + R ^ 2)) :=
      le_max_left _ _
    nlinarith [key, mul_nonneg (sub_nonneg.mpr hCle) (sq_nonneg ‖z‖)]

/-- **Cauchy vanishing from far-field decay alone.** -/
theorem integral_eq_zero_of_upperHalfPlane_farDecay {u : ℂ → ℂ} {M R : ℝ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ u z) (hR : 0 < R)
    (hfar : ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖u z‖ ≤ M / ‖z‖ ^ 2) :
    (∫ x : ℝ, u ((x : ℝ) : ℂ)) = 0 := by
  obtain ⟨C, hC⟩ := exists_global_decay_bound_of_farDecay hdiff hR hfar
  exact integral_eq_zero_of_upperHalfPlane_decay hdiff hC

/-- The boundary restriction is integrable under far-field quadratic decay. -/
theorem integrable_ofReal_of_farDecay {u : ℂ → ℂ} {M R : ℝ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ u z) (hR : 0 < R)
    (hfar : ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖u z‖ ≤ M / ‖z‖ ^ 2) :
    Integrable (fun x : ℝ => u ((x : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := exists_global_decay_bound_of_farDecay hdiff hR hfar
  exact integrable_ofReal_of_decay hdiff hC

end

end GaloisForLFunctions.HTGeometry

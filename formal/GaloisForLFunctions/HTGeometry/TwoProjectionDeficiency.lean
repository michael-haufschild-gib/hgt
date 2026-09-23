import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The Friedrichs angle deficiency bound for two subspaces

If two closed subspaces `U`, `V` of a Hilbert space make an angle bounded away from zero, in the
sense that `|⟪a, r⟫| ≤ c ‖a‖ ‖r‖` for `a ∈ U`, `r ∈ V` with `c < 1`, then a vector orthogonal to
`Uᗮ ⊓ Vᗮ` is controlled by its two projections:

`‖v − Q v‖² ≤ (‖P_U v‖² + ‖P_V v‖²) / (1 − c)`,

where `Q` is the orthogonal projection onto `Uᗮ ⊓ Vᗮ`.  In particular `Q v → v` whenever both
projections of `v` tend to zero, which is the standard route to strong convergence of an
intersection projection.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The parallelogram lower bound produced by an angle bound. -/
theorem norm_sq_add_le_of_angle {U V : Submodule ℂ H} {c : ℝ} (hc0 : 0 ≤ c)
    (hangle : ∀ a ∈ U, ∀ r ∈ V, ‖(⟪a, r⟫_ℂ)‖ ≤ c * ‖a‖ * ‖r‖)
    {a r : H} (ha : a ∈ U) (hr : r ∈ V) :
    (1 - c) * (‖a‖ ^ (2 : ℕ) + ‖r‖ ^ (2 : ℕ)) ≤ ‖a + r‖ ^ (2 : ℕ) := by
  have hexp : ‖a + r‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) + 2 * (⟪a, r⟫_ℂ).re + ‖r‖ ^ (2 : ℕ) := by
    simpa using norm_add_sq (𝕜 := ℂ) a r
  have hre : |(⟪a, r⟫_ℂ).re| ≤ c * ‖a‖ * ‖r‖ :=
    (Complex.abs_re_le_norm _).trans (hangle a ha r hr)
  have habs : -(c * ‖a‖ * ‖r‖) ≤ (⟪a, r⟫_ℂ).re := neg_le_of_abs_le hre
  rw [hexp]
  nlinarith [sq_nonneg (‖a‖ - ‖r‖), norm_nonneg a, norm_nonneg r]

theorem two_cauchy_schwarz {x₁ x₂ y₁ y₂ : ℝ} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    x₁ * y₁ + x₂ * y₂ ≤ Real.sqrt (x₁ ^ (2 : ℕ) + x₂ ^ (2 : ℕ)) * Real.sqrt (y₁ ^ (2 : ℕ) + y₂ ^ (2 : ℕ)) := by
  have hxs : (0 : ℝ) ≤ x₁ ^ (2 : ℕ) + x₂ ^ (2 : ℕ) := by positivity
  have hys : (0 : ℝ) ≤ y₁ ^ (2 : ℕ) + y₂ ^ (2 : ℕ) := by positivity
  rw [← Real.sqrt_mul hxs]
  have hsum : 0 ≤ x₁ * y₁ + x₂ * y₂ := by positivity
  rw [show x₁ * y₁ + x₂ * y₂ = Real.sqrt ((x₁ * y₁ + x₂ * y₂) ^ (2 : ℕ)) from
    (Real.sqrt_sq hsum).symm]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (x₁ * y₂ - x₂ * y₁)]

/-- **The Friedrichs angle deficiency bound.** -/
theorem norm_sq_le_of_mem_closure {U V : Submodule ℂ H} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hangle : ∀ a ∈ U, ∀ r ∈ V, ‖(⟪a, r⟫_ℂ)‖ ≤ c * ‖a‖ * ‖r‖)
    {w : H} (hw : w ∈ (U ⊔ V)ᗮᗮ) :
    ‖w‖ ^ (2 : ℕ) ≤ (‖U.starProjection w‖ ^ (2 : ℕ) + ‖V.starProjection w‖ ^ (2 : ℕ)) / (1 - c) := by
  have hone : (0 : ℝ) < 1 - c := by linarith
  set N : ℝ := ‖U.starProjection w‖ ^ (2 : ℕ) + ‖V.starProjection w‖ ^ (2 : ℕ) with hN
  have hNnn : 0 ≤ N := by positivity
  set B : ℝ := Real.sqrt (N / (1 - c)) with hB
  have hBnn : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ (2 : ℕ) = N / (1 - c) := Real.sq_sqrt (by positivity)
  have hBeq : B = Real.sqrt N / Real.sqrt (1 - c) := by
    rw [hB, Real.sqrt_div hNnn]
  have hclos : w ∈ closure ((U ⊔ V : Submodule ℂ H) : Set H) := by
    rw [Submodule.orthogonal_orthogonal_eq_closure (U ⊔ V)] at hw
    exact hw
  have hq : ‖w‖ ^ (2 : ℕ) ≤ B * ‖w‖ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hden : (0 : ℝ) < B + ‖w‖ + 1 := by positivity
    set δ : ℝ := ε / (B + ‖w‖ + 1) with hδdef
    have hδ : 0 < δ := by positivity
    obtain ⟨m, hm, hdist⟩ := Metric.mem_closure_iff.mp hclos δ hδ
    obtain ⟨a, ha, r, hr, hmar⟩ := Submodule.mem_sup.mp hm
    have hwm : ‖w - m‖ < δ := by
      rw [← dist_eq_norm]
      exact hdist
    have hmnorm : ‖m‖ ≤ ‖w‖ + δ := by
      have h1 : ‖m‖ - ‖w‖ ≤ ‖m - w‖ := norm_sub_norm_le m w
      rw [norm_sub_rev] at h1
      linarith
    have hPa : (⟪w, a⟫_ℂ) = (⟪U.starProjection w, a⟫_ℂ) := by
      rw [Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr ha]
    have hPr : (⟪w, r⟫_ℂ) = (⟪V.starProjection w, r⟫_ℂ) := by
      rw [Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hr]
    have hsplit : ‖w‖ ^ (2 : ℕ) = (⟪w, m⟫_ℂ).re + (⟪w, w - m⟫_ℂ).re := by
      have h : (⟪w, w⟫_ℂ) = (⟪w, m⟫_ℂ) + (⟪w, w - m⟫_ℂ) := by
        rw [← inner_add_right]
        congr 1
        abel
      have h2 : ‖w‖ ^ (2 : ℕ) = (⟪w, w⟫_ℂ).re := by
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
      rw [h2, h, Complex.add_re]
    have hrest : (⟪w, w - m⟫_ℂ).re ≤ ‖w‖ * δ := by
      calc (⟪w, w - m⟫_ℂ).re ≤ ‖(⟪w, w - m⟫_ℂ)‖ := Complex.re_le_norm _
        _ ≤ ‖w‖ * ‖w - m‖ := norm_inner_le_norm _ _
        _ ≤ ‖w‖ * δ := by
            exact mul_le_mul_of_nonneg_left hwm.le (norm_nonneg w)
    have hmain : (⟪w, m⟫_ℂ).re ≤ B * ‖m‖ := by
      have hsum : (⟪w, m⟫_ℂ).re = (⟪w, a⟫_ℂ).re + (⟪w, r⟫_ℂ).re := by
        rw [← hmar, inner_add_right, Complex.add_re]
      have h1 : (⟪w, a⟫_ℂ).re ≤ ‖U.starProjection w‖ * ‖a‖ := by
        rw [hPa]
        calc (⟪U.starProjection w, a⟫_ℂ).re ≤ ‖(⟪U.starProjection w, a⟫_ℂ)‖ :=
              Complex.re_le_norm _
          _ ≤ ‖U.starProjection w‖ * ‖a‖ := norm_inner_le_norm _ _
      have h2 : (⟪w, r⟫_ℂ).re ≤ ‖V.starProjection w‖ * ‖r‖ := by
        rw [hPr]
        calc (⟪V.starProjection w, r⟫_ℂ).re ≤ ‖(⟪V.starProjection w, r⟫_ℂ)‖ :=
              Complex.re_le_norm _
          _ ≤ ‖V.starProjection w‖ * ‖r‖ := norm_inner_le_norm _ _
      have hcs := two_cauchy_schwarz (norm_nonneg (U.starProjection w))
        (norm_nonneg (V.starProjection w)) (norm_nonneg a) (norm_nonneg r)
      have hangle' := norm_sq_add_le_of_angle hc0 hangle ha hr
      rw [hmar] at hangle'
      have hsq : Real.sqrt (‖a‖ ^ (2 : ℕ) + ‖r‖ ^ (2 : ℕ)) ≤ ‖m‖ / Real.sqrt (1 - c) := by
        rw [le_div_iff₀ (Real.sqrt_pos.mpr hone), ← Real.sqrt_mul (by positivity)]
        have : (‖a‖ ^ (2 : ℕ) + ‖r‖ ^ (2 : ℕ)) * (1 - c) ≤ ‖m‖ ^ (2 : ℕ) := by nlinarith
        calc Real.sqrt ((‖a‖ ^ (2 : ℕ) + ‖r‖ ^ (2 : ℕ)) * (1 - c)) ≤ Real.sqrt (‖m‖ ^ (2 : ℕ)) :=
              Real.sqrt_le_sqrt this
          _ = ‖m‖ := Real.sqrt_sq (norm_nonneg m)
      have hNsqrt : Real.sqrt (‖U.starProjection w‖ ^ (2 : ℕ) + ‖V.starProjection w‖ ^ (2 : ℕ))
          = Real.sqrt N := by rw [hN]
      rw [hsum]
      calc (⟪w, a⟫_ℂ).re + (⟪w, r⟫_ℂ).re
          ≤ ‖U.starProjection w‖ * ‖a‖ + ‖V.starProjection w‖ * ‖r‖ := by linarith
        _ ≤ Real.sqrt (‖U.starProjection w‖ ^ (2 : ℕ) + ‖V.starProjection w‖ ^ (2 : ℕ))
              * Real.sqrt (‖a‖ ^ (2 : ℕ) + ‖r‖ ^ (2 : ℕ)) := hcs
        _ ≤ Real.sqrt N * (‖m‖ / Real.sqrt (1 - c)) := by
            rw [hNsqrt]
            exact mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
        _ = B * ‖m‖ := by rw [hBeq]; ring
    have hfinal : ‖w‖ ^ (2 : ℕ) ≤ B * (‖w‖ + δ) + ‖w‖ * δ := by
      have hB1 : B * ‖m‖ ≤ B * (‖w‖ + δ) := mul_le_mul_of_nonneg_left hmnorm hBnn
      linarith
    have hδbound : B * δ + ‖w‖ * δ ≤ ε := by
      have h : δ * (B + ‖w‖ + 1) = ε := by
        rw [hδdef]
        field_simp
      nlinarith [hδ.le, norm_nonneg w]
    nlinarith [hfinal, hδbound]
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
  · rw [← h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · have hle : ‖w‖ ≤ B := by
      have := hq
      nlinarith
    calc ‖w‖ ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by nlinarith
      _ = N / (1 - c) := hBsq

/-- **The deficiency of the intersection projection.**  If two closed subspaces make an angle
bounded away from zero, the projection onto the orthogonal complement of their span is controlled
by the two individual projections. -/
theorem norm_sub_intersectionProjection_sq_le {U V : Submodule ℂ H}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hangle : ∀ a ∈ U, ∀ r ∈ V, ‖(⟪a, r⟫_ℂ)‖ ≤ c * ‖a‖ * ‖r‖) (v : H) :
    ‖v - ((U ⊔ V)ᗮ).starProjection v‖ ^ (2 : ℕ)
      ≤ (‖U.starProjection v‖ ^ (2 : ℕ) + ‖V.starProjection v‖ ^ (2 : ℕ)) / (1 - c) := by
  have hsplit := Submodule.starProjection_add_starProjection_orthogonal (K := (U ⊔ V)ᗮ) v
  have hw : v - ((U ⊔ V)ᗮ).starProjection v = ((U ⊔ V)ᗮᗮ).starProjection v := by
    linear_combination (norm := module) -hsplit
  have hmem : v - ((U ⊔ V)ᗮ).starProjection v ∈ (U ⊔ V)ᗮᗮ := by
    rw [hw]
    exact Submodule.starProjection_apply_mem _ _
  have hkill : ∀ (W : Submodule ℂ H) [W.HasOrthogonalProjection], W ≤ U ⊔ V →
      W.starProjection (((U ⊔ V)ᗮ).starProjection v) = 0 := by
    intro W _ hle
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.orthogonal_le hle (Submodule.starProjection_apply_mem _ _)
  have hU : U.starProjection (v - ((U ⊔ V)ᗮ).starProjection v) = U.starProjection v := by
    rw [map_sub, hkill U le_sup_left, sub_zero]
  have hV : V.starProjection (v - ((U ⊔ V)ᗮ).starProjection v) = V.starProjection v := by
    rw [map_sub, hkill V le_sup_right, sub_zero]
  have := norm_sq_le_of_mem_closure hc0 hc1 hangle hmem
  rwa [hU, hV] at this

omit [CompleteSpace H] in
/-- The angle hypothesis follows from an operator-norm bound on the product of the two
projections. -/
theorem angle_of_norm_starProjection_mul_le {U V : Submodule ℂ H}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] {c : ℝ}
    (h : ‖U.starProjection * V.starProjection‖ ≤ c) :
    ∀ a ∈ U, ∀ r ∈ V, ‖(⟪a, r⟫_ℂ)‖ ≤ c * ‖a‖ * ‖r‖ := by
  intro a ha r hr
  have hUa : U.starProjection a = a := Submodule.starProjection_eq_self_iff.mpr ha
  have hVr : V.starProjection r = r := Submodule.starProjection_eq_self_iff.mpr hr
  have hinner : (⟪a, r⟫_ℂ) = (⟪a, (U.starProjection * V.starProjection) r⟫_ℂ) := by
    have hstep : (U.starProjection * V.starProjection) r = U.starProjection r := by
      show U.starProjection (V.starProjection r) = U.starProjection r
      rw [hVr]
    rw [hstep, ← Submodule.inner_starProjection_left_eq_right, hUa]
  rw [hinner]
  calc ‖(⟪a, (U.starProjection * V.starProjection) r⟫_ℂ)‖
      ≤ ‖a‖ * ‖(U.starProjection * V.starProjection) r‖ := norm_inner_le_norm _ _
    _ ≤ ‖a‖ * (c * ‖r‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg a)
        exact (ContinuousLinearMap.le_opNorm _ r).trans
          (mul_le_mul_of_nonneg_right h (norm_nonneg r))
    _ = c * ‖a‖ * ‖r‖ := by ring

end GaloisForLFunctions.HTGeometry

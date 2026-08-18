import GaloisForLFunctions.HTGeometry.CoefficientJetRelation
import GaloisForLFunctions.HTGeometry.DominantNeighborhood

/-!
# A dominant region for a relation whose coefficients move

The relation with frozen coefficients is linear in the coefficients, so its derivative in the jet is
the corresponding combination of the derivatives of the monomials.  On a bounded region those
derivatives are bounded, so a small change of the coefficients moves the derivative by little,
uniformly on the region.

Consequently a jet at which the separant does not vanish carries a convex region and a reference
functional dominating the derivative not only at that time but at every nearby time — the datum a
nonautonomous implicit-function argument consumes.
-/

open Metric Set

namespace GaloisForLFunctions.HTGeometry

variable {N n : ℕ}

/-- A monomial in the jet. -/
noncomputable def jetMonomial (ee : Fin (n + 1) → ℕ) (y : Fin (n + 1) → ℂ) : ℂ :=
  ∏ k : Fin (n + 1), (y k) ^ (ee k)

theorem contDiff_jetMonomial (ee : Fin (n + 1) → ℕ) :
    ContDiff ℂ (⊤ : ℕ∞) (jetMonomial ee) :=
  contDiff_prod fun k _ =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) k).contDiff).pow _

theorem differentiable_jetMonomial (ee : Fin (n + 1) → ℕ) :
    Differentiable ℂ (jetMonomial ee) :=
  (contDiff_jetMonomial ee).differentiable (by simp)

theorem continuous_fderiv_jetMonomial (ee : Fin (n + 1) → ℕ) :
    Continuous fun y => fderiv ℂ (jetMonomial ee) y :=
  (contDiff_jetMonomial ee).continuous_fderiv (by simp)

theorem frozenRelation_eq_sum_monomial (e : Fin N → Fin (n + 1) → ℕ) (c : Fin N → ℂ) :
    frozenRelation e c = fun y => ∑ i : Fin N, c i * jetMonomial (e i) y := rfl

/-- **The derivative of the frozen relation is linear in the coefficients.** -/
theorem fderiv_frozenRelation (e : Fin N → Fin (n + 1) → ℕ) (c : Fin N → ℂ)
    (y : Fin (n + 1) → ℂ) :
    fderiv ℂ (frozenRelation e c) y = ∑ i : Fin N, c i • fderiv ℂ (jetMonomial (e i)) y := by
  rw [frozenRelation_eq_sum_monomial]
  rw [fderiv_fun_sum (fun i _ => ((differentiable_jetMonomial (e i)) y).const_mul (c i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact fderiv_const_mul ((differentiable_jetMonomial (e i)) y) (c i)

/-- Changing the coefficients moves the derivative by the corresponding combination. -/
theorem norm_fderiv_frozenRelation_sub_le (e : Fin N → Fin (n + 1) → ℕ) (c c' : Fin N → ℂ)
    (y : Fin (n + 1) → ℂ) :
    ‖fderiv ℂ (frozenRelation e c) y - fderiv ℂ (frozenRelation e c') y‖
      ≤ ∑ i : Fin N, ‖c i - c' i‖ * ‖fderiv ℂ (jetMonomial (e i)) y‖ := by
  rw [fderiv_frozenRelation, fderiv_frozenRelation, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have hsm : c i • fderiv ℂ (jetMonomial (e i)) y - c' i • fderiv ℂ (jetMonomial (e i)) y
      = (c i - c' i) • fderiv ℂ (jetMonomial (e i)) y := (sub_smul (c i) (c' i) _).symm
  rw [hsm, norm_smul]

/-- **A dominant region valid at every nearby time.** -/
theorem exists_time_dominant_nbhd (e : Fin N → Fin (n + 1) → ℕ) {c : ℝ → Fin N → ℂ} {t : ℝ}
    (hc : ∀ i, ContinuousAt (fun s : ℝ => c s i) t) {y₀ : Fin (n + 1) → ℂ}
    (hne : partialCoeff (fderiv ℂ (frozenRelation e (c t)) y₀) (Fin.last n) ≠ 0) :
    ∃ (S : Set ((Fin (n + 1)) → ℂ)) (L : ((Fin (n + 1)) → ℂ) →L[ℂ] ℂ) (C : ℝ),
      IsOpen S ∧ Convex ℝ S ∧ y₀ ∈ S ∧ 0 ≤ C ∧
      (∀ᶠ s : ℝ in nhds t, ∀ y ∈ S, ‖fderiv ℂ (frozenRelation e (c s)) y - L‖ ≤ C) ∧
      C < ‖partialCoeff L (Fin.last n)‖ := by
  classical
  set L : ((Fin (n + 1)) → ℂ) →L[ℂ] ℂ := fderiv ℂ (frozenRelation e (c t)) y₀ with hL
  set a : ℝ := ‖partialCoeff L (Fin.last n)‖ with ha
  have ha0 : 0 < a := by
    rw [ha, norm_pos_iff]
    exact hne
  -- a ball on which the derivative at the base time stays close to its value at the centre
  have hcont : ContinuousAt (fun y => fderiv ℂ (frozenRelation e (c t)) y) y₀ :=
    (continuous_fderiv_frozenRelation e (c t)).continuousAt
  have hnhds : {K : ((Fin (n + 1)) → ℂ) →L[ℂ] ℂ | ‖K - L‖ < a / 4} ∈ nhds L := by
    refine Filter.mem_of_superset
      (Metric.ball_mem_nhds L (show (0 : ℝ) < a / 4 by positivity)) fun K hK => ?_
    show ‖K - L‖ < a / 4
    rw [Metric.mem_ball, dist_eq_norm] at hK
    exact hK
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.mem_nhds_iff.mp (hcont hnhds)
  set δ : ℝ := min δ₀ 1 with hδdef
  have hδ : 0 < δ := lt_min hδ₀ one_pos
  have hballδ : ∀ y ∈ ball y₀ δ, ‖fderiv ℂ (frozenRelation e (c t)) y - L‖ ≤ a / 4 := by
    intro y hy
    exact le_of_lt (hball (ball_subset_ball (min_le_left _ _) hy))
  -- a bound for the monomial derivatives on the closed ball
  have hcompact : IsCompact (closedBall y₀ δ) := isCompact_closedBall y₀ δ
  have hcontsum : ContinuousOn
      (fun y => ∑ i : Fin N, ‖fderiv ℂ (jetMonomial (e i)) y‖) (closedBall y₀ δ) := by
    exact continuousOn_finsetSum Finset.univ fun i _ =>
      ((continuous_fderiv_jetMonomial (e i)).norm).continuousOn
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcontsum
  have hM0 : 0 ≤ M := by
    have h0 : y₀ ∈ closedBall y₀ δ := mem_closedBall_self hδ.le
    have := hM y₀ h0
    have hnn : (0 : ℝ) ≤ ∑ i : Fin N, ‖fderiv ℂ (jetMonomial (e i)) y₀‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    exact le_trans hnn (le_trans (le_abs_self _) (by simpa using this))
  -- a time window on which the coefficients barely move
  have hcsum : ContinuousAt (fun s : ℝ => ∑ i : Fin N, ‖c s i - c t i‖) t := by
    have : ∀ i : Fin N, ContinuousAt (fun s : ℝ => ‖c s i - c t i‖) t := fun i =>
      ((hc i).sub continuousAt_const).norm
    exact tendsto_finsetSum Finset.univ fun i _ => this i
  have hzero : (fun s : ℝ => ∑ i : Fin N, ‖c s i - c t i‖) t = 0 := by simp
  have htime : ∀ᶠ s : ℝ in nhds t,
      (∑ i : Fin N, ‖c s i - c t i‖) ≤ a / (4 * (M + 1)) := by
    have hpos : (0 : ℝ) < a / (4 * (M + 1)) := by positivity
    have hmem : Metric.ball ((fun s : ℝ => ∑ i : Fin N, ‖c s i - c t i‖) t)
        (a / (4 * (M + 1))) ∈ nhds ((fun s : ℝ => ∑ i : Fin N, ‖c s i - c t i‖) t) :=
      Metric.ball_mem_nhds _ hpos
    filter_upwards [hcsum hmem] with s hs
    have hd : |(∑ i : Fin N, ‖c s i - c t i‖) - (∑ i : Fin N, ‖c t i - c t i‖)|
        < a / (4 * (M + 1)) := by
      have := Metric.mem_ball.mp hs
      rwa [Real.dist_eq] at this
    have hz : (∑ i : Fin N, ‖c t i - c t i‖) = 0 := by simp
    rw [hz, sub_zero] at hd
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hd)
  refine ⟨ball y₀ δ, L, a / 2, Metric.isOpen_ball, convex_ball y₀ δ, Metric.mem_ball_self hδ,
    by positivity, ?_, by rw [← ha]; linarith⟩
  filter_upwards [htime] with s hs
  intro y hy
  have hyc : y ∈ closedBall y₀ δ := ball_subset_closedBall hy
  have h1 : ‖fderiv ℂ (frozenRelation e (c s)) y - fderiv ℂ (frozenRelation e (c t)) y‖
      ≤ (∑ i : Fin N, ‖c s i - c t i‖) * M := by
    refine le_trans (norm_fderiv_frozenRelation_sub_le e (c s) (c t) y) ?_
    have hb : ∑ i : Fin N, ‖fderiv ℂ (jetMonomial (e i)) y‖ ≤ M := by
      have := hM y hyc
      exact le_trans (le_abs_self _) this
    calc ∑ i : Fin N, ‖c s i - c t i‖ * ‖fderiv ℂ (jetMonomial (e i)) y‖
        ≤ ∑ i : Fin N, ‖c s i - c t i‖ * M := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine le_trans ?_ hb
          exact Finset.single_le_sum
            (f := fun j : Fin N => ‖fderiv ℂ (jetMonomial (e j)) y‖)
            (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      _ = (∑ i : Fin N, ‖c s i - c t i‖) * M := by rw [← Finset.sum_mul]
  have h2 : ‖fderiv ℂ (frozenRelation e (c t)) y - L‖ ≤ a / 4 := hballδ y hy
  have h3 : (∑ i : Fin N, ‖c s i - c t i‖) * M ≤ a / 4 := by
    have hMle : M ≤ M + 1 := by linarith
    calc (∑ i : Fin N, ‖c s i - c t i‖) * M ≤ (a / (4 * (M + 1))) * M :=
          mul_le_mul_of_nonneg_right hs hM0
      _ ≤ (a / (4 * (M + 1))) * (M + 1) := by
          refine mul_le_mul_of_nonneg_left hMle (by positivity)
      _ = a / 4 := by field_simp
  calc ‖fderiv ℂ (frozenRelation e (c s)) y - L‖
      ≤ ‖fderiv ℂ (frozenRelation e (c s)) y - fderiv ℂ (frozenRelation e (c t)) y‖
        + ‖fderiv ℂ (frozenRelation e (c t)) y - L‖ := by
        have := norm_add_le (fderiv ℂ (frozenRelation e (c s)) y
          - fderiv ℂ (frozenRelation e (c t)) y)
          (fderiv ℂ (frozenRelation e (c t)) y - L)
        simpa using this
    _ ≤ a / 4 + a / 4 := add_le_add (le_trans h1 h3) h2
    _ = a / 2 := by ring

end GaloisForLFunctions.HTGeometry

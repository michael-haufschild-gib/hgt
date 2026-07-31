import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Jets of a resolvent family

The below-spectrum resolvents `R_u = (A - u)⁻¹` of one operator satisfy the first resolvent
identity

`R_u - R_v = (u - v) R_u R_v`.

That single algebraic law already forces everything analytic about the family.  It makes the
family continuous, differentiable with `∂_u R_u = R_u²`, and — by induction through the product
rule — it makes the `n`-th shift derivative exactly `n! R_u^{n+1}`.

Nothing here needs the operator `A`, its domain, or its spectrum: the statements are about an
arbitrary family in a normed algebra obeying the identity on an open set of shifts.  In
particular they apply to the resolvent family of an unbounded operator, whose values are bounded
even though the operator is not.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Nat

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The first resolvent identity on a set of shifts. -/
def IsResolventFamilyOn (S : ℝ → A) (s : Set ℝ) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, S u - S v = (u - v) • (S u * S v)

namespace IsResolventFamilyOn

variable {S : ℝ → A} {s : Set ℝ} {v : ℝ}

/-- The identity bounds the family near any of its points. -/
theorem norm_sub_le (hS : IsResolventFamilyOn S s) {u : ℝ} (hu : u ∈ s) (hv : v ∈ s) :
    ‖S u - S v‖ ≤ |u - v| * (‖S u‖ * ‖S v‖) := by
  rw [hS u hu v hv, norm_smul]
  simp only [Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (abs_nonneg _)

/-- Near a point of the family the norms stay bounded by twice the reference norm. -/
theorem norm_le_two_mul (hS : IsResolventFamilyOn S s) {u : ℝ} (hu : u ∈ s) (hv : v ∈ s)
    (hsmall : |u - v| * ‖S v‖ ≤ 1 / 2) :
    ‖S u‖ ≤ 2 * ‖S v‖ := by
  have hbound := hS.norm_sub_le hu hv
  have h1 : ‖S u‖ - ‖S v‖ ≤ ‖S u - S v‖ := norm_sub_norm_le _ _
  have h2 : |u - v| * (‖S u‖ * ‖S v‖) = (|u - v| * ‖S v‖) * ‖S u‖ := by ring
  have h3 : (|u - v| * ‖S v‖) * ‖S u‖ ≤ (1 / 2) * ‖S u‖ :=
    mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  rw [h2] at hbound
  linarith

/-- **Continuity of a resolvent family.**  The identity alone forces it. -/
theorem continuousAt (hS : IsResolventFamilyOn S s) (hs : IsOpen s) (hv : v ∈ s) :
    ContinuousAt S v := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hs v hv
  set M := ‖S v‖ with hM
  have hMnn : 0 ≤ M := norm_nonneg _
  refine ⟨min δ₀ (min (1 / (2 * (M + 1))) (ε / (2 * M ^ 2 + 1))), ?_, ?_⟩
  · have h1 : (0:ℝ) < 1 / (2 * (M + 1)) := by positivity
    have h2 : (0:ℝ) < ε / (2 * M ^ 2 + 1) := by positivity
    exact lt_min hδ₀ (lt_min h1 h2)
  · intro u hu
    have hdist : |u - v| < min δ₀ (min (1 / (2 * (M + 1))) (ε / (2 * M ^ 2 + 1))) := by
      rwa [Real.dist_eq] at hu
    have hus : u ∈ s := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_lt_of_le hdist (min_le_left _ _)
    have hd1 : |u - v| < 1 / (2 * (M + 1)) :=
      lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_left _ _))
    have hd2 : |u - v| < ε / (2 * M ^ 2 + 1) :=
      lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_right _ _))
    have hsmall : |u - v| * M ≤ 1 / 2 := by
      have hpos : (0:ℝ) < 2 * (M + 1) := by positivity
      have := mul_le_mul_of_nonneg_right hd1.le hMnn
      calc |u - v| * M ≤ 1 / (2 * (M + 1)) * M := this
        _ ≤ 1 / 2 := by
            rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hpos (by norm_num : (0:ℝ) < 2)]
            nlinarith
    have hnorm : ‖S u‖ ≤ 2 * M := hS.norm_le_two_mul hus hv hsmall
    have hbound := hS.norm_sub_le hus hv
    have hchain : ‖S u - S v‖ ≤ |u - v| * (2 * M ^ 2) := by
      refine le_trans hbound ?_
      have : ‖S u‖ * ‖S v‖ ≤ (2 * M) * M := by
        exact mul_le_mul_of_nonneg_right hnorm hMnn
      have h2 : (2 * M) * M = 2 * M ^ 2 := by ring
      rw [h2] at this
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
    have hfinal : |u - v| * (2 * M ^ 2) < ε := by
      have hden : (0:ℝ) < 2 * M ^ 2 + 1 := by positivity
      have := mul_lt_mul_of_pos_right hd2 (by positivity : (0:ℝ) < 2 * M ^ 2 + 1)
      rw [div_mul_cancel₀ _ (ne_of_gt hden)] at this
      nlinarith [abs_nonneg (u - v)]
    rw [dist_eq_norm]
    linarith

/-- **The derivative of a resolvent family is its square.** -/
theorem hasDerivAt (hS : IsResolventFamilyOn S s) (hs : IsOpen s) (hv : v ∈ s) :
    HasDerivAt S (S v * S v) v := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hcont : Tendsto S (𝓝[≠] v) (𝓝 (S v)) :=
    (hS.continuousAt hs hv).tendsto.mono_left nhdsWithin_le_nhds
  have hmul : Tendsto (fun u => S u * S v) (𝓝[≠] v) (𝓝 (S v * S v)) :=
    hcont.mul tendsto_const_nhds
  refine hmul.congr' ?_
  have hmem : ∀ᶠ u in 𝓝[≠] v, u ∈ s :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hs.mem_nhds hv)
  filter_upwards [hmem, self_mem_nhdsWithin] with u hus hune
  have hne : u - v ≠ 0 := sub_ne_zero.mpr hune
  rw [slope_def_module, hS u hus v hv, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- The `(n+1)`-st power of a resolvent family differentiates to `(n+1)` times the next power. -/
theorem hasDerivAt_pow (hS : IsResolventFamilyOn S s) (hs : IsOpen s) (hv : v ∈ s) :
    ∀ n : ℕ, HasDerivAt (fun u => S u ^ (n + 1)) (((n : ℝ) + 1) • S v ^ (n + 2)) v := by
  intro n
  induction n with
  | zero =>
      have h := hS.hasDerivAt hs hv
      have hfun : (fun u => S u ^ (0 + 1)) = S := by
        funext u; simp
      rw [hfun]
      convert h using 1
      simp [pow_two]
  | succ k ih =>
      have hbase := hS.hasDerivAt hs hv
      have hprod : HasDerivAt (fun u => S u ^ (k + 1) * S u)
          (((k : ℝ) + 1) • S v ^ (k + 2) * S v + S v ^ (k + 1) * (S v * S v)) v := ih.mul hbase
      have hfun : (fun u => S u ^ (k + 1) * S u) = fun u => S u ^ (k + 1 + 1) := by
        funext u
        exact (pow_succ (S u) (k + 1)).symm
      rw [hfun] at hprod
      have hexp : S v ^ (k + 2) * S v = S v ^ (k + 1 + 2) := by
        rw [← pow_succ]
      have hexp2 : S v ^ (k + 1) * (S v * S v) = S v ^ (k + 1 + 2) := by
        rw [← mul_assoc, ← pow_succ, ← pow_succ]
      convert hprod using 1
      rw [smul_mul_assoc, hexp, hexp2]
      push_cast
      module

/-- **The `n`-th shift jet of a resolvent family.**  The jet `n! S^{n+1}` differentiates to the
next jet `(n+1)! S^{n+2}`, so the `n`-th derivative of the family is exactly `n! S^{n+1}`. -/
theorem hasDerivAt_jet (hS : IsResolventFamilyOn S s) (hs : IsOpen s) (hv : v ∈ s) (n : ℕ) :
    HasDerivAt (fun u => ((n ! : ℝ)) • S u ^ (n + 1))
      (((n + 1)! : ℝ) • S v ^ (n + 2)) v := by
  have h := (hS.hasDerivAt_pow hs hv n).const_smul ((n ! : ℝ))
  have hval : ((n ! : ℝ)) • (((n : ℝ) + 1) • S v ^ (n + 2)) = ((n + 1)! : ℝ) • S v ^ (n + 2) := by
    rw [smul_smul, Nat.factorial_succ]
    congr 1
    push_cast
    ring
  rwa [hval] at h

end IsResolventFamilyOn

end GaloisForLFunctions.HTGeometry

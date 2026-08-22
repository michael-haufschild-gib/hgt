import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Local existence for an analytic ordinary differential equation, with a uniform radius
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set Filter
open scoped Topology
open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- One Picard step: a primitive of `z ↦ Φ z (F z)` on `ball z₁ δ`, normalized to `w₁` at `z₁`. -/
noncomputable def picardStep (Φ : ℂ → E → E) (z₁ : ℂ) (w₁ : E) (δ : ℝ) (F : ℂ → E) : ℂ → E :=
  if h : Complex.IsExactOn (fun z => Φ z (F z)) (ball z₁ δ) then
    (h.with_val_at z₁ w₁).choose
  else fun _ => w₁

theorem picardStep_apply_self {Φ : ℂ → E → E} {z₁ : ℂ} {w₁ : E} {δ : ℝ} {F : ℂ → E}
    (h : Complex.IsExactOn (fun z => Φ z (F z)) (ball z₁ δ)) :
    picardStep Φ z₁ w₁ δ F z₁ = w₁ := by
  rw [picardStep, dif_pos h]
  exact (h.with_val_at z₁ w₁).choose_spec.1

theorem hasDerivAt_picardStep {Φ : ℂ → E → E} {z₁ : ℂ} {w₁ : E} {δ : ℝ} {F : ℂ → E}
    (h : Complex.IsExactOn (fun z => Φ z (F z)) (ball z₁ δ)) {z : ℂ} (hz : z ∈ ball z₁ δ) :
    HasDerivAt (picardStep Φ z₁ w₁ δ F) (Φ z (F z)) z := by
  rw [picardStep, dif_pos h]
  exact (h.with_val_at z₁ w₁).choose_spec.2 z hz

/-- The Picard iterates of the analytic initial value problem. -/
noncomputable def picardIter (Φ : ℂ → E → E) (z₁ : ℂ) (w₁ : E) (δ : ℝ) : ℕ → (ℂ → E)
  | 0 => fun _ => w₁
  | (k + 1) => picardStep Φ z₁ w₁ δ (picardIter Φ z₁ w₁ δ k)

section

variable {Φ : ℂ → E → E} {z₁ : ℂ} {w₁ : E} {ρ ρ' M L δ : ℝ}

/-- The exactness input for one Picard step. -/
theorem isExactOn_of_differentiableOn (hδ0 : 0 < δ) (hδρ : δ ≤ ρ)
    (hΦdiff : DifferentiableOn ℂ (fun p : ℂ × E => Φ p.1 p.2) (ball z₁ ρ ×ˢ ball w₁ ρ'))
    {F : ℂ → E} (hF : DifferentiableOn ℂ F (ball z₁ δ))
    (hFmem : ∀ z ∈ ball z₁ δ, F z ∈ ball w₁ ρ') :
    Complex.IsExactOn (fun z => Φ z (F z)) (ball z₁ δ) := by
  refine DifferentiableOn.isExactOn_ball ?_
  have hmap : MapsTo (fun z : ℂ => (z, F z)) (ball z₁ δ) (ball z₁ ρ ×ˢ ball w₁ ρ') := by
    intro z hz
    exact ⟨ball_subset_ball hδρ hz, hFmem z hz⟩
  have hpair : DifferentiableOn ℂ (fun z : ℂ => (z, F z)) (ball z₁ δ) :=
    differentiableOn_id.prodMk hF
  exact hΦdiff.comp hpair hmap

/-- Every Picard iterate is analytic, fixes the initial value, and stays inside the target ball. -/
theorem picardIter_spec (hδ0 : 0 < δ) (hδρ : δ ≤ ρ) (hM0 : 0 ≤ M) (hMδ : δ * M < ρ')
    (hΦdiff : DifferentiableOn ℂ (fun p : ℂ × E => Φ p.1 p.2) (ball z₁ ρ ×ˢ ball w₁ ρ'))
    (hΦbound : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball w₁ ρ', ‖Φ z w‖ ≤ M) :
    ∀ k : ℕ, DifferentiableOn ℂ (picardIter Φ z₁ w₁ δ k) (ball z₁ δ) ∧
      picardIter Φ z₁ w₁ δ k z₁ = w₁ ∧
      ∀ z ∈ ball z₁ δ, ‖picardIter Φ z₁ w₁ δ k z - w₁‖ ≤ δ * M := by
  have hρ'0 : 0 < ρ' := lt_of_le_of_lt (mul_nonneg (le_of_lt hδ0) hM0) hMδ
  intro k
  induction k with
  | zero =>
      refine ⟨differentiableOn_const w₁, rfl, fun z _ => ?_⟩
      simp only [picardIter, sub_self, norm_zero]
      exact mul_nonneg (le_of_lt hδ0) hM0
  | succ k ih =>
      obtain ⟨hdiff, hval, hbnd⟩ := ih
      have hmem : ∀ z ∈ ball z₁ δ, picardIter Φ z₁ w₁ δ k z ∈ ball w₁ ρ' := by
        intro z hz
        rw [mem_ball, dist_eq_norm]
        exact lt_of_le_of_lt (hbnd z hz) hMδ
      have hex := isExactOn_of_differentiableOn hδ0 hδρ hΦdiff hdiff hmem
      have hderiv : ∀ z ∈ ball z₁ δ,
          HasDerivAt (picardIter Φ z₁ w₁ δ (k + 1)) (Φ z (picardIter Φ z₁ w₁ δ k z)) z := by
        intro z hz
        exact hasDerivAt_picardStep hex hz
      refine ⟨fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt,
        picardStep_apply_self hex, fun z hz => ?_⟩
      have hbound : ∀ x ∈ ball z₁ δ, ‖Φ x (picardIter Φ z₁ w₁ δ k x)‖ ≤ M := by
        intro x hx
        exact hΦbound x (ball_subset_ball hδρ hx) _ (hmem x hx)
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := picardIter Φ z₁ w₁ δ (k + 1))
        (f' := fun x => Φ x (picardIter Φ z₁ w₁ δ k x))
        (fun x hx => (hderiv x hx).hasDerivWithinAt) hbound (convex_ball z₁ δ)
        (mem_ball_self hδ0) hz
      have hval1 : picardIter Φ z₁ w₁ δ (k + 1) z₁ = w₁ := picardStep_apply_self hex
      rw [hval1] at hmvt
      refine le_trans hmvt ?_
      have hzd : ‖z - z₁‖ ≤ δ := by
        have := mem_ball.mp hz
        rw [dist_eq_norm] at this
        linarith
      calc M * ‖z - z₁‖ ≤ M * δ := by
            exact mul_le_mul_of_nonneg_left hzd hM0
        _ = δ * M := by ring

theorem isExactOn_picardIter (hδ0 : 0 < δ) (hδρ : δ ≤ ρ) (hM0 : 0 ≤ M) (hMδ : δ * M < ρ')
    (hΦdiff : DifferentiableOn ℂ (fun p : ℂ × E => Φ p.1 p.2) (ball z₁ ρ ×ˢ ball w₁ ρ'))
    (hΦbound : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball w₁ ρ', ‖Φ z w‖ ≤ M) (k : ℕ) :
    Complex.IsExactOn (fun z => Φ z (picardIter Φ z₁ w₁ δ k z)) (ball z₁ δ) := by
  obtain ⟨hdiff, _, hbnd⟩ := picardIter_spec hδ0 hδρ hM0 hMδ hΦdiff hΦbound k
  refine isExactOn_of_differentiableOn hδ0 hδρ hΦdiff hdiff fun z hz => ?_
  rw [mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt (hbnd z hz) hMδ

theorem picardIter_mem (hδ0 : 0 < δ) (hδρ : δ ≤ ρ) (hM0 : 0 ≤ M) (hMδ : δ * M < ρ')
    (hΦdiff : DifferentiableOn ℂ (fun p : ℂ × E => Φ p.1 p.2) (ball z₁ ρ ×ˢ ball w₁ ρ'))
    (hΦbound : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball w₁ ρ', ‖Φ z w‖ ≤ M) (k : ℕ) {z : ℂ}
    (hz : z ∈ ball z₁ δ) : picardIter Φ z₁ w₁ δ k z ∈ ball w₁ ρ' := by
  obtain ⟨_, _, hbnd⟩ := picardIter_spec hδ0 hδρ hM0 hMδ hΦdiff hΦbound k
  rw [mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt (hbnd z hz) hMδ

theorem hasDerivAt_picardIter_succ (hδ0 : 0 < δ) (hδρ : δ ≤ ρ) (hM0 : 0 ≤ M) (hMδ : δ * M < ρ')
    (hΦdiff : DifferentiableOn ℂ (fun p : ℂ × E => Φ p.1 p.2) (ball z₁ ρ ×ˢ ball w₁ ρ'))
    (hΦbound : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball w₁ ρ', ‖Φ z w‖ ≤ M) (k : ℕ) {z : ℂ}
    (hz : z ∈ ball z₁ δ) :
    HasDerivAt (picardIter Φ z₁ w₁ δ (k + 1)) (Φ z (picardIter Φ z₁ w₁ δ k z)) z :=
  hasDerivAt_picardStep (isExactOn_picardIter hδ0 hδρ hM0 hMδ hΦdiff hΦbound k) hz

/-- **The geometric contraction estimate.** -/
theorem picardIter_succ_sub_le (hδ0 : 0 < δ) (hδρ : δ ≤ ρ) (hM0 : 0 ≤ M) (hL0 : 0 ≤ L)
    (hMδ : δ * M < ρ')
    (hΦdiff : DifferentiableOn ℂ (fun p : ℂ × E => Φ p.1 p.2) (ball z₁ ρ ×ˢ ball w₁ ρ'))
    (hΦbound : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball w₁ ρ', ‖Φ z w‖ ≤ M)
    (hΦlip : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball w₁ ρ', ∀ v ∈ ball w₁ ρ',
      ‖Φ z w - Φ z v‖ ≤ L * ‖w - v‖) :
    ∀ k : ℕ, ∀ z ∈ ball z₁ δ,
      ‖picardIter Φ z₁ w₁ δ (k + 1) z - picardIter Φ z₁ w₁ δ k z‖ ≤ (δ * L) ^ k * (δ * M) := by
  intro k
  induction k with
  | zero =>
      intro z hz
      obtain ⟨_, _, hbnd⟩ := picardIter_spec hδ0 hδρ hM0 hMδ hΦdiff hΦbound 1
      have h0 : picardIter Φ z₁ w₁ δ 0 z = w₁ := rfl
      rw [h0]
      simpa using hbnd z hz
  | succ k ih =>
      intro z hz
      have hderiv : ∀ x ∈ ball z₁ δ,
          HasDerivAt (fun t => picardIter Φ z₁ w₁ δ (k + 2) t - picardIter Φ z₁ w₁ δ (k + 1) t)
            (Φ x (picardIter Φ z₁ w₁ δ (k + 1) x) - Φ x (picardIter Φ z₁ w₁ δ k x)) x := by
        intro x hx
        exact (hasDerivAt_picardIter_succ hδ0 hδρ hM0 hMδ hΦdiff hΦbound (k + 1) hx).sub
          (hasDerivAt_picardIter_succ hδ0 hδρ hM0 hMδ hΦdiff hΦbound k hx)
      have hbound : ∀ x ∈ ball z₁ δ,
          ‖Φ x (picardIter Φ z₁ w₁ δ (k + 1) x) - Φ x (picardIter Φ z₁ w₁ δ k x)‖
            ≤ L * ((δ * L) ^ k * (δ * M)) := by
        intro x hx
        refine le_trans (hΦlip x (ball_subset_ball hδρ hx) _
          (picardIter_mem hδ0 hδρ hM0 hMδ hΦdiff hΦbound (k + 1) hx) _
          (picardIter_mem hδ0 hδρ hM0 hMδ hΦdiff hΦbound k hx)) ?_
        exact mul_le_mul_of_nonneg_left (ih x hx) hL0
      have hv1 : picardIter Φ z₁ w₁ δ (k + 2) z₁ = w₁ :=
        (picardIter_spec hδ0 hδρ hM0 hMδ hΦdiff hΦbound (k + 2)).2.1
      have hv2 : picardIter Φ z₁ w₁ δ (k + 1) z₁ = w₁ :=
        (picardIter_spec hδ0 hδρ hM0 hMδ hΦdiff hΦbound (k + 1)).2.1
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun t => picardIter Φ z₁ w₁ δ (k + 2) t - picardIter Φ z₁ w₁ δ (k + 1) t)
        (f' := fun x => Φ x (picardIter Φ z₁ w₁ δ (k + 1) x) - Φ x (picardIter Φ z₁ w₁ δ k x))
        (fun x hx => (hderiv x hx).hasDerivWithinAt) hbound (convex_ball z₁ δ)
        (mem_ball_self hδ0) hz
      rw [hv1, hv2, sub_self, sub_zero] at hmvt
      have hzd : ‖z - z₁‖ ≤ δ := by
        have := mem_ball.mp hz
        rw [dist_eq_norm] at this
        linarith
      have hnn : (0 : ℝ) ≤ L * ((δ * L) ^ k * (δ * M)) := by
        have h1 : (0 : ℝ) ≤ (δ * L) ^ k := pow_nonneg (mul_nonneg (le_of_lt hδ0) hL0) k
        have h2 : (0 : ℝ) ≤ δ * M := mul_nonneg (le_of_lt hδ0) hM0
        positivity
      refine le_trans hmvt ?_
      calc L * ((δ * L) ^ k * (δ * M)) * ‖z - z₁‖
          ≤ L * ((δ * L) ^ k * (δ * M)) * δ := mul_le_mul_of_nonneg_left hzd hnn
        _ = (δ * L) ^ (k + 1) * (δ * M) := by ring

/-! ## The limit of the Picard iterates -/

/-- The limit of the Picard iterates. -/
noncomputable def picardLimit (Φ : ℂ → E → E) (z₁ : ℂ) (w₁ : E) (δ : ℝ) (z : ℂ) : E :=
  w₁ + ∑' k : ℕ, (picardIter Φ z₁ w₁ δ (k + 1) z - picardIter Φ z₁ w₁ δ k z)

theorem tendstoUniformlyOn_picardIter (hδ0 : 0 < δ) (hδρ : δ ≤ ρ) (hM0 : 0 ≤ M) (hL0 : 0 ≤ L)
    (hMδ : δ * M < ρ') (hLδ : δ * L < 1)
    (hΦdiff : DifferentiableOn ℂ (fun p : ℂ × E => Φ p.1 p.2) (ball z₁ ρ ×ˢ ball w₁ ρ'))
    (hΦbound : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball w₁ ρ', ‖Φ z w‖ ≤ M)
    (hΦlip : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball w₁ ρ', ∀ v ∈ ball w₁ ρ',
      ‖Φ z w - Φ z v‖ ≤ L * ‖w - v‖) :
    TendstoUniformlyOn (fun N => picardIter Φ z₁ w₁ δ N) (picardLimit Φ z₁ w₁ δ)
      atTop (ball z₁ δ) := by
  have hnn : (0 : ℝ) ≤ δ * L := mul_nonneg (le_of_lt hδ0) hL0
  have hu : Summable (fun k : ℕ => (δ * L) ^ k * (δ * M)) :=
    (summable_geometric_of_lt_one hnn hLδ).mul_right _
  have hbnd := picardIter_succ_sub_le hδ0 hδρ hM0 hL0 hMδ hΦdiff hΦbound hΦlip
  have hfin := tendstoUniformlyOn_tsum (u := fun k : ℕ => (δ * L) ^ k * (δ * M))
    (f := fun k z => picardIter Φ z₁ w₁ δ (k + 1) z - picardIter Φ z₁ w₁ δ k z) hu
    (s := ball z₁ δ) (fun k z hz => hbnd k z hz)
  have hnat : TendstoUniformlyOn
      (fun N : ℕ => fun z => ∑ k ∈ Finset.range N,
        (picardIter Φ z₁ w₁ δ (k + 1) z - picardIter Φ z₁ w₁ δ k z))
      (fun z => ∑' k : ℕ, (picardIter Φ z₁ w₁ δ (k + 1) z - picardIter Φ z₁ w₁ δ k z))
      atTop (ball z₁ δ) := by
    intro u hu'
    exact Filter.tendsto_finset_range.eventually (hfin u hu')
  have hpart : ∀ (N : ℕ) (z : ℂ), (∑ k ∈ Finset.range N,
      (picardIter Φ z₁ w₁ δ (k + 1) z - picardIter Φ z₁ w₁ δ k z))
      = picardIter Φ z₁ w₁ δ N z - w₁ := by
    intro N z
    rw [Finset.sum_range_sub (fun k => picardIter Φ z₁ w₁ δ k z) N]
    rfl
  rw [Metric.tendstoUniformlyOn_iff] at hnat ⊢
  intro ε hε
  filter_upwards [hnat ε hε] with N hN z hz
  have h := hN z hz
  rw [hpart N z] at h
  rw [dist_eq_norm] at h ⊢
  rw [picardLimit]
  have hrw : (w₁ + ∑' k : ℕ,
      (picardIter Φ z₁ w₁ δ (k + 1) z - picardIter Φ z₁ w₁ δ k z))
      - picardIter Φ z₁ w₁ δ N z
      = (∑' k : ℕ, (picardIter Φ z₁ w₁ δ (k + 1) z - picardIter Φ z₁ w₁ δ k z))
        - (picardIter Φ z₁ w₁ δ N z - w₁) := by abel
  rw [hrw]
  exact h

/-! ## The local existence theorem -/

/-- **Local existence for an analytic ODE, with a radius depending only on the polydisc data.**
If the vector field `Φ` is holomorphic on `ball z₁ ρ ×ˢ ball w₁ ρ'`, bounded there by `M`, and
Lipschitz in the second variable with constant `L`, then for every `δ ≤ ρ` with `δ M < ρ'` and
`δ L < 1` the initial value problem `F' = Φ(·, F)`, `F z₁ = w₁` has a solution on `ball z₁ δ`
taking values in `ball w₁ ρ'`.  The radius `δ` depends only on `(ρ, ρ', M, L)`, never on the
particular initial point inside the polydisc. -/
theorem exists_analytic_ode_solution (hδ0 : 0 < δ) (hδρ : δ ≤ ρ) (hM0 : 0 ≤ M) (hL0 : 0 ≤ L)
    (hMδ : δ * M < ρ') (hLδ : δ * L < 1)
    (hΦdiff : DifferentiableOn ℂ (fun p : ℂ × E => Φ p.1 p.2) (ball z₁ ρ ×ˢ ball w₁ ρ'))
    (hΦbound : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball w₁ ρ', ‖Φ z w‖ ≤ M)
    (hΦlip : ∀ z ∈ ball z₁ ρ, ∀ w ∈ ball w₁ ρ', ∀ v ∈ ball w₁ ρ',
      ‖Φ z w - Φ z v‖ ≤ L * ‖w - v‖) :
    ∃ F : ℂ → E, F z₁ = w₁ ∧ (∀ z ∈ ball z₁ δ, F z ∈ ball w₁ ρ') ∧
      (∀ z ∈ ball z₁ δ, HasDerivAt F (Φ z (F z)) z) := by
  have hUnif := tendstoUniformlyOn_picardIter hδ0 hδρ hM0 hL0 hMδ hLδ hΦdiff hΦbound hΦlip
  have hdiffEv : ∀ᶠ N : ℕ in atTop,
      DifferentiableOn ℂ (picardIter Φ z₁ w₁ δ N) (ball z₁ δ) := by
    filter_upwards with N
    exact (picardIter_spec hδ0 hδρ hM0 hMδ hΦdiff hΦbound N).1
  have hLim : DifferentiableOn ℂ (picardLimit Φ z₁ w₁ δ) (ball z₁ δ) :=
    hUnif.tendstoLocallyUniformlyOn.differentiableOn hdiffEv isOpen_ball
  have hval : picardLimit Φ z₁ w₁ δ z₁ = w₁ := by
    rw [picardLimit]
    have hz : ∀ k : ℕ,
        picardIter Φ z₁ w₁ δ (k + 1) z₁ - picardIter Φ z₁ w₁ δ k z₁ = 0 := by
      intro k
      rw [(picardIter_spec hδ0 hδρ hM0 hMδ hΦdiff hΦbound (k + 1)).2.1,
        (picardIter_spec hδ0 hδρ hM0 hMδ hΦdiff hΦbound k).2.1, sub_self]
    rw [tsum_congr hz, tsum_zero, add_zero]
  have hmem : ∀ z ∈ ball z₁ δ, picardLimit Φ z₁ w₁ δ z ∈ ball w₁ ρ' := by
    intro z hz
    have hpt := hUnif.tendsto_at hz
    have hnorm : Filter.Tendsto (fun N : ℕ => ‖picardIter Φ z₁ w₁ δ N z - w₁‖) atTop
        (𝓝 ‖picardLimit Φ z₁ w₁ δ z - w₁‖) :=
      (continuous_norm.tendsto _).comp (hpt.sub tendsto_const_nhds)
    have hle : ‖picardLimit Φ z₁ w₁ δ z - w₁‖ ≤ δ * M := by
      refine le_of_tendsto hnorm ?_
      filter_upwards with N
      exact (picardIter_spec hδ0 hδρ hM0 hMδ hΦdiff hΦbound N).2.2 z hz
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hle hMδ
  refine ⟨picardLimit Φ z₁ w₁ δ, hval, hmem, fun z hz => ?_⟩
  have hderivUnif := hUnif.tendstoLocallyUniformlyOn.deriv hdiffEv isOpen_ball
  have hpt1 : Filter.Tendsto (fun N : ℕ => deriv (picardIter Φ z₁ w₁ δ N) z) atTop
      (𝓝 (deriv (picardLimit Φ z₁ w₁ δ) z)) := hderivUnif.tendsto_at hz
  have hpt2 : Filter.Tendsto (fun N : ℕ => deriv (picardIter Φ z₁ w₁ δ (N + 1)) z) atTop
      (𝓝 (deriv (picardLimit Φ z₁ w₁ δ) z)) := hpt1.comp (Filter.tendsto_add_atTop_nat 1)
  have hstep : ∀ N : ℕ, deriv (picardIter Φ z₁ w₁ δ (N + 1)) z
      = Φ z (picardIter Φ z₁ w₁ δ N z) := fun N =>
    (hasDerivAt_picardIter_succ hδ0 hδρ hM0 hMδ hΦdiff hΦbound N hz).deriv
  have hpt3 : Filter.Tendsto (fun N : ℕ => Φ z (picardIter Φ z₁ w₁ δ N z)) atTop
      (𝓝 (deriv (picardLimit Φ z₁ w₁ δ) z)) := by
    refine hpt2.congr fun N => ?_
    exact hstep N
  have hpt4 : Filter.Tendsto (fun N : ℕ => Φ z (picardIter Φ z₁ w₁ δ N z)) atTop
      (𝓝 (Φ z (picardLimit Φ z₁ w₁ δ z))) := by
    have hnormto : Filter.Tendsto
        (fun N : ℕ => ‖Φ z (picardIter Φ z₁ w₁ δ N z) - Φ z (picardLimit Φ z₁ w₁ δ z)‖)
        atTop (𝓝 0) := by
      have hsq : Filter.Tendsto
          (fun N : ℕ => L * ‖picardIter Φ z₁ w₁ δ N z - picardLimit Φ z₁ w₁ δ z‖)
          atTop (𝓝 0) := by
        have hpt := hUnif.tendsto_at hz
        have hz0 : Filter.Tendsto
            (fun N : ℕ => ‖picardIter Φ z₁ w₁ δ N z - picardLimit Φ z₁ w₁ δ z‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.mp hpt
        simpa using hz0.const_mul L
      refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hsq
      exact hΦlip z (ball_subset_ball hδρ hz) _
        (picardIter_mem hδ0 hδρ hM0 hMδ hΦdiff hΦbound N hz) _ (hmem z hz)
    have := tendsto_iff_norm_sub_tendsto_zero.mpr hnormto
    exact this
  have hderivEq : deriv (picardLimit Φ z₁ w₁ δ) z = Φ z (picardLimit Φ z₁ w₁ δ z) :=
    tendsto_nhds_unique hpt3 hpt4
  have hdiffAt : DifferentiableAt ℂ (picardLimit Φ z₁ w₁ δ) z :=
    hLim.differentiableAt (isOpen_ball.mem_nhds hz)
  rw [← hderivEq]
  exact hdiffAt.hasDerivAt

/-! ## Uniqueness -/

/-- **Local uniqueness for an analytic ODE.**  Two solutions with the same value at the centre,
both staying inside a ball on which the field is Lipschitz with `δ L < 1`, coincide. -/
theorem ode_solution_unique {Φ : ℂ → E → E} {z₁ : ℂ} {w₁ : E} {ρ' L δ : ℝ}
    (hδ0 : 0 < δ) (hLδ : δ * L < 1) (hL0 : 0 ≤ L) (hρ' : 0 ≤ ρ')
    (hΦlip : ∀ z ∈ ball z₁ δ, ∀ w ∈ ball w₁ ρ', ∀ v ∈ ball w₁ ρ',
      ‖Φ z w - Φ z v‖ ≤ L * ‖w - v‖)
    {F G : ℂ → E} (hF : ∀ z ∈ ball z₁ δ, HasDerivAt F (Φ z (F z)) z)
    (hG : ∀ z ∈ ball z₁ δ, HasDerivAt G (Φ z (G z)) z)
    (hFmem : ∀ z ∈ ball z₁ δ, F z ∈ ball w₁ ρ') (hGmem : ∀ z ∈ ball z₁ δ, G z ∈ ball w₁ ρ')
    (hFG : F z₁ = G z₁) : ∀ z ∈ ball z₁ δ, F z = G z := by
  have hstep : ∀ B : ℝ, 0 ≤ B → (∀ z ∈ ball z₁ δ, ‖F z - G z‖ ≤ B) →
      ∀ z ∈ ball z₁ δ, ‖F z - G z‖ ≤ (δ * L) * B := by
    intro B hB0 hbnd z hz
    have hderiv : ∀ x ∈ ball z₁ δ,
        HasDerivWithinAt (fun t => F t - G t) (Φ x (F x) - Φ x (G x)) (ball z₁ δ) x :=
      fun x hx => ((hF x hx).sub (hG x hx)).hasDerivWithinAt
    have hbound : ∀ x ∈ ball z₁ δ, ‖Φ x (F x) - Φ x (G x)‖ ≤ L * B := by
      intro x hx
      refine le_trans (hΦlip x hx _ (hFmem x hx) _ (hGmem x hx)) ?_
      exact mul_le_mul_of_nonneg_left (hbnd x hx) hL0
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => F t - G t) (f' := fun x => Φ x (F x) - Φ x (G x))
      hderiv hbound (convex_ball z₁ δ) (mem_ball_self hδ0) hz
    rw [hFG, sub_self, sub_zero] at hmvt
    have hzd : ‖z - z₁‖ ≤ δ := by
      have := mem_ball.mp hz
      rw [dist_eq_norm] at this
      linarith
    refine le_trans hmvt ?_
    calc L * B * ‖z - z₁‖ ≤ L * B * δ :=
          mul_le_mul_of_nonneg_left hzd (mul_nonneg hL0 hB0)
      _ = (δ * L) * B := by ring
  have hinit : ∀ z ∈ ball z₁ δ, ‖F z - G z‖ ≤ 2 * ρ' := by
    intro z hz
    have h1 : ‖F z - w₁‖ ≤ ρ' := le_of_lt (by
      have := mem_ball.mp (hFmem z hz)
      rwa [dist_eq_norm] at this)
    have h2 : ‖G z - w₁‖ ≤ ρ' := le_of_lt (by
      have := mem_ball.mp (hGmem z hz)
      rwa [dist_eq_norm] at this)
    calc ‖F z - G z‖ = ‖(F z - w₁) - (G z - w₁)‖ := by
          congr 1
          abel
      _ ≤ ‖F z - w₁‖ + ‖G z - w₁‖ := norm_sub_le _ _
      _ ≤ 2 * ρ' := by linarith
  have hiter : ∀ k : ℕ, ∀ z ∈ ball z₁ δ, ‖F z - G z‖ ≤ (δ * L) ^ k * (2 * ρ') := by
    intro k
    induction k with
    | zero => simpa using hinit
    | succ k ih =>
        intro z hz
        have := hstep ((δ * L) ^ k * (2 * ρ'))
          (by positivity) ih z hz
        calc ‖F z - G z‖ ≤ (δ * L) * ((δ * L) ^ k * (2 * ρ')) := this
          _ = (δ * L) ^ (k + 1) * (2 * ρ') := by ring
  intro z hz
  have hlim : Filter.Tendsto (fun k : ℕ => (δ * L) ^ k * (2 * ρ')) atTop (𝓝 0) := by
    have hgeo : Filter.Tendsto (fun k : ℕ => (δ * L) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg (le_of_lt hδ0) hL0) hLδ
    simpa using hgeo.mul_const (2 * ρ')
  have hzero : ‖F z - G z‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall fun k => hiter k z hz)
  have : F z - G z = 0 := by
    have := norm_nonneg (F z - G z)
    have hnz : ‖F z - G z‖ = 0 := le_antisymm hzero this
    exact norm_eq_zero.mp hnz
  exact sub_eq_zero.mp this

end

end GaloisForLFunctions.HTGeometry

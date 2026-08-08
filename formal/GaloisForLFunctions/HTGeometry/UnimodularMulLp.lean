import Mathlib
import GaloisForLFunctions.HTGeometry.LechnerPairMultiplier

/-!
# Multiplication by a unimodular class is a linear isometry of `L^p`

Pointwise multiplication by an almost-everywhere unimodular function preserves the modulus of every
value, hence every `L^p` seminorm.  Bundling that observation gives a linear isometry of `L^p`, and
since the conjugate of a unimodular class inverts it, the isometry is surjective: an isometric
equivalence.

This is the packaging the Lechner intertwiner needs: its multiplier is unimodular at every particle
number, so multiplication by it is a unitary of the one-particle-number space.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The `L^p` seminorm is unchanged by multiplication by a unimodular class. -/
theorem eLpNorm_aeEqFun_mul {g : α →ₘ[μ] ℂ} (hg : ∀ᵐ x ∂μ, ‖g x‖ = 1) (f : α →ₘ[μ] ℂ) :
    eLpNorm (g * f) p μ = eLpNorm f p μ := by
  rw [eLpNorm_congr_ae (AEEqFun.coeFn_mul g f)]
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [hg] with x hx
  rw [Pi.mul_apply, norm_mul, hx, one_mul]

/-- Multiplication by a unimodular class as a map of `L^p`. -/
noncomputable def mulLp {g : α →ₘ[μ] ℂ} (hg : ∀ᵐ x ∂μ, ‖g x‖ = 1) (f : Lp ℂ p μ) : Lp ℂ p μ :=
  ⟨g * (f : α →ₘ[μ] ℂ), by
    rw [Lp.mem_Lp_iff_eLpNorm_lt_top, eLpNorm_aeEqFun_mul hg]
    exact Lp.eLpNorm_lt_top f⟩

omit [Fact (1 ≤ p)] in
@[simp]
theorem coe_mulLp {g : α →ₘ[μ] ℂ} (hg : ∀ᵐ x ∂μ, ‖g x‖ = 1) (f : Lp ℂ p μ) :
    ((mulLp hg f : Lp ℂ p μ) : α →ₘ[μ] ℂ) = g * (f : α →ₘ[μ] ℂ) := rfl

omit [Fact (1 ≤ p)] in
theorem norm_mulLp {g : α →ₘ[μ] ℂ} (hg : ∀ᵐ x ∂μ, ‖g x‖ = 1) (f : Lp ℂ p μ) :
    ‖mulLp hg f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, coe_mulLp, eLpNorm_aeEqFun_mul hg]

theorem aeEqFun_mul_add (g f₁ f₂ : α →ₘ[μ] ℂ) : g * (f₁ + f₂) = g * f₁ + g * f₂ := by
  refine AEEqFun.ext ?_
  filter_upwards [AEEqFun.coeFn_mul g (f₁ + f₂), AEEqFun.coeFn_add f₁ f₂,
    AEEqFun.coeFn_add (g * f₁) (g * f₂), AEEqFun.coeFn_mul g f₁, AEEqFun.coeFn_mul g f₂]
    with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.mul_apply, Pi.add_apply]
  ring

theorem aeEqFun_mul_smul (g f : α →ₘ[μ] ℂ) (c : ℂ) : g * (c • f) = c • (g * f) := by
  refine AEEqFun.ext ?_
  filter_upwards [AEEqFun.coeFn_mul g (c • f), AEEqFun.coeFn_smul c f,
    AEEqFun.coeFn_smul c (g * f), AEEqFun.coeFn_mul g f] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fact (1 ≤ p)] in
theorem mulLp_add {g : α →ₘ[μ] ℂ} (hg : ∀ᵐ x ∂μ, ‖g x‖ = 1) (f₁ f₂ : Lp ℂ p μ) :
    mulLp hg (f₁ + f₂) = mulLp hg f₁ + mulLp hg f₂ := by
  refine Subtype.ext ?_
  rw [coe_mulLp]
  change g * ((f₁ : α →ₘ[μ] ℂ) + (f₂ : α →ₘ[μ] ℂ)) = _
  rw [aeEqFun_mul_add]
  rfl

omit [Fact (1 ≤ p)] in
theorem mulLp_smul {g : α →ₘ[μ] ℂ} (hg : ∀ᵐ x ∂μ, ‖g x‖ = 1) (c : ℂ) (f : Lp ℂ p μ) :
    mulLp hg (c • f) = c • mulLp hg f := by
  refine Subtype.ext ?_
  rw [coe_mulLp]
  change g * (c • (f : α →ₘ[μ] ℂ)) = _
  rw [aeEqFun_mul_smul]
  rfl

/-- **Multiplication by a unimodular class is a linear isometry of `L^p`.** -/
noncomputable def mulLpₗᵢ {g : α →ₘ[μ] ℂ} (hg : ∀ᵐ x ∂μ, ‖g x‖ = 1) :
    Lp ℂ p μ →ₗᵢ[ℂ] Lp ℂ p μ where
  toFun := mulLp hg
  map_add' := mulLp_add hg
  map_smul' := mulLp_smul hg
  norm_map' := norm_mulLp hg

/-! ### The multiplier in rapidity coordinates -/

section FinCoords

/-- A finite rapidity tuple read as a sequence. -/
noncomputable def embedFin {n : ℕ} (θ : Fin n → ℝ) : ℕ → ℝ :=
  fun k => if h : k < n then θ ⟨k, h⟩ else 0

/-- The pair multiplier in rapidity coordinates. -/
noncomputable def pairMultiplierFin (y : ℝ → ℂ) {n : ℕ} (θ : Fin n → ℝ) : ℂ :=
  pairMultiplier y (embedFin θ) n

theorem norm_pairMultiplierFin {y : ℝ → ℂ} (hy : ∀ t : ℝ, ‖y t‖ = 1) {n : ℕ} (θ : Fin n → ℝ) :
    ‖pairMultiplierFin y θ‖ = 1 :=
  norm_pairMultiplier y hy _ n

theorem embedFin_zero {n : ℕ} (θ : Fin (n + 1) → ℝ) : embedFin θ 0 = θ 0 := by
  rw [embedFin, dif_pos (Nat.succ_pos n)]
  rfl

theorem embedFin_succ {n : ℕ} (θ : Fin (n + 1) → ℝ) (j : Fin n) :
    embedFin θ (j.val + 1) = θ j.succ := by
  rw [embedFin, dif_pos (by omega : j.val + 1 < n + 1)]
  rfl

/-- **The creation recursion in rapidity coordinates.**  Equation `(10a)`: adjoining a new first
rapidity multiplies the intertwiner by the string of its phases against the others. -/
theorem pairMultiplierFin_succ (y : ℝ → ℂ) {n : ℕ} (θ : Fin (n + 1) → ℝ) :
    pairMultiplierFin y θ
      = (∏ j : Fin n, y (θ 0 - θ j.succ))
        * pairMultiplierFin y (fun j : Fin n => θ j.succ) := by
  rw [pairMultiplierFin, pairMultiplierFin, pairMultiplier_shift]
  congr 1
  · rw [← Fin.prod_univ_eq_prod_range (fun j => y (embedFin θ 0 - embedFin θ (j + 1))) n]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [embedFin_zero, embedFin_succ]
  · refine pairMultiplier_congr y n fun k hk => ?_
    rw [embedFin, embedFin, dif_pos (by omega : k + 1 < n + 1), dif_pos hk]
    rfl

theorem measurable_embedFin_apply {n : ℕ} (k : ℕ) :
    Measurable fun θ : Fin n → ℝ => embedFin θ k := by
  by_cases h : k < n
  · have hfun : (fun θ : Fin n → ℝ => embedFin θ k) = fun θ : Fin n → ℝ => θ ⟨k, h⟩ := by
      funext θ
      rw [embedFin, dif_pos h]
    rw [hfun]
    exact measurable_pi_apply _
  · have hfun : (fun θ : Fin n → ℝ => embedFin θ k) = fun _ : Fin n → ℝ => (0 : ℝ) := by
      funext θ
      rw [embedFin, dif_neg h]
    rw [hfun]
    exact measurable_const

theorem measurable_pairMultiplierFin {y : ℝ → ℂ} (hy : Measurable y) (n : ℕ) :
    Measurable fun θ : Fin n → ℝ => pairMultiplierFin y θ := by
  have hfun : (fun θ : Fin n → ℝ => pairMultiplierFin y θ)
      = fun θ : Fin n → ℝ =>
        ∏ l ∈ Finset.range n, ∏ k ∈ Finset.range l, y (embedFin θ k - embedFin θ l) := rfl
  rw [hfun]
  refine Finset.measurable_prod _ fun l _ => ?_
  refine Finset.measurable_prod _ fun k _ => ?_
  exact hy.comp ((measurable_embedFin_apply k).sub (measurable_embedFin_apply l))

/-- **The intertwiner at a fixed particle number.**  Multiplication by Lechner's pair multiplier is
a linear isometry of the rapidity `L^p` space. -/
noncomputable def lechnerIntertwiner {y : ℝ → ℂ} (hy1 : ∀ t : ℝ, ‖y t‖ = 1) (hym : Measurable y)
    (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℂ p (volume : Measure (Fin n → ℝ)) →ₗᵢ[ℂ] Lp ℂ p (volume : Measure (Fin n → ℝ)) :=
  mulLpₗᵢ (g := AEEqFun.mk (fun θ : Fin n → ℝ => pairMultiplierFin y θ)
      (measurable_pairMultiplierFin hym n).aestronglyMeasurable) (by
    filter_upwards [AEEqFun.coeFn_mk (fun θ : Fin n → ℝ => pairMultiplierFin y θ)
      (measurable_pairMultiplierFin hym n).aestronglyMeasurable] with θ hθ
    rw [hθ]
    exact norm_pairMultiplierFin hy1 θ)

end FinCoords

end GaloisForLFunctions.HTGeometry

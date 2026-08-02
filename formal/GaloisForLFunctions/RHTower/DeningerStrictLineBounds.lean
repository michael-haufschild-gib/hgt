import GaloisForLFunctions.RHTower.DeningerCapInversion
import GaloisForLFunctions.RHTower.DeningerPoissonContinuous

/-!
# The line norms of a Poisson sum

The `L¹` norm of a Mellin transform along a vertical line is the quantity that Mellin inversion
converts into a pointwise bound.  Two facts make it usable on the Poisson side:

* on the lines `Re s = σ ≥ 2` and `Re s = −1` the multiplier `1/ζ` is bounded, so the line norm of
  a member of Meyer's space is at most a constant times the line norm of its Poisson sum;
* the line norm of a Poisson sum is the `L¹` norm of a Fourier transform of a Schwartz function,
  hence bounded by two Schwartz seminorms of the corresponding logarithmic weight — data of the
  radial space.

Together these bound `f` pointwise by finitely many radial seminorms of `Zf`, with a factor
`x^{-σ}` for every `σ ≥ 2` and a factor `x` at the origin.

* `deningerLineNorm` : the `L¹` norm along a vertical line.
* `norm_le_of_poisson_right`, `norm_le_of_poisson_left` : **`f` bounded by the line norms of `Zf`.**
* `exists_bound_deningerLineNorm` : **the line norm of `Zf` is bounded by finitely many Schwartz
  seminorms of the weight `Z_s f`.**
-/

open scoped Real SchwartzMap FourierTransform ContDiff NNReal
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The line norm -/

/-- The `L¹` norm of a Mellin transform along the vertical line `Re s = σ`. -/
def deningerLineNorm (σ : ℝ) (g : ℝ → ℂ) : ℝ := ∫ y : ℝ, ‖mellin g ((σ : ℂ) + y * I)‖

theorem deningerLineNorm_nonneg (σ : ℝ) (g : ℝ → ℂ) : 0 ≤ deningerLineNorm σ g :=
  integral_nonneg fun _ => norm_nonneg _

/-! ## The multiplier estimates for the line norms -/

/-- On a vertical line right of `2` the line norm of a member of Meyer's space is at most four
times the line norm of its Poisson sum. -/
theorem deningerLineNorm_le_right (s : ℤ) (hs : 2 ≤ s) (f : 𝓢(ℝ, ℂ))
    (hf : f ∈ DeningerMeyerCap) :
    deningerLineNorm (s : ℝ) (f : ℝ → ℂ)
      ≤ 4 * deningerLineNorm (s : ℝ) (deningerPoissonValue f) := by
  have hint : Integrable
      (fun y : ℝ => mellin (deningerPoissonValue f) (((s : ℝ) : ℂ) + y * I)) :=
    verticalIntegrable_mellin_poisson s f hf
  have hmaj : Integrable
      (fun y : ℝ => 4 * ‖mellin (deningerPoissonValue f) (((s : ℝ) : ℂ) + y * I)‖) :=
    hint.norm.const_mul 4
  have hle : ∀ y : ℝ, ‖mellin (f : ℝ → ℂ) (((s : ℝ) : ℂ) + y * I)‖
      ≤ 4 * ‖mellin (deningerPoissonValue f) (((s : ℝ) : ℂ) + y * I)‖ := by
    intro y
    refine norm_mellin_le_of_two_le_re f ?_
    have hre : ((((s : ℝ)) : ℂ) + (y : ℂ) * I).re = (s : ℝ) := by simp
    rw [hre]
    exact_mod_cast hs
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y : ℝ => norm_nonneg
      (mellin (f : ℝ → ℂ) (((s : ℝ) : ℂ) + y * I)))
    hmaj (Filter.Eventually.of_forall hle)
  rw [integral_const_mul] at hmono
  exact hmono

/-- On the line `Re s = −1` the line norm of a member of Meyer's space is at most `8π²` times the
line norm of its Poisson sum. -/
theorem deningerLineNorm_le_left (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) :
    deningerLineNorm (-1) (f : ℝ → ℂ)
      ≤ 8 * π ^ 2 * deningerLineNorm (-1) (deningerPoissonValue f) := by
  have hcast : (((-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_num
  have hint : Integrable
      (fun y : ℝ => mellin (deningerPoissonValue f) (((-1 : ℝ) : ℂ) + y * I)) := by
    have h := verticalIntegrable_mellin_poisson (-1) f hf
    rw [hcast] at h
    exact h
  have hmaj : Integrable
      (fun y : ℝ => 8 * π ^ 2 * ‖mellin (deningerPoissonValue f) (((-1 : ℝ) : ℂ) + y * I)‖) :=
    hint.norm.const_mul _
  have hae : ∀ᵐ y : ℝ, ‖mellin (f : ℝ → ℂ) (((-1 : ℝ) : ℂ) + y * I)‖
      ≤ 8 * π ^ 2 * ‖mellin (deningerPoissonValue f) (((-1 : ℝ) : ℂ) + y * I)‖ := by
    have hzero : ∀ᵐ y : ℝ, y ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hzero] with y hy
    have hpt := norm_mellin_le_left_line hf hy
    have hone : (((-1 : ℝ)) : ℂ) = -1 := by push_cast; ring
    rw [hone]
    exact hpt
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y : ℝ => norm_nonneg
      (mellin (f : ℝ → ℂ) (((-1 : ℝ) : ℂ) + y * I)))
    hmaj hae
  rw [integral_const_mul] at hmono
  exact hmono

/-! ## The pointwise bounds -/

/-- **A member of Meyer's space decays at any polynomial order controlled by the line norms of its
Poisson sum.** -/
theorem norm_le_of_poisson_right (s : ℤ) (hs : 2 ≤ s) (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap)
    {x : ℝ} (hx : 0 < x) :
    ‖f x‖ ≤ 4 / (2 * π) * x ^ (-(s : ℝ))
      * deningerLineNorm (s : ℝ) (deningerPoissonValue f) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h1 := norm_le_mellin_line s (by omega) f hf hx
  have h2 := deningerLineNorm_le_right s hs f hf
  have hcoef : (0 : ℝ) ≤ 1 / (2 * π) * x ^ (-(s : ℝ)) := by positivity
  calc ‖f x‖ ≤ 1 / (2 * π) * x ^ (-(s : ℝ)) * deningerLineNorm (s : ℝ) (f : ℝ → ℂ) := h1
    _ ≤ 1 / (2 * π) * x ^ (-(s : ℝ)) * (4 * deningerLineNorm (s : ℝ) (deningerPoissonValue f)) :=
        mul_le_mul_of_nonneg_left h2 hcoef
    _ = 4 / (2 * π) * x ^ (-(s : ℝ)) * deningerLineNorm (s : ℝ) (deningerPoissonValue f) := by
        ring

/-- **A member of Meyer's space vanishes at the origin at the rate of its Poisson line norm.** -/
theorem norm_le_of_poisson_left (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) {x : ℝ} (hx : 0 < x) :
    ‖f x‖ ≤ 8 * π ^ 2 / (2 * π) * x * deningerLineNorm (-1) (deningerPoissonValue f) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hcast : (((-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_num
  have h1 := norm_le_mellin_line (-1) (le_refl _) f hf hx
  rw [hcast, neg_neg, Real.rpow_one] at h1
  have h2 := deningerLineNorm_le_left f hf
  have hcoef : (0 : ℝ) ≤ 1 / (2 * π) * x := by positivity
  calc ‖f x‖ ≤ 1 / (2 * π) * x * deningerLineNorm (-1) (f : ℝ → ℂ) := h1
    _ ≤ 1 / (2 * π) * x * (8 * π ^ 2 * deningerLineNorm (-1) (deningerPoissonValue f)) :=
        mul_le_mul_of_nonneg_left h2 hcoef
    _ = 8 * π ^ 2 / (2 * π) * x * deningerLineNorm (-1) (deningerPoissonValue f) := by ring

/-! ## The line norm of a Poisson sum is a Schwartz seminorm bound -/

/-- The reflection operator on Schwartz space. -/
def deningerReflectCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv)

theorem deningerReflectCLM_apply (g : 𝓢(ℝ, ℂ)) : deningerReflectCLM g = deningerReflect g := rfl

/-- The symbol operator: the Fourier transform of the reflected logarithmic weight, whose values
along the real line are the Mellin transform of the Poisson sum on a vertical line. -/
def deningerPoissonSymbolCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := fourierSCLM.comp deningerReflectCLM

/-- The `L¹` norm of a Schwartz function is bounded by two of its seminorms. -/
theorem integral_norm_le_seminorm (h : 𝓢(ℝ, ℂ)) :
    (∫ z : ℝ, ‖h z‖) ≤ π * (SchwartzMap.seminorm ℂ 0 0 h + SchwartzMap.seminorm ℂ 2 0 h) := by
  set M : ℝ := SchwartzMap.seminorm ℂ 0 0 h + SchwartzMap.seminorm ℂ 2 0 h with hM
  have hpt : ∀ z : ℝ, ‖h z‖ ≤ M * (1 + z ^ 2)⁻¹ := by
    intro z
    have h0 := SchwartzMap.norm_pow_mul_le_seminorm ℂ h 0 z
    have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ h 2 z
    rw [pow_zero, one_mul] at h0
    have hz : ‖z‖ ^ 2 = z ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [hz] at h2
    have hpos : (0 : ℝ) < 1 + z ^ 2 := by positivity
    have key : ‖h z‖ * (1 + z ^ 2) ≤ M := by
      rw [hM]
      nlinarith [norm_nonneg (h z)]
    calc ‖h z‖ = ‖h z‖ * (1 + z ^ 2) * (1 + z ^ 2)⁻¹ := by
          field_simp
      _ ≤ M * (1 + z ^ 2)⁻¹ := mul_le_mul_of_nonneg_right key (by positivity)
  have hmaj : Integrable (fun z : ℝ => M * (1 + z ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul M
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z : ℝ => norm_nonneg (h z)) hmaj
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hmono
  calc (∫ z : ℝ, ‖h z‖) ≤ M * π := hmono
    _ = π * M := by ring

/-- The line norm of a Poisson sum is `2π` times the `L¹` norm of the symbol of the corresponding
logarithmic weight. -/
theorem deningerLineNorm_poisson_eq (s : ℤ) (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) :
    deningerLineNorm (s : ℝ) (deningerPoissonValue f)
      = 2 * π * ∫ z : ℝ, ‖deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf) z‖ := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hval : ∀ z : ℝ, 𝓕 ((deningerReflect (deningerPoissonSchwartz s f hf) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z
      = deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf) z := by
    intro z
    have hcoe := SchwartzMap.fourier_coe (deningerReflect (deningerPoissonSchwartz s f hf))
    rw [← hcoe]
    rfl
  have hfun : (fun y : ℝ => ‖mellin (deningerPoissonValue f) (((s : ℝ) : ℂ) + y * I)‖)
      = fun y : ℝ => ‖deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf)
        (y / (2 * π))‖ := by
    funext y
    rw [mellin_deningerPoissonValue_eq_fourier s f hf y, hval]
  have hscale := MeasureTheory.Measure.integral_comp_div
    (fun z : ℝ => ‖deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf) z‖) (2 * π)
  rw [deningerLineNorm, hfun, hscale, smul_eq_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]

/-- **The line norm of a Poisson sum is bounded by two Schwartz seminorms of the weight.** -/
theorem deningerLineNorm_poisson_le (s : ℤ) (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) :
    deningerLineNorm (s : ℝ) (deningerPoissonValue f)
      ≤ 2 * π * π * (SchwartzMap.seminorm ℂ 0 0
            (deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf))
          + SchwartzMap.seminorm ℂ 2 0
            (deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf))) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hbound := integral_norm_le_seminorm
    (deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf))
  rw [deningerLineNorm_poisson_eq s f hf]
  calc 2 * π * ∫ z : ℝ, ‖deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf) z‖
      ≤ 2 * π * (π * (SchwartzMap.seminorm ℂ 0 0
            (deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf))
          + SchwartzMap.seminorm ℂ 2 0
            (deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf)))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 2 * π * π * (SchwartzMap.seminorm ℂ 0 0
            (deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf))
          + SchwartzMap.seminorm ℂ 2 0
            (deningerPoissonSymbolCLM (deningerPoissonSchwartz s f hf))) := by ring

/-- **The line norm of a Poisson sum is bounded by finitely many Schwartz seminorms of the
weight `Z_s f`** — a seminorm of the radial space. -/
theorem exists_bound_deningerLineNorm (s : ℤ) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
      deningerLineNorm (s : ℝ) (deningerPoissonValue f)
        ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz s f hf) := by
  classical
  have hpi : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨K₁, C₁, hC₁, hb₁⟩ := exists_bound_seminorm_comp deningerPoissonSymbolCLM 0
  obtain ⟨K₂, C₂, hC₂, hb₂⟩ := exists_bound_seminorm_comp deningerPoissonSymbolCLM 2
  refine ⟨K₁ ∪ K₂, 2 * π * π * (C₁ + C₂), by positivity, fun f hf => ?_⟩
  set w : 𝓢(ℝ, ℂ) := deningerPoissonSchwartz s f hf with hw
  set S : ℝ := ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) w with hS
  have hSnn : 0 ≤ S := apply_nonneg _ _
  have hle₁ : K₁.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ≤ (K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.sup_mono Finset.subset_union_left
  have hle₂ : K₂.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ≤ (K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.sup_mono Finset.subset_union_right
  have hmono₁ : (K₁.sup (schwartzSeminormFamily ℂ ℝ ℂ)) w ≤ S := hle₁ w
  have hmono₂ : (K₂.sup (schwartzSeminormFamily ℂ ℝ ℂ)) w ≤ S := hle₂ w
  have h₁ : SchwartzMap.seminorm ℂ 0 0 (deningerPoissonSymbolCLM w) ≤ C₁ * S :=
    le_trans (hb₁ w) (mul_le_mul_of_nonneg_left hmono₁ hC₁)
  have h₂ : SchwartzMap.seminorm ℂ 2 0 (deningerPoissonSymbolCLM w) ≤ C₂ * S :=
    le_trans (hb₂ w) (mul_le_mul_of_nonneg_left hmono₂ hC₂)
  calc deningerLineNorm (s : ℝ) (deningerPoissonValue f)
      ≤ 2 * π * π * (SchwartzMap.seminorm ℂ 0 0 (deningerPoissonSymbolCLM w)
          + SchwartzMap.seminorm ℂ 2 0 (deningerPoissonSymbolCLM w)) :=
        deningerLineNorm_poisson_le s f hf
    _ ≤ 2 * π * π * (C₁ * S + C₂ * S) := by
        refine mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity)
    _ = 2 * π * π * (C₁ + C₂) * S := by ring

end RHTower

end

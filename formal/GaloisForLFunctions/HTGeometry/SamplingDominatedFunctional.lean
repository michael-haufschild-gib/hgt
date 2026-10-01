import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Linear forms dominated by a sampling norm

If a linear form `φ` on a complex vector space satisfies `|φ f|² ≤ C Σ_i |S_i f|²` for linear
forms `S_i` with square-summable values, then `φ = Σ β_i S_i` with `β ∈ ℓ²`. This is the step that
turns a sampling (frame-type) lower bound into explicit linear relations among sample values.
-/

open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Functionals dominated by a sampling norm are sampling series.** Let `S i` be linear forms on a
complex vector space `E` with `Σ |S_i f|² < ∞` for every `f`, and let `φ` be a linear form with
`|φ f|² ≤ C Σ |S_i f|²`. Then `φ f = Σ β_i S_i f` for one coefficient sequence `β ∈ ℓ²`.

The map `f ↦ (S_i f)` lands in `ℓ²`; `φ` factors through its range with norm `≤ √C`, extends to
all of `ℓ²` by Hahn–Banach, and the extension is an inner product by Riesz. No completeness or
inner product on `E` is needed. -/
theorem exists_coeff_of_dominated {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    (S : ι → E →ₗ[ℂ] ℂ) (hS : ∀ f, Summable fun i => ‖S i f‖ ^ 2)
    (φ : E →ₗ[ℂ] ℂ) {C : ℝ} (hφ : ∀ f, ‖φ f‖ ^ 2 ≤ C * ∑' i, ‖S i f‖ ^ 2) :
    ∃ β : ι → ℂ, Summable (fun i => ‖β i‖ ^ 2) ∧ ∀ f, φ f = ∑' i, β i * S i f := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hmem : ∀ f, Memℓp (fun i => S i f) 2 := fun f => by
    rw [memℓp_gen_iff h2]
    simpa [ENNReal.toReal_ofNat, Real.rpow_two] using hS f
  let T : E →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 :=
    { toFun := fun f => ⟨fun i => S i f, hmem f⟩
      map_add' := fun f g => by ext i; simp
      map_smul' := fun c f => by ext i; simp }
  have hT : ∀ f i, (T f : ι → ℂ) i = S i f := fun f i => rfl
  have hnormT : ∀ f, ‖T f‖ ^ 2 = ∑' i, ‖S i f‖ ^ 2 := by
    intro f
    have := lp.norm_rpow_eq_tsum h2 (T f)
    simpa [ENNReal.toReal_ofNat, Real.rpow_two, hT] using this
  set C' := max C 0 with hC'
  have hbd : ∀ f, ‖φ f‖ ≤ Real.sqrt C' * ‖T f‖ := by
    intro f
    have h1 : ‖φ f‖ ^ 2 ≤ C' * ‖T f‖ ^ 2 := by
      rw [hnormT]
      calc ‖φ f‖ ^ 2 ≤ C * ∑' i, ‖S i f‖ ^ 2 := hφ f
        _ ≤ C' * ∑' i, ‖S i f‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (tsum_nonneg fun i => by positivity)
    have hC'0 : 0 ≤ C' := le_max_right _ _
    rw [← Real.sqrt_sq (norm_nonneg (φ f)), ← Real.sqrt_sq (norm_nonneg (T f)),
      ← Real.sqrt_mul hC'0]
    exact Real.sqrt_le_sqrt h1
  have hker : LinearMap.ker T ≤ LinearMap.ker φ := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have := hbd f
    rw [hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.mp this
  let ψ₀ : LinearMap.range T →ₗ[ℂ] ℂ :=
    (LinearMap.ker T).liftQ φ hker ∘ₗ (T.quotKerEquivRange).symm.toLinearMap
  have hψ₀ : ∀ f, ψ₀ ⟨T f, LinearMap.mem_range_self T f⟩ = φ f := by
    intro f
    have : (T.quotKerEquivRange).symm ⟨T f, LinearMap.mem_range_self T f⟩
        = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]
      ext1
      rw [LinearMap.quotKerEquivRange_apply_mk]
    simp only [ψ₀, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, this,
      Submodule.liftQ_apply]
  have hψbd : ∀ v : LinearMap.range T, ‖ψ₀ v‖ ≤ Real.sqrt C' * ‖v‖ := by
    rintro ⟨v, f, rfl⟩
    rw [hψ₀ f]
    exact hbd f
  let ψ : StrongDual ℂ (LinearMap.range T) := ψ₀.mkContinuous (Real.sqrt C') hψbd
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range T) ψ
  set b := (InnerProductSpace.toDual ℂ (lp (fun _ : ι => ℂ) 2)).symm g with hb
  refine ⟨fun i => (starRingEnd ℂ) ((b : ι → ℂ) i), ?_, fun f => ?_⟩
  · have hb2 := (lp.memℓp b)
    rw [memℓp_gen_iff h2] at hb2
    simpa [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_conj] using hb2
  · have h1 : g (T f) = φ f := by
      have := hg ⟨T f, LinearMap.mem_range_self T f⟩
      rw [this]
      simp only [ψ, LinearMap.mkContinuous_apply]
      exact hψ₀ f
    rw [← h1, ← InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (x := T f) (y := g), ← hb,
      lp.inner_eq_tsum]
    congr 1
    funext i
    rw [hT]
    simp [inner, mul_comm]

end GaloisForLFunctions.HTGeometry

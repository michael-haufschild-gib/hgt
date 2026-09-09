import GaloisForLFunctions.HTGeometry.FokasLenellsRawComplexRecovery

/-!
# Exact inversion of raw complex-time graphs

Pointwise exponential cancellation induces an isometric exchange of the
complete maximal graphs at opposite complex times. Output ranges are exactly
the opposite-time input domains, even when neither operator is bounded on L².
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The raw derivative hierarchy composes by adding orders and complex times. -/
theorem rawComplexSymbol_mul (n k : ℕ) (τ σ : ℂ) (z : ℝ) :
    rawComplexSymbol n τ z * rawComplexSymbol k σ z = rawComplexSymbol (n+k) (τ+σ) z := by
  unfold rawComplexSymbol
  rw [pow_add]
  have he : -(τ + σ) * (((2*z)⁻¹ : ℝ) : ℂ) * I =
      -τ * (((2*z)⁻¹ : ℝ) : ℂ) * I + -σ * (((2*z)⁻¹ : ℝ) : ℂ) * I := by ring
  rw [he,Complex.exp_add]
  ring

/-- The initial zeroth raw symbol is identically one. -/
theorem rawComplexSymbol_zero_zero (z : ℝ) : rawComplexSymbol 0 0 z = 1 := by
  simp [rawComplexSymbol]

/-- No zeroth raw complex-time multiplier vanishes, including at the totalized origin. -/
theorem rawComplexSymbol_zero_ne_zero (τ : ℂ) (z : ℝ) : rawComplexSymbol 0 τ z ≠ 0 := by
  simp [rawComplexSymbol]

/-- Opposite raw complex times cancel exactly at every spectral value. -/
theorem rawComplexSymbol_neg_mul (τ : ℂ) (z : ℝ) :
    rawComplexSymbol 0 (-τ) z * rawComplexSymbol 0 τ z = 1 := by
  rw [rawComplexSymbol_mul,zero_add,neg_add_cancel,rawComplexSymbol_zero_zero]

/-- Swapping input and output is exactly equivalent to reversing the raw complex time. -/
theorem rawComplexGraph_swap_iff (τ : ℂ) (u v : Lp ℂ 2 (volume : Measure ℝ)) :
    (u,v) ∈ rawComplexGraph 0 τ ↔ (v,u) ∈ rawComplexGraph 0 (-τ) := by
  constructor
  · intro h
    change (v : ℝ → ℂ) =ᵐ[volume] (fun z => rawComplexSymbol 0 τ z * u z) at h
    change (u : ℝ → ℂ) =ᵐ[volume] (fun z => rawComplexSymbol 0 (-τ) z * v z)
    filter_upwards [h] with z hz
    rw [hz,← mul_assoc,rawComplexSymbol_neg_mul,one_mul]
  · intro h
    change (u : ℝ → ℂ) =ᵐ[volume] (fun z => rawComplexSymbol 0 (-τ) z * v z) at h
    change (v : ℝ → ℂ) =ᵐ[volume] (fun z => rawComplexSymbol 0 τ z * u z)
    filter_upwards [h] with z hz
    rw [hz,← mul_assoc,mul_comm (rawComplexSymbol 0 τ z),rawComplexSymbol_neg_mul,one_mul]

/-- The actual opposite-time graph inverse is a linear isometry in the complete graph norms. -/
def rawComplexGraphTimeReverse (τ : ℂ) : rawComplexGraph 0 τ ≃ₗᵢ[ℂ] rawComplexGraph 0 (-τ) where
  toFun p := ⟨(p.val.2,p.val.1),(rawComplexGraph_swap_iff τ _ _).1 p.property⟩
  invFun p := ⟨(p.val.2,p.val.1),(rawComplexGraph_swap_iff τ _ _).2 p.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl
  map_add' p q := by apply Subtype.ext; rfl
  map_smul' c p := by apply Subtype.ext; rfl
  norm_map' p := by
    change max ‖p.val.2‖ ‖p.val.1‖ = max ‖p.val.1‖ ‖p.val.2‖
    exact max_comm _ _

/-- Time reversal exchanges the literal graph input and raw output. -/
theorem rawComplexGraphTimeReverse_coordinates (τ : ℂ) (p : rawComplexGraph 0 τ) :
    rawComplexGraphInput 0 (-τ) (rawComplexGraphTimeReverse τ p) = rawComplexGraphOutput 0 τ p ∧
      rawComplexGraphOutput 0 (-τ) (rawComplexGraphTimeReverse τ p) = rawComplexGraphInput 0 τ p :=
  ⟨rfl,rfl⟩

/-- Every raw zeroth complex-time graph output determines its input uniquely. -/
theorem rawComplexGraphOutput_injective (τ : ℂ) : Function.Injective (rawComplexGraphOutput 0 τ) := by
  intro p q h
  apply (rawComplexGraphTimeReverse τ).injective
  apply rawComplexGraphInput_injective 0 (-τ)
  exact h

/-- The output range is precisely the maximal raw domain at the opposite complex time. -/
theorem range_rawComplexGraphOutput (τ : ℂ) :
    Set.range (rawComplexGraphOutput 0 τ) = Set.range (rawComplexGraphInput 0 (-τ)) := by
  ext u
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨rawComplexGraphTimeReverse τ p,rfl⟩
  · rintro ⟨p,rfl⟩
    exact ⟨(rawComplexGraphTimeReverse τ).symm p,rfl⟩

/-- Raw complex evolution has dense output range at every complex time. -/
theorem rawComplexGraphOutput_denseRange (τ : ℂ) : DenseRange (rawComplexGraphOutput 0 τ) := by
  change Dense (Set.range (rawComplexGraphOutput 0 τ))
  rw [range_rawComplexGraphOutput]
  exact rawComplexGraphInput_denseRange 0 (-τ)

/-- Raw complex evolution is onto the full Hilbert space exactly at real time. -/
theorem rawComplexGraphOutput_surjective_iff (τ : ℂ) :
    Function.Surjective (rawComplexGraphOutput 0 τ) ↔ τ.im = 0 := by
  rw [← Set.range_eq_univ,range_rawComplexGraphOutput,Set.range_eq_univ,
    rawComplexGraphInput_surjective_iff]
  simp

/-- Nonreal complex time has a dense proper output range, nonclosed in the ambient L² norm. -/
theorem isClosed_range_rawComplexGraphOutput_iff (τ : ℂ) :
    IsClosed (Set.range (rawComplexGraphOutput 0 τ)) ↔ τ.im = 0 := by
  rw [range_rawComplexGraphOutput,isClosed_range_rawComplexGraphInput_iff]
  simp

end
end GaloisForLFunctions.HTGeometry.FokasLenells

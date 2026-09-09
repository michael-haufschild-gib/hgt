import GaloisForLFunctions.HTGeometry.FokasLenellsRawComplexSymbols
import GaloisForLFunctions.HTGeometry.MultiplierClosedGraph
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert

/-!
# Complete dense graph domains for the raw complex derivative hierarchy

Positive damping d = 1/(1+|m|) makes both d and m*d bounded. The existing
self-adjoint multiplier density theorem gives a dense set of genuine graph
inputs. The existing closed-graph theorem makes the actual linear graph
complete, including every unbounded nonreal-time and positive-order case.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The canonical positive damping of the actual raw symbol. -/
def rawComplexDamping (n : ℕ) (τ : ℂ) (z : ℝ) : ℝ := (1 + ‖rawComplexSymbol n τ z‖)⁻¹

private theorem damping_pos (n : ℕ) (τ : ℂ) (z : ℝ) : 0 < rawComplexDamping n τ z := by
  unfold rawComplexDamping
  positivity

private theorem damping_le_one (n : ℕ) (τ : ℂ) (z : ℝ) : rawComplexDamping n τ z ≤ 1 := by
  unfold rawComplexDamping
  exact inv_le_one_of_one_le₀ (by linarith [norm_nonneg (rawComplexSymbol n τ z)])

private theorem measurable_damping (n : ℕ) (τ : ℂ) : Measurable (rawComplexDamping n τ) := by
  have hm := measurable_rawComplexSymbol n τ
  unfold rawComplexDamping
  fun_prop

private theorem damping_complex_bound (n : ℕ) (τ : ℂ) (z : ℝ) :
    ‖(rawComplexDamping n τ z : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (damping_pos n τ z)]
  exact damping_le_one n τ z

/-- The actual raw symbol after its canonical bounded damping. -/
def rawComplexDampedSymbol (n : ℕ) (τ : ℂ) (z : ℝ) : ℂ :=
  rawComplexSymbol n τ z * (rawComplexDamping n τ z : ℂ)

private theorem measurable_dampedSymbol (n : ℕ) (τ : ℂ) : Measurable (rawComplexDampedSymbol n τ) := by
  exact (measurable_rawComplexSymbol n τ).mul (Complex.measurable_ofReal.comp (measurable_damping n τ))

private theorem dampedSymbol_bound (n : ℕ) (τ : ℂ) (z : ℝ) : ‖rawComplexDampedSymbol n τ z‖ ≤ 1 := by
  rw [rawComplexDampedSymbol,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (damping_pos n τ z)]
  change ‖rawComplexSymbol n τ z‖ / (1 + ‖rawComplexSymbol n τ z‖) ≤ 1
  apply (div_le_one (by positivity)).2
  linarith

/-- The bounded positive damping operator on the existing Hilbert carrier. -/
def rawComplexDampingOperator (n : ℕ) (τ : ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := volume)
    (Complex.measurable_ofReal.comp (measurable_damping n τ))
    (by norm_num : (0:ℝ) ≤ 1) (fun z => damping_complex_bound n τ z)

/-- The bounded output multiplier paired with the positive damping operator. -/
def rawComplexDampedOperator (n : ℕ) (τ : ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := volume) (measurable_dampedSymbol n τ)
    (by norm_num : (0:ℝ) ≤ 1) (dampedSymbol_bound n τ)

/-- The canonical damping has dense range at every raw order and complex time. -/
theorem rawComplexDampingOperator_denseRange (n : ℕ) (τ : ℂ) :
    DenseRange (rawComplexDampingOperator n τ) := by
  apply denseRange_lpBoundedMulCLM
  · intro z
    simp
  · intro z
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (damping_pos n τ z))

/-- The actual maximal linear graph of raw complex multiplication. -/
def rawComplexGraph (n : ℕ) (τ : ℂ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ)) where
  carrier := multiplierGraph (rawComplexSymbol n τ) volume
  zero_mem' := by
    change ((0 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun z => rawComplexSymbol n τ z * (0 : Lp ℂ 2 (volume : Measure ℝ)) z
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with z hz
    simp only [hz,Pi.zero_apply,mul_zero]
  add_mem' := by
    intro p q hp hq
    change ((p.2 + q.2 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun z => rawComplexSymbol n τ z * (p.1 + q.1) z
    filter_upwards [Lp.coeFn_add p.2 q.2,Lp.coeFn_add p.1 q.1,hp,hq] with z h0 h1 h2 h3
    rw [h0,Pi.add_apply,h1,Pi.add_apply,h2,h3,mul_add]
  smul_mem' := by
    intro c p hp
    change ((c • p.2 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun z => rawComplexSymbol n τ z * (c • p.1) z
    filter_upwards [Lp.coeFn_smul c p.2,Lp.coeFn_smul c p.1,hp] with z h0 h1 h2
    rw [h0,Pi.smul_apply,h1,Pi.smul_apply,h2]
    simp only [smul_eq_mul]
    ring

/-- The actual raw multiplication graph is closed for every order and complex time. -/
theorem isClosed_rawComplexGraph (n : ℕ) (τ : ℂ) :
    IsClosed (rawComplexGraph n τ : Set (Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ))) :=
  isClosed_multiplierGraph _

/-- The raw graph is a complete normed space in the inherited graph norm. -/
instance rawComplexGraph_completeSpace (n : ℕ) (τ : ℂ) : CompleteSpace (rawComplexGraph n τ) :=
  completeSpace_coe_iff_isComplete.2 (isClosed_rawComplexGraph n τ).isComplete

/-- Input projection from the complete actual graph domain. -/
def rawComplexGraphInput (n : ℕ) (τ : ℂ) : rawComplexGraph n τ →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (ContinuousLinearMap.fst ℂ _ _).comp (rawComplexGraph n τ).subtypeL

/-- Output projection is the raw multiplication operator on its complete graph domain. -/
def rawComplexGraphOutput (n : ℕ) (τ : ℂ) : rawComplexGraph n τ →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (ContinuousLinearMap.snd ℂ _ _).comp (rawComplexGraph n τ).subtypeL

/-- A raw graph input determines its output uniquely. -/
theorem rawComplexGraphInput_injective (n : ℕ) (τ : ℂ) : Function.Injective (rawComplexGraphInput n τ) := by
  intro p q hpq
  have hx : p.val.1 = q.val.1 := hpq
  have hy : p.val.2 = q.val.2 := by
    apply Lp.ext
    filter_upwards [p.property,q.property] with z hp hq
    rw [hp,hq,hx]
  exact Subtype.ext (Prod.ext hx hy)

/-- Every positively damped vector is an actual raw graph input, with its concrete bounded output. -/
theorem rawComplexGraph_regularized_pair_mem (n : ℕ) (τ : ℂ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (rawComplexDampingOperator n τ u,rawComplexDampedOperator n τ u) ∈ rawComplexGraph n τ := by
  have h0 := lpBoundedMulCLM_coeFn (p := 2) (μ := volume)
    (Complex.measurable_ofReal.comp (measurable_damping n τ))
    (by norm_num : (0:ℝ) ≤ 1) (fun z => damping_complex_bound n τ z) u
  have h1 := lpBoundedMulCLM_coeFn (p := 2) (μ := volume) (measurable_dampedSymbol n τ)
    (by norm_num : (0:ℝ) ≤ 1) (dampedSymbol_bound n τ) u
  change (rawComplexDampingOperator n τ u : ℝ → ℂ) =ᵐ[volume]
    (fun z => (rawComplexDamping n τ z : ℂ) * u z) at h0
  change (rawComplexDampedOperator n τ u : ℝ → ℂ) =ᵐ[volume]
    (fun z => rawComplexDampedSymbol n τ z * u z) at h1
  filter_upwards [h0,h1] with z hd hm
  change (rawComplexDampedOperator n τ u) z = rawComplexSymbol n τ z * (rawComplexDampingOperator n τ u) z
  rw [hm,hd]
  exact mul_assoc _ _ _

/-- The complete raw graph domain is densely defined on the full original Hilbert space. -/
theorem rawComplexGraphInput_denseRange (n : ℕ) (τ : ℂ) : DenseRange (rawComplexGraphInput n τ) := by
  apply Dense.mono ?_ (rawComplexDampingOperator_denseRange n τ)
  rintro _ ⟨u,rfl⟩
  exact ⟨⟨(rawComplexDampingOperator n τ u,rawComplexDampedOperator n τ u),
    rawComplexGraph_regularized_pair_mem n τ u⟩,rfl⟩

end
end GaloisForLFunctions.HTGeometry.FokasLenells

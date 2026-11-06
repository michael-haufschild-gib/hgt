import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheHalfLineLogarithmicGreenSolutionsHaveBoundaryValues
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFormHasItsMixedJumpPairing

/-!
# The half-line Green operator under a shift of the edge

Write `G = A A*`, where `A` is causal convolution on the half-line, and let `S_τ` be the right shift. The shift
commutes with `A`, and `A* S_τ f(p) = 𝓡_f(p − τ)` for `p ≥ 0`, where `𝓡_f` is the backward convolution. Only the
values at `p < τ` distinguish `A* S_τ` from `S_τ A*`.

**Theorem** (`halfLineForm_shift_green_cut`). If `Q = G f₂` and `B = Q 1_{[0,τ)}` has finite energy, then

  `E(S_τ G f₁, B) = − ∫_{[0,τ)} conj 𝓡_{f₁}(p − τ) 𝓡_{f₂}(p) dp`.

So the energy between a Green solution with edge at `τ` and the collar `[0,τ)` of a Green solution with edge at `0`
is of size `τ ‖f₁‖_∞ ‖f₂‖_∞`, with no logarithm (`norm_halfLineForm_shift_green_cut_le`). This is the source of
the `L¹` Lipschitz bound of the Weil Riesz vectors in the aperture.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

local notation "v" => logarithmicCausalKernel

/-- The logarithmic form is additive in its second slot on the energy domain. -/
theorem logarithmicFullForm_sub_right {w x y : RealLineL2} (hw : HasLogarithmicEnergy w)
    (hx : HasLogarithmicEnergy x) (hy : HasLogarithmicEnergy y) :
    logarithmicFullForm w (x - y) = logarithmicFullForm w x - logarithmicFullForm w y := by
  have hix : Integrable (fun ξ : ℝ => (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
      star (fourierUnitary w ξ) * fourierUnitary x ξ) := integrable_logarithmicFullForm hw hx
  have hiy : Integrable (fun ξ : ℝ => (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
      star (fourierUnitary w ξ) * fourierUnitary y ξ) := integrable_logarithmicFullForm hw hy
  unfold logarithmicFullForm
  rw [← integral_sub hix hiy]
  apply integral_congr_ae
  have he : (fourierUnitary (x - y) : ℝ → ℂ) =ᵐ[volume] fourierUnitary x - fourierUnitary y := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [he] with ξ hξ
  rw [hξ, Pi.sub_apply]
  ring

/-- The energy domain is closed under differences. -/
theorem HasLogarithmicEnergy.sub {x y : RealLineL2} (hx : HasLogarithmicEnergy x)
    (hy : HasLogarithmicEnergy y) : HasLogarithmicEnergy (x - y) := by
  rw [hasLogarithmicEnergy_iff_range_convolution] at hx hy ⊢
  exact (LinearMap.range logarithmicConvolution.toLinearMap).sub_mem hx hy

/-! ### The shift -/

/-- The right shift on the half-line. -/
def halfShift (τ : ℝ) (hτ : 0 ≤ τ) (w : LogarithmicHalfLineL2) : LogarithmicHalfLineL2 :=
  ⟨logTranslationCLM (-τ) (w : RealLineL2), by
    rw [mem_halfLineL2_iff]
    have hs := (measurePreserving_add_right (volume : Measure ℝ) (-τ)).quasiMeasurePreserving.ae
      ((mem_halfLineL2_iff (w : RealLineL2)).mp w.property)
    filter_upwards [logarithmicTranslation_coeFn (-τ) (w : RealLineL2), hs] with x hx hz hneg
    rw [hx]
    exact hz (by linarith only [hneg, hτ])⟩

theorem halfShift_coeFn (τ : ℝ) (hτ : 0 ≤ τ) (w : LogarithmicHalfLineL2) :
    ((halfShift τ hτ w : LogarithmicHalfLineL2) : RealLineL2) =ᵐ[volume] fun x =>
      (w : RealLineL2) (x - τ) := by
  filter_upwards [logarithmicTranslation_coeFn (-τ) (w : RealLineL2)] with x hx
  change logTranslationCLM (-τ) (w : RealLineL2) x = _
  rw [hx, sub_eq_add_neg]

/-- Shift and causal convolution commute. -/
theorem halfShift_causal (τ : ℝ) (hτ : 0 ≤ τ) (g : LogarithmicHalfLineL2) :
    halfShift τ hτ (logarithmicCausalOperator g) =
      logarithmicCausalOperator (halfShift τ hτ g) := by
  apply Subtype.ext
  apply Lp.ext
  have hc := (measurePreserving_sub_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae
    (logarithmicConvolution_coeFn (g : RealLineL2))
  filter_upwards [halfShift_coeFn τ hτ (logarithmicCausalOperator g), hc,
    logarithmicConvolution_coeFn ((halfShift τ hτ g : LogarithmicHalfLineL2) : RealLineL2)]
    with x h1 h2 h3
  rw [h1, logarithmicCausalOperator_coe]
  rw [logarithmicCausalOperator_coe, h3, h2]
  rw [← integral_sub_right_eq_self
    (fun y : ℝ => (v (x - τ - y) : ℂ) * (g : RealLineL2) y) τ]
  apply integral_congr_ae
  filter_upwards [halfShift_coeFn τ hτ g] with y hy
  rw [hy, show x - τ - (y - τ) = x - y by ring]

/-- The readout of a shifted forcing is the readout at the shifted level. -/
theorem logarithmicBackwardConvolution_halfShift (τ : ℝ) (hτ : 0 ≤ τ) (f : LogarithmicHalfLineL2)
    (p : ℝ) :
    logarithmicBackwardConvolution ((halfShift τ hτ f : LogarithmicHalfLineL2) : RealLineL2) p =
      logarithmicBackwardConvolution (f : RealLineL2) (p - τ) := by
  rw [logarithmicBackwardConvolution_congr (halfShift_coeFn τ hτ f)]
  unfold logarithmicBackwardConvolution
  rw [← integral_sub_right_eq_self
    (fun y : ℝ => (v (y - (p - τ)) : ℂ) * (f : RealLineL2) y) τ]
  apply integral_congr_ae
  filter_upwards with y
  rw [show y - τ - (p - τ) = y - p by ring]

private theorem inner_halfShift (τ : ℝ) (hτ : 0 ≤ τ) (x y : LogarithmicHalfLineL2) :
    inner ℂ (halfShift τ hτ x) (halfShift τ hτ y) = inner ℂ x y :=
  (MellinL2.additiveTranslationUnitary (-τ)).inner_map_map (x : RealLineL2) (y : RealLineL2)

/-! ### The identity -/

/-- **The shift identity of the half-line Green operator.** -/
theorem halfLineForm_shift_green_cut (f₁ f₂ : LogarithmicHalfLineL2) (τ : ℝ) (hτ : 0 ≤ τ)
    (B : LogarithmicHalfLineL2) (hB : HasLogarithmicEnergy (B : RealLineL2))
    (hBv : (B : RealLineL2) =ᵐ[volume] (Iio τ).indicator
      ((logarithmicHalfLineGreenOperator f₂ : LogarithmicHalfLineL2) : RealLineL2)) :
    logarithmicHalfLineForm (halfShift τ hτ (logarithmicHalfLineGreenOperator f₁)) B =
      -∫ p in Ico (0 : ℝ) τ, conj (logarithmicBackwardConvolution (f₁ : RealLineL2) (p - τ)) *
        logarithmicBackwardConvolution (f₂ : RealLineL2) p := by
  obtain ⟨A, hA⟩ : ∃ A, A = logarithmicCausalOperator := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = logarithmicHalfLineGreenOperator f₁ := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = logarithmicHalfLineGreenOperator f₂ := ⟨_, rfl⟩
  obtain ⟨hPE, hPs⟩ := logarithmicHalfLineGreenOperator_solves f₁
  obtain ⟨hQE, hQs⟩ := logarithmicHalfLineGreenOperator_solves f₂
  rw [← hP] at hPE hPs ⊢
  rw [← hQ] at hQE hQs hBv
  have hSPE : HasLogarithmicEnergy ((halfShift τ hτ P : LogarithmicHalfLineL2) : RealLineL2) :=
    hasLogarithmicEnergy_translation (-τ) hPE
  -- The complement of the collar.
  obtain ⟨Z, hZ⟩ : ∃ Z : LogarithmicHalfLineL2, Z = Q - B := ⟨_, rfl⟩
  have hZE : HasLogarithmicEnergy (Z : RealLineL2) := by
    rw [hZ]
    exact hQE.sub hB
  have hZv : ∀ᵐ r ∂volume, r < τ → (Z : RealLineL2) r = 0 := by
    rw [hZ]
    filter_upwards [Lp.coeFn_sub (Q : RealLineL2) (B : RealLineL2), hBv] with r h1 h2 hr
    change ((Q : RealLineL2) - (B : RealLineL2)) r = 0
    rw [h1, Pi.sub_apply, h2, indicator_of_mem (show r ∈ Iio τ from hr), sub_self]
  -- The collar complement is a shift.
  obtain ⟨Z', hZ'⟩ : ∃ Z' : LogarithmicHalfLineL2, (Z' : RealLineL2) =
      logTranslationCLM τ (Z : RealLineL2) :=
    ⟨⟨logTranslationCLM τ (Z : RealLineL2), by
      rw [mem_halfLineL2_iff]
      have hs := (measurePreserving_add_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae hZv
      filter_upwards [logarithmicTranslation_coeFn τ (Z : RealLineL2), hs] with x hx hz hneg
      rw [hx]
      exact hz (by linarith only [hneg])⟩, rfl⟩
  have hZ'E : HasLogarithmicEnergy (Z' : RealLineL2) := by
    rw [hZ']
    exact hasLogarithmicEnergy_translation τ hZE
  have hSZ' : halfShift τ hτ Z' = Z := by
    apply Subtype.ext
    change logTranslationCLM (-τ) (Z' : RealLineL2) = _
    rw [hZ']
    exact congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T (Z : RealLineL2)) (logTranslationCLM_neg_mul τ)
  -- The energy against the complement.
  have hEZ : logarithmicHalfLineForm (halfShift τ hτ P) Z =
      inner ℂ (halfShift τ hτ f₁) Q - inner ℂ (halfShift τ hτ f₁) B := by
    have h1 : logarithmicHalfLineForm (halfShift τ hτ P) Z = logarithmicFullForm (P : RealLineL2)
        (Z' : RealLineL2) := by
      rw [← hSZ']
      exact logarithmicFullForm_translation (-τ) hPE hZ'E
    have h2 := logarithmicFullForm_conj (Z' : RealLineL2) (P : RealLineL2)
    have h3 : logarithmicFullForm (Z' : RealLineL2) (P : RealLineL2) = inner ℂ Z' f₁ := hPs Z' hZ'E
    have h4 : inner ℂ f₁ Z' = inner ℂ (halfShift τ hτ f₁) Z := by
      rw [← hSZ']
      exact (inner_halfShift τ hτ f₁ Z').symm
    have h5 : inner ℂ (halfShift τ hτ f₁) Z =
        inner ℂ (halfShift τ hτ f₁) Q - inner ℂ (halfShift τ hτ f₁) B := by
      rw [hZ]
      exact inner_sub_right _ _ _
    have h6 : star (inner ℂ Z' f₁) = inner ℂ f₁ Z' := inner_conj_symm (𝕜 := ℂ) f₁ Z'
    rw [h1, ← h2, h3, h6, h4, h5]
  have hEsplit : logarithmicHalfLineForm (halfShift τ hτ P) B =
      logarithmicHalfLineForm (halfShift τ hτ P) Q - logarithmicHalfLineForm (halfShift τ hτ P) Z := by
    have he : (B : RealLineL2) = (Q : RealLineL2) - (Z : RealLineL2) := by
      rw [hZ]
      change (B : RealLineL2) = (Q : RealLineL2) - ((Q : RealLineL2) - (B : RealLineL2))
      abel
    change logarithmicFullForm _ (B : RealLineL2) = logarithmicFullForm _ _ - logarithmicFullForm _ _
    rw [he]
    exact logarithmicFullForm_sub_right hSPE hQE hZE
  -- The forcing shifted past the collar does not see it.
  have hSfB : inner ℂ (halfShift τ hτ f₁) B = 0 := by
    change inner ℂ ((halfShift τ hτ f₁ : LogarithmicHalfLineL2) : RealLineL2) (B : RealLineL2) = 0
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    have hs := (measurePreserving_sub_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae
      ((mem_halfLineL2_iff (f₁ : RealLineL2)).mp f₁.property)
    filter_upwards [halfShift_coeFn τ hτ f₁, hBv, hs] with r h1 h2 h3
    rw [h1, h2]
    by_cases hr : r < τ
    · rw [h3 (by linarith only [hr]), inner_zero_left]
      rfl
    · rw [indicator_of_notMem (s := Iio τ) hr, inner_zero_right]
      rfl
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = logarithmicCausalOperator.adjoint f₁ := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g₂, g₂ = logarithmicCausalOperator.adjoint f₂ := ⟨_, rfl⟩
  have hPg : P = logarithmicCausalOperator g₁ := by rw [hP, hg₁]; rfl
  have hQg : Q = logarithmicCausalOperator g₂ := by rw [hQ, hg₂]; rfl
  have hEQ : logarithmicHalfLineForm (halfShift τ hτ P) Q = inner ℂ (halfShift τ hτ g₁) g₂ := by
    rw [hQs _ hSPE, hPg, halfShift_causal, hg₂]
    exact (logarithmicCausalOperator.adjoint_inner_right _ _).symm
  have hSfQ : inner ℂ (halfShift τ hτ f₁) Q =
      inner ℂ (logarithmicCausalOperator.adjoint (halfShift τ hτ f₁)) g₂ := by
    rw [hQg]
    exact (logarithmicCausalOperator.adjoint_inner_left _ _).symm
  rw [hEsplit, hEQ, hEZ, hSfB, sub_zero, hSfQ]
  refine (inner_sub_left (𝕜 := ℂ) (halfShift τ hτ g₁)
    (logarithmicCausalOperator.adjoint (halfShift τ hτ f₁)) g₂).symm.trans ?_
  -- Pointwise evaluation.
  change inner ℂ (((halfShift τ hτ g₁ : LogarithmicHalfLineL2) : RealLineL2) -
    ((logarithmicCausalOperator.adjoint (halfShift τ hτ f₁) : LogarithmicHalfLineL2) : RealLineL2))
      (g₂ : RealLineL2) = _
  rw [L2.inner_def, ← integral_indicator measurableSet_Ico, ← integral_neg]
  apply integral_congr_ae
  have hg₁' := (measurePreserving_sub_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae
    (logarithmicCausalOperator_adjoint_coeFn f₁)
  filter_upwards [Lp.coeFn_sub ((halfShift τ hτ g₁ : LogarithmicHalfLineL2) : RealLineL2)
      ((logarithmicCausalOperator.adjoint (halfShift τ hτ f₁) : LogarithmicHalfLineL2) : RealLineL2),
    halfShift_coeFn τ hτ g₁, logarithmicCausalOperator_adjoint_coeFn (halfShift τ hτ f₁),
    logarithmicCausalOperator_adjoint_coeFn f₂, hg₁'] with p h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, hg₂, h4, hg₁]
  have hfn : logarithmicBackwardConvolution ((halfShift τ hτ f₁ : LogarithmicHalfLineL2) : RealLineL2) =
      fun q => logarithmicBackwardConvolution (f₁ : RealLineL2) (q - τ) :=
    funext (logarithmicBackwardConvolution_halfShift τ hτ f₁)
  rw [h5, hfn]
  simp only [RCLike.inner_apply]
  by_cases hp0 : 0 ≤ p
  · rw [indicator_of_mem (s := Ici (0 : ℝ)) hp0, indicator_of_mem (s := Ici (0 : ℝ)) hp0]
    by_cases hpτ : p < τ
    · have hn : p - τ ∉ Ici (0 : ℝ) := by
        simpa only [mem_Ici, not_le, sub_neg] using hpτ
      rw [indicator_of_notMem hn, indicator_of_mem (show p ∈ Ico (0 : ℝ) τ from ⟨hp0, hpτ⟩), zero_sub,
        map_neg]
      ring
    · have hm : p - τ ∈ Ici (0 : ℝ) := by
        simpa only [mem_Ici, sub_nonneg] using not_lt.mp hpτ
      rw [indicator_of_mem hm, indicator_of_notMem (s := Ico (0 : ℝ) τ) (fun h => hpτ h.2), sub_self,
        map_zero, mul_zero, neg_zero]
  · rw [indicator_of_notMem (s := Ici (0 : ℝ)) hp0, indicator_of_notMem (s := Ico (0 : ℝ) τ)
      (fun h => hp0 h.1), zero_mul, neg_zero]

/-- **The energy across the collar is linear in the shift.** -/
theorem norm_halfLineForm_shift_green_cut_le (f₁ f₂ : LogarithmicHalfLineL2) (τ : ℝ) (hτ : 0 ≤ τ)
    (B : LogarithmicHalfLineL2) (hB : HasLogarithmicEnergy (B : RealLineL2))
    (hBv : (B : RealLineL2) =ᵐ[volume] (Iio τ).indicator
      ((logarithmicHalfLineGreenOperator f₂ : LogarithmicHalfLineL2) : RealLineL2))
    {A₁ A₂ : ℝ} (h₁ : ∀ᵐ y ∂volume, ‖(f₁ : RealLineL2) y‖ ≤ A₁)
    (h₂ : ∀ᵐ y ∂volume, ‖(f₂ : RealLineL2) y‖ ≤ A₂) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) :
    ‖logarithmicHalfLineForm (halfShift τ hτ (logarithmicHalfLineGreenOperator f₁)) B‖ ≤
      τ * (A₁ * A₂) := by
  rw [halfLineForm_shift_green_cut f₁ f₂ τ hτ B hB hBv, norm_neg]
  have hb : ∀ p ∈ Ico (0 : ℝ) τ, ‖conj (logarithmicBackwardConvolution (f₁ : RealLineL2) (p - τ)) *
      logarithmicBackwardConvolution (f₂ : RealLineL2) p‖ ≤ A₁ * A₂ := fun p _ => by
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (norm_logarithmicBackwardConvolution_le h₁ _)
      (norm_logarithmicBackwardConvolution_le h₂ _) (norm_nonneg _) hA₁
  have hn := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
    (s := Ico (0 : ℝ) τ) (by simp) hb
  rw [Real.volume_real_Ico_of_le hτ, sub_zero] at hn
  linarith only [hn]

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower

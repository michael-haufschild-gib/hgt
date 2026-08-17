import GaloisForLFunctions.HTGeometry.ContextOrderPSDHierarchy

/-!
# Exact visibility threshold for the balanced context anomaly

Uniform attenuation multiplies every off-diagonal coherence by `1 - η`, with visibility loss
`η ∈ [0,1]`. At every context order this file proves an exact transition: the balanced anomalous
kernel becomes positive semidefinite if and only if `η ≥ 1 / (2(r+2))`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Set
open scoped ComplexOrder

noncomputable section

/-- Exact visibility-loss threshold at context order `r+3`. -/
def balancedContextVisibilityThreshold (r : ℕ) : ℝ := 1 / (2 * ((r : ℝ) + 2))

/-- Balanced context kernel after uniform loss of off-diagonal visibility. -/
def visibilityAttenuatedBalancedContextKernel (r : ℕ) (η : Set.Icc (0 : ℝ) 1) :
    Matrix (Fin (r + 3)) (Fin (r + 3)) ℂ :=
  contextOrderKernel ((1 - (η : ℝ)) * balancedContextScale r)

/-- Exact constant-line coefficient after visibility attenuation. -/
theorem visibilityAttenuatedBalancedContext_constantCoefficient (r : ℕ)
    (η : Set.Icc (0 : ℝ) 1) :
    1 - ((Fintype.card (Fin (r + 3)) : ℝ) - 1) *
        ((1 - (η : ℝ)) * balancedContextScale r) =
      (2 * ((r : ℝ) + 2) * (η : ℝ) - 1) / (2 * (r : ℝ) + 3) := by
  simp [balancedContextScale]
  field_simp
  ring

/-- Exact action of the attenuated kernel on the global constant section. -/
theorem visibilityAttenuatedBalancedContext_section_action (r : ℕ)
    (η : Set.Icc (0 : ℝ) 1) :
    visibilityAttenuatedBalancedContextKernel r η *ᵥ
        _root_.HTGeometry.simplexEffectiveSection =
      (((2 * ((r : ℝ) + 2) * (η : ℝ) - 1) / (2 * (r : ℝ) + 3) : ℝ) : ℂ) •
        _root_.HTGeometry.simplexEffectiveSection := by
  rw [visibilityAttenuatedBalancedContextKernel, contextOrderKernel_decomposition,
    visibilityAttenuatedBalancedContext_constantCoefficient]
  let P := _root_.HTGeometry.simplexEffectiveHarmonicProjection (ι := Fin (r + 3))
  let s := _root_.HTGeometry.simplexEffectiveSection (ι := Fin (r + 3))
  have hP : P *ᵥ s = s :=
    _root_.HTGeometry.simplexEffectiveHarmonicProjection_mulVec_section
  have hcomp : (1 - P) *ᵥ s = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hP]
    simp
  change (((((1 + (1 - (η : ℝ)) * balancedContextScale r : ℝ) : ℂ) • (1 - P)) +
      ((((2 * ((r : ℝ) + 2) * (η : ℝ) - 1) / (2 * (r : ℝ) + 3) : ℝ) : ℂ) • P)) *ᵥ s) = _
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hcomp, hP]
  simp [s]

/-- **Exact visibility transition.** The attenuated balanced kernel is PSD exactly at and above
the order-dependent loss threshold. -/
theorem visibilityAttenuatedBalancedContext_posSemidef_iff (r : ℕ)
    (η : Set.Icc (0 : ℝ) 1) :
    (visibilityAttenuatedBalancedContextKernel r η).PosSemidef ↔
      balancedContextVisibilityThreshold r ≤ (η : ℝ) := by
  constructor
  · intro h
    have hq := h.dotProduct_mulVec_nonneg
      (_root_.HTGeometry.simplexEffectiveSection : Fin (r + 3) → ℂ)
    rw [visibilityAttenuatedBalancedContext_section_action] at hq
    simp [dotProduct, _root_.HTGeometry.simplexEffectiveSection] at hq
    have hqR := (Complex.nonneg_iff.mp hq).1
    simp [Complex.mul_re, Complex.div_re, Complex.normSq_apply] at hqR
    have hcard : 0 < (r : ℝ) + 3 := by positivity
    have hden : 0 < 2 * (r : ℝ) + 3 := by positivity
    have hquotient :
        (2 * ((r : ℝ) + 2) * (η : ℝ) - 1) * (2 * (r : ℝ) + 3) /
            ((2 * (r : ℝ) + 3) * (2 * (r : ℝ) + 3)) =
          (2 * ((r : ℝ) + 2) * (η : ℝ) - 1) / (2 * (r : ℝ) + 3) := by
      field_simp
    rw [hquotient] at hqR
    have hcoef : 0 ≤ (2 * ((r : ℝ) + 2) * (η : ℝ) - 1) / (2 * (r : ℝ) + 3) := by
      by_contra hn
      have hneg : (2 * ((r : ℝ) + 2) * (η : ℝ) - 1) / (2 * (r : ℝ) + 3) < 0 :=
        lt_of_not_ge hn
      exact (not_lt_of_ge hqR) (mul_neg_of_pos_of_neg hcard hneg)
    have hnum : 0 ≤ 2 * ((r : ℝ) + 2) * (η : ℝ) - 1 := by
      rcases div_nonneg_iff.mp hcoef with hpos | hneg
      · exact hpos.1
      · exfalso
        linarith [hneg.2]
    rw [balancedContextVisibilityThreshold]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  · intro hη
    rw [visibilityAttenuatedBalancedContextKernel, contextOrderKernel_decomposition,
      visibilityAttenuatedBalancedContext_constantCoefficient]
    apply Matrix.PosSemidef.add
    · apply _root_.HTGeometry.one_sub_simplexEffectiveHarmonicProjection_posSemidef.smul
      rw [Complex.nonneg_iff]
      refine ⟨?_, by simp⟩
      have hη1 : (η : ℝ) ≤ 1 := η.property.2
      have hs := balancedContextScale_nonneg r
      have ht : 0 ≤ (1 - (η : ℝ)) * balancedContextScale r :=
        mul_nonneg (sub_nonneg.mpr hη1) hs
      norm_num
      linarith
    · apply _root_.HTGeometry.simplexEffectiveHarmonicProjection_posSemidef.smul
      rw [Complex.nonneg_iff]
      refine ⟨?_, by simp only [Complex.ofReal_im]⟩
      rw [balancedContextVisibilityThreshold] at hη
      have hden : 0 < 2 * (r : ℝ) + 3 := by positivity
      apply div_nonneg
      · have hr : 0 < (r : ℝ) + 2 := by positivity
        apply (div_le_iff₀ (by positivity)).mp at hη
        nlinarith
      · positivity

end

end GaloisForLFunctions.HTGeometry

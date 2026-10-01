import GaloisForLFunctions.RHTower.ThetaTemperedCompactReconstruction

/-!
# Canonical signed coefficients of actual Xi-kernel localizers

Every original Xi-kernel functional has unique finite signed Dirac-jet
coordinates at each real point, indexed by its actual Xi multiplicity.
The coordinates are independent of the admitted isolating cutoff and give
the exact double finite derivative sum on every compact original test.
-/

noncomputable section

open Set
open scoped BigOperators SchwartzMap

namespace RHTower

/-- The finite combination of original signed jets below the actual Xi multiplicity. -/
def thetaXiFiniteJetCombination (t : ℝ) (a : Fin (thetaRealXiMultiplicity t) → ℂ) :
    𝓢'(ℝ, ℂ) :=
  ∑ r, a r • thetaRealDiracJet t r

theorem thetaXiFiniteJetCombination_apply (t : ℝ)
    (a : Fin (thetaRealXiMultiplicity t) → ℂ) (φ : 𝓢(ℝ, ℂ)) :
    thetaXiFiniteJetCombination t a φ =
      ∑ r, a r * ((-1 : ℂ) ^ (r : ℕ) * iteratedDeriv r (φ : ℝ → ℂ) t) := by
  simp only [thetaXiFiniteJetCombination, sum_apply, smul_apply,
    thetaRealDiracJet_apply, smul_eq_mul]

theorem thetaXiFiniteJetCombination_injective (t : ℝ) :
    Function.Injective (thetaXiFiniteJetCombination t) := by
  intro a b h
  apply LinearIndependent.fintypeLinearCombination_injective
    (thetaRealDiracJet_fin_linearIndependent t (thetaRealXiMultiplicity t))
  simpa only [Fintype.linearCombination_apply, thetaXiFiniteJetCombination] using h

/-- Exact finite-span membership, with uniqueness also at multiplicity zero. -/
theorem thetaXiTemperedLowerJetSpan_mem_iff_existsUniqueCoefficients
    (Q : 𝓢'(ℝ, ℂ)) (t : ℝ) :
    Q ∈ thetaXiTemperedLowerJetSpan t ↔
      ∃! a : Fin (thetaRealXiMultiplicity t) → ℂ, thetaXiFiniteJetCombination t a = Q := by
  constructor
  · intro hQ
    change Q ∈ Submodule.span ℂ (range
      (fun r : Fin (thetaRealXiMultiplicity t) => thetaRealDiracJet t r)) at hQ
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hQ
    refine ⟨a, ha, fun b hb => ?_⟩
    exact thetaXiFiniteJetCombination_injective t (hb.trans ha.symm)
  · rintro ⟨a, ha, _⟩
    change Q ∈ Submodule.span ℂ (range
      (fun r : Fin (thetaRealXiMultiplicity t) => thetaRealDiracJet t r))
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨a, ha⟩

/-- An original Xi-kernel functional supplies its own unique local coordinates. -/
theorem thetaXiTemperedLocalization_existsUniqueCoefficients
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) :
    ∃! a : Fin (thetaRealXiMultiplicity t) → ℂ,
      thetaXiFiniteJetCombination t a = thetaXiTemperedLocalization t Q :=
  (thetaXiTemperedLowerJetSpan_mem_iff_existsUniqueCoefficients _ t).mp
    (thetaXiTemperedLocalization_mem_lowerJetSpan Q hQ t)

/-- Canonical coordinates chosen only after existence and uniqueness have been proved. -/
def thetaXiTemperedLocalCoefficients
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) :
    Fin (thetaRealXiMultiplicity t) → ℂ :=
  Classical.choose (thetaXiTemperedLocalization_existsUniqueCoefficients Q hQ t).exists

theorem thetaXiTemperedLocalCoefficients_spec
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) :
    thetaXiFiniteJetCombination t (thetaXiTemperedLocalCoefficients Q hQ t) =
      thetaXiTemperedLocalization t Q :=
  Classical.choose_spec (thetaXiTemperedLocalization_existsUniqueCoefficients Q hQ t).exists

theorem thetaXiTemperedLocalCoefficients_unique
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ)
    (a : Fin (thetaRealXiMultiplicity t) → ℂ)
    (ha : thetaXiFiniteJetCombination t a = thetaXiTemperedLocalization t Q) :
    a = thetaXiTemperedLocalCoefficients Q hQ t :=
  thetaXiFiniteJetCombination_injective t
    (ha.trans (thetaXiTemperedLocalCoefficients_spec Q hQ t).symm)

/-- The same canonical coefficients represent every admitted isolating cutoff. -/
theorem thetaXiTemperedLocalCoefficients_spec_of_cutoff
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) (χ : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (hiso : ∀ x ∈ tsupport (χ : ℝ → ℂ), thetaXiRealSymbol x = 0 → x = t)
    (hone : ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → χ x = 1) :
    thetaXiFiniteJetCombination t (thetaXiTemperedLocalCoefficients Q hQ t) =
      thetaTemperedLocalize χ Q :=
  (thetaXiTemperedLocalCoefficients_spec Q hQ t).trans
    (thetaXiTemperedLocalization_eq_localize Q hQ t χ hχ hiso hone)

/-- Every coefficient representation from such a cutoff is the proved canonical one. -/
theorem thetaXiTemperedLocalCoefficients_unique_of_cutoff
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) (χ : 𝓢(ℝ, ℂ))
    (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (hiso : ∀ x ∈ tsupport (χ : ℝ → ℂ), thetaXiRealSymbol x = 0 → x = t)
    (hone : ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → χ x = 1)
    (a : Fin (thetaRealXiMultiplicity t) → ℂ)
    (ha : thetaXiFiniteJetCombination t a = thetaTemperedLocalize χ Q) :
    a = thetaXiTemperedLocalCoefficients Q hQ t :=
  thetaXiTemperedLocalCoefficients_unique Q hQ t a
    (ha.trans (thetaXiTemperedLocalization_eq_localize Q hQ t χ hχ hiso hone).symm)

/-- Literal signed derivative formula on ALL original Schwartz tests. -/
theorem thetaXiTemperedLocalization_apply_coefficients
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0) (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    thetaXiTemperedLocalization t Q φ =
      ∑ r, thetaXiTemperedLocalCoefficients Q hQ t r *
        ((-1 : ℂ) ^ (r : ℕ) * iteratedDeriv r (φ : ℝ → ℂ) t) := by
  rw [← thetaXiTemperedLocalCoefficients_spec Q hQ t]
  exact thetaXiFiniteJetCombination_apply t _ φ

/-- Exact double finite sum for any finite set covering the actual compact-test zeros. -/
theorem thetaXiTemperedKernel_compact_coefficients_of_cover
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0)
    (W : Finset ℝ) (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ))
    (hcover : ∀ t ∈ tsupport (φ : ℝ → ℂ), thetaXiRealSymbol t = 0 → t ∈ W) :
    Q φ = ∑ t ∈ W, ∑ r, thetaXiTemperedLocalCoefficients Q hQ t r *
      ((-1 : ℂ) ^ (r : ℕ) * iteratedDeriv r (φ : ℝ → ℂ) t) := by
  rw [thetaXiTemperedKernel_compact_reconstruction_of_cover Q hQ W φ hφ hcover]
  apply Finset.sum_congr rfl
  intro t _
  exact thetaXiTemperedLocalization_apply_coefficients Q hQ t φ

/-- Every compact original test reconstructs over its own actual finite Xi-zero set. -/
theorem thetaXiTemperedKernel_compact_coefficients
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0)
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    Q φ = ∑ t ∈ thetaXiCompactTestZeros φ hφ, ∑ r,
      thetaXiTemperedLocalCoefficients Q hQ t r *
        ((-1 : ℂ) ^ (r : ℕ) * iteratedDeriv r (φ : ℝ → ℂ) t) := by
  rw [thetaXiTemperedKernel_compact_reconstruction Q hQ φ hφ]
  apply Finset.sum_congr rfl
  intro t _
  exact thetaXiTemperedLocalization_apply_coefficients Q hQ t φ

end RHTower

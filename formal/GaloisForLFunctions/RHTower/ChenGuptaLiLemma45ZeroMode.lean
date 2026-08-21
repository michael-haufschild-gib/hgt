/-
# Chen--Gupta--Li Lemma 4.5 zero-frequency character reduction

At the zero vector in CGL's three-dimensional Poisson expansion, each
residue coordinate factors into a complete Dirichlet-character correlation.
Exact character orthogonality therefore leaves only triples whose three rows
carry one character.  This is the precise finite reduction used before the
source applies same-character ordinate spacing and Lemma 4.3 decay.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45OffDiagonalSplit
import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterOrthogonality

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- Complete complex character orthogonality at CGL's literal positive
modulus, rather than the predecessor-index convention used by the reusable
packet layer. -/
theorem cglLemma45ZeroModeCharacterOrthogonality
    (Q : CGLPositiveModulus) (chi psi : DirichletCharacter ℂ Q.value) :
    ∑ a : ZMod Q.value, chi a * (starRingEnd ℂ) (psi a) =
      if chi = psi then (Q.value.totient : ℂ) else 0 := by
  rcases Q with ⟨(_ | q), hq⟩
  · simp at hq
  · simpa using cgl_sum_character_mul_conj_character q chi psi

/-- The analytic zero-frequency factor of one CGL Poisson coordinate. -/
def cglLemma45ZeroModePairAmplitude (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) : ℂ :=
  (cglAffineFourierScale N Q : ℂ) *
    𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) 0

/-- At zero frequency, one CGL character-Poisson coordinate splits exactly
into its character factor and analytic Fourier factor. -/
theorem cglLemma45CharacterPairFourierTerm_zero
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (chi psi : DirichletCharacter ℂ Q.value) (t : ℝ) (a : ZMod Q.value) :
    cglLemma45CharacterPairFourierTerm w N Q chi psi t a 0 =
      chi a * (starRingEnd ℂ) (psi a) * cglLemma45ZeroModePairAmplitude w N Q t := by
  simp [cglLemma45CharacterPairFourierTerm, cglLemma45ZeroModePairAmplitude]

/-- Product of CGL's three complete zero-frequency character correlations. -/
def cglLemma45ZeroModeTripleCharacterFactor (Q : CGLPositiveModulus)
    (chi₁ psi₁ chi₂ psi₂ chi₃ psi₃ : DirichletCharacter ℂ Q.value) : ℂ :=
  (∑ a : ZMod Q.value, chi₁ a * (starRingEnd ℂ) (psi₁ a)) *
    (∑ a : ZMod Q.value, chi₂ a * (starRingEnd ℂ) (psi₂ a)) *
      (∑ a : ZMod Q.value, chi₃ a * (starRingEnd ℂ) (psi₃ a))

/-- The corresponding product of the three zero-frequency Fourier factors. -/
def cglLemma45ZeroModeTripleAnalyticAmplitude (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t₁ t₂ t₃ : ℝ) : ℂ :=
  cglLemma45ZeroModePairAmplitude w N Q t₁ * cglLemma45ZeroModePairAmplitude w N Q t₂ *
    cglLemma45ZeroModePairAmplitude w N Q t₃

/-- **CGL Lemma 4.5, zero-frequency residue factorization.** The three
complete residue sums are exactly the product of the three character
correlations and the three analytic zero-frequency factors. -/
theorem cglLemma45_tripleResidue_zeroMode_eq_characterFactor_mul_analyticAmplitude
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (chi₁ psi₁ chi₂ psi₂ chi₃ psi₃ : DirichletCharacter ℂ Q.value)
    (t₁ t₂ t₃ : ℝ) :
    ∑ a₁ : ZMod Q.value, ∑ a₂ : ZMod Q.value, ∑ a₃ : ZMod Q.value,
      cglLemma45TripleFrequencyTerm w N Q chi₁ psi₁ chi₂ psi₂ chi₃ psi₃
        t₁ t₂ t₃ a₁ a₂ a₃ 0 =
      cglLemma45ZeroModeTripleCharacterFactor Q chi₁ psi₁ chi₂ psi₂ chi₃ psi₃ *
        cglLemma45ZeroModeTripleAnalyticAmplitude w N Q t₁ t₂ t₃ := by
  let f₁ : ZMod Q.value → ℂ := fun a => chi₁ a * (starRingEnd ℂ) (psi₁ a)
  let f₂ : ZMod Q.value → ℂ := fun a => chi₂ a * (starRingEnd ℂ) (psi₂ a)
  let f₃ : ZMod Q.value → ℂ := fun a => chi₃ a * (starRingEnd ℂ) (psi₃ a)
  let A₁ := cglLemma45ZeroModePairAmplitude w N Q t₁
  let A₂ := cglLemma45ZeroModePairAmplitude w N Q t₂
  let A₃ := cglLemma45ZeroModePairAmplitude w N Q t₃
  have hterm : ∀ a₁ a₂ a₃ : ZMod Q.value,
      cglLemma45TripleFrequencyTerm w N Q chi₁ psi₁ chi₂ psi₂ chi₃ psi₃
          t₁ t₂ t₃ a₁ a₂ a₃ 0 =
        f₁ a₁ * A₁ * (f₂ a₂ * A₂) * (f₃ a₃ * A₃) := by
    intro a₁ a₂ a₃
    simp [cglLemma45TripleFrequencyTerm, cglLemma45CharacterPairFourierTerm_zero,
      f₁, f₂, f₃, A₁, A₂, A₃]
  simp_rw [hterm]
  change (∑ a₁ : ZMod Q.value, ∑ a₂ : ZMod Q.value, ∑ a₃ : ZMod Q.value,
      f₁ a₁ * A₁ * (f₂ a₂ * A₂) * (f₃ a₃ * A₃)) =
    (∑ a : ZMod Q.value, f₁ a) * (∑ a : ZMod Q.value, f₂ a) *
      (∑ a : ZMod Q.value, f₃ a) * (A₁ * A₂ * A₃)
  have hFG : (∑ a : ZMod Q.value, f₁ a) * (∑ b : ZMod Q.value, f₂ b) =
      ∑ a : ZMod Q.value, ∑ b : ZMod Q.value, f₁ a * f₂ b := by
    rw [Finset.sum_mul_sum]
  have hFGH : (∑ a : ZMod Q.value, f₁ a) * (∑ b : ZMod Q.value, f₂ b) *
      (∑ c : ZMod Q.value, f₃ c) =
      ∑ a : ZMod Q.value, ∑ b : ZMod Q.value, ∑ c : ZMod Q.value,
        f₁ a * f₂ b * f₃ c := by
    rw [hFG]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_mul_sum]
  have hMult : (∑ a : ZMod Q.value, ∑ b : ZMod Q.value, ∑ c : ZMod Q.value,
      f₁ a * f₂ b * f₃ c) * (A₁ * A₂ * A₃) =
      ∑ a : ZMod Q.value, ∑ b : ZMod Q.value, ∑ c : ZMod Q.value,
        (f₁ a * f₂ b * f₃ c) * (A₁ * A₂ * A₃) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_mul]
  symm
  calc
    _ = ((∑ a : ZMod Q.value, f₁ a) * (∑ b : ZMod Q.value, f₂ b) *
        (∑ c : ZMod Q.value, f₃ c)) * (A₁ * A₂ * A₃) := by ring
    _ = (∑ a : ZMod Q.value, ∑ b : ZMod Q.value, ∑ c : ZMod Q.value,
        f₁ a * f₂ b * f₃ c) * (A₁ * A₂ * A₃) := by rw [hFGH]
    _ = ∑ a : ZMod Q.value, ∑ b : ZMod Q.value, ∑ c : ZMod Q.value,
        (f₁ a * f₂ b * f₃ c) * (A₁ * A₂ * A₃) := hMult
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      ring

/-- Orthogonality form of the three zero-frequency character correlations. -/
def cglLemma45ZeroModeTripleCharacterIndicator (Q : CGLPositiveModulus)
    (chi₁ psi₁ chi₂ psi₂ chi₃ psi₃ : DirichletCharacter ℂ Q.value) : ℂ :=
  (if chi₁ = psi₁ then (Q.value.totient : ℂ) else 0) *
    (if chi₂ = psi₂ then (Q.value.totient : ℂ) else 0) *
      (if chi₃ = psi₃ then (Q.value.totient : ℂ) else 0)

/-- Exact character-orthogonality rewrite of CGL's triple zero-mode factor. -/
theorem cglLemma45ZeroModeTripleCharacterFactor_eq_indicator
    (Q : CGLPositiveModulus) (chi₁ psi₁ chi₂ psi₂ chi₃ psi₃ :
      DirichletCharacter ℂ Q.value) :
    cglLemma45ZeroModeTripleCharacterFactor Q chi₁ psi₁ chi₂ psi₂ chi₃ psi₃ =
      cglLemma45ZeroModeTripleCharacterIndicator Q chi₁ psi₁ chi₂ psi₂ chi₃ psi₃ := by
  unfold cglLemma45ZeroModeTripleCharacterFactor cglLemma45ZeroModeTripleCharacterIndicator
  rw [cglLemma45ZeroModeCharacterOrthogonality Q chi₁ psi₁,
    cglLemma45ZeroModeCharacterOrthogonality Q chi₂ psi₂,
    cglLemma45ZeroModeCharacterOrthogonality Q chi₃ psi₃]

/-- CGL's zero-frequency contribution of one non-all-equal row triple after
the complete residue sums have been carried out. -/
def cglLemma45ZeroModeRowTerm (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value)
    (rst : Fin R × Fin R × Fin R) : ℂ :=
  cglLemma45ZeroModeTripleCharacterFactor Q
      (rows rst.1).character (rows rst.2.1).character
      (rows rst.2.1).character (rows rst.2.2).character
      (rows rst.2.2).character (rows rst.1).character *
    cglLemma45ZeroModeTripleAnalyticAmplitude w N Q
      ((rows rst.1).time - (rows rst.2.1).time)
      ((rows rst.2.1).time - (rows rst.2.2).time)
      ((rows rst.2.2).time - (rows rst.1).time)

/-- **CGL Lemma 4.5, exact `Z'` finite reduction.** The zero-frequency
off-diagonal contribution is the finite sum over non-all-equal row triples
of their three orthogonalized character/Fourier factors. -/
theorem cglLemma45OffDiagonalFrequencyTerm_zero_eq_sum_zeroModeRowTerm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    cglLemma45OffDiagonalFrequencyTerm w N Q R rows 0 =
      ∑ rst ∈ (cglCharacterDyadicGramCubicIndexSet R).filter
        (fun rst => ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2)),
        cglLemma45ZeroModeRowTerm w N Q R rows rst := by
  unfold cglLemma45OffDiagonalFrequencyTerm
  dsimp only [cglLemma45OffDiagonalFrequencyIndex]
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro rst hrst
  exact cglLemma45_tripleResidue_zeroMode_eq_characterFactor_mul_analyticAmplitude
    w N Q
    (rows rst.1).character (rows rst.2.1).character
    (rows rst.2.1).character (rows rst.2.2).character
    (rows rst.2.2).character (rows rst.1).character
    ((rows rst.1).time - (rows rst.2.1).time)
    ((rows rst.2.1).time - (rows rst.2.2).time)
    ((rows rst.2.2).time - (rows rst.1).time)

end RHTower

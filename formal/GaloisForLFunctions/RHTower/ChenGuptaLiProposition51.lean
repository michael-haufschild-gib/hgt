/-
# Chen--Gupta--Li Proposition 5.1

The source splits its nonzero three-frequency total into `S₁`, `S₂`, and
`S₃`.  This module begins the literal `S₁` component: frequencies with exactly
one nonzero coordinate.  Subsequent sections prove its character reduction and
all-order Fourier decay estimate.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The three-dimensional Poisson frequencies with exactly one nonzero
coordinate: the source carrier of CGL's component `S₁`. -/
def cglProposition51S1Frequency (m : (ℤ × ℤ) × ℤ) : Prop :=
  (m.1.1 ≠ 0 ∧ m.1.2 = 0 ∧ m.2 = 0) ∨
    (m.1.1 = 0 ∧ m.1.2 ≠ 0 ∧ m.2 = 0) ∨
      (m.1.1 = 0 ∧ m.1.2 = 0 ∧ m.2 ≠ 0)

/-- The literal `S₁` total before the analytic estimate of CGL Proposition 5.1. -/
noncomputable def cglProposition51S1
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) : ℂ :=
  ∑' m : {m : (ℤ × ℤ) × ℤ // cglProposition51S1Frequency m},
    cglLemma45OffDiagonalFrequencyTerm w N Q R rows m

/-- Every source `S₁` frequency is nonzero in the full `Z³` carrier. -/
theorem cglProposition51S1Frequency_nonzero
    (m : {m : (ℤ × ℤ) × ℤ // cglProposition51S1Frequency m}) :
    m.val ≠ 0 := by
  rintro hzero
  have hfirst : m.val.1.1 = 0 := by
    simpa using congrArg (fun x : (ℤ × ℤ) × ℤ => x.1.1) hzero
  have hsecond : m.val.1.2 = 0 := by
    simpa using congrArg (fun x : (ℤ × ℤ) × ℤ => x.1.2) hzero
  have hthird : m.val.2 = 0 := by
    simpa using congrArg (fun x : (ℤ × ℤ) × ℤ => x.2) hzero
  rcases m.2 with h | h | h
  · exact h.1 hfirst
  · exact h.2.1 hsecond
  · exact h.2.2 hthird

/-- The `S₁` frequency subtype maps canonically into the nonzero-frequency
carrier used in CGL Lemma 4.5. -/
def cglProposition51S1ToNonzeroFrequency
    (m : {m : (ℤ × ℤ) × ℤ // cglProposition51S1Frequency m}) :
    {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))} :=
  ⟨m.val, by simpa using cglProposition51S1Frequency_nonzero m⟩

/-- One representative axis of the source `S₁` carrier.  The other two are
obtained by cyclically permuting the three Poisson coordinates. -/
def cglProposition51AxialFrequencyVector (m : ℤ) : (ℤ × ℤ) × ℤ := ((0, 0), m)

/-- The sole nonzero-coordinate character sum after the two zero-coordinate
correlations have been factored out. -/
def cglProposition51AxialTwistedCharacterFactor (Q : CGLPositiveModulus)
    (chi psi : DirichletCharacter ℂ Q.value) (m : ℤ) : ℂ :=
  ∑ a : ZMod Q.value,
    chi a * (starRingEnd ℂ) (psi a) * ZMod.stdAddChar (a * (m : ZMod Q.value))

/-- The analytic part of one axial `S₁` frequency: two zero-frequency
Fourier factors and the remaining nonzero-frequency Fourier factor. -/
def cglProposition51AxialAnalyticAmplitude (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t₁ t₂ t₃ : ℝ) (m : ℤ) : ℂ :=
  cglLemma45ZeroModePairAmplitude w N Q t₁ *
    cglLemma45ZeroModePairAmplitude w N Q t₂ *
      ((cglAffineFourierScale N Q : ℂ) *
        𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t₃ : ℝ → ℂ)
          (cglAffineFourierScale N Q * (m : ℝ)))

/-- Exact finite residue factorization on an axial `S₁` frequency. -/
theorem cglProposition51_tripleResidue_axial_eq_characterFactors_mul_analyticAmplitude
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (chi₁ psi₁ chi₂ psi₂ chi₃ psi₃ : DirichletCharacter ℂ Q.value)
    (t₁ t₂ t₃ : ℝ) (m : ℤ) :
    ∑ a₁ : ZMod Q.value, ∑ a₂ : ZMod Q.value, ∑ a₃ : ZMod Q.value,
      cglLemma45TripleFrequencyTerm w N Q chi₁ psi₁ chi₂ psi₂ chi₃ psi₃
        t₁ t₂ t₃ a₁ a₂ a₃ (cglProposition51AxialFrequencyVector m) =
      (∑ a : ZMod Q.value, chi₁ a * (starRingEnd ℂ) (psi₁ a)) *
        (∑ a : ZMod Q.value, chi₂ a * (starRingEnd ℂ) (psi₂ a)) *
          cglProposition51AxialTwistedCharacterFactor Q chi₃ psi₃ m *
            cglProposition51AxialAnalyticAmplitude w N Q t₁ t₂ t₃ m := by
  let f₁ : ZMod Q.value → ℂ := fun a => chi₁ a * (starRingEnd ℂ) (psi₁ a)
  let f₂ : ZMod Q.value → ℂ := fun a => chi₂ a * (starRingEnd ℂ) (psi₂ a)
  let f₃ : ZMod Q.value → ℂ := fun a =>
    chi₃ a * (starRingEnd ℂ) (psi₃ a) * ZMod.stdAddChar (a * (m : ZMod Q.value))
  let A₁ := cglLemma45ZeroModePairAmplitude w N Q t₁
  let A₂ := cglLemma45ZeroModePairAmplitude w N Q t₂
  let A₃ : ℂ := (cglAffineFourierScale N Q : ℂ) *
    𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t₃ : ℝ → ℂ)
      (cglAffineFourierScale N Q * (m : ℝ))
  have hterm : ∀ a₁ a₂ a₃ : ZMod Q.value,
      cglLemma45TripleFrequencyTerm w N Q chi₁ psi₁ chi₂ psi₂ chi₃ psi₃
          t₁ t₂ t₃ a₁ a₂ a₃ (cglProposition51AxialFrequencyVector m) =
        f₁ a₁ * A₁ * (f₂ a₂ * A₂) * (f₃ a₃ * A₃) := by
    intro a₁ a₂ a₃
    simp only [cglLemma45TripleFrequencyTerm, cglProposition51AxialFrequencyVector]
    rw [cglLemma45CharacterPairFourierTerm_zero,
      cglLemma45CharacterPairFourierTerm_zero]
    unfold f₁ f₂ f₃ A₁ A₂ A₃
    unfold cglLemma45CharacterPairFourierTerm
    ring
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

/-- CGL Proposition 5.1's axial residue reduction: two zero-frequency
coordinates force their adjacent character pairs to agree. -/
theorem cglProposition51_tripleResidue_axial_eq_orthogonalized
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (chi₁ psi₁ chi₂ psi₂ chi₃ psi₃ : DirichletCharacter ℂ Q.value)
    (t₁ t₂ t₃ : ℝ) (m : ℤ) :
    ∑ a₁ : ZMod Q.value, ∑ a₂ : ZMod Q.value, ∑ a₃ : ZMod Q.value,
      cglLemma45TripleFrequencyTerm w N Q chi₁ psi₁ chi₂ psi₂ chi₃ psi₃
        t₁ t₂ t₃ a₁ a₂ a₃ (cglProposition51AxialFrequencyVector m) =
      (if chi₁ = psi₁ then (Q.value.totient : ℂ) else 0) *
        (if chi₂ = psi₂ then (Q.value.totient : ℂ) else 0) *
          cglProposition51AxialTwistedCharacterFactor Q chi₃ psi₃ m *
            cglProposition51AxialAnalyticAmplitude w N Q t₁ t₂ t₃ m := by
  rw [cglProposition51_tripleResidue_axial_eq_characterFactors_mul_analyticAmplitude]
  rw [cglLemma45ZeroModeCharacterOrthogonality Q chi₁ psi₁,
    cglLemma45ZeroModeCharacterOrthogonality Q chi₂ psi₂]

end RHTower

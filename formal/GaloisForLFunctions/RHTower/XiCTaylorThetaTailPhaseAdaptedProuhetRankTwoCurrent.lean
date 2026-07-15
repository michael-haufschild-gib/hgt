import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetPacket

/-!
# Fubini identification of the rank-two Haar current

The reflected Haar prefix is a symmetric rank-two source tensor.  This file identifies its
integrated finite-core current with one half of the Hermitian cross current of the two one-variable
value--derivative transform vectors.  The statement is source-generic and keeps the two cross
terms together.
-/

open Complex Real Polynomial MeasureTheory Set

namespace RHTower

noncomputable section

/-- Pointwise algebra behind the rank-two Fubini theorem.  It is stated separately so the measure
proof never expands complex real and imaginary parts. -/
private theorem rankTwoSource_mul_symmetricHermitianPair_eq
    (a₁ a₂ e₁ e₂ : ℝ) (v₁ v₂ d₁ d₂ : ℂ) :
    ((1 / 2 : ℝ) * (a₁ * e₂ + e₁ * a₂)) *
        ((d₁ * (starRingEnd ℂ) v₂).im +
          (d₂ * (starRingEnd ℂ) v₁).im) / 2 =
      (((1 / 2 : ℂ) *
          (((a₁ : ℂ) * d₁) * (starRingEnd ℂ) ((e₂ : ℂ) * v₂) +
            ((e₁ : ℂ) * d₁) * (starRingEnd ℂ) ((a₂ : ℂ) * v₂))).im +
        ((1 / 2 : ℂ) *
          (((a₂ : ℂ) * d₂) * (starRingEnd ℂ) ((e₁ : ℂ) * v₁) +
            ((e₂ : ℂ) * d₂) * (starRingEnd ℂ) ((a₁ : ℂ) * v₁))).im) / 2 := by
  have h₁ : (1 / 2 : ℂ) *
        (((a₁ : ℂ) * d₁) * (starRingEnd ℂ) ((e₂ : ℂ) * v₂) +
          ((e₁ : ℂ) * d₁) * (starRingEnd ℂ) ((a₂ : ℂ) * v₂)) =
      ((((1 / 2 : ℝ) * (a₁ * e₂ + e₁ * a₂) : ℝ) : ℂ) *
        (d₁ * (starRingEnd ℂ) v₂)) := by
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have h₂ : (1 / 2 : ℂ) *
        (((a₂ : ℂ) * d₂) * (starRingEnd ℂ) ((e₁ : ℂ) * v₁) +
          ((e₂ : ℂ) * d₂) * (starRingEnd ℂ) ((a₁ : ℂ) * v₁)) =
      ((((1 / 2 : ℝ) * (a₁ * e₂ + e₁ * a₂) : ℝ) : ℂ) *
        (d₂ * (starRingEnd ℂ) v₁)) := by
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [h₁, h₂]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  ring

/-- Symmetric value--derivative pair current of an arbitrary one-variable complex kernel. -/
def symmetricHermitianPairCurrentKernel
    (V D : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ((D p.1 * (starRingEnd ℂ) (V p.2)).im +
    (D p.2 * (starRingEnd ℂ) (V p.1)).im) / 2

/-- Fubini factorization for a symmetric rank-two real source coupled to an arbitrary symmetric
Hermitian value--derivative pair current. -/
theorem integral_rankTwoSource_mul_symmetricHermitianPairCurrent_eq
    (A E : ℝ → ℝ) (V D : ℝ → ℂ)
    (hAV : IntegrableOn (fun x : ℝ => (A x : ℂ) * V x) (Ioi 0))
    (hAD : IntegrableOn (fun x : ℝ => (A x : ℂ) * D x) (Ioi 0))
    (hEV : IntegrableOn (fun x : ℝ => (E x : ℂ) * V x) (Ioi 0))
    (hED : IntegrableOn (fun x : ℝ => (E x : ℂ) * D x) (Ioi 0)) :
    (∫ p : ℝ × ℝ,
      ((1 / 2 : ℝ) * (A p.1 * E p.2 + E p.1 * A p.2)) *
        symmetricHermitianPairCurrentKernel V D p
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      (1 / 2 : ℝ) * symmetricHermitianCrossCurrentData
        (∫ x : ℝ in Ioi 0,
          (A x : ℂ) * V x)
        (∫ x : ℝ in Ioi 0,
          (A x : ℂ) * D x)
        (∫ x : ℝ in Ioi 0,
          (E x : ℂ) * V x)
        (∫ x : ℝ in Ioi 0,
          (E x : ℂ) * D x) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let aV : ℝ → ℂ := fun x => (A x : ℂ) * V x
  let aD : ℝ → ℂ := fun x => (A x : ℂ) * D x
  let eV : ℝ → ℂ := fun x => (E x : ℂ) * V x
  let eD : ℝ → ℂ := fun x => (E x : ℂ) * D x
  let J : ℝ × ℝ → ℂ := fun p =>
    (1 / 2 : ℂ) *
      (aD p.1 * (starRingEnd ℂ) (eV p.2) +
        eD p.1 * (starRingEnd ℂ) (aV p.2))
  let K : ℝ × ℝ → ℝ := fun p => (J p).im
  have haV : Integrable aV mu := hAV
  have haD : Integrable aD mu := hAD
  have heV : Integrable eV mu := hEV
  have heD : Integrable eD mu := hED
  have heVconj : Integrable (fun x => (starRingEnd ℂ) (eV x)) mu :=
    (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp heV
  have haVconj : Integrable (fun x => (starRingEnd ℂ) (aV x)) mu :=
    (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp haV
  have hADVE : Integrable (fun p : ℝ × ℝ =>
      aD p.1 * (starRingEnd ℂ) (eV p.2)) (mu.prod mu) :=
    haD.mul_prod heVconj
  have hEDVA : Integrable (fun p : ℝ × ℝ =>
      eD p.1 * (starRingEnd ℂ) (aV p.2)) (mu.prod mu) :=
    heD.mul_prod haVconj
  have hJ : Integrable J (mu.prod mu) := by
    dsimp only [J]
    exact (hADVE.add hEDVA).const_mul (1 / 2 : ℂ)
  have hK : Integrable K (mu.prod mu) := hJ.im
  have hswap : (∫ p : ℝ × ℝ, K p.swap ∂mu.prod mu) =
      ∫ p : ℝ × ℝ, K p ∂mu.prod mu :=
    MeasureTheory.integral_prod_swap (μ := mu) (ν := mu) K
  have hsymm :
      (∫ p : ℝ × ℝ, (K p + K p.swap) / 2 ∂mu.prod mu) =
        ∫ p : ℝ × ℝ, K p ∂mu.prod mu := by
    rw [show (fun p : ℝ × ℝ => (K p + K p.swap) / 2) =
        fun p : ℝ × ℝ => (1 / 2 : ℝ) * (K p + K p.swap) by
      funext p
      ring]
    rw [MeasureTheory.integral_const_mul]
    rw [show (∫ a : ℝ × ℝ, K a + K a.swap ∂mu.prod mu) =
        (∫ a : ℝ × ℝ, K a ∂mu.prod mu) +
          ∫ a : ℝ × ℝ, K a.swap ∂mu.prod mu by
      exact integral_add hK hK.swap,
      hswap]
    ring
  have hpoint : (fun p : ℝ × ℝ =>
      ((1 / 2 : ℝ) * (A p.1 * E p.2 + E p.1 * A p.2)) *
        symmetricHermitianPairCurrentKernel V D p) =
      fun p : ℝ × ℝ => (K p + K p.swap) / 2 := by
    funext p
    rcases p with ⟨x, y⟩
    simp only [symmetricHermitianPairCurrentKernel, K, J, aV, aD, eV, eD,
      Prod.swap_prod_mk]
    convert rankTwoSource_mul_symmetricHermitianPair_eq
        (A x) (A y) (E x) (E y)
        (V x) (V y) (D x) (D y) using 1 <;> ring
  rw [hpoint, hsymm]
  have hADVEint :
      (∫ p : ℝ × ℝ, aD p.1 * (starRingEnd ℂ) (eV p.2) ∂mu.prod mu) =
        (∫ x : ℝ, aD x ∂mu) *
          (starRingEnd ℂ) (∫ y : ℝ, eV y ∂mu) := by
    have h := MeasureTheory.integral_prod_mul (μ := mu) (ν := mu)
      aD (fun y => (starRingEnd ℂ) (eV y))
    rw [integral_conj] at h
    exact h
  have hEDVAint :
      (∫ p : ℝ × ℝ, eD p.1 * (starRingEnd ℂ) (aV p.2) ∂mu.prod mu) =
        (∫ x : ℝ, eD x ∂mu) *
          (starRingEnd ℂ) (∫ y : ℝ, aV y ∂mu) := by
    have h := MeasureTheory.integral_prod_mul (μ := mu) (ν := mu)
      eD (fun y => (starRingEnd ℂ) (aV y))
    rw [integral_conj] at h
    exact h
  have hJint : (∫ p : ℝ × ℝ, J p ∂mu.prod mu) =
      (1 / 2 : ℂ) *
        ((∫ x : ℝ, aD x ∂mu) *
            (starRingEnd ℂ) (∫ y : ℝ, eV y ∂mu) +
          (∫ x : ℝ, eD x ∂mu) *
            (starRingEnd ℂ) (∫ y : ℝ, aV y ∂mu)) := by
    dsimp only [J]
    rw [MeasureTheory.integral_const_mul,
      integral_add hADVE hEDVA, hADVEint, hEDVAint]
  have hKint : (∫ p : ℝ × ℝ, K p ∂mu.prod mu) =
      ((1 / 2 : ℂ) *
        ((∫ x : ℝ, aD x ∂mu) *
            (starRingEnd ℂ) (∫ y : ℝ, eV y ∂mu) +
          (∫ x : ℝ, eD x ∂mu) *
            (starRingEnd ℂ) (∫ y : ℝ, aV y ∂mu))).im := by
    rw [← hJint]
    simpa only [K] using integral_im hJ
  rw [hKint]
  dsimp only [aV, aD, eV, eD, mu]
  unfold symmetricHermitianCrossCurrentData
  simp [Complex.mul_im]

/-- Finite-core specialization of the source-generic rank-two Fubini identity. -/
theorem integral_rankTwoSource_mul_xiCTaylorThetaTailCorePairCurrent_eq
    (A E : ℝ → ℝ) (d : ℕ) (z : ℂ)
    (hAV : IntegrableOn (fun x : ℝ => (A x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x) (Ioi 0))
    (hAD : IntegrableOn (fun x : ℝ => (A x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x) (Ioi 0))
    (hEV : IntegrableOn (fun x : ℝ => (E x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x) (Ioi 0))
    (hED : IntegrableOn (fun x : ℝ => (E x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x) (Ioi 0)) :
    (∫ p : ℝ × ℝ,
      ((1 / 2 : ℝ) * (A p.1 * E p.2 + E p.1 * A p.2)) *
        xiCTaylorThetaTailCorePairCurrent d z p
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      (1 / 2 : ℝ) * symmetricHermitianCrossCurrentData
        (∫ x : ℝ in Ioi 0,
          (A x : ℂ) * thetaCuspTailSecondCoreAtom d z x)
        (∫ x : ℝ in Ioi 0,
          (A x : ℂ) * thetaCuspTailSecondCoreAtomDerivative d z x)
        (∫ x : ℝ in Ioi 0,
          (E x : ℂ) * thetaCuspTailSecondCoreAtom d z x)
        (∫ x : ℝ in Ioi 0,
          (E x : ℂ) * thetaCuspTailSecondCoreAtomDerivative d z x) := by
  simpa only [symmetricHermitianPairCurrentKernel,
    xiCTaylorThetaTailCorePairCurrent] using
    integral_rankTwoSource_mul_symmetricHermitianPairCurrent_eq
      A E
      (thetaCuspTailSecondCoreAtom d z)
      (thetaCuspTailSecondCoreAtomDerivative d z)
      hAV hAD hEV hED

end

end RHTower

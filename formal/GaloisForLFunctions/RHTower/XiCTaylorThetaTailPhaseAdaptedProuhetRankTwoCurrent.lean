import GaloisForLFunctions.RHTower.XiCTaylorThetaTailHaarResidualRankTwo
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

/-- Fubini factorization for a symmetric rank-two real source coupled to the symmetric finite-core
pair current. -/
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
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let aV : ℝ → ℂ := fun x => (A x : ℂ) *
    thetaCuspTailSecondCoreAtom d z x
  let aD : ℝ → ℂ := fun x => (A x : ℂ) *
    thetaCuspTailSecondCoreAtomDerivative d z x
  let eV : ℝ → ℂ := fun x => (E x : ℂ) *
    thetaCuspTailSecondCoreAtom d z x
  let eD : ℝ → ℂ := fun x => (E x : ℂ) *
    thetaCuspTailSecondCoreAtomDerivative d z x
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
    rw [integral_add hK hK.swap, hswap]
    ring
  have hpoint : (fun p : ℝ × ℝ =>
      ((1 / 2 : ℝ) * (A p.1 * E p.2 + E p.1 * A p.2)) *
        xiCTaylorThetaTailCorePairCurrent d z p) =
      fun p : ℝ × ℝ => (K p + K p.swap) / 2 := by
    funext p
    rcases p with ⟨x, y⟩
    unfold xiCTaylorThetaTailCorePairCurrent K J aV aD eV eD
    simp only [Prod.fst, Prod.snd, Prod.swap_prod_mk, map_mul,
      Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      zero_sub, mul_zero]
    push_cast
    ring
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

end

end RHTower

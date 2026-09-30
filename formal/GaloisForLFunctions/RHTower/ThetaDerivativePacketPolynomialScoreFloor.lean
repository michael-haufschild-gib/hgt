import GaloisForLFunctions.RHTower.ThetaDerivativePacketScoreMoments
import GaloisForLFunctions.RHTower.ThetaDerivativePacketScoreFloor
import GaloisForLFunctions.RHTower.PrimeArchThetaPolynomialScoreGap
/-!
# Every derivative packet preserves the strict polynomial score floor

The complete pointwise first-atom floor integrates against every polynomial square.  Strict
source slack gives strict integral comparison for each nonzero polynomial.  One common
parameter interval preserves all these inequalities simultaneously.
-/

open MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

private theorem firstAtomSquare_integrable (P : ℝ[X]) :
    IntegrableOn (fun x : ℝ => P.eval (x^2)^2*(x-1)^2*
      thetaCuspBornWittenAmplitude 1 x^2) (Ioi 0) := by
  by_cases hP : P=0
  · subst P
    simp
  · exact Integrable.of_integral_ne_zero
      (integral_thetaCuspFirstAtom_polynomialSquare_pos hP).ne'

/-- A pointwise packet score floor bounds every signed polynomial moment form. -/
theorem thetaDerivativePacketPolynomialScoreGap_ge_firstAtomSquare_of_floor
    (m : ℕ) (t : ℝ) (P : ℝ[X])
    (hfloor : ∀ x : ℝ, 0 ≤ x →
      Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 ≤
        thetaScoreFloorOperator (thetaDerivativePacket m t) x) :
    2 * Real.pi * (∫ x : ℝ in Ioi 0,
      P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) ≤
      thetaDerivativePacketPolynomialScoreGap m t P := by
  have hf := (firstAtomSquare_integrable P).const_mul Real.pi
  have hg := integrableOn_polynomialSquare_mul_thetaDerivativePacket_score m t P
  have hpoint : (fun x : ℝ => Real.pi *
      (P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2)) ≤ᵐ[volume.restrict (Ioi 0)]
      (fun x => P.eval (x ^ 2) ^ 2 * thetaScoreFloorOperator (thetaDerivativePacket m t) x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    calc
      _ = P.eval (x^2)^2 *
          (Real.pi * thetaCuspBornWittenAmplitude 1 x^2*(x-1)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfloor x hx.le) (sq_nonneg _)
  have hi := integral_mono_ae hf hg hpoint
  rw [integral_const_mul] at hi
  rw [thetaDerivativePacketPolynomialScoreGap_eq_integral]
  nlinarith

/-- One common parameter interval preserves every polynomial score floor. -/
theorem exists_thetaDerivativePacket_polynomial_score_floor (m : ℕ) (hm : 0 < m) :
    ∃ ε > 0, ∀ t : ℝ, 0 ≤ t → t < ε → ∀ P : ℝ[X],
      2 * Real.pi * (∫ x : ℝ in Ioi 0,
        P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) ≤
        thetaDerivativePacketPolynomialScoreGap m t P := by
  obtain ⟨ε, hε, hf⟩ := exists_thetaDerivativePacket_score_gt_firstAtomSquare m hm
  exact ⟨ε,hε,fun t ht htε P =>
    thetaDerivativePacketPolynomialScoreGap_ge_firstAtomSquare_of_floor m t P
      (fun x hx => (hf t ht htε x hx).le)⟩
/-- Strict pointwise source slack yields a strict polynomial floor for every nonzero polynomial. -/
theorem thetaDerivativePacketPolynomialScoreGap_gt_firstAtomSquare_of_floor
    (m : ℕ) (t : ℝ) (P : ℝ[X]) (hP : P ≠ 0)
    (hfloor : ∀ x : ℝ, 0 ≤ x →
      Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 <
        thetaScoreFloorOperator (thetaDerivativePacket m t) x) :
    2 * Real.pi * (∫ x : ℝ in Ioi 0,
      P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) <
      thetaDerivativePacketPolynomialScoreGap m t P := by
  let f : ℝ → ℝ := fun x => P.eval (x^2)^2*(x-1)^2*thetaCuspBornWittenAmplitude 1 x^2
  let g : ℝ → ℝ := fun x => P.eval (x^2)^2*thetaScoreFloorOperator (thetaDerivativePacket m t) x
  let d : ℝ → ℝ := fun x => g x-Real.pi*f x
  have hf : IntegrableOn f (Ioi 0) := firstAtomSquare_integrable P
  have hg : IntegrableOn g (Ioi 0) :=
    integrableOn_polynomialSquare_mul_thetaDerivativePacket_score m t P
  have hd : IntegrableOn d (Ioi 0) := hg.sub (hf.const_mul Real.pi)
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f :=
    Eventually.of_forall fun x => by dsimp [f]; positivity
  have hdnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] d := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h := mul_le_mul_of_nonneg_left (hfloor x hx.le).le (sq_nonneg (P.eval (x^2)))
    dsimp [d,g,f]
    nlinarith
  have hsubset : Function.support f ∩ Ioi (0:ℝ) ⊆ Function.support d ∩ Ioi (0:ℝ) := by
    intro x hx
    have hfx : f x ≠ 0 := hx.1
    have hPx : P.eval (x^2) ≠ 0 := by
      intro hzero
      apply hfx
      simp [f,hzero]
    have h := mul_lt_mul_of_pos_left (hfloor x hx.2.le) (sq_pos_of_ne_zero hPx)
    have hdpos : 0 < d x := by
      dsimp [d,g,f]
      nlinarith
    exact ⟨hdpos.ne',hx.2⟩
  have hfpos : 0 < ∫ x : ℝ in Ioi 0, f x :=
    integral_thetaCuspFirstAtom_polynomialSquare_pos hP
  have hdpos : 0 < ∫ x : ℝ in Ioi 0, d x :=
    (setIntegral_pos_iff_support_of_nonneg_ae hdnn hd).2
      ((setIntegral_pos_iff_support_of_nonneg_ae hfnn hf).1 hfpos |>.trans_le
        (measure_mono hsubset))
  change 0 < ∫ x : ℝ in Ioi 0, g x-Real.pi*f x at hdpos
  rw [integral_sub hg (hf.const_mul Real.pi), integral_const_mul] at hdpos
  rw [thetaDerivativePacketPolynomialScoreGap_eq_integral]
  change 2*Real.pi*(∫x:ℝ in Ioi 0,f x) < 2*(∫x:ℝ in Ioi 0,g x)
  nlinarith

/-- One common parameter interval strictly preserves every nonzero polynomial score floor. -/
theorem exists_thetaDerivativePacket_strict_polynomial_score_floor (m : ℕ) (hm : 0 < m) :
    ∃ ε > 0, ∀ t : ℝ, 0 ≤ t → t < ε → ∀ P : ℝ[X], P ≠ 0 →
      2 * Real.pi * (∫ x : ℝ in Ioi 0,
        P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) <
        thetaDerivativePacketPolynomialScoreGap m t P := by
  obtain ⟨ε, hε, hf⟩ := exists_thetaDerivativePacket_score_gt_firstAtomSquare m hm
  exact ⟨ε,hε,fun t ht htε P hP =>
    thetaDerivativePacketPolynomialScoreGap_gt_firstAtomSquare_of_floor m t P hP
      (fun x hx => hf t ht htε x hx)⟩

/-- Every strict polynomial floor and the full original dark-divisor properties coexist
on one common parameter interval. -/
theorem thetaDerivativePacket_dark_divisor_with_polynomial_score_floor (m : ℕ) (hm : 0 < m) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
      (∀ P : ℝ[X], P ≠ 0 →
        2 * Real.pi * (∫ x : ℝ in Ioi 0,
          P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) <
            thetaDerivativePacketPolynomialScoreGap m t P) ∧
      (∀ x : ℝ, 0 ≤ x →
        Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 <
          thetaScoreFloorOperator (thetaDerivativePacket m t) x) ∧
      (∀ x, 0 < thetaDerivativePacket m t x) ∧
      (∀ x, thetaDerivativePacket m t (-x) = thetaDerivativePacket m t x) ∧
      (∃ δ > 0, ∀ x, iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) x ≤ -δ) ∧
      (∀ c : ℝ, Integrable (fun x => Real.exp (c * |x|) * |thetaDerivativePacket m t x|)) ∧
      (∀ j < 4 * m, ∫ x : ℝ, x ^ j * thetaDerivativePacket m t x =
        ∫ x : ℝ, x ^ j * thetaCuspFullSource x) ∧
      (∀ z : ℂ, sourceTransform (thetaDerivativePacketC m t) z = XiC z * (1 + t * z ^ (4 * m))) ∧
      (∀ x : ℝ, analyticOrderAt (sourceTransform (thetaDerivativePacketC m t)) (x : ℂ) =
        analyticOrderAt XiC x) ∧
      (∀ j < 4 * m, sourceTransform (thetaDerivativePacketC m t) (thetaPacketRoot m t j) = 0 ∧
        analyticOrderAt (sourceTransform (thetaDerivativePacketC m t)) (thetaPacketRoot m t j) =
          analyticOrderAt XiC (thetaPacketRoot m t j) + 1 ∧
        (thetaPacketRoot m t j).re ≠ 0 ∧ (thetaPacketRoot m t j).im ≠ 0) := by
  obtain ⟨ε, hε, hpacket⟩ := thetaDerivativePacket_dark_divisor_with_score_floor m hm
  refine ⟨ε, hε, fun t ht htε => ?_⟩
  have h := hpacket t ht htε
  exact ⟨fun P hP =>
    thetaDerivativePacketPolynomialScoreGap_gt_firstAtomSquare_of_floor m t P hP h.1, h⟩

end
end RHTower

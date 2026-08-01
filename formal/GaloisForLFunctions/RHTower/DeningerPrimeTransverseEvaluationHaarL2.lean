import GaloisForLFunctions.RHTower.DeningerPrimeTransverseEvaluationRestriction
import GaloisForLFunctions.RHTower.DeningerPrimeArithmeticHaarL2Green

/-!
# Source-visible mean-zero Haar-L² modes on literal Deninger packets

The finite cyclotomic restriction constructed in
`DeningerPrimeTransverseEvaluationRestriction` supplies a nonconstant complex linear combination
of Frobenius-orbit root evaluations on every literal prime packet.  At least one of its real or
imaginary parts is nonconstant.  Subtracting its normalized Haar average gives a nonzero
continuous mean-zero real function, and full support of Haar measure keeps it nonzero in `L²`.

The theorem records the exact source representation after centering.  Thus the faithful packet
Haar target is not merely known abstractly to contain transverse modes: one such mode is generated
unconditionally by finite cyclotomic evaluation data at every prime.
-/

namespace RHTower

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- **Cyclotomic source reaches nonzero mean-zero Haar energy.**  For every prime, a centered real
or imaginary part of a finite Frobenius-orbit evaluation combination has zero Haar mean and
nonzero image in the literal packet Haar `L²` fibre. -/
theorem deningerPrimeTransverseOrbitEvaluation_exists_nonzero_meanZeroHaarMode
    (p : Nat.Primes) :
    ∃ (c : ZMod (deningerPrimeTransverseCyclotomicStage p) → ℂ)
      (f : C(DeningerPacketFrobeniusQuotient p, ℝ)),
      deningerPacketAv (deningerPrimePacketHaarMeasure p) f = 0 ∧
      deningerPrimePacketContinuousToHaarL2 p f ≠ 0 ∧
      ((∃ a : ℝ, ∀ x, f x =
          (∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
            c j * deningerPrimeTransverseOrbitEvaluation p j x).re - a) ∨
       (∃ a : ℝ, ∀ x, f x =
          (∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
            c j * deningerPrimeTransverseOrbitEvaluation p j x).im - a)) := by
  classical
  obtain ⟨c, x, y, hxy⟩ :=
    deningerPrimeTransverseOrbitEvaluation_exists_nonconstant p
  let F : C(DeningerPacketFrobeniusQuotient p, ℂ) :=
    ⟨fun z => ∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
        c j * deningerPrimeTransverseOrbitEvaluation p j z,
      continuous_finsetSum _ fun j _ =>
        continuous_const.mul
          (deningerPrimeTransverseOrbitEvaluation_continuous p j)⟩
  have hFxy : F x ≠ F y := hxy
  by_cases hre : (F x).re ≠ (F y).re
  · let g : C(DeningerPacketFrobeniusQuotient p, ℝ) :=
      ⟨fun z => (F z).re, Complex.continuous_re.comp F.continuous⟩
    let a : ℝ := deningerPacketAv (deningerPrimePacketHaarMeasure p) g
    let f : C(DeningerPacketFrobeniusQuotient p, ℝ) :=
      g - deningerPacketIncl a
    have havg : deningerPacketAv (deningerPrimePacketHaarMeasure p) f = 0 := by
      change deningerPacketAv (deningerPrimePacketHaarMeasure p)
          (g - deningerPacketIncl a) = 0
      rw [map_sub, deningerPacketAv_incl]
      exact sub_self _
    have hf : f ≠ 0 := by
      intro hf0
      have hpoint := DFunLike.congr_fun hf0 x
      have hpoint' := DFunLike.congr_fun hf0 y
      change (F x).re - a = 0 at hpoint
      change (F y).re - a = 0 at hpoint'
      exact hre (sub_eq_zero.mp hpoint |>.trans (sub_eq_zero.mp hpoint').symm)
    refine ⟨c, f, havg,
      (deningerPrimePacketContinuousToHaarL2_injective p).ne hf, Or.inl ?_⟩
    exact ⟨a, fun z => rfl⟩
  · have him : (F x).im ≠ (F y).im := by
      intro him
      apply hFxy
      apply Complex.ext
      · exact not_ne_iff.mp hre
      · exact him
    let g : C(DeningerPacketFrobeniusQuotient p, ℝ) :=
      ⟨fun z => (F z).im, Complex.continuous_im.comp F.continuous⟩
    let a : ℝ := deningerPacketAv (deningerPrimePacketHaarMeasure p) g
    let f : C(DeningerPacketFrobeniusQuotient p, ℝ) :=
      g - deningerPacketIncl a
    have havg : deningerPacketAv (deningerPrimePacketHaarMeasure p) f = 0 := by
      change deningerPacketAv (deningerPrimePacketHaarMeasure p)
          (g - deningerPacketIncl a) = 0
      rw [map_sub, deningerPacketAv_incl]
      exact sub_self _
    have hf : f ≠ 0 := by
      intro hf0
      have hpoint := DFunLike.congr_fun hf0 x
      have hpoint' := DFunLike.congr_fun hf0 y
      change (F x).im - a = 0 at hpoint
      change (F y).im - a = 0 at hpoint'
      exact him (sub_eq_zero.mp hpoint |>.trans (sub_eq_zero.mp hpoint').symm)
    refine ⟨c, f, havg,
      (deningerPrimePacketContinuousToHaarL2_injective p).ne hf, Or.inr ?_⟩
    exact ⟨a, fun z => rfl⟩

/-- **Literal arithmetic target is reached nontrivially.**  The same source-generated mean-zero
mode remains nonzero after the canonical Haar-`L²` identification with
`Aut((AlgebraicClosure (ZMod p))ˣ) / closure(⟨Frob_p⟩)`. -/
theorem deningerPrimeTransverseOrbitEvaluation_exists_nonzero_arithmeticHaarMode
    (p : Nat.Primes) :
    ∃ (c : ZMod (deningerPrimeTransverseCyclotomicStage p) → ℂ)
      (f : C(DeningerPacketFrobeniusQuotient p, ℝ)),
      deningerPacketAv (deningerPrimePacketHaarMeasure p) f = 0 ∧
      deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p
          (deningerPrimePacketContinuousToHaarL2 p f) ≠ 0 ∧
      ((∃ a : ℝ, ∀ x, f x =
          (∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
            c j * deningerPrimeTransverseOrbitEvaluation p j x).re - a) ∨
       (∃ a : ℝ, ∀ x, f x =
          (∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
            c j * deningerPrimeTransverseOrbitEvaluation p j x).im - a)) := by
  obtain ⟨c, f, havg, hf, hsource⟩ :=
    deningerPrimeTransverseOrbitEvaluation_exists_nonzero_meanZeroHaarMode p
  refine ⟨c, f, havg, ?_, hsource⟩
  intro hzero
  apply hf
  apply (deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p).injective
  simpa using hzero

/-- **Source-generated positive global Green energy.**  Embedding the arithmetic Haar mode at its
prime coordinate gives a literal all-prime arithmetic vector with strictly positive Green
energy. -/
theorem deningerPrimeTransverseOrbitEvaluation_exists_pos_arithmeticGreenEnergy
    (p : Nat.Primes) :
    ∃ (c : ZMod (deningerPrimeTransverseCyclotomicStage p) → ℂ)
      (f : C(DeningerPacketFrobeniusQuotient p, ℝ)),
      deningerPacketAv (deningerPrimePacketHaarMeasure p) f = 0 ∧
      0 < deningerPrimeArithmeticHaarSummedGreenForm
        (lp.single 2 p
          (deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p
            (deningerPrimePacketContinuousToHaarL2 p f)))
        (lp.single 2 p
          (deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p
            (deningerPrimePacketContinuousToHaarL2 p f))) ∧
      ((∃ a : ℝ, ∀ x, f x =
          (∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
            c j * deningerPrimeTransverseOrbitEvaluation p j x).re - a) ∨
       (∃ a : ℝ, ∀ x, f x =
          (∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
            c j * deningerPrimeTransverseOrbitEvaluation p j x).im - a)) := by
  obtain ⟨c, f, havg, hv, hsource⟩ :=
    deningerPrimeTransverseOrbitEvaluation_exists_nonzero_arithmeticHaarMode p
  let v : DeningerPrimeArithmeticHaarL2 p :=
    deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p
      (deningerPrimePacketContinuousToHaarL2 p f)
  let x : DeningerPrimeArithmeticHaarHilbertSum := lp.single 2 p v
  have hx : x ≠ 0 := by
    intro hx0
    have hp := congrArg (fun z : DeningerPrimeArithmeticHaarHilbertSum => z p) hx0
    apply hv
    simpa [x, v] using hp
  have hnonneg :
      0 ≤ deningerPrimeArithmeticHaarSummedGreenForm x x :=
    deningerPrimeArithmeticHaarSummedGreenForm_nonneg x
  have hne :
      deningerPrimeArithmeticHaarSummedGreenForm x x ≠ 0 := by
    intro hzero
    exact hx
      ((deningerPrimeArithmeticHaarSummedGreenForm_self_eq_zero_iff x).mp hzero)
  refine ⟨c, f, havg, ?_, hsource⟩
  change 0 < deningerPrimeArithmeticHaarSummedGreenForm x x
  exact lt_of_le_of_ne hnonneg hne.symm

end

end RHTower

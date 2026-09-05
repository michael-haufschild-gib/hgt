import GaloisForLFunctions.RHTower.L2MellinUnitary
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Independence of equally spaced translations in complex L²

A finite relation becomes an ordinary polynomial in a Fourier character. The roots of
a nonzero polynomial have countable exponential preimage, hence null real-frequency
preimage. Thus no nonzero L² vector admits such a relation. Compact support and smoothness
are unnecessary.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal FourierTransform BigOperators
open RHTower

noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem polynomial_fourierPhase_ne_zero_ae {h : ℝ} (hh : h ≠ 0)
    {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∀ᵐ x : ℝ, p.eval (MellinL2.fourierPhase h x) ≠ 0 := by
  let A : ℝ → ℂ := fun x => ((2 * Real.pi * (h * x) : ℝ) : ℂ) * Complex.I
  have hA : Function.Injective A := by
    intro x y hxy
    have hr : 2 * Real.pi * (h * x) = 2 * Real.pi * (h * y) :=
      Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hxy)
    exact mul_left_cancel₀ hh (mul_left_cancel₀
      (mul_ne_zero (by norm_num) Real.pi_ne_zero) hr)
  have hc := ((Polynomial.finite_setOf_isRoot hp).countable.preimage_cexp).preimage hA
  have hzero : volume {x : ℝ | p.eval (MellinL2.fourierPhase h x) = 0} = 0 := by
    exact hc.measure_zero volume
  apply ae_iff.mpr
  simpa only [not_not] using hzero

private theorem fourierPhase_nat_mul (h x : ℝ) (n : ℕ) :
    MellinL2.fourierPhase ((n : ℝ) * h) x = MellinL2.fourierPhase h x ^ n := by
  have hp := congrArg (fun z : Circle => (z : ℂ))
    (Real.fourierChar.map_nsmul_eq_pow n (h * x))
  simpa only [MellinL2.fourierPhase, nsmul_eq_mul, mul_assoc, Circle.coe_pow] using hp

/-- Distinct equally spaced translations of any nonzero complex L² vector are linearly
independent, without any regularity or compact-support assumption. -/
theorem linearIndependent_arithmetic_L2_translates (n : ℕ) {h : ℝ} (hh : h ≠ 0)
    {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) :
    LinearIndependent ℂ (fun i : Fin n => MellinL2.additiveTranslationUnitary ((i : ℝ) * h) f) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  by_contra hc
  push Not at hc
  obtain ⟨j, hj⟩ := hc
  let p : Polynomial ℂ := Polynomial.ofFn n c
  have hp : p ≠ 0 := by
    intro hz
    have hjz := congrArg (fun q : Polynomial ℂ => q.coeff j) hz
    rw [Polynomial.coeff_zero] at hjz
    exact hj (by simpa only [p, Polynomial.ofFn_coeff_eq_val_of_lt c j.isLt] using hjz)
  let F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 f
  have hF : F ≠ 0 := by
    intro hzero
    apply hf
    exact (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).injective
      (hzero.trans (map_zero _).symm)
  have hsumF : ∑ i : Fin n, c i • MellinL2.fourierPhaseMulUnitary ((i : ℝ) * h) F = 0 := by
    have hh := congrArg (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) hsum
    simp only [map_sum, map_smul, map_zero] at hh
    change (∑ i : Fin n, c i • 𝓕 (MellinL2.additiveTranslationUnitary ((i : ℝ) * h) f)) = 0 at hh
    simp_rw [MellinL2.fourier_additiveTranslation] at hh
    exact hh
  have hsumcoe : ∀ s : Finset (Fin n),
      ((∑ i ∈ s, c i • MellinL2.fourierPhaseMulUnitary ((i : ℝ) * h) F : Lp ℂ 2 volume) : ℝ → ℂ)
        =ᵐ[volume] fun x => (∑ i ∈ s, c i * MellinL2.fourierPhase ((i : ℝ) * h) x) * F x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, zero_mul]
      filter_upwards [Lp.coeFn_zero ℂ 2 volume] with x hx
      exact hx
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • MellinL2.fourierPhaseMulUnitary ((i : ℝ) * h) F)
        (∑ j ∈ s, c j • MellinL2.fourierPhaseMulUnitary ((j : ℝ) * h) F),
        Lp.coeFn_smul (c i) (MellinL2.fourierPhaseMulUnitary ((i : ℝ) * h) F),
        MellinL2.fourierPhaseMulAux_ae ((i : ℝ) * h) F, ih] with x hadd hsmul hphase htail
      rw [hadd]
      change (c i • MellinL2.fourierPhaseMulUnitary ((i : ℝ) * h) F : Lp ℂ 2 volume) x +
        (∑ j ∈ s, c j • MellinL2.fourierPhaseMulUnitary ((j : ℝ) * h) F : Lp ℂ 2 volume) x = _
      rw [hsmul, htail]
      change c i * MellinL2.fourierPhaseMulAux ((i : ℝ) * h) F x + _ = _
      rw [hphase, Finset.sum_insert hi]
      ring
  have heval : ∀ x : ℝ, p.eval (MellinL2.fourierPhase h x) =
      ∑ i : Fin n, c i * MellinL2.fourierPhase ((i : ℝ) * h) x := by
    intro x
    simp only [p, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial, fourierPhase_nat_mul]
  have hz : (fun x => p.eval (MellinL2.fourierPhase h x) * F x) =ᵐ[volume] 0 := by
    simp only [heval]
    exact (hsumcoe Finset.univ).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hsumF)
  apply hF
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hz, polynomial_fourierPhase_ne_zero_ae hh hp] with x hx hn
  exact (mul_eq_zero.mp hx).resolve_left hn

end GaloisForLFunctions.HTGeometry

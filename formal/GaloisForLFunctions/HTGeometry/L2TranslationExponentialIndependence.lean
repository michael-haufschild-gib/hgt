import GaloisForLFunctions.RHTower.L2MellinUnitary
import GaloisForLFunctions.Hurwitz.ExpIndependence
import GaloisForLFunctions.Bottcher.ZeroSet

/-!
# Independence of arbitrary distinct translations in complex L²

The Fourier multiplier of a finite translation relation is the real trace
of an entire exponential sum. Distinct-exponent independence and countable
analytic zero sets replace the arithmetic-grid polynomial argument.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal FourierTransform BigOperators
open RHTower

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A nontrivial combination of distinct Fourier characters has only
countably many real zeros, without any arithmetic condition on its shifts. -/
theorem fourierPhase_sum_zeros_countable {n : ℕ} (a : Fin n → ℝ)
    (ha : Function.Injective a) (c : Fin n → ℂ) (hc : c ≠ 0) :
    {x : ℝ | ∑ i, c i * MellinL2.fourierPhase (a i) x = 0}.Countable := by
  classical
  let β : Fin n → ℂ := fun i => ((2 * Real.pi * a i : ℝ) : ℂ) * Complex.I
  have hβ : Function.Injective β := by
    intro i j hij
    apply ha
    change ((2 * Real.pi * a i : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * a j : ℝ) : ℂ) * Complex.I at hij
    have hr : 2 * Real.pi * a i = 2 * Real.pi * a j :=
      Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hij)
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero) hr
  let G : ℂ → ℂ := fun z => ∑ i, c i * Complex.exp (β i * z)
  have hdiff : Differentiable ℂ G := by
    apply Differentiable.fun_sum
    intro i _
    exact (differentiable_const _).mul
      (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))
  have hex : ∃ z : ℂ, G z ≠ 0 := by
    by_contra h
    push Not at h
    have hsum : (∑ i, c i • fun z : ℂ => Complex.exp (β i * z)) = 0 := by
      funext z
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h z
    have hcoeff := (Fintype.linearIndependent_iff.mp (HurwitzExp.expLin_linearIndependent hβ)) c hsum
    apply hc
    funext i
    exact hcoeff i
  obtain ⟨z, hz⟩ := hex
  have hcount : {z : ℂ | G z = 0}.Countable := by
    simpa only [Set.mem_univ, true_and] using
      Bottcher.analyticOnNhd_zeros_countable
        (hdiff.differentiableOn.analyticOnNhd isOpen_univ)
        isPreconnected_univ (Set.mem_univ z) hz
  have hreal : {x : ℝ | G (x : ℂ) = 0}.Countable :=
    hcount.preimage Complex.ofReal_injective
  have hphase (i : Fin n) (x : ℝ) :
      Complex.exp (β i * (x : ℂ)) = MellinL2.fourierPhase (a i) x := by
    rw [MellinL2.fourierPhase, Real.fourierChar_apply]
    congr 1
    dsimp only [β]
    push_cast
    ring
  simpa only [G, hphase] using hreal

/-- The nontrivial Fourier multiplier of arbitrary distinct shifts is
nonzero almost everywhere; the exceptional set is already countable. -/
theorem fourierPhase_sum_ne_zero_ae {n : ℕ} (a : Fin n → ℝ)
    (ha : Function.Injective a) (c : Fin n → ℂ) (hc : c ≠ 0) :
    ∀ᵐ x : ℝ, ∑ i, c i * MellinL2.fourierPhase (a i) x ≠ 0 := by
  apply ae_iff.mpr
  simpa only [not_not] using (fourierPhase_sum_zeros_countable a ha c hc).measure_zero volume

/-- Distinct translates of any nonzero complex L² vector are linearly
independent. No arithmetic grid, support, or regularity premise is needed. -/
theorem linearIndependent_L2_translates {n : ℕ} (a : Fin n → ℝ)
    (ha : Function.Injective a) {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) :
    LinearIndependent ℂ (fun i : Fin n => MellinL2.additiveTranslationUnitary (a i) f) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  by_cases hc : c = 0
  · simp [hc]
  · exfalso
    let F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 f
    have hF : F ≠ 0 := by
      intro hzero
      apply hf
      exact (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).injective
        (hzero.trans (map_zero _).symm)
    have hsumF : ∑ i, c i • MellinL2.fourierPhaseMulUnitary (a i) F = 0 := by
      have hh := congrArg (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) hsum
      simp only [map_sum, map_smul, map_zero] at hh
      change (∑ i, c i • 𝓕 (MellinL2.additiveTranslationUnitary (a i) f)) = 0 at hh
      simp_rw [MellinL2.fourier_additiveTranslation] at hh
      exact hh
    have hterms (i : Fin n) :
        ((c i • MellinL2.fourierPhaseMulUnitary (a i) F : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => c i * MellinL2.fourierPhase (a i) x * F x := by
      filter_upwards [Lp.coeFn_smul (c i) (MellinL2.fourierPhaseMulUnitary (a i) F),
        MellinL2.fourierPhaseMulAux_ae (a i) F] with x hs hp
      rw [hs]
      change c i * MellinL2.fourierPhaseMulAux (a i) F x = _
      rw [hp]
      ring
    have hcoe :
        ((∑ i, c i • MellinL2.fourierPhaseMulUnitary (a i) F : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => (∑ i, c i * MellinL2.fourierPhase (a i) x) * F x := by
      filter_upwards [Lp.coeFn_finsetSum Finset.univ
        (fun i => c i • MellinL2.fourierPhaseMulUnitary (a i) F), ae_all_iff.mpr hterms] with x hs ht
      calc
        _ = ∑ i, (c i • MellinL2.fourierPhaseMulUnitary (a i) F : Lp ℂ 2 volume) x := by
          simpa only [Finset.sum_apply] using hs
        _ = ∑ i, c i * MellinL2.fourierPhase (a i) x * F x :=
          Finset.sum_congr rfl (fun i _ => ht i)
        _ = _ := (Finset.sum_mul _ _ _).symm
    have hz : (fun x => (∑ i, c i * MellinL2.fourierPhase (a i) x) * F x) =ᵐ[volume] 0 :=
      hcoe.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hsumF)
    apply hF
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hz, fourierPhase_sum_ne_zero_ae a ha c hc] with x hx hn
    exact (mul_eq_zero.mp hx).resolve_left hn

/-- Exact classification of finite translation relations, including the
zero source vector, without an arithmetic-grid assumption. -/
theorem sum_smul_L2_translates_eq_zero_iff {n : ℕ} (a : Fin n → ℝ)
    (ha : Function.Injective a) (c : Fin n → ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (∑ i, c i • MellinL2.additiveTranslationUnitary (a i) f) = 0 ↔ f = 0 ∨ c = 0 := by
  constructor
  · intro h
    by_cases hf : f = 0
    · exact Or.inl hf
    · right
      have hc := (Fintype.linearIndependent_iff.mp (linearIndependent_L2_translates a ha hf)) c h
      funext i
      exact hc i
  · rintro (rfl | rfl) <;> simp

end GaloisForLFunctions.HTGeometry

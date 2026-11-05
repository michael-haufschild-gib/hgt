import GaloisForLFunctions.FrustratedArithmeticDirichletForms.SoftEntryInEveryStageFibre

/-!
# Beyond a finite window the primes pay by sign

The edge-law certificate (`SoftEntryInEveryStageFibre`) pays the primes by size: it bounds
`|P_λ(f)|` by a nonnegative energy and asks the archimedean–polar form `H = W + P` to dominate it.
This module shows that every certificate of that kind dies at a finite window, unconditionally.

* **The archimedean–polar form fails on a real test** (`exists_archPolar_neg`): DZG's failure of the
  archimedean place at a finite aperture is attained by a real test, since real tests decide the
  calibration space.
* **The primes pay by sign** (`primes_pay_by_sign`). There is `A` such that on every window `[−c, c]`,
  `c ≥ A`, one real test `f` has `H(f) < 0`. For every admissible weight system `λ ∈ 𝒜(c)`,
  `0 ≤ W_λ(f) = H(f) − P_λ(f)` forces `P_λ(f) ≤ H(f) < 0`: on `f` the prime part is a strict gain, of
  the same sign for the whole calibration space, and no bound `|P| ≤ E𝒥` with `E ≥ 0` can certify the
  window.

Under RH the failure aperture satisfies `2A ≥ log 2` (DZG); its exact location is open.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower _root_.Zeta23

/-- **The archimedean–polar form is negative on a real test supported in a finite window.** -/
theorem exists_archPolar_neg : ∃ A : ℝ, ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧
    tsupport (fun u => (f u : ℂ)) ⊆ Icc (-A) A ∧
    (weilFullFunctional (fun _ => 0)
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re < 0 := by
  obtain ⟨A, hA⟩ := DimensionZeroGeometryOfSpecZ.exists_not_weilPositiveFullUpTo_zero
  refine ⟨A, ?_⟩
  by_contra h
  push Not at h
  exact hA (realCalibration_subset_calibration A h)

/-- **Beyond a finite window the primes pay by sign.** There is `A` such that on every window
`[−c, c]` with `c ≥ A` a single real test `f` has negative prime part `P_λ(f) < 0` for every
admissible weight system `λ ∈ 𝒜(c)`, and `H(f) < E𝒥(f)` for every `E ≥ 0`. -/
theorem primes_pay_by_sign : ∃ A : ℝ, ∀ c : ℝ, A ≤ c → ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧
    tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c ∧
    (∀ lam ∈ calibration c,
      (weightedPrimePart lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re < 0) ∧
    ∀ E : ℝ, 0 ≤ E → (weilFullFunctional (fun _ => 0)
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re < E * levyEnergy f := by
  obtain ⟨A, f, hf, hfs, hneg⟩ := exists_archPolar_neg
  refine ⟨A, fun c hc => ?_⟩
  have hfs' : tsupport (fun u => (f u : ℂ)) ⊆ Icc (-c) c :=
    hfs.trans (Icc_subset_Icc (neg_le_neg hc) hc)
  refine ⟨f, hf, hfs', fun lam hlam => ?_, fun E hE => ?_⟩
  · have h0 := hlam (fun u => (f u : ℂ)) (Complex.ofRealCLM.contDiff.comp hf) hfs'
    have hsplit := congrArg Complex.re (weilFullFunctional_eq_sub_weightedPrimePart lam
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))))
    rw [Complex.sub_re] at hsplit
    linarith
  · exact lt_of_lt_of_le hneg (mul_nonneg hE (SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' f))

end GaloisForLFunctions.FrustratedArithmeticDirichletForms

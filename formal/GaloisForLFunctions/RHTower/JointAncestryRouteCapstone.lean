import GaloisForLFunctions.RHTower.JointAncestryArithmeticCriterion
import GaloisForLFunctions.RHTower.JointAncestryAbscissaStructure
import GaloisForLFunctions.RHTower.WeilLagFunctionSingleBase

/-!
# Route JAS: the exact remaining content

The dressed-aggregate form of route JAS reduces the Riemann Hypothesis to two statements.

* **Existence** — the `1`-dressed aggregate is positive semidefinite on rational characters
  (`JasDressedPSD 1`).  Equivalently: every zero sum of twisted partial Euler densities on a finite
  prime torus is nonnegative; or, with no zeros at all, every arithmetic Fejér form built from
  `ψ` and the partial sums of `Λ(n)/n` is nonnegative.
* **No chain** — the off-line zeros do not form a chain without a farthest zero
  (`¬ JasOffLineChain`).

Both are consequences of RH, and together they imply RH:

`RH ⟺ JasDressedPSD 1 ∧ ¬ JasOffLineChain`,

and likewise with the vertical or the arithmetic criterion in place of `JasDressedPSD 1`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Under RH every zero copy is critical, so there is no off-line chain. -/
theorem not_jasOffLineChain_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ¬ JasOffLineChain := by
  rintro ⟨⟨q, hq⟩, -⟩
  exact hq (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)

/-- Without RH some zero copy is off the critical line. -/
theorem exists_offLine_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 := by
  by_contra h
  push Not at h
  exact hRH (riemannHypothesis_of_forall_xiZeroCopy_re_eq_half_weilLagFunctionSingleBase h)

/-- A positive semidefinite dressing at `σ ≤ 1` together with the absence of a chain gives RH. -/
theorem riemannHypothesis_of_jasDressedPSD_of_not_chain {σ : ℝ} (hσ : σ ≤ 1)
    (hpsd : JasDressedPSD σ) (hno : ¬ JasOffLineChain) : RiemannHypothesis := by
  by_contra hRH
  rcases riemannHypothesis_or_offLine_chain_of_jasDressedPSD hσ hpsd with h | h
  · exact hRH h
  · exact hno ⟨exists_offLine_of_not_riemannHypothesis hRH, h⟩

/-- **Route JAS capstone.**  RH holds if and only if the `1`-dressed aggregate is positive
semidefinite and the off-line zeros do not form a chain. -/
theorem riemannHypothesis_iff_jasDressedPSD_one_and_not_chain :
    RiemannHypothesis ↔ JasDressedPSD 1 ∧ ¬ JasOffLineChain :=
  ⟨fun hRH => ⟨jasDressedPSD_of_riemannHypothesis hRH (by norm_num),
      not_jasOffLineChain_of_riemannHypothesis hRH⟩,
    fun h => riemannHypothesis_of_jasDressedPSD_of_not_chain le_rfl h.1 h.2⟩

/-- **Capstone, vertical form.** -/
theorem riemannHypothesis_iff_vertical_and_not_chain :
    RiemannHypothesis ↔ (∀ (P : Finset Nat.Primes) (τ : ℝ),
      0 ≤ (jasZeroSumDensity (1 / 2) P (fun i => jasVerticalPoint τ i)).re) ∧
        ¬ JasOffLineChain := by
  constructor
  · intro hRH
    exact ⟨vertical_one_of_riemannHypothesis hRH, not_jasOffLineChain_of_riemannHypothesis hRH⟩
  · rintro ⟨hv, hno⟩
    have hpsd := (jasDressedPSD_iff_vertical (by norm_num : (0 : ℝ) < 1 / 2)).mpr hv
    norm_num at hpsd
    exact riemannHypothesis_of_jasDressedPSD_of_not_chain le_rfl hpsd hno

/-- **Capstone, arithmetic (zero-free) form.** -/
theorem riemannHypothesis_iff_arithmetic_and_not_chain :
    RiemannHypothesis ↔ (∀ (P : Finset Nat.Primes) (K : ℕ) (τ : ℝ),
      0 ≤ (jasArithmeticForm P K τ).re) ∧ ¬ JasOffLineChain := by
  constructor
  · intro hRH
    exact ⟨re_jasArithmeticForm_nonneg_of_riemannHypothesis hRH,
      not_jasOffLineChain_of_riemannHypothesis hRH⟩
  · rintro ⟨ha, hno⟩
    by_contra hRH
    rcases riemannHypothesis_or_chain_of_arithmetic ha with h | h
    · exact hRH h
    · exact hno ⟨exists_offLine_of_not_riemannHypothesis hRH, h⟩

end

end RHTower

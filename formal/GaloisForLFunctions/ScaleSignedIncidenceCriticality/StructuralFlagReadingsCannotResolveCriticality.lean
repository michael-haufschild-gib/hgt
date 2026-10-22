import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.RHTower.NonTemperedShiftedZetaPairCountermodel

/-!
# Structural flag readings cannot resolve criticality

The datum is the shift `a` of the pair `L_a(s) = ζ(s − a) ζ(s + a)`, the property is that the zeros
of `L_a` in the open strip lie on the critical line, and the reading is the list of structural flags
a Selberg-type argument may invoke: nonnegative Dirichlet coefficients, a nonnegative von Mangoldt
weight supported on the prime powers, the functional equation of the completed pair, and polynomial
vertical growth.

All four flags hold for every `|a| ≤ ¼` with the same proofs as for `ζ`
(`RHTower.shiftedPairCoeff_nonneg`, `RHTower.shiftedPairVonMangoldt_nonneg`,
`RHTower.shiftedCompletedPair_one_sub`, `RHTower.exists_norm_shiftedZetaPair_le`), so the reading is
constant on `[−¼, ¼]` (`structuralFlags_eq`), while the property holds at `a = 0` exactly under RH
and fails at `a = ¼`, where Hardy's theorem supplies zeros of real part `¼`
(`RHTower.exists_offLine_zero_shiftedZetaPair'`).

* `not_riemannHypothesis_of_resolves_structuralFlags`: a reading of the structural flags resolves
  criticality only if RH fails — this is the temperedness gate, and what is missing from the flags
  is exactly the Ramanujan ceiling `|Λ(n)| ≤ log n`, which `L_a` violates
  (`RHTower.not_ramanujan_shiftedPairCoeff`).
* `not_riemannHypothesis_of_resolves_flagDerived`: and no quantity computed from the flags does
  better, however elaborate.
-/

open Complex RHTower

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

/-! ### 1. The datum and the property -/

/-- The zeros of the shifted pair in the open strip lie on the critical line. -/
def PairZerosOnLine (a : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → shiftedZetaPair a s = 0 → s.re = 1 / 2

/-- At shift `0` the property is RH: the pair is `ζ²`. -/
theorem pairZerosOnLine_zero_of_riemannHypothesis (hRH : RiemannHypothesis) :
    PairZerosOnLine 0 := by
  intro s hs0 hs1 hzero
  have hz : riemannZeta s = 0 := by
    have h : riemannZeta s * riemannZeta s = 0 := by
      simpa [shiftedZetaPair] using hzero
    rcases mul_eq_zero.mp h with h | h <;> exact h
  refine hRH s hz (fun ⟨n, hn⟩ => ?_) (fun h => ?_)
  · rw [hn] at hs0
    simp only [neg_mul, Complex.neg_re, Complex.mul_re] at hs0
    norm_num at hs0
    nlinarith [hs0, Nat.cast_nonneg (α := ℝ) n]
  · rw [h] at hs1
    norm_num at hs1

/-- At shift `¼` the property fails: Hardy's theorem gives zeros of real part `¼`. -/
theorem not_pairZerosOnLine_quarter : ¬ PairZerosOnLine (1 / 4) := by
  obtain ⟨s, -, hne, hzero, hre⟩ :=
    exists_offLine_zero_shiftedZetaPair' (a := 1 / 4) (by norm_num) 0
  intro h
  exact hne (h s (by rw [hre]; norm_num) (by rw [hre]; norm_num) hzero)

/-! ### 2. The structural flags -/

/-- The structural flags of the pair: nonnegative Dirichlet coefficients; a nonnegative von
Mangoldt weight supported on the prime powers; the functional equation; polynomial vertical
growth. -/
def structuralFlags (a : ℝ) : Prop × Prop × Prop × Prop :=
  ((∀ n : ℕ, 0 ≤ shiftedPairCoeff a n),
    ((∀ n : ℕ, 0 ≤ shiftedPairVonMangoldt a n) ∧
      ∀ n : ℕ, ¬ IsPrimePow n → shiftedPairVonMangoldt a n = 0),
    (∀ s : ℂ, shiftedCompletedPair a (1 - s) = shiftedCompletedPair a s),
    (∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, -1 / 4 ≤ σ → σ ≤ 5 / 4 → 8 ≤ t →
      ‖shiftedZetaPair a ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ (2 : ℝ)))

/-- **The flags are blind to the shift.** Every flag holds for every `|a| ≤ ¼`, so the reading on
`[−¼, ¼]` is the reading of `ζ` itself. -/
theorem structuralFlags_eq {a : ℝ} (ha : |a| ≤ 1 / 4) : structuralFlags a = structuralFlags 0 := by
  have h0 : |(0 : ℝ)| ≤ 1 / 4 := by norm_num
  have f1 : (∀ n : ℕ, 0 ≤ shiftedPairCoeff a n) = (∀ n : ℕ, 0 ≤ shiftedPairCoeff 0 n) :=
    propext (iff_of_true (shiftedPairCoeff_nonneg a) (shiftedPairCoeff_nonneg 0))
  have f2 : ((∀ n : ℕ, 0 ≤ shiftedPairVonMangoldt a n) ∧
        ∀ n : ℕ, ¬ IsPrimePow n → shiftedPairVonMangoldt a n = 0) =
      ((∀ n : ℕ, 0 ≤ shiftedPairVonMangoldt 0 n) ∧
        ∀ n : ℕ, ¬ IsPrimePow n → shiftedPairVonMangoldt 0 n = 0) :=
    propext (iff_of_true
      ⟨shiftedPairVonMangoldt_nonneg a, fun _ hn => shiftedPairVonMangoldt_eq_zero_of_not_isPrimePow a hn⟩
      ⟨shiftedPairVonMangoldt_nonneg 0, fun _ hn => shiftedPairVonMangoldt_eq_zero_of_not_isPrimePow 0 hn⟩)
  have f3 : (∀ s : ℂ, shiftedCompletedPair a (1 - s) = shiftedCompletedPair a s) =
      (∀ s : ℂ, shiftedCompletedPair 0 (1 - s) = shiftedCompletedPair 0 s) :=
    propext (iff_of_true (shiftedCompletedPair_one_sub a) (shiftedCompletedPair_one_sub 0))
  have f4 : (∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, -1 / 4 ≤ σ → σ ≤ 5 / 4 → 8 ≤ t →
        ‖shiftedZetaPair a ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ (2 : ℝ)) =
      (∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, -1 / 4 ≤ σ → σ ≤ 5 / 4 → 8 ≤ t →
        ‖shiftedZetaPair 0 ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ (2 : ℝ)) :=
    propext (iff_of_true (exists_norm_shiftedZetaPair_le ha) (exists_norm_shiftedZetaPair_le h0))
  unfold structuralFlags
  rw [f1, f2, f3, f4]

/-! ### 3. The temperedness gate -/

/-- **The temperedness gate.** A reading of the structural flags resolves criticality of the pair
only if RH fails: the flags are shared by `ζ(s − ¼) ζ(s + ¼)`, whose zeros are off the line. An
argument using only these properties must therefore use the Ramanujan ceiling as well. -/
theorem not_riemannHypothesis_of_resolves_structuralFlags
    (hres : Resolves structuralFlags PairZerosOnLine) : ¬ RiemannHypothesis := fun hRH =>
  not_pairZerosOnLine_quarter
    ((hres 0 (1 / 4) (structuralFlags_eq (by norm_num))).mpr
      (pairZerosOnLine_zero_of_riemannHypothesis hRH))

/-- No quantity computed from the flags resolves criticality either. -/
theorem not_riemannHypothesis_of_resolves_flagDerived {O : Type*}
    (g : Prop × Prop × Prop × Prop → O)
    (hres : Resolves (fun a : ℝ => g (structuralFlags a)) PairZerosOnLine) :
    ¬ RiemannHypothesis :=
  not_riemannHypothesis_of_resolves_structuralFlags
    (Resolves.of_refines (refines_of_comp structuralFlags (fun _ => rfl)) hres)

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

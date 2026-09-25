import GaloisForLFunctions.RHTower.AngularEnergyQuantization

/-!
# Bubble counting: the number of off-line zeros is bounded by the total energy

The angular energy of a zero is the local Gagliardo form of the critical Sobolev seminorm: the
seminorm of `Ḣ^{1/2}(ℝ)` is comparable to the double integral of `|f(x) − f(y)|²/|x−y|²`, and the
zero network with conductances `1/|ρ_j − ρ_k|²` is exactly its discretisation on the divisor. In that
reading the results already established here are statements about a critical exponent:

* the angular energy of a zero is its **local critical energy**;
* the unit contributed by the functional-equation partner, independent of the distance to the line,
  is **energy quantisation** — a spike at the critical exponent has scale-independent cost;
* the equivalence with the strict bound below one is the statement that the configuration lies
  **below the first critical level**, where no spike can exist.

This module adds the counting consequence, which is the additivity of those costs. Since every
off-line zero carries at least one unit, the number of off-line zeros in any finite collection is at
most the total energy of that collection. Controlling an energy therefore controls a count, with the
threshold an absolute constant and no dependence on the height — the shape required of any certificate
in this field.
-/

namespace RHTower

noncomputable section

/-- **Bubble counting.** In any finite collection of off-line zeros, the cardinality is at most the
total angular energy. -/
theorem card_le_sum_angularEnergy (S : Finset XiDivisorSupport)
    (h : ∀ ρ ∈ S, (ρ : ℂ).re ≠ 1 / 2) :
    (S.card : ℝ) ≤ ∑ ρ ∈ S, angularEnergy ρ := by
  calc (S.card : ℝ) = ∑ _ρ ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ ρ ∈ S, angularEnergy ρ :=
        Finset.sum_le_sum fun ρ hρ => one_le_angularEnergy (h ρ hρ)

/-- **Below the first critical level there are no off-line zeros.** If every angular energy is under
one, the divisor meets the critical line only. -/
theorem re_eq_half_of_forall_angularEnergy_lt_one
    (h : ∀ ρ : XiDivisorSupport, angularEnergy ρ < 1) (ρ : XiDivisorSupport) :
    (ρ : ℂ).re = 1 / 2 := by
  by_contra hc
  exact absurd (one_le_angularEnergy hc) (not_le.mpr (h ρ))

/-- A finite collection whose total energy is under one contains no off-line zero. -/
theorem eq_empty_of_sum_angularEnergy_lt_one {S : Finset XiDivisorSupport}
    (hoff : ∀ ρ ∈ S, (ρ : ℂ).re ≠ 1 / 2)
    (h : ∑ ρ ∈ S, angularEnergy ρ < 1) : S = ∅ := by
  by_contra hne
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hne)
  have hcard : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hpos
  exact absurd (hcard.trans (card_le_sum_angularEnergy S hoff)) (not_le.mpr h)

end

end RHTower

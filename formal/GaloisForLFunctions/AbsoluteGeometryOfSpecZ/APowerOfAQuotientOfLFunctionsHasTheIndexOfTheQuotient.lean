import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexOfAQuotientOfLFunctionsCountsItsZerosAndItsPoles

/-!
# A power of a quotient of `L`-functions has the index of the quotient

The index of a virtual configuration counts points, not multiplicities: the points right of the
line where the net multiplicity is not zero and the points on the line where it is negative. So
the `n`-th power of a quotient of products has the defect points of the quotient
(`virtualDefect_superposeFamily_power`) and its index (`exists_le_negIndex_power_iff`).

Artin's induction theorem (`exists_nsmul_mem_closure_monomial`, `RHTower`) writes a positive
multiple `nχ` of every character of a finite group as an integer combination of characters
induced from linear characters. With the reciprocity law, which is not in the corpus, the
`L`-function of such an induced character is a Hecke `L`-function, and the `n`-th power of an
Artin `L`-function is a quotient of products of Hecke `L`-functions. Its index is given here: it
does not depend on `n`. The index law of an Artin character therefore needs the rational
theorem only; the integral theorem of Brauer is needed for the function, not for the index.
-/

open Finset Matrix
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri

variable {κ κ' : Type*} [Fintype κ] [Fintype κ']

/-- The multiplicities of `n` copies of a family. -/
theorem sum_extMult_power (Z : κ → ZeroConfig) (n : ℕ) (ρ : ℂ) :
    ∑ p : κ × Fin n, extMult (Z p.1) ρ = n * ∑ k, extMult (Z k) ρ := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The defect points of a power of a quotient are those of the quotient.** -/
theorem virtualDefect_superposeFamily_power (Z : κ → ZeroConfig) (Z' : κ' → ZeroConfig) {n : ℕ}
    (hn : 0 < n) :
    virtualDefect (superposeFamily fun p : κ × Fin n => Z p.1)
        (superposeFamily fun p : κ' × Fin n => Z' p.1) =
      virtualDefect (superposeFamily Z) (superposeFamily Z') := by
  ext ρ
  rw [mem_virtualDefect_superposeFamily, mem_virtualDefect_superposeFamily, sum_extMult_power,
    sum_extMult_power, Ne, Nat.mul_left_cancel_iff hn, Nat.mul_lt_mul_left hn]

/-- **The index of a power of a quotient.** For two finite families of tempered configurations
and `n ≥ 1`, the form of `n` copies of the first family minus `n` copies of the second has `r`
negative squares on some family of `r` tests iff the quotient has at least `r` defect points. -/
theorem exists_le_negIndex_power_iff (Z : κ → ZeroConfig) (Z' : κ' → ZeroConfig)
    (hZ : ∀ k, SquareRootThreshold.TemperedConfig (Z k))
    (hZ' : ∀ k, SquareRootThreshold.TemperedConfig (Z' k)) {n : ℕ} (hn : 0 < n) (r : ℕ) :
    (∃ f : Fin r → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        r ≤ hermNegIndex (∑ p : κ × Fin n, zeroGram (Z p.1) f -
          ∑ p : κ' × Fin n, zeroGram (Z' p.1) f)) ↔
      (r : ℕ∞) ≤ (virtualDefect (superposeFamily Z) (superposeFamily Z')).encard := by
  rw [exists_le_negIndex_quotient_iff (fun p : κ × Fin n => Z p.1) (fun p : κ' × Fin n => Z' p.1)
    (fun p => hZ p.1) (fun p => hZ' p.1) r, virtualDefect_superposeFamily_power Z Z' hn]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

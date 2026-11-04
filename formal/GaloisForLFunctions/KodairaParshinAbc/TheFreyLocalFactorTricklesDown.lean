import GaloisForLFunctions.KodairaParshinAbc.TheFreyCurvesHaveFullTwoTorsion
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheLocalFactorTricklesDownByRamanujan
import GaloisForLFunctions.ArithmeticEffectivityTheory.TatesLimitLaw

/-!
# The Frey local factor trickles down

At a good odd prime `p ∤ ab(a+b)` the Frey curve `y² = x(x - a)(x + b)` has local factor
`1 - a_p T + p T²` with `|a_p| ≤ 2√p` (Hasse).  This is exactly the input of the corpus Ramanujan
datum (`ArithmeticLorentzianGeometry.ramanujanDatum`), so the Frey local factor joins the
Kloosterman factor among the local data whose Lorentzian structure is decided:

* every Frobenius ladder of the Frey datum is Metzler, satisfies the weighted trickle-down
  inequality and has hyperbolic links (`freyDatum_trickleDown`);
* its depth-one Frobenius Gram matrix has the Hodge index (`freyDatum_frobeniusGram_one`);
* its degree form `deg(m - nF)` on `ℤ²` has a naive height (`freyDatum_exists_naiveHeight`);
* its trace is `a_p/√p` with `a_p ≡ p + 1 (mod 4)` (`freyDatum_trace_one`).
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc

open ArithmeticCastelnuovoSeveri ArithmeticLorentzianGeometry

variable {p : ℕ} [hp : Fact p.Prime]

/-- Hasse's bound for the Frobenius trace of the Frey curve: `|a_p| ≤ 2 √p`. -/
theorem abs_frobeniusTrace_freyModP_le {a b : ℤ} (hp2 : p ≠ 2)
    (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    |(frobeniusTrace (freyModP a b p) : ℝ)| ≤ 2 * Real.sqrt p := by
  have h := abs_card_freyCurve_sub_le hp2 habc
  rw [frobeniusTrace]
  push_cast
  rw [abs_sub_comm]
  exact h

theorem one_lt_prime_real : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

/-- **The Frey datum**: the Ramanujan datum of the local factor `1 - a_p T + p T²`. -/
def freyDatum {a b : ℤ} (hp2 : p ≠ 2) (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) : CurveDatum (Fin 2) :=
  ramanujanDatum p one_lt_prime_real (frobeniusTrace (freyModP a b p))
    (abs_frobeniusTrace_freyModP_le hp2 habc)

/-- **The Frey local factor trickles down** at every depth `K`. -/
theorem freyDatum_trickleDown {a b : ℤ} (hp2 : p ≠ 2) (habc : ¬ (p : ℤ) ∣ a * b * (a + b))
    (K : ℕ) :
    IsMetzler (frobeniusGram (freyDatum hp2 habc) K) ∧
      WeightedTrickleDown (frobeniusWeight (freyDatum hp2 habc) K)
        (frobeniusGram (freyDatum hp2 habc) K) ∧
      HasHyperbolicLinks (diagConj (frobeniusWeight (freyDatum hp2 habc) K)
        (frobeniusGram (freyDatum hp2 habc) K)) :=
  ramanujanDatum_trickleDown _ _ K

theorem freyDatum_trace_one {a b : ℤ} (hp2 : p ≠ 2) (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    (freyDatum hp2 habc).trace 1 = frobeniusTrace (freyModP a b p) / Real.sqrt p ∧
      (4 : ℤ) ∣ (p : ℤ) + 1 - frobeniusTrace (freyModP a b p) :=
  ⟨ramanujanDatum_trace_one _ _, freyModP_trace_mod_four hp2 habc⟩

/-- **Hodge index at depth one** for the Frey datum. -/
theorem freyDatum_frobeniusGram_one {a b : ℤ} (hp2 : p ≠ 2)
    (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    IsHyperbolic (frobeniusGram (freyDatum hp2 habc) 1) := by
  rw [frobeniusGram_one_isHyperbolic_iff, freyDatum, ramanujanDatum_trace_one, abs_div,
    abs_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)),
    div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos))]
  exact abs_frobeniusTrace_freyModP_le hp2 habc

/-- **The Frey degree form has a naive height**: `deg(m - nF)` on `ℤ²` is at bounded distance from
a function bounded below. -/
theorem freyDatum_exists_naiveHeight {a b : ℤ} (hp2 : p ≠ 2)
    (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    ∃ h : ℤ × ℤ → ℝ, ∃ K B : ℝ, (∀ v, -K ≤ h v) ∧
      ∀ v, |h v - ArithmeticEffectivityTheory.intEndDeg (freyDatum hp2 habc) v| ≤ B :=
  (ArithmeticEffectivityTheory.genusOne_exists_naiveHeight_iff _).mpr
    (ramanujanDatum_unitary _ _)

end GaloisForLFunctions.KodairaParshinAbc

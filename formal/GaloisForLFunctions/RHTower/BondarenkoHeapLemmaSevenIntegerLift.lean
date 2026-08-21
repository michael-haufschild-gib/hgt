/-
# Bondarenko--Heap Lemma 7: integer-lifted fiber energy

The source Lemma 7 groups finite pairs `(r,m)` by the residue class
`r m⁻¹ mod q`, with `(m,q)=1`, and counts collisions through the lifted
equation `r₁m₂-r₂m₁ = ℓq`.  This module packages the exact finite energy
identity with the collision predicate already expressed as integer
divisibility by `q`.
-/
import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaSeven

noncomputable section

namespace RHTower

/-- A source integer denominator together with its certified unit residue modulo `q`. -/
structure BHLemmaSevenUnitInteger (q : ℕ) [NeZero q] where
  value : ℕ
  residue : (ZMod q)ˣ
  residue_eq : (residue : ZMod q) = (value : ZMod q)

/-- The literal source incidence class `r m⁻¹` for a certified unit integer denominator. -/
def bhLemmaSevenInverseIncidence (q : ℕ) [NeZero q] (r : ℕ)
    (m : BHLemmaSevenUnitInteger q) : ZMod q :=
  unitInverseIncidenceClass q (r : ZMod q) m.residue

/-- Equality of source inverse-incidence classes is precisely divisibility of the lifted
cross-product difference. -/
theorem bhLemmaSeven_inverseIncidence_eq_iff_dvd_crossMul
    (q : ℕ) [NeZero q] (r₁ r₂ : ℕ) (m₁ m₂ : BHLemmaSevenUnitInteger q) :
    bhLemmaSevenInverseIncidence q r₁ m₁ = bhLemmaSevenInverseIncidence q r₂ m₂ ↔
      (q : ℤ) ∣ (r₂ : ℤ) * (m₁.value : ℤ) - (r₁ : ℤ) * (m₂.value : ℤ) := by
  rw [bhLemmaSevenInverseIncidence, bhLemmaSevenInverseIncidence,
    unitInverseIncidenceClass_eq_iff_crossMul, m₁.residue_eq, m₂.residue_eq]
  simpa using
    (ZMod.intCast_eq_intCast_iff_dvd_sub ((r₁ : ℤ) * (m₂.value : ℤ))
      ((r₂ : ℤ) * (m₁.value : ℤ)) q)

/-- Equality of source inverse-incidence classes is precisely the lifted integer equation
`r₁m₂ - r₂m₁ = ℓq` for some signed quotient `ℓ`. -/
theorem bhLemmaSeven_inverseIncidence_eq_iff_exists_crossMul_lift
    (q : ℕ) [NeZero q] (r₁ r₂ : ℕ) (m₁ m₂ : BHLemmaSevenUnitInteger q) :
    bhLemmaSevenInverseIncidence q r₁ m₁ = bhLemmaSevenInverseIncidence q r₂ m₂ ↔
      ∃ ell : ℤ,
        (r₁ : ℤ) * (m₂.value : ℤ) - (r₂ : ℤ) * (m₁.value : ℤ) = ell * (q : ℤ) := by
  rw [bhLemmaSeven_inverseIncidence_eq_iff_dvd_crossMul]
  constructor
  · rintro ⟨ell, hell⟩
    refine ⟨-ell, ?_⟩
    linarith
  · rintro ⟨ell, hell⟩
    refine ⟨-ell, ?_⟩
    linarith

/-- Finite source fiber sum over arbitrary certified integer numerator/denominator data. -/
def bhLemmaSevenFiniteFibreSum {A : Type*} [Fintype A]
    (q : ℕ) [NeZero q] (r : A → ℕ) (m : A → BHLemmaSevenUnitInteger q)
    (c : A → ℂ) (x : ZMod q) : ℂ :=
  finiteFibreSum (fun a => bhLemmaSevenInverseIncidence q (r a) (m a)) c x

/-- Exact finite energy expansion in the integer cross-product divisibility form used by
Bondarenko--Heap Lemma 7 before its additive-divisor estimate. -/
theorem bhLemmaSeven_finiteFibreSum_energy {A : Type*} [Fintype A]
    (q : ℕ) [NeZero q] (r : A → ℕ) (m : A → BHLemmaSevenUnitInteger q)
    (c : A → ℂ) :
    ∑ x : ZMod q,
      bhLemmaSevenFiniteFibreSum q r m c x * star (bhLemmaSevenFiniteFibreSum q r m c x) =
      ∑ a : A, ∑ b : A,
        if (q : ℤ) ∣ (r b : ℤ) * (m a).value - (r a : ℤ) * (m b).value then
          c a * star (c b) else 0 := by
  unfold bhLemmaSevenFiniteFibreSum
  rw [finiteFibreSum_energy]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [bhLemmaSeven_inverseIncidence_eq_iff_dvd_crossMul]

end RHTower

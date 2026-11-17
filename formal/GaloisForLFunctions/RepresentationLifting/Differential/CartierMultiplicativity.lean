import GaloisForLFunctions.RepresentationLifting.Differential.CartierGapContraction
import Mathlib.Algebra.Polynomial.Basic

/-!
# The multiplicative boundary of spectrum projection

Polynomial coefficient projection is multiplicative exactly for constants or all exponents. Retaining Cartier horizontal modes forces the latter.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.RepresentationLifting.DividedPower
variable (p : ℕ) [Fact p.Prime]
local instance (S : AddSubmonoid ℕ) (n : ℕ) : Decidable (n ∈ S) := Classical.propDecidable _

/-- The additive-spectrum projection acting on the actual polynomial algebra. -/
def polynomialSpectrumProjection (S : AddSubmonoid ℕ) (P : (ZMod p)[X]) : (ZMod p)[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (spectrumProjection p S P.toFinsupp.coeff))

@[simp] theorem polynomialSpectrumProjection_coeff (S : AddSubmonoid ℕ)
    (P : (ZMod p)[X]) (n : ℕ) :
    (polynomialSpectrumProjection p S P).coeff n = if n ∈ S then P.coeff n else 0 := by
  classical
  exact spectrumProjection_apply p S P.toFinsupp.coeff n

theorem polynomialSpectrumProjection_one (S : AddSubmonoid ℕ) :
    polynomialSpectrumProjection p S 1 = 1 := by
  classical
  ext n
  by_cases hn : n = 0 <;> simp [polynomialSpectrumProjection_coeff, Polynomial.coeff_one, hn, S.zero_mem]

/-- The projection retains exactly the monomials in its exponent spectrum. -/
theorem polynomialSpectrumProjection_X_pow (S : AddSubmonoid ℕ) (n : ℕ) :
    polynomialSpectrumProjection p S (X ^ n) = if n ∈ S then X ^ n else 0 := by
  classical
  ext j
  by_cases hj : j = n
  · subst j
    by_cases hn : n ∈ S <;> simp [polynomialSpectrumProjection_coeff, hn]
  · by_cases hn : n ∈ S <;> simp [polynomialSpectrumProjection_coeff, hn, hj]

private theorem polynomialSpectrumProjection_top (P : (ZMod p)[X]) :
    polynomialSpectrumProjection p ⊤ P = P := by
  ext n
  simp [polynomialSpectrumProjection_coeff]

private theorem polynomialSpectrumProjection_bot (P : (ZMod p)[X]) :
    polynomialSpectrumProjection p ⊥ P = C (P.coeff 0) := by
  ext n
  by_cases hn : n = 0 <;> simp [polynomialSpectrumProjection_coeff, Polynomial.coeff_C, hn]

/-- A coefficient projection is multiplicative exactly for constant terms or the entire polynomial algebra. -/
theorem polynomialSpectrumProjection_multiplicative_iff (S : AddSubmonoid ℕ) :
    (∀ P Q : (ZMod p)[X], polynomialSpectrumProjection p S (P * Q) =
      polynomialSpectrumProjection p S P * polynomialSpectrumProjection p S Q) ↔
      S = ⊥ ∨ S = ⊤ := by
  classical
  constructor
  · intro hmul
    by_cases h1 : 1 ∈ S
    · right
      apply top_unique
      intro n _
      induction n with
      | zero => exact S.zero_mem
      | succ n hn => exact S.add_mem (hn (AddSubmonoid.mem_top n)) h1
    · left
      have hX : polynomialSpectrumProjection p S X = 0 := by
        simpa only [pow_one, if_neg h1] using polynomialSpectrumProjection_X_pow p S 1
      have hpow (n : ℕ) : polynomialSpectrumProjection p S (X ^ n) =
          (polynomialSpectrumProjection p S X) ^ n := by
        induction n with
        | zero => simpa only [pow_zero] using polynomialSpectrumProjection_one p S
        | succ n hn => rw [pow_succ, hmul, hn, pow_succ]
      apply le_antisymm ?_ bot_le
      intro n hn
      have hn0 : n = 0 := by
        by_contra hn0
        have h := hpow n
        rw [polynomialSpectrumProjection_X_pow, if_pos hn, hX, zero_pow hn0] at h
        exact (pow_ne_zero n (X_ne_zero : (X : (ZMod p)[X]) ≠ 0)) h
      simpa only [hn0] using (AddSubmonoid.zero_mem (⊥ : AddSubmonoid ℕ))
  · rintro (rfl | rfl) P Q
    · rw [polynomialSpectrumProjection_bot, polynomialSpectrumProjection_bot,
        polynomialSpectrumProjection_bot]
      simp
    · rw [polynomialSpectrumProjection_top, polynomialSpectrumProjection_top,
        polynomialSpectrumProjection_top]

/-- Retaining the characteristic rules out every proper multiplicative spectrum projection. -/
theorem retained_characteristic_multiplicative_iff (S : AddSubmonoid ℕ) (hp : p ∈ S) :
    (∀ P Q : (ZMod p)[X], polynomialSpectrumProjection p S (P * Q) =
      polynomialSpectrumProjection p S P * polynomialSpectrumProjection p S Q) ↔ S = ⊤ := by
  rw [polynomialSpectrumProjection_multiplicative_iff]
  constructor
  · rintro (hs | hs)
    · have hz : p = 0 := by simpa only [hs, AddSubmonoid.mem_bot] using hp
      exact ((Fact.out : p.Prime).ne_zero hz).elim
    · exact hs
  · exact Or.inr

/-- A multiplicative projection retaining every Cartier horizontal mode must retain every exponent. -/
theorem horizontal_multiplicative_projection_iff (S : AddSubmonoid ℕ) :
    ((∀ f : ℕ →₀ ZMod p, logarithmicEuler p f = 0 → spectrumProjection p S f = f) ∧
      ∀ P Q : (ZMod p)[X], polynomialSpectrumProjection p S (P * Q) =
        polynomialSpectrumProjection p S P * polynomialSpectrumProjection p S Q) ↔ S = ⊤ := by
  rw [horizontal_retention_iff]
  constructor
  · rintro ⟨hp, hm⟩
    exact (retained_characteristic_multiplicative_iff p S hp).mp hm
  · rintro rfl
    exact ⟨AddSubmonoid.mem_top _, (polynomialSpectrumProjection_multiplicative_iff p ⊤).mpr (Or.inr rfl)⟩

#print axioms polynomialSpectrumProjection_multiplicative_iff
#print axioms horizontal_multiplicative_projection_iff
end GaloisForLFunctions.RepresentationLifting.DividedPower

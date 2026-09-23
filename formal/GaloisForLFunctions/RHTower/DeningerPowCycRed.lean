import GaloisForLFunctions.RHTower.DeningerCycLenBound
import GaloisForLFunctions.RHTower.DeningerPowerLength

/-!
# An element whose power is cyclically reduced is cyclically reduced

The length of a power of an element is its conjugator length plus a multiple of its cyclic length,
so comparing two exponents reads off the cyclic length from the power alone.  If the power is a
cyclically reduced word, its length is the exponent times the cyclic length, which forces the
conjugator to be empty: the element is its own cyclic word.

* `deningerCycRed_of_pow` : an element whose power is cyclically reduced is cyclically reduced.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **An element whose power is cyclically reduced is cyclically reduced.**  Its cyclic length is the
length of the power divided by the exponent, and its conjugator is empty. -/
theorem deningerCycRed_of_pow (C R V V₀ : List (Σ i, G i)) (n : ℕ)
    (hCRred : ∀ p ∈ C ++ R, p.2 ∉ (φ p.1).range)
    (hCRalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (C ++ R))
    (hVne : V ≠ []) (hVred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (hValt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V)
    (hVcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1)
    (hhead : V.head?.map Sigma.fst = R.head?.map Sigma.fst)
    (hprod : deningerLetterProd (φ := φ) R =
      deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C)⁻¹)
    (hVR : V.length ≤ R.length)
    (hV₀ne : V₀ ≠ []) (hV₀red : ∀ p ∈ V₀, p.2 ∉ (φ p.1).range)
    (hV₀alt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V₀)
    (hV₀cyc : ∀ p ∈ V₀.getLast?, ∀ q ∈ V₀.head?, p.1 ≠ q.1)
    (hx : (deningerLetterProd (φ := φ) (C ++ R)) ^ (n + 1) =
      deningerLetterProd (φ := φ) V₀) :
    C = [] ∧ deningerLetterProd (φ := φ) (C ++ R) = deningerLetterProd (φ := φ) V ∧
      (n + 1) * V.length = V₀.length := by
  have e1 : deningerLen d ((deningerLetterProd (φ := φ) (C ++ R)) ^ (n + 1)) =
      C.length + n * V.length + R.length :=
    deningerLen_conj_pow (d := d) C R V hCRred hCRalt hVne hVred hValt hVcyc hhead hprod n
  have e2 : deningerLen d ((deningerLetterProd (φ := φ) (C ++ R)) ^ (2 * n + 2)) =
      C.length + (2 * n + 1) * V.length + R.length :=
    deningerLen_conj_pow (d := d) C R V hCRred hCRalt hVne hVred hValt hVcyc hhead hprod (2 * n + 1)
  have f1 : deningerLen d (deningerLetterProd (φ := φ) V₀) = V₀.length :=
    deningerLen_letterProd (d := d) V₀ hV₀red hV₀alt
  have f2 : deningerLen d ((deningerLetterProd (φ := φ) V₀) ^ (2 : ℕ)) = 2 * V₀.length := by
    have := deningerLen_pow (d := d) V₀ 1 1 hV₀ne hV₀red hV₀alt hV₀cyc
    simpa using this
  have hsq : (deningerLetterProd (φ := φ) (C ++ R)) ^ (2 * n + 2) =
      (deningerLetterProd (φ := φ) V₀) ^ (2 : ℕ) := by
    rw [show 2 * n + 2 = (n + 1) * 2 by ring, pow_mul, hx]
  rw [hx, f1] at e1
  rw [hsq, f2] at e2
  have hVV : (n + 1) * V.length = V₀.length := by
    have h1 : (2 * n + 1) * V.length = n * V.length + (n + 1) * V.length := by ring
    rw [h1] at e2
    omega
  have hCR : C.length + R.length ≤ V.length := by
    rw [← hVV] at e1
    have : (n + 1) * V.length = n * V.length + V.length := by ring
    omega
  obtain ⟨hC, hprodL⟩ :=
    deningerCycRed_of_cycLen_eq (φ := φ) (C ++ R) C R V rfl hprod hVR (by simpa using hCR)
  exact ⟨hC, hprodL, hVV⟩

end RHTower

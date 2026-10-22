import GaloisForLFunctions.RHTower.Deninger.DeningerPowCycRed
import GaloisForLFunctions.RHTower.Deninger.DeningerPushoutMetric

/-!
# A conjugate of a factor element has no cyclically reduced power

All powers of a conjugate of a factor element are conjugates of factor elements, so their lengths
are bounded by one plus twice the length of the conjugator.  The powers of a nonempty cyclically
reduced word have unbounded length, so no power of a conjugate of a factor element is one.

* `deningerLen_of_le_one` : a factor element has length at most one.
* `deningerFactorConj_pow_ne_cycRed` : the exclusion.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **A factor element has length at most one.** -/
theorem deningerLen_of_le_one (i : ι) (v : G i) :
    deningerLen d (PushoutI.of (φ := φ) i v) ≤ 1 := by
  by_cases h : v ∈ (φ i).range
  · obtain ⟨w, rfl⟩ := h
    rw [PushoutI.of_apply_eq_base, deningerLen_base]
    omega
  · have hlen := deningerLen_letterProd (d := d) [(⟨i, v⟩ : Σ i, G i)]
      (by simpa using h) (List.isChain_singleton _)
    rw [deningerLetterProd_cons, deningerLetterProd_nil, mul_one] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    omega

include d in
/-- **A conjugate of a factor element has no cyclically reduced power.** -/
theorem deningerFactorConj_pow_ne_cycRed (c : PushoutI φ) (i : ι) (u : G i)
    (V₀ : List (Σ i, G i)) (n : ℕ)
    (hV₀ne : V₀ ≠ []) (hV₀red : ∀ p ∈ V₀, p.2 ∉ (φ p.1).range)
    (hV₀alt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V₀)
    (hV₀cyc : ∀ p ∈ V₀.getLast?, ∀ q ∈ V₀.head?, p.1 ≠ q.1)
    (hx : (c⁻¹ * PushoutI.of (φ := φ) i u * c) ^ (n + 1) =
      deningerLetterProd (φ := φ) V₀) : False := by
  set m : ℕ := 2 * deningerLen d c + 1 with hm
  have hpow : ((c⁻¹ * PushoutI.of (φ := φ) i u * c) ^ (n + 1)) ^ (m + 1) =
      c⁻¹ * PushoutI.of (φ := φ) i (u ^ ((n + 1) * (m + 1))) * c := by
    rw [← pow_mul, ← deningerConj_zpow, ← map_pow]
  have hle : deningerLen d (((c⁻¹ * PushoutI.of (φ := φ) i u * c) ^ (n + 1)) ^ (m + 1)) ≤
      1 + 2 * deningerLen d c := by
    rw [hpow]
    have h1 := deningerLen_conj_le (d := d) c (PushoutI.of (φ := φ) i (u ^ ((n + 1) * (m + 1))))
    have h2 := deningerLen_of_le_one (d := d) (φ := φ) i (u ^ ((n + 1) * (m + 1)))
    omega
  have hge : deningerLen d ((deningerLetterProd (φ := φ) V₀) ^ (m + 1)) = (m + 1) * V₀.length := by
    have := deningerLen_pow (d := d) V₀ 1 m hV₀ne hV₀red hV₀alt hV₀cyc
    simpa using this
  rw [hx, hge] at hle
  have hpos : 1 ≤ V₀.length := List.length_pos_iff.2 hV₀ne
  have : m + 1 ≤ (m + 1) * V₀.length := Nat.le_mul_of_pos_right _ (by omega)
  omega

end RHTower

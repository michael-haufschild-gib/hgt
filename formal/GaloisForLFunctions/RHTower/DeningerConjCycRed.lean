import GaloisForLFunctions.RHTower.DeningerCycRedWordOfPow
import GaloisForLFunctions.RHTower.DeningerCycLenEq

/-!
# Reducing an equality of powers to the cyclically reduced case

An element outside the base group is conjugate to a cyclically reduced word, its cyclic reduction.
Conjugating both sides of an equality of powers by the same element preserves it, so an equality of
powers whose common value has a cyclically reduced conjugate is settled by the cyclically reduced
case.

* `deningerExists_cycRed_conj` : the cyclic reduction, as a conjugation.
* `deningerPow_eq_of_conj_cycRed` : the reduction of an equality of powers.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The cyclic reduction, as a conjugation.** -/
theorem deningerExists_cycRed_conj (z : PushoutI φ) (hz : deningerLen d z ≠ 0) :
    ∃ (w : PushoutI φ) (V : List (Σ i, G i)), V ≠ [] ∧
      (∀ p ∈ V, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V ∧
      (V.length ≤ 1 ∨ ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) ∧
      w⁻¹ * z * w = deningerLetterProd (φ := φ) V := by
  classical
  rcases deningerExists_letterProd (d := d) z with ⟨h₀, -, hlen0⟩ | ⟨L, hLne, hLred, hLalt, -, hzL⟩
  · exact absurd hlen0 hz
  obtain ⟨C, R, V, hsplit, -, hVne, hVred, hValt, -, hprod, hdisj, -⟩ :=
    deningerExists_cycData_len (φ := φ) L hLne hLred hLalt
  subst hsplit
  refine ⟨deningerLetterProd (φ := φ) C, V, hVne, hVred, hValt, hdisj, ?_⟩
  have hconj : deningerLetterProd (φ := φ) (C ++ R) =
      deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) V *
        (deningerLetterProd (φ := φ) C)⁻¹ := (deningerCycData_iff C R V).2 hprod
  rw [hzL, hconj]
  group

include d in
/-- **The reduction of an equality of powers to the cyclically reduced case.** -/
theorem deningerPow_eq_of_conj_cycRed (hφ : ∀ i, Function.Injective (φ i))
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (hcomm : ∀ u v : H, u * v = v * u)
    (htf : ∀ (u : H) (n : ℕ), 0 < n → u ^ n = 1 → u = 1)
    (x y w : PushoutI φ) (V₀ : List (Σ i, G i)) (n : ℕ)
    (hV₀ne : V₀ ≠ []) (hV₀red : ∀ p ∈ V₀, p.2 ∉ (φ p.1).range)
    (hV₀alt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V₀)
    (hV₀cyc : ∀ p ∈ V₀.getLast?, ∀ q ∈ V₀.head?, p.1 ≠ q.1)
    (heq : x ^ (n + 1) = y ^ (n + 1))
    (hz : w⁻¹ * x ^ (n + 1) * w = deningerLetterProd (φ := φ) V₀) : x = y := by
  have hx : (w⁻¹ * x * w) ^ (n + 1) = deningerLetterProd (φ := φ) V₀ := by
    rw [← deningerConj_zpow]
    exact hz
  have hy : (w⁻¹ * y * w) ^ (n + 1) = deningerLetterProd (φ := φ) V₀ := by
    rw [← deningerConj_zpow, ← heq]
    exact hz
  have := deningerPow_eq_of_cycRedPow (d := d) hφ hcent hcomm htf (w⁻¹ * x * w) (w⁻¹ * y * w)
    V₀ n hV₀ne hV₀red hV₀alt hV₀cyc hx hy
  have hcancel : w * (w⁻¹ * x * w) * w⁻¹ = w * (w⁻¹ * y * w) * w⁻¹ := by rw [this]
  calc x = w * (w⁻¹ * x * w) * w⁻¹ := by group
    _ = w * (w⁻¹ * y * w) * w⁻¹ := hcancel
    _ = y := by group

end RHTower

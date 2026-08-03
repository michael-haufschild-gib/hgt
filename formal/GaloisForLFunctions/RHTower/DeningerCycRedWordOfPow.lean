import GaloisForLFunctions.RHTower.DeningerFactorConjPow
import GaloisForLFunctions.RHTower.DeningerCycRedEltEq

/-!
# Elements with a cyclically reduced power

An element whose positive power is a nonempty cyclically reduced word is itself such a word: its
cyclic reduction cannot have an empty conjugator by the length computation, and its cyclic word
cannot be a single letter because a conjugate of a factor element has no cyclically reduced power.
Two elements with the same such power are therefore equal.

* `deningerCycRedWord_of_pow` : the element is a cyclically reduced word.
* `deningerPow_eq_of_cycRedPow` : two elements with the same cyclically reduced power are equal.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **An element whose positive power is a nonempty cyclically reduced word is such a word.** -/
theorem deningerCycRedWord_of_pow (x : PushoutI φ) (V₀ : List (Σ i, G i)) (n : ℕ)
    (hV₀ne : V₀ ≠ []) (hV₀red : ∀ p ∈ V₀, p.2 ∉ (φ p.1).range)
    (hV₀alt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V₀)
    (hV₀cyc : ∀ p ∈ V₀.getLast?, ∀ q ∈ V₀.head?, p.1 ≠ q.1)
    (hx : x ^ (n + 1) = deningerLetterProd (φ := φ) V₀) :
    ∃ U : List (Σ i, G i), U ≠ [] ∧ (∀ p ∈ U, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U ∧
      (∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1) ∧
      (n + 1) * U.length = V₀.length ∧ x = deningerLetterProd (φ := φ) U := by
  classical
  have hlenV₀ : deningerLen d (deningerLetterProd (φ := φ) V₀) = V₀.length :=
    deningerLen_letterProd (d := d) V₀ hV₀red hV₀alt
  rcases deningerExists_letterProd (d := d) x with ⟨h₀, hxb, -⟩ | ⟨L, hLne, hLred, hLalt, -, hxL⟩
  · exfalso
    rw [hxb, ← map_pow] at hx
    have : deningerLen d (PushoutI.base φ (h₀ ^ (n + 1))) = V₀.length := by
      rw [hx]; exact hlenV₀
    rw [deningerLen_base] at this
    exact hV₀ne (List.length_eq_zero_iff.1 this.symm)
  obtain ⟨C, R, V, hsplit, hRne, hVne, hVred, hValt, hhead, hprod, hdisj, hVR⟩ :=
    deningerExists_cycData_len (φ := φ) L hLne hLred hLalt
  subst hsplit
  rcases hdisj with hshort | hVcyc
  · exfalso
    obtain ⟨p, hp⟩ : ∃ p, V = [p] := by
      refine List.length_eq_one_iff.1 ?_
      have := List.length_pos_iff.2 hVne
      omega
    have hconj : deningerLetterProd (φ := φ) (C ++ R) =
        deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) V *
          (deningerLetterProd (φ := φ) C)⁻¹ := (deningerCycData_iff C R V).2 hprod
    rw [hp, deningerLetterProd_cons, deningerLetterProd_nil, mul_one] at hconj
    refine deningerFactorConj_pow_ne_cycRed (d := d) (deningerLetterProd (φ := φ) C)⁻¹ p.1 p.2
      V₀ n hV₀ne hV₀red hV₀alt hV₀cyc ?_
    rw [inv_inv, ← hconj, ← hxL]
    exact hx
  · obtain ⟨hC, hprodL, hlen⟩ :=
      deningerCycRed_of_pow (d := d) C R V V₀ n hLred hLalt hVne hVred hValt hVcyc hhead hprod
        hVR hV₀ne hV₀red hV₀alt hV₀cyc (by rw [← hxL]; exact hx)
    exact ⟨V, hVne, hVred, hValt, hVcyc, hlen, by rw [hxL, hprodL]⟩

include d in
/-- **Two elements with the same cyclically reduced positive power are equal.** -/
theorem deningerPow_eq_of_cycRedPow (hφ : ∀ i, Function.Injective (φ i))
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (hcomm : ∀ u v : H, u * v = v * u)
    (htf : ∀ (u : H) (n : ℕ), 0 < n → u ^ n = 1 → u = 1)
    (x y : PushoutI φ) (V₀ : List (Σ i, G i)) (n : ℕ)
    (hV₀ne : V₀ ≠ []) (hV₀red : ∀ p ∈ V₀, p.2 ∉ (φ p.1).range)
    (hV₀alt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V₀)
    (hV₀cyc : ∀ p ∈ V₀.getLast?, ∀ q ∈ V₀.head?, p.1 ≠ q.1)
    (hx : x ^ (n + 1) = deningerLetterProd (φ := φ) V₀)
    (hy : y ^ (n + 1) = deningerLetterProd (φ := φ) V₀) : x = y := by
  obtain ⟨U, hUne, hUred, hUalt, hUcyc, hUlen, hxU⟩ :=
    deningerCycRedWord_of_pow (d := d) x V₀ n hV₀ne hV₀red hV₀alt hV₀cyc hx
  obtain ⟨W, hWne, hWred, hWalt, hWcyc, hWlen, hyW⟩ :=
    deningerCycRedWord_of_pow (d := d) y V₀ n hV₀ne hV₀red hV₀alt hV₀cyc hy
  have hlen : U.length = W.length := by
    have : (n + 1) * U.length = (n + 1) * W.length := by rw [hUlen, hWlen]
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  rw [hxU, hyW]
  refine deningerCycRedWord_pow_eq (d := d) hφ hcent hcomm htf U W hUne hUred hUalt hUcyc
    hWne hWred hWalt hWcyc hlen n ?_
  rw [← hxU, ← hyW, hx, hy]

end RHTower

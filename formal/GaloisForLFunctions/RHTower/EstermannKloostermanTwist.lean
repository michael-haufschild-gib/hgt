import GaloisForLFunctions.RHTower.EstermannDivisorSeries
import GaloisForLFunctions.RHTower.Sieve.KloostermanSum

/-!
# The inverse twist of the Estermann family is a Kloosterman-weighted divisor series

The character decomposition of the family is diagonal in the twist `a`, so no cancellation is
available there.  The modulus aspect is different, and the gateway to it is the inversion `a ↦ a⁻¹`
carried by the Estermann functional equation: pairing the family against the **inverse** twist
`e(a⁻¹ b / q)` instead of `e(ab/q)` produces, coefficient by coefficient,

`∑_{a ∈ (ZMod q)ˣ} e(a⁻¹ b/q) · e(aN/q) = S(N, b; q)`,

the complete Kloosterman sum.  Hence

`∑_{a ∈ (ZMod q)ˣ} e(a⁻¹ b/q) · D(s, a/q) = ∑_N d(N) S(N, b; q) N^{-s}`.

The left side is a twist average of the family; the right side is a divisor series weighted by
Kloosterman sums, whose square-root cancellation is Weil's theorem.  This is where the `q`-aspect
mixing enters, and it is the object the shifted divisor correlation needs, since term-by-term
summation over moduli is excluded.
-/

open Complex
open RHTower.Sieve

namespace RHTower

noncomputable section

/-- **The Kloosterman twist identity, summable form.** -/
theorem hasSum_kloosterman_estermannZeta (q : ℕ) [NeZero q] (b : ZMod q) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun N : ℕ => (N.divisors.card : ℂ) * (kloostermanSum q (N : ZMod q) b / (N : ℂ) ^ s))
      (∑ a : (ZMod q)ˣ, (ZMod.stdAddChar (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * b) : ℂ) *
        estermannZeta q ((a : ZMod q)) s) := by
  classical
  have hterm : ∀ a : (ZMod q)ˣ, HasSum
      (fun N : ℕ => (N.divisors.card : ℂ) *
        ((ZMod.stdAddChar ((a : ZMod q) * (N : ZMod q)
            + ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * b) : ℂ) / (N : ℂ) ^ s))
      ((ZMod.stdAddChar (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * b) : ℂ) *
        estermannZeta q ((a : ZMod q)) s) := by
    intro a
    have h := (hasSum_estermannZeta_divisor ((a : ZMod q)) hs).mul_left
      ((ZMod.stdAddChar (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * b) : ℂ))
    refine h.congr_fun (fun N => ?_)
    rw [AddChar.map_add_eq_mul]
    ring
  have hsum := hasSum_sum (fun (a : (ZMod q)ˣ) (_ : a ∈ Finset.univ) => hterm a)
  refine hsum.congr_fun (fun N => ?_)
  simp only [kloostermanSum, kloostermanPhase]
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [show ((a : ZMod q) * (N : ZMod q) + ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * b)
      = ((N : ZMod q) * (a : ZMod q) + b * ((a⁻¹ : (ZMod q)ˣ) : ZMod q)) from by ring]

/-- **The Kloosterman twist identity.**  The inverse-twist average of the Estermann family is the
divisor series weighted by complete Kloosterman sums. -/
theorem sum_invTwist_estermannZeta (q : ℕ) [NeZero q] (b : ZMod q) {s : ℂ} (hs : 1 < s.re) :
    ∑ a : (ZMod q)ˣ, (ZMod.stdAddChar (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * b) : ℂ) *
        estermannZeta q ((a : ZMod q)) s
      = ∑' N : ℕ, (N.divisors.card : ℂ) * (kloostermanSum q (N : ZMod q) b / (N : ℂ) ^ s) :=
  (hasSum_kloosterman_estermannZeta q b hs).tsum_eq.symm

end

end RHTower

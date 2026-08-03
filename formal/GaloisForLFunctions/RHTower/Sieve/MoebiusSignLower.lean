import GaloisForLFunctions.RHTower.Sieve.MoebiusSignCount

/-!
# Both signs occur linearly often

Combining the sign-count identity with a lower bound for the squarefree count and an upper bound for
the Möbius sum: if

`Q(t,L) ≥ ½ D L`   and   `|M(t,L)| ≤ ⅛ D L`,

then `2·#{n ∈ (t,t+L] : μ(n) = ±1} = Q ± M ≥ ⅜ D L`, so **both** sign counts are at least
`(3/16) D L`.

The two hypotheses come from opposite sources — the first is elementary sieve theory, the second is
the mean-square input — and the identity is what lets them be used together.  The constant `3/16` is
not sharp; only its positivity matters.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Both Möbius signs occur at least `(3/16)DL` times.** -/
theorem card_moebius_sign_ge {t L : ℕ} {D : ℝ}
    (hQ : (1 / 2) * D * (L : ℝ) ≤ ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2)
    (hM : |∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ)| ≤ (1 / 8) * D * (L : ℝ)) :
    (3 / 16) * D * (L : ℝ)
        ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
      ∧ (3 / 16) * D * (L : ℝ)
        ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ) := by
  classical
  have habs := abs_le.mp hM
  have hpos := two_mul_card_moebius_eq_one t L
  have hneg := two_mul_card_moebius_eq_neg_one t L
  constructor
  · linarith [hpos, habs.1, hQ]
  · linarith [hneg, habs.2, hQ]

end RHTower.Sieve

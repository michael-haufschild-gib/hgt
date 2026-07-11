/-
# The all-`N` Hurwitz independence against the actual Hurwitz zeta

For `Re s > 1` and `s ∉ ℤ`, a polynomial-coefficient relation of `Y`-degree at most two among
the genuine shifted Hurwitz values `hzeta (s+k) a` (`0 ≤ k ≤ N`), holding near the
negative-integer ray on the upper side, forces every coefficient polynomial to vanish.  This
composes the strip transport of the `hzeta` relation into the factored-tail model with the
unconditional model-level close of all rows, columns, and the constant.  The upper-half-plane
form specializes the ray hypothesis to a relation holding at every point with positive
imaginary part.
-/
import GaloisForLFunctions.Hurwitz.AllNComplete
import GaloisForLFunctions.Hurwitz.N2HZeta

open Complex HurwitzN2Tail HurwitzZetaShift

namespace HurwitzAllNHZeta

variable {N : ℕ}

/-- **All-`N` Hurwitz independence — no quadratic relation among the actual
`ζ(s,a), …, ζ(s+N,a)`, unconditional.**  With `Re s > 1` and `s ∉ ℤ` only: if the genuine
polynomial-coefficient degree-≤2 relation among `hzeta (s+k) a` (`0 ≤ k ≤ N`) holds at every
`a = -n + x` with `n ≥ M`, `‖x‖ < 1/2`, `0 < Im x`, then the symmetric quadratic form, the
linear coefficients, and the constant all vanish. -/
theorem hurwitz_allN_hzeta_unconditional {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (l : Fin (N + 1) → Polynomial ℂ)
    (cc : Polynomial ℂ) (hSymm : ∀ i j, q i j = q j i) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ x : ℂ, ‖x‖ < 1 / 2 → 0 < x.im →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + x)
          * (hzeta (s + (i : ℂ)) (-(n : ℂ) + x) * hzeta (s + (j : ℂ)) (-(n : ℂ) + x)))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + x) * hzeta (s + (k : ℂ)) (-(n : ℂ) + x))
        + cc.eval (-(n : ℂ) + x) = 0) :
    (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0 := by
  refine HurwitzAllNComplete.hurwitz_allN_independence_all_noninteger hs1 hsZ q l cc hSymm
    (M := M) ?_
  intro n hn
  exact HurwitzN2HZeta.model_relation_of_hzeta_relation hs1 q l cc n (hrel n hn)

/-- **All-`N` Hurwitz independence, upper-half-plane form.**  If the genuine degree-≤2 `hzeta`
relation holds at every `a` with `Im a > 0`, all coefficient polynomials vanish. -/
theorem hurwitz_allN_hzeta_upper_half_plane {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (l : Fin (N + 1) → Polynomial ℂ)
    (cc : Polynomial ℂ) (hSymm : ∀ i j, q i j = q j i)
    (hrel : ∀ a : ℂ, 0 < a.im →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval a
          * (hzeta (s + (i : ℂ)) a * hzeta (s + (j : ℂ)) a))
        + (∑ k : Fin (N + 1), (l k).eval a * hzeta (s + (k : ℂ)) a) + cc.eval a = 0) :
    (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0 :=
  hurwitz_allN_hzeta_unconditional hs1 hsZ q l cc hSymm (M := 0)
    (fun n _ x _ hxim => hrel (-(n : ℂ) + x) (by simpa using hxim))

end HurwitzAllNHZeta

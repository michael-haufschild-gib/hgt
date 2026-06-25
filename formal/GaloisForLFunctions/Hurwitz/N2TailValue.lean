/-
# Hurwitz N=2 — the factored tail's value at `x = 0` is `ζ(s,−n)`

The density-shadow row relation is `q(−n)·R_{n,0}(0) + l₂(−n) = 0`, where `R_{n,0}(0)` is the value of the
(factored) Hurwitz tail at `x = 0`. This file identifies that value with the committed `hzeta s (−n)`:
both equal `∑_{m≠n} (m−n)^{−s}` (the `m=n` term is `0^{−s}=0` in `hzeta`, and dropped explicitly in
`tailFactored`; the `(1+0/(m−n))^{−s} = 1` factor is trivial). This feeds `survivor_q_eq_zero`'s `V_n`.
-/
import GaloisForLFunctions.Hurwitz.N2Tail

open Complex

namespace HurwitzN2Tail

/-- **`R_{n,0}(0) = ζ(s,−n)`.** The factored tail at `x = 0` equals the committed regularized Hurwitz
value `hzeta s (−n) = ζ(s) + η·H_n^{(s)}` — both are `∑_{m≠n} (m−n)^{−s}`. This is the survivor's
`V_n`, whose finite difference (`hzeta_neg_nat_diff`) is `η·n^{−s}`. -/
theorem tailFactored_zero_eq (s : ℂ) (hs : s ≠ 0) (n : ℕ) :
    tailFactored s 0 n 0 = HurwitzZetaShift.hzeta s (-(n : ℂ)) := by
  rw [tailFactored, HurwitzZetaShift.hzeta]
  refine tsum_congr (fun m => ?_)
  by_cases hm : m = n
  · subst hm
    rw [if_pos rfl, show ((m : ℂ) + -(m : ℂ)) = 0 from by ring,
      Complex.zero_cpow (neg_ne_zero.mpr hs)]
  · rw [if_neg hm, Nat.cast_zero, add_zero, zero_div, add_zero, Complex.one_cpow, mul_one,
      show ((m : ℂ) + -(n : ℂ)) = (m : ℂ) - (n : ℂ) from by ring]

end HurwitzN2Tail

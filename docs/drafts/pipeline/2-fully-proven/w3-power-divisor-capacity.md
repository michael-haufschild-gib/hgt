# W3: multiplicity determines double-exponential capacity

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** If a nonzero integrable source has bound `C exp(−a exp(b|x|))`, `a,b>0`, and its entire transform contains the divisor of `Ξ^k`, then `kb≤2`.

## Proof [PROVED HERE]

The Xi divisor count in a disc of radius `T+3/2+|c|` is at least its symmetric Riemann–von Mangoldt mass, `(1/π+o(1))T log T`. Raising Xi to power `k` multiplies this count by `k`. Divisor containment therefore forces lower coefficient `k/π` for the transform's count.

The source bound gives angular Jensen upper coefficient `2/(πb)`, by `ThetaTailDivisorCapacity.false_of_capacity`. If `kb>2`, choose a count coefficient strictly between these two numbers; the Riemann–von Mangoldt remainder is smaller than their gap for all sufficiently large `T`. Jensen gives a contradiction. Thus the transform vanishes identically, and Fourier uniqueness makes the source zero almost everywhere.

## Scope

For a spectral square carrying the full Xi divisor twice, the necessary exponent is `b≤1`. This improves the simple-critical bound `b≤3/2` only when multiplicities are proved. Pointwise factorization by an arbitrary, possibly discontinuous quotient does not prove multiplicity containment.

Positive statement: the exact finite-disc count is at least `k` times the symmetric Xi mass, before taking any limit. No blind function has yet been constructed; sharpness at equality remains to be established.

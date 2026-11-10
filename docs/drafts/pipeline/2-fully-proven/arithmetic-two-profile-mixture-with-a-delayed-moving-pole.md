# Arithmetic phase mixing with a delayed moving pole

- **ID:** B130-arithmetic-phase-mixture
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean in progress)
- **Source:** [Endpoint tangent obstruction](../3-formalized/endpoint-tangent-moment-obstructs-polynomial-scaling.md).

## Candidate

Let `χ` be the nonprincipal real character modulo four and put

`P(z)=1-4z²+2z⁴`, `S(z)=2z(1-z²)√(2-z²)`, `Φ±=P±iS`.

Use the square root analytic near the closed unit disc. For odd primes
set `v_p(t)=P(p^-t)+iχ(p)S(p^-t)`; at two use `Φ+(2^-t)`.
The algebraic identity `P²+S²=1` on `[0,1]` gives unit prime
phases with common endpoints `1,-1`.

## Arithmetic theorem

For every sufficiently small real `t>0`, the actual Euler product has
pole regularization

`U(t,s)=(s-1)Π_p(1-v_p(t)p^-s)^(-1)`

and continuation near one of the form

`U(t,s)=A_t(s)(s-(1-2t))⁴/(s-(1-4t))²`,

where `A_t` is analytic and nonzero near both shifted points. Thus the
first singular shift becomes a regular zero of order four, but a later
pole of order two survives. The full scaling limit is

`U(t,1+tw)/t² → ζ(2)(w+2)⁴/(w+4)²`, locally uniformly on `Re w>0`.

## Proof

1. **The character prime logarithm.** For a nonprincipal character,
   `L(s,χ)` is analytic and nonzero near one. On a sufficiently small
   zero-free disc choose an analytic logarithm. Its derivative and the
   Euler logarithm's derivative are both `L′/L`. Their difference is
   constant on the right half-disc; fixing that constant gives a local
   continuation of the actual Euler logarithm. Subtract
   `Σ_p[-log(1-χ(p)p^-s)-χ(p)p^-s]`. Its terms are bounded by
   `2p^(-2 Re s)` on `Re s>1/2`, including the zero ramified terms.
   This gives an analytic continuation `Fχ` of `Σ_p χ(p)p^-s` near one.
   Glue it to the actual series on `Re s>1`. On a horizontal region
   `Re s>1-ε`, `|Im s|<ε`, it is bounded: compactness controls the
   local disc, while absolute prime summability controls `Re s≥1+ε`.

2. **The phases.** Define the root as `exp(log(2-z²)/2)` on a disc
   of radius `6/5`; `Re(2-z²)>0` there. It squares to `2-z²` and is
   real positive on `[0,1]`. Hence `P²+S²=1` and `Φ±` are unimodular,
   with endpoint values `1,-1`. At odd primes `χ(p)=±1`; at two the
   chosen value is `+1`.

3. **The exact prime sum.** Let `S(z)=Σ c_k z^k`. The larger analytic
   disc gives `Σ|c_k|<∞`, `c₀=0`, and `Σ c_k=S(1)=0`. Absolute
   convergence on `Re s>1` permits the identity

   `Σ_p(v_p(t)-1)p^-s = -4P_prime(s+2t)+2P_prime(s+4t)`
   `                         + iΣ_k c_k Fχ(s+kt)+iS(2^-t)2^-s`.

   The last term is the exact correction at the ramified prime.
   Boundedness of `Fχ` gives normal convergence of the shifted series
   on a fixed disc about one for real `t≥0` sufficiently small.

4. **The divisor.** Write `E(s)=P_prime(s)+log(s-1)` for the analytic
   regular part and `H_t` for the higher-prime-power remainder. The
   regularized Euler product has continuation

   `U(t,s)=A_t(s)(s-(1-2t))⁴/(s-(1-4t))²`,

   `A_t(s)=Z(s)exp(-4E(s+2t)+2E(s+4t)+iΣ c_k Fχ(s+kt)`
   `                      +iS(2^-t)2^-s+H_t(s)-H_triv(s))`,

   with `Z(s)=(s-1)ζ(s)` continued at one. Choose a common disc where
   `Z` is nonzero, `E` is analytic, the character shifts remain in the
   bounded horizontal region, and `Re s>1/2`. Then `A_t` is analytic
   and nonzero. The shifted zero and pole therefore have exact orders
   four and two. A joint holomorphic endpoint germ would, by the
   identity theorem after multiplication by `(s-(1-4t))²`, force
   `0=A_t(1-4t)(-2t)⁴`; hence no such germ exists, even if agreement
   with the Euler product is required only for nearby positive real
   parameters and real spectral values above one.

5. **The scaling limit.** For compact sets of `w`, boundedness of
   `Fχ` and summability of `c_k` give
   `Σ c_k Fχ(1+t(w+k))→Fχ(1)Σ c_k=0` locally uniformly. The finite
   correction also tends to zero. Unit prime phases and the summable
   higher-power majorant give `H_t(1+tw)→H_Liouville(1)` uniformly.
   Since `E(1)=-H_triv(1)`, `Z(1)=1`, and
   `exp(H_triv(1)+H_Liouville(1))=ζ(2)`, one gets
   `A_t(1+tw)→ζ(2)`. The two explicit shifted powers supply the stated
   factor `t²(w+2)⁴/(w+4)²`.

The limiting formula concerns the actual Euler product for `t>0` and
`Re w>0`; it assigns no value to a totalized Euler series at the joint
endpoint. Corpus search found no matching arithmetic mixture theorem.
External novelty has not been assessed. Lean formalization is underway.

## Consequence

This realizes the endpoint-moment obstruction in an
actual arithmetic mixture where the earlier first-imaginary-jet test
fails. The mean-profile obstruction alone does not prove this arithmetic
statement. B130 remains open; the stated paper theorem still requires
its complete Lean formalization.

# Coherent prime-tail annular lower bound

- **ID:** critical-rigidity-prime-tail-annular-lower
- **Stage:** 2-fully-proven
- **Type:** THEOREM; Lean verification pending
- **Statement:** A source-preserving lower bound for the coherent prime tail, with the exact annular sampling loss.

## Objects

Let `Q≥2`, `P≥1`, `A=floor(N/P)`, and use coefficients `a_p=sqrt(p−1)/p` on primes at most `Q`. Write

`B_(P,Q)=Σ_(P<p≤Q)log p/p`,

`T_(P,Q)(n)=Σ_(P<p≤Q)log p/(p−1) · 1_(p∤n)`.

## Exact finite bound

`Σ_(n≤N) Tail_Q(a;floor(N/n),n)²/n`

`≥ [Σ_(A<n≤N)1/n − Q(Q−1)/(A+1)] B_(P,Q)²`.

This statement also holds when the bracket is negative, since its left side is nonnegative.

## Dependency-closed proof

For `A<n≤N`, the quotient `N/n` is below `P`. The prime-incidence source identity therefore gives `Tail≥T≥0` pointwise.

The function `T` is an actual conductor packet. Its constant coefficient is `B_(P,Q)`; its prime coefficient for `p>P` is `−sqrt(p−1)/p · log p/(p−1)`, and every other coefficient vanishes. This follows by substituting the exact centered-divisibility identity. Consequently its squared coefficient mass is at least `B_(P,Q)²`.

Apply the existing sharp annular harmonic frame to this packet. Its lower coefficient is `Σ_(A<n≤N)1/n−Q(Q−1)/(A+1)`. If this coefficient is nonnegative, retain only the constant part of coefficient mass. If it is negative, use nonnegativity of the tail square. Pointwise domination and inclusion of the annulus in `1≤n≤N` finish the proof.

## Scalar correction

The exact residual is `(r_N(n)F_a(n)−Tail_a(N/n,n))/sqrt n`. The elementary inequality `(s−t)²≥t²/2−s²`, summed over rows, and the proved scalar residual estimate give

`Σ_n R_a(N,n)² ≥ (1/2)Σ_n Tail_a(N/n,n)²/n − C(1+log Q)Σ_m a_m²`.

Combining this with the annular bound proves an explicit finite lower bound for the actual coherent residual, with its scalar coefficient cost subtracted. The constant `C` is unconditional and uniform in all cutoffs and horizons.

The cubic logarithmic specialization and matching relative-residual threshold remain separate questions. No complete-Weil obstruction follows from the prime piece alone.

## Lean

`CriticalScaleArithmeticRigidity/CoherentPrimeTailLowerBound.lean`. Imports the exact incidence source and `CriticalArithmeticCorrelationTheory.abs_ramanujanPoleProfile_annular_gram_discrepancy_le`.

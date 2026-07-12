# Prime-log Cauchy packets have exact finite independence after positive transport

- **ID:** `prime-log-cauchy-seam-rank-core`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (Lean), `[FORMALIZATION]`
- **Source:** `PrimeLogCauchySeamRank.lean` and
  `prime-log-cauchy-seam-infinite-renormalization-rank.md`
- **Scientific status:** The Lean formalization is not itself new scientific knowledge. The exact
  prime-log quotient-rank interpretation remains under scientific novelty audit in the paper card.

## Formal theorem

For every `b>0`, every finite injective family of upper-half-plane nodes `z_j`, and every complex
coefficient packet `c_j`, Lean proves

```text
Summable (p |->
  p^(2b-1) * normSq (sum_j c_j/(z_j-log p)))
iff
c=0.                                                       (1)
```

The forward implication is

```text
not_summable_primeLogCauchyPacketTransportEnergy_of_pos,
```

and the exact equivalence is

```text
summable_primeLogCauchyPacketTransportEnergy_iff.
```

Thus the transported Cauchy sections are finitely linearly independent modulo the prime
square-summable class. Since finite packets may have arbitrary size, their quotient span has
unbounded finite dimension and hence infinite algebraic rank.

## Formal proof chain

The module proves the chain without new axioms:

1. `tendsto_eval_div_pow_natDegree`: a complex polynomial divided by its highest real monomial
   tends to its leading coefficient.
2. `tendsto_rational_mul_pow_order`: a proper rational function multiplied by its finite order at
   infinity tends to the quotient of leading coefficients.
3. `eventually_rational_cauchy_lower`: every nonzero proper rational function has a positive
   Cauchy-order lower bound on the real ray.
4. `tendsto_primeLogSupport_cofinite`: the prime-log support tends to infinity along the cofinite
   prime filter.
5. `not_summable_primeLogRationalTransportEnergy_of_pos`: the rational lower bound and the
   all-orders theorem in `PrimeLogHerglotz.lean` force divergent transported prime energy.
6. `cauchyPacketNumerator_ne_zero` and the denominator degree lemmas identify every nonzero finite
   packet with a nonzero proper rational function.
7. Equation `(1)` follows.

## Positive CCM consequence

Every additive prime-coordinate renormalization that repairs the complete upper-half-plane Cauchy
family must have infinite-dimensional correction range modulo the positive prime Hilbert space.
Accordingly, a successful CCM seam must positively exhibit an infinite prime--Gamma coupling, a
relative or indefinite completion before the norm, an infinite-dimensional operator/test space,
or an equivalent global marked constraint. A finite-rank correction cannot carry the seam.

This does not prove RH and does not exclude non-additive or category-changing continuations. It
fixes the resource that such a continuation must replace.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/PrimeLogCauchySeamRank.lean` -- pass
- `lake build GaloisForLFunctions.HTGeometry.PrimeLogCauchySeamRank` -- pass
- theorem axioms: `[propext, Classical.choice, Quot.sound]`

## Gates

- [x] all finite prime-log cancellation orders formalized
- [x] complex rational order at infinity formalized
- [x] rational prime-log transport divergence formalized
- [x] finite Cauchy numerator nonvanishing formalized
- [x] exact summability iff zero-coefficient theorem formalized
- [ ] audit scientific novelty of the exact prime-log quotient-rank interpretation
- [ ] construct the required infinite prime--Gamma seam carrier
- [ ] transport complete inertia into the screw spaces
- [ ] RH

## Log

- 2026-07-11 -- formalized the complete finite-packet divergence and exact independence theorem.

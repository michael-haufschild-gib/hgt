# Sharp integer-return bounds for projective arithmetic transport

- **ID:** goldbach-projective-integral-returns
- **Stage:** 3-formalized
- **Type:** BRIDGE; elementary arithmetic geometry, no novelty claim
- **Source:** [failed fixed-family coverage attempt](../../5-failed/goldbach-projective-parity-returns.md)
- **Lean:** [ProjectiveIntegralReturns.lean](../../../../../formal/GaloisForLFunctions/goldbach/ProjectiveIntegralReturns.lean)

## Statement

For integer coefficients g=(a,b,c,d), write Δ=ad−bc. For a finite integer
set S, let R_g(S) contain the m∈S such that cm+d is nonzero and divides
am+b. Define the unconditional cap

    C_g(S)=|S|                         if c=0 or Δ=0,
           min(|S|,2τ(|Δ|))           otherwise.

Then |R_g(S)|≤C_g(S). Inversion x↦D/x has exactly the nonzero signed
divisors of D as its integer returns when D≠0; consequently the divisor
bound is sharp. The degenerate case D=0 returns every nonzero input and
is handled explicitly.

For the original kernel T−mn, the column coordinate induced by applying
the same projective map to T/n has coefficients

    g_T=(Td,T²c,b,Ta),       det(g_T)=T²Δ.

The joint return set on S×U is R_g(S)×R_(g_T)(U), and hence has cardinality
at most C_g(S)C_(g_T)(U). For any finite family I of maps, the union of
their joint return sets has cardinality at most the sum of these caps.
All statements include zero targets and singular matrices through the
displayed definitions; there is no unproved premise.

## Paper proof

At an integral return, t=cm+d divides am+b. Thus t divides
a(cm+d)−c(am+b)=Δ. If c≠0, different inputs have different denominators.
For Δ≠0 there are exactly 2τ(|Δ|) nonzero signed divisors, establishing
the cap. The alternative cap |S| follows by subset inclusion. Inversion
has denominator m and numerator D, so its return set is exactly the
stated divisor set, proving sharpness.

Direct expansion gives det(g_T)=T²Δ and

    T((cm+d)(aT+bn)−(am+b)(cT+dn))=TΔ(T−mn).

The row and column integrality conditions are independent; their joint
set is the Cartesian product. Cardinalities multiply, and union cardinality
is at most the sum of cardinalities. This proves the full finite theorem.

## Lean declarations and audit

Namespace `GaloisForLFunctions.Goldbach.ProjectiveCoefficients`:

- `card_integralReturns_le`
- `integralReturns_inversion_eq`
- `card_integralReturns_inversion`
- `det_columnCoordinates`
- `bilinearKernel_numerator`
- `card_jointIntegralReturns_le`
- `card_jointIntegralReturns_family_le`

The helper `GaloisForLFunctions.Goldbach.card_signedDivisors` supplies the
exact signed-divisor count.

`lake --old env lean GaloisForLFunctions/goldbach/ProjectiveIntegralReturns.lean`
passed from `formal/`, exit 0, no warnings. Six closures were audited:
the signed-divisor count, single-map cap, inversion classification and
sharpness, bilinear numerator, and family cap. Only standard Lean foundations
occur. Temporary audit directives were removed without changing proof bodies.
The module is imported by `goldbach/Main.lean`; the umbrella was not built.

Log: `/tmp/hgt-goldbach-projective-returns-audit.log`.

The asymptotic failure of the fixed-family coverage proposal is a paper
corollary of these finite bounds and the elementary divisor estimate,
recorded on the failed-route card. This theorem does not bound the remaining
signed Möbius covariance and does not prove Goldbach.

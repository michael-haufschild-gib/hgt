# Interior secular roots force strict joint-prime gap decrease

- **ID:** ACP-FINITE-PRIME-ROOT-RIGIDITY
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** arithmetic-counting-finite-prime-secular-gap.md
- **Sources:** full finite-prime resolvent and strict monotonicity; exact finite-prime gap criterion and attainment
- **Statement:** The arithmetic secular function is continuous below the dyadic ceiling; its interior zero is exactly the greatest gap. Under proper inclusion of prime sets, the greatest gap decreases strictly exactly when the larger-set gap is below the ceiling.

## Exact statements

Write g0=2 log 2, Phi_F for the normalized arithmetic secular function,
and delta_F for the attained positive greatest gap. For each finite prime set:

1. Phi_F is continuous at every s in (0,g0).
2. If delta_F<g0, then Phi_F(delta_F)=0.
3. For 0<s<g0, `delta_F=s iff Phi_F(s)=0`.
4. If F is a proper subset of G, then Phi_F(s)<Phi_G(s) for 0<s<g0.
5. For proper inclusion, `delta_G<delta_F iff delta_G<g0`.

Thus a submaximal gap is characterized by a unique explicit arithmetic root.
Equality under proper inclusion can occur only when both gaps equal g0.
The empty prime set remains included.

## Closed proof

### Continuity

The positive conductor weights are summable. For any b<g0 and s<=b,
the reciprocal summand is nonnegative and bounded by
`w_F(m)/(g0-b)`. Each summand is continuous on this half-line because its
denominator is positive. The summable uniform majorant gives continuity
of the entire tail there. Around each 0<s<g0 choose b with s<b<g0;
the ground term -1/s is also continuous. This proves continuity locally
throughout the physical first gap without ordering conductor energies.

### The attained interior threshold is a zero

Assume 0<delta_F<g0. If Phi_F(delta_F)>0, continuity supplies a positive
reading at some 0<s<delta_F, contradicting the necessary sign criterion
for the attained gap. If Phi_F(delta_F)<0, continuity supplies a negative
reading at some delta_F<t<g0. Strict increase makes every reading at
0<s<t negative. The sufficient sign criterion then makes t a gap,
contradicting maximality. Hence Phi_F(delta_F)=0.

Conversely, a zero s in (0,g0) has negative readings below it, so s is a
gap. If delta_F>s, choose t strictly between s and delta_F. Strict
increase makes Phi_F(t)>0, contradicting the gap criterion for delta_F.
Therefore delta_F=s. Strict increase also gives uniqueness of any
interior zero.

### Strict prime-set comparison

For proper inclusion choose a prime p in G but outside F. Its Möbius
coefficient is zero for F and -2 for G, so its normalized squared weight
increases from zero to 4/phi(p)>0. All other conductor weights are
nondecreasing. Every denominator below g0 is positive. Comparison of
the two summable tails is therefore strict at the conductor p, giving
Phi_F(s)<Phi_G(s) throughout (0,g0).

Weak gap comparison already gives delta_G<=delta_F<=g0. Strict decrease
immediately implies delta_G<g0. Conversely, if delta_G<g0 and the gaps
were equal, both secular functions would vanish at the common interior
threshold. Strict comparison at that point forbids equality. Thus
delta_G<delta_F. No continuity in the finite prime set, or horizon bound
uniform in that set, is assumed.

## Scope and formalization

This is an exact rigidity law for the attained gaps of actual prime
matrices. It neither asserts that every proper inclusion decreases a
maximal gap nor supplies a quantitative rate of decrease. Collective
prime-exhaustion collapse and complete Weil positivity remain separate.

Canonical source: `formal/GaloisForLFunctions/ArithmeticCountingPositivity/InteriorSecularRootsForceStrictPrimeGapDecrease.lean`.

- `finiteFlipSecular_continuousAt`
- `finiteFlipSecular_greatestGap_eq_zero`
- `finiteFlipGreatestGap_eq_iff_secular_zero`
- `finiteFlipSecular_lt_of_ssubset`
- `finiteFlipGreatestGap_lt_iff_of_ssubset`

Scratch 87135 and canonical check 70852 both exited zero without diagnostics.
All five transitive audits use only `propext`, `Classical.choice`, and
`Quot.sound`. Exact commands, source hash and actual output are in the
adjacent `-audit.txt`. The umbrella is wired but was not compiled. No olean
was built because no new file imports this module.

- [x] Dependency-complete paper proof.
- [x] Five Lean endpoints and transitive axiom audit.
- [x] Canonical audit, umbrella wiring, durable evidence and cleanup.

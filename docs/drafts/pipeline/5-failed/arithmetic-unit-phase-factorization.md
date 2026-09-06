# Holomorphic unit-phase factorization: obstruction and exact local classification

- **Stage:** 5-failed for frozen proposals U1 and U2 only
- **Positive survivors:** constant classification, exact rational-boundary fibres, zero-free multipliers, tangent identity, and local existence iff a simple critical zero
- **RH chain:** literal Euler deletion → retained arithmetic remainder → independently forced head orientation → exclusion of off-line zeros → RH
- **RH status:** unproved; EDQ remains open

## Fixed source and frozen proposals

The literal normalized unit remainder is `g_s(1)=conjugate(G(s))`, with

`B(s)=-1/[2*s*(1-s)]`, `G(s)=B(s)-zeta(s)/[s*(s+1)]`.

The strip is `0<Re(s)<1`. No factor H is assumed in an RH theorem.

**U1:** a holomorphic H on the entire strip satisfies `Im(g_s(1))=Im(zeta(s)*H(s))` at every strip point.

**U2:** finitely many connected open subsets of the strip have their own holomorphic multipliers satisfying the same pointwise identity, and together cover every positive-height strip zero.

Both proposals are false. The finite-cover theorem also allows empty domains; these contribute no zeros. The obstruction concerns this precise identity; it does not forbid arbitrary classwise proofs, other arithmetic identities, or EDQ itself.

## Dependency-closed paper proof

1. Strip membership excludes `s=0`, `s=1`, and `s=-1`. Thus B, G, and zeta are holomorphic there. The existing exact unit-remainder formula gives `g(1)=conjugate(G)`, so the phase identity is exactly `Im(G+zeta*H)=0`.
2. On a connected open domain the holomorphic function `G+zeta*H` has image in the real axis. The open mapping theorem therefore makes it one real constant c. Conversely `G+zeta*H=c` gives the phase identity. This is a full equivalence, not a one-way necessary condition.
3. At a zero rho, `c=B(rho)`. Globally, including the two rational singular parameters under Lean's total inverse convention, `B(s)=B(t)` iff `s=t` or `s+t=1`: injectivity of inverse reduces this to `(s-t)*(1-s-t)=0`. Two positive-height points cannot sum to one. Each chart consequently contains at most one positive-height zero, regardless of multiplicity.
4. The corpus's analytic Hardy theorem supplies critical-line zeros above every real height. The positive zeros contained in finitely many charts form a finite set, whose imaginary parts are bounded above. Hardy supplies a zero above that bound. This contradicts U2's exhaustive cover, and U1 is its one-chart case. No numerical zero location or computational certificate is used.

## Exact positive survivors

The connected-domain classification is `G+zeta*H=c`, with c real. On every zero-free strip domain, each real c supplies the holomorphic solution `H=(c-G)/zeta`; on a connected open zero-free domain these exhaust all solutions.

**S1, tangent and necessity.** At a positive-height strip zero rho in a phase germ,

`zeta'(rho)*(H(rho)-1/[rho*(rho+1)])=-(1-2*rho)/[2*(rho*(1-rho))^2]`.

This follows by differentiating the local constant identity. The rational derivative is nonzero at positive height. Consequently `zeta'(rho)!=0`. Also `B(rho)` is real. Its imaginary part is

`Im(rho)*(1-2*Re(rho))/(2*|rho*(1-rho)|^2)`,

so `Re(rho)=1/2`. This proves simplicity as well as critical-line membership; neither is assumed in the implication.

**S2, exact local converse.** Suppose rho is a simple critical-line zero. Put `c=B(rho)`, which is real, and `F=c-G`. Both F and zeta vanish at rho. Their analytic divided differences `dF(s)` and `dZ(s)` satisfy

`F(s)=(s-rho)*dF(s)`, `zeta(s)=(s-rho)*dZ(s)`.

The latter divided difference takes the nonzero value `zeta'(rho)` at rho and stays nonzero nearby. Hence `H=dF/dZ` is holomorphic at rho and satisfies `zeta*H=F` throughout a neighborhood, including rho itself. This proves the phase identity there. Thus local holomorphic phase-factor existence is **equivalent** to a simple critical-line zero. The construction neither proves all zeros simple nor proves RH.

This exact local classification is the nontrivial positive salvage. An infinite collection of these germs would still demand simplicity in addition to zero location. Zero-free solutions show why failure is specifically an extension-through-zeros obstruction.

## Formal status and remaining goal

The statements are proved in `ArithmeticUnitPhaseRigidity` and `ArithmeticUnitPhaseNoGo`, namespace `RHTower.DeletionMixedRefinement`. The literal source is linked through `normalizedWeightedRemainder_one_eq_star_source`; the principal capstones are `unitPhaseGerm_iff_simple_critical_zero`, `not_finite_unitPhaseIdentity_cover`, and `not_unitPhaseIdentity_strip`.

Verification record is maintained in [the formalized certificate](../3-formalized/arithmetic-unit-phase-classification.md). U1/U2 are retired only with the positive survivors formalized. No literature-wide novelty claim is made: this applies open mapping, rational algebra, local analytic division, and the corpus Hardy theorem to the fixed EDQ source.

The active RH goal still needs an independent arithmetic law controlling the exceptional head or orienting the joint chronological signature. The [uniform quartic-tail bound](../1-in-progress/edq-quartic-remainder-phase-cutoff.md) remains valid but does not supply that law. Proposed linear cutoff and complete-prefix/clock laws retain their separate frozen statements.

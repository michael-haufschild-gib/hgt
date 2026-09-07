# EDQ even reflection and midpoint exclusion

- **ID:** EDQ-ERE
- **Stage:** 3-formalized
- **Type:** exact even source bound and actual quantitative zero exclusion; Lean formalized
- **Sources:** ArithmeticFullReflectionResponse, ArithmeticReflectionErrorHeight, ArithmeticHardyResponseCoercivity, ZetaLineFirstMoment. Current Hardy and Speiser/Laguerre interfaces audited; no RH-dependent inequality used.

## Full chain and missing information

Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. The existing divided reflected difference controls the normalized derivative but its current disks admit whole off-line regions. The reflected sum supplies a separate quantitative midpoint value constraint from the same literal source.

## Paper proof

Let c=1/2+i*t, delta=Re(s)-1/2, r=1-conj(s), Z(s)=zeta(s)/(s*(s+1)), and A(s)=-1/[2*s*(1-s)]+1/[12*(s+1)]. The full arithmetic source is F(s)=conj(A(s)-Z(s)).

The paired density in F(s)+F(r)-2F(c) is exactly

2*P(x)*x^(-5/2)*(cosh(delta*log(x))-1)*exp(i*t*log(x)),

where abs(P)<=1/12. For abs(delta)<=1/2 its norm is at most delta^2*x^(-2)*log(x)^2/12. The exact integral of x^(-2)*log(x)^2 over x>1 is 2, giving norm(F(s)+F(r)-2F(c))<=delta^2/6, uniformly in height.

At a zero, reflection also vanishes. Retaining the rational terms yields norm(2*Z(c)+delta^2*E(s))<=delta^2/6, where

E(s)=-1/[c*(c^2-delta^2)]-1/[(1-c)*((1-c)^2-delta^2)]+1/[6*(c+1)*((c+1)^2-delta^2)].

Each quadratic denominator factors into the two shifted endpoints. For abs(t)>=1 all three factors in each term have norm at least abs(t), hence norm(E)<=13/(6*abs(t)^3)<=13/6. Therefore norm(Z(c))<=7*delta^2/6. Also norm(c*(c+1))<=6*t^2 in this height range. Thus every strip zero satisfies abs(hardyZ(t))<=7*t^2*delta^2.

Consequently abs(hardyZ(t))>=1/4 excludes every point at that height with abs(delta)<=1/(8*abs(t)); the bound gives at most 7/64<1/4. The corpus's unconditional dyadic second-moment floor supplies such heights arbitrarily high (a universal amplitude ceiling below 1/4 would contradict the floor). This yields actual explicit horizontal exclusion regions, not only a conditional disk translation.

## Limits

The amplitude floor is not proved at every height; critical zeros violate it. Arbitrarily high excluded segments do not cover the strip. No RH, simplicity, or all-height separation is asserted. The complete odd constraints and even value constraint remain available together.

## Gates

- [x] Current corpus and ledgers inspected; paper proof checked.
- [x] Scratch even source estimate and exact rational correction.
- [x] Explicit amplitude constraint and actual cofinal exclusion regions.
- [x] Leaf audit, new-only axioms, wiring, lint, and current ledgers.
- [x] Index refreshed (2 changed, 0 removed); both owned scratch sources removed; no owned Lean/lake process remains.
- [ ] Independent comparison excluding every off-line zero; RH.

## Formal certificate

- Leaf: `formal/GaloisForLFunctions/RHTower/ArithmeticEvenReflectionExclusion.lean` (357 lines, 16 theorems, 4 definitions), namespace `RHTower.DeletionMixedRefinement`.
- Exact source: `unitFullFourierSource_even_eq_integral`, `norm_unitFullFourierSource_even_le`.
- Exact rational transport: `reflectionEvenBoundary_pair`, `normalized_value_even_constraint_at_zero`, `norm_reflectionEvenCorrection_le`.
- Actual exclusion: `hardy_amplitude_at_zero_le`, `zeta_ne_zero_of_hardy_floor`, `exists_high_hardy_amplitude_floor`, `exists_high_even_reflection_exclusion`.
- Scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_even_reflection.lean`, exit 0, no diagnostics.
- Final audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticEvenReflectionExclusion`, exit 0; only this leaf built (4.5 seconds), dependencies replayed from cache. Umbrella import appended; no umbrella build.
- Axioms: only the 20 new declarations checked in `/tmp/edq_even_reflection_axioms.lean`, exit 0. Dependencies confined to `propext`, `Classical.choice`, `Quot.sound`; no admitted proof, added axiom, or computational certificate.
- Repository lint: exit 0. No old axiom checks or full builds.
- Cleanup: all owned check/build/axiom/index processes reached a terminal state. Implementation and axiom scratch sources removed; logs retained.
- Logs: `/tmp/edq_even_reflection.check.log`, `.build.log`, `.axioms.log`, `.lint.log`, `.index.log`.

The formal correction uses factored endpoint products rather than expanded critical-point quadratics. They are identical because `s=c+delta` and `r=c-delta`. This form exposes all three height factors directly and retains the full rational mean. The actual cofinal floor proof uses the existing Hardy second-moment lower bound and continuity, not numerical samples or a zero-location premise.

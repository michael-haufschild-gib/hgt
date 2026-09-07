# Literal half-order cross terms grouped by gcd

- **Stage:** 5-failed — SG1, the separate-component sign producer, is refuted in Lean.
- **Positive survivor:** exact masked homothety and complete gcd reconstruction; dependency-closed paper proof and Lean formalization complete.
- **Chain:** completed Guinand–Weil source -> marked rectangular current -> affine Suzuki checkpoints -> signed curvature -> coherent prime–polar–Gamma/unit-Riesz boundary -> Xi-screw Green -> RH.
- **Remaining target:** [SD1, aggregate signed diagonal dominance](../1-in-progress/mobius-divisor-source-diagonal-dominance.md), remains open. RH is neither proved nor refuted here.

## Frozen claim and exact obstruction

With the literal source `D(q)=log(q!)-sum_(n<=q)tau(n)+2 gamma q`, put

`K_d(M)=sum_(k=d..M-1) (sqrt(k+1)-sqrt(k)) D(floor(k/d))`,
`C_d(M)=mu(d)K_d(M)`,
`G_r(M)=sum_(1<=d,e<=M, d!=e, gcd(d,e)=r) C_d(M) C_e(M)`.

SG1 asserted `G_r(M)<=0` for every M and positive r. It is a stronger independent producer for SD1, not a reformulation. Lean proves the literal strict inequalities

`G_1(11)>1/100`,
`sum_(r=1..11) G_r(11)<-1/100`.

Thus a positive primitive component is compensated by other common-divisor components. The full SD1 inequality holds strictly at this witness. More strongly, Lean proves

`forall N:Nat, exists M r, N<=M and 1<=r and N<G_r(M)`.

Individual positive components are unbounded at unbounded cutoffs. This refutes even a fixed upper ceiling for every component. It does not refute a ceiling or sign for their complete sum.

## Exact positive survivor and paper proof

1. **Unsigned homothety:** `K_(rd)(rM)=sqrt(r) K_d(M)` for all natural r,M,d, including zeros. Since D(0)=0, replace the lower-truncated sum by the full range k<M. Split k<rM into blocks k=rq+i, i<r. For r>0 the floor is q/d, constant on the block, while the square-root increment telescopes to `sqrt(r)*(sqrt(q+1)-sqrt(q))`. Zero cases vanish directly. This retains the literal terminal block.
2. **Signed mask:** `C_(rd)(rM)=sqrt(r) mu(r) [if gcd(r,d)=1 then C_d(M) else 0]`. Coprime multiplicativity proves the first case; a shared prime makes rd nonsquarefree, so its Möbius coefficient is zero.
3. **Exact component classification:** scaling `(a,b)` to `(ra,rb)` bijects distinct coprime pairs in `[1,M]^2` with distinct pairs in `[1,rM]^2` having gcd r. Consequently
   `G_r(rM)=r mu(r)^2 sum_(a,b<=M, a!=b, gcd(a,b)=1) [if gcd(r,a)=1 then C_a(M) else 0] [if gcd(r,b)=1 then C_b(M) else 0]`.
   The prime exclusions on both legs remain explicit.
4. **Prime replication:** for prime p>M both masks are one and mu(p)^2=1, hence `G_p(pM)=p G_1(M)`. The eleven witness gives `G_p(11p)>p/100`. Euclid's unbounded primes, choosing p>=100N+12, prove the unbounded statement above.
5. **Complete reconstruction:** every ordered distinct pair has exactly one positive gcd at most M, so `sum_(r<=M)G_r(M)=(sum_(d<=M)C_d(M))^2-sum_(d<=M)C_d(M)^2`. Controlling this complete signed sum remains the open source obligation; its partition does not supply its sign.

These identities extract and formalize the surviving source structure. They do not substitute a weakened claim for SG1.

## Analytic witness proof

Write `(x,a,b,c,y,e,z)=(C_1,-C_2,-C_3,-C_5,C_6,-C_7,C_10)` at M=11. Lean establishes

`x in [.15,.18], a in [.20,.21], b in [.19,.20], c in [.14,.15],`
`y in [.13,.14], e in [.10,.11], z in [.023,.025]`.

Channels 4,8,9,11 vanish exactly. The gamma bounds follow from the harmonic half-reciprocal inequality at n=16 and the existing corrected upper bound, giving `.5768<=gamma<=.57722`. Analytic logarithm bounds for 2,3,5, together with
`3 log2-15/112 <= log7 <= 3 log2-1/8`, bound every log-factorial term. The log7 sandwich follows from elementary logarithm inequalities at 8/7 and 7/8. Rational square-root sandwiches follow from ordered square identities. These analytic inequalities, not experimental values, bound the ten literal source defects and the seven finite channels.

The primitive cross term is exactly
`2[ab+ac+ae+bc+be+ce-x(a+b+c+e-y-z)-bz-cy-ey-ez]`.
Interval multiplication gives a strict lower bound 1/100. The complete cross term is
`(x-a-b-c+y-e+z)^2-(x^2+a^2+b^2+c^2+y^2+e^2+z^2)`.
The sum lies in `[-.367,-.285]` and the diagonal is at least `.145629`, giving a strict upper bound -1/100. All finite expansions and rational inequalities are kernel-checked.

## Lean and audit

Four modules, all wired once into `RHTower.lean`:

- `MobiusDivisorAbelHomothety.lean`: unsigned homothety, signed coprime homothety and complete shared-prime mask.
- `MobiusDivisorElevenChannelBounds.lean`: the seven analytic channel boxes and four exact zeros.
- `MobiusDivisorAbelGcdCross.lean`: complete reconstruction, masked component homothety and prime replication.
- `MobiusDivisorGcdCrossObstruction.lean`: opposite witness signs, prime lower bound and unbounded positive components.

All four passed individual foreground `lake env lean` source checks; exact oleans were produced only for these dependencies. No umbrella or large rebuild was run. A single `/tmp` axiom audit of only this work's 16 public declarations reports exactly `propext`, `Classical.choice`, `Quot.sound`; no added axioms, `sorryAx` or computational certificate axioms. Global formal lint passed after wiring, with existing file-size warnings. The declaration index was refreshed. No Lean process remains. No numerical result is imported into a proof.

## Corpus and exploratory evidence

The corpus starting points were `Sieve.sum_offDiagPairs_eq_sum_primitiveTriples`, `mobius_coprime_dilation_pair_product`, exact quotient-block transport, and the signed hyperbola diagonal theorem. They provide arithmetic incidence and orientation, not aggregate sign.

The [screen and data](../2-fully-proven/computations/ccm-fu-gcd-cross-sign-2026-09-06/README.md) cover every M<=100 and every r<=M: 5050 values, including 168 positive components. The first witness was independently evaluated at 80 digits. This numerical guidance selected the analytic witness; the formal proof is independent of those outputs.

# CCM-FU: prescribed prime two with a bounded remaining front

- **Stage:** 3-formalized.
- **Type:** [BRIDGE], actual finite prime-batch construction.
- **RH status:** Neither proof nor falsification of RH.

## Actual theorem

There is a fixed b>=15 such that, for every fixed integer J>=0 and every
C>0, there is A>0 with the following property for all sufficiently large N.
Put M=14(b+1)N and let W
be the existing three actual prime windows with floor(M/p)=2,7,14.
Let P contain all odd primes below 15, exclude 2, and leave W unused.
Assume Psi(M,P)<=C*M^2. Suppose every remaining prime OTHER THAN 2 has
floor(M/q)<=J. Then an actual finite set L satisfies

`2 in L`, `L subset {2} union W`,
`card(L)=ceil(A*sqrt(M))+1`, `Psi(M,P union L)+M <= Psi(M,P)`.

A and the threshold depend on J and C, and are uniform in P, which may
vary with N and have unbounded cardinality. The prescribed prime's own quotient floor(M/2)
is unrestricted. This is different from the earlier producer, which
required the prescribed prime itself to have quotient at most 14.

## What the diagnostic ruled out

The [frozen RunPod diagnostic](../2-fully-proven/computations/ccm-fu-prepared-two-envelope-2026-09-08/README.md)
checked all 3,185,446 prepared-core states at M=16..96. Pointwise envelope
monotonicity for inserting 2 failed numerically 526 times. At the first
state, M=84 and P={3,5,7,11,13}, current energy decreases but the successor
at 17 increases the envelope by about 0.0616854. Independent 80-decimal
reconstruction retains all successors and confirms the sign. This is
numerical evidence, not a Lean counterexample or a proof input. No tested
state violated the original diagonal budget after inserting 2.

The positive replacement retains the new envelope excess and pays for it.
It does not assume that current-energy contraction preserves future costs.

## Remaining-front bound

For an arbitrary available prescribed prime p, assume all remaining primes
q after p is inserted have floor(M/q)<=K. Write E=Psi(M,P). The energy at
P+p already obeys Q(P+p)<=E, by the definition of the old envelope. For
each remaining q, the existing complete quotient transport gives

`Q(P+p+q)-Q(P+p) <= (6/5)*floor(M/q)*sqrt(M*Q(P+p))`.

Thus the full new envelope satisfies the general bound

`Psi(M,P+p) <= E+(6/5)*K*sqrt(M*E)`.

This charges the cost to the other remaining primes instead of to p's own
quotient. No restriction on the starting core, signs, or overlaps is used
in this general transport inequality.

For p=2 and K=J, put E'=Psi(M,P+2), F=2*(J+1). With E<=C*M^2,

`E' <= E+F*sqrt(C)*M*sqrt(M) <= C'*M^2`,
`C'=C+F*sqrt(C)`.

The second inequality uses M>=1. This controls the entire remaining front,
including the successors newly created by inserting 2.

## Actual repair and complete payment

Use the existing clipped source geometry at P, with normalized two-vectors
`v_p=sqrt(p/M)*(I_{p,0},I_{p,2})` of product norm at most 9, inward margin c>0,
and merged square reserve at least d*M per source prime. These constants
are uniform in P because its child fibres through cutoff 15 agree with
the prepared core.

Choose n distinct unused window primes by the existing finite directional
construction, starting with zero displacement. Its normalized total has
coordinate absolute sum at most H=2*(81/c+9), independently of n. Every
partial selected set of cardinality below the minimum window capacity
minus one still leaves each direction available.

After inserting 2, the exact child profile becomes `(I_{p,0}+I_{p,2},0)`.
Consequently this same selected batch S has merged physical displacement

`Z=sum_(p in S) sqrt(p)*(I_p,0+I_p,2)`, `|Z|<=H*sqrt(M)`,

and consumes the exact reserve

`T=sum_(p in S) p*(I_p,0+I_p,2)^2 >= d*n*M`.

All selected primes are at least 15 and their adjacent child cutoffs are
at most 15, so selected sources remain mutually inactive. Apply the full
approximate-envelope reserve law at P+2. Both reserves coincide with T:

`Psi(M,P+2+S)+T <= E'+2*sqrt(E')*|Z|+|Z|^2`.

Set

`A_r=(2*sqrt(C')*H+H^2+1)/(d/2)`,
`A_f=2*F*sqrt(C)/d`, `A=A_r+A_f`, `n=ceil(A*sqrt(M))`.

The prime number theorem ensures this n is at most the available minimum
window capacity minus one for sufficiently large N. Half the reserve pays
the complete receiving error plus M:

`2*sqrt(E')*|Z|+|Z|^2+M <= (d/2)*n*M`.

The other half pays the new-front excess:

`E'-E <= F*sqrt(C)*M*sqrt(M) <= (d/2)*n*M`.

Adding these inequalities and using T>=d*n*M proves the asserted endpoint
with L={2} union S. Since every member of S exceeds 2, the cardinality is
exactly n+1. No numerical result enters any inequality in this proof.

## Lean and validation

- `MobiusDivisorRemainingFrontTransport.lean`:
  `mobiusDivisorSuccessorEnvelope_insert_le_remaining_quotient`.
- `MobiusDivisorPrescribedWindowRepair.lean`:
  `exists_mobiusDivisor_two_bounded_front_repair`.

Scratch checks and exact `lake env lean` leaf emissions passed without
warnings, including the arbitrary fixed J generalization. Only these two
new declarations were axiom-audited, each once. Both depend solely on
`propext`, `Classical.choice`, and `Quot.sound`; there is no added axiom,
proof hole, or computational premise. The numerical cutoff-84 values are
absent from the Lean proofs.

The new transport leaf is wired into the RHTower umbrella and imported by
the actual producer. Generated indexes were refreshed. The repository-wide
`scripts/formal_tools.py lint --check-generated` check reports six unrelated
unwired Coppo modules in HTGeometry and three stale generated indexes under
concurrent work; it reports no proof-debt or RHTower wiring error. The
`lake build` package audit remains pending because its known dependency
expansion would rebuild broad stale prerequisites. No full or umbrella
build was run. Owned scratch files and local/remote processes were cleaned.

## Remaining RH obligation

Here J is fixed before N; the theorem supplies no uniform license to choose J=M.
This handles the last exceptional small prime after every OTHER remaining
prime has bounded quotient. It does not prepare that front, renew depleted
windows, or handle several unresolved small primes with overlapping child
profiles. The quadratic admission bound remains an invariant to establish
and propagate through the complete source. An exhaustive prime order and
its uniform signed Abel estimate remain unproved.

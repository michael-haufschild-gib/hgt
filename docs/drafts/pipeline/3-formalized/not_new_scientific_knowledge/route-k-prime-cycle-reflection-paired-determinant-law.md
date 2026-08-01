# Route K prime-cycle reflection-paired determinant law

- **ID:** `route-k-prime-cycle-reflection-paired-determinant-law`
- **Stage:** 3-formalized
- **Type:** `THEOREM` / `[NOT NEW SCIENTIFIC KNOWLEDGE]` / Route K guardrail
- **Source:** `../../1-in-progress/route-k-prime-cycle-trace-class-relocation.md`
- **Statement:** Every closed-walk-flat sign field on a finite connected support graph is a
  determinant-blind diagonal gauge.  On a positive three-label background, a nonzero triangle is
  detected by the centered reflection-paired determinant and first survives its trace cumulants at
  quartic order.

## Gates

- [x] 0 → 1: source role and falsified alternatives recorded on active Route K card
- [x] 1 → 2: exact determinant identities and detection proof dependency-closed on paper
- [x] 2 → 3: unconditional Lean proof, umbrella import, target build, standard-axiom audit
- [ ] 3 → 4: no publication claim; elementary parent identity

## Theorem `[PROVED HERE]`

Let `q_0,q_1,q_2>0`, let `x_01,x_12,x_20` be nonzero real numbers, and put

```text
A_x = [q_0   x_01  x_20;
       x_01  q_1   x_12;
       x_20  x_12  q_2].
```

Write `P_x(w)=det(wI-A_x)`.  Let `x'` be obtained by replacing `x_01` by `-x_01`,
and define the reflection-paired characteristic function

```text
D_x(w)=P_x(w)P_x(-w).
```

Then

```text
P_x(w)
= (w-q_0)((w-q_1)(w-q_2)-x_12^2)
  -x_01^2(w-q_2)-x_20^2(w-q_1)-2x_01x_12x_20,        (1)

P_x(w)-P_x'(w)=-4x_01x_12x_20,                       (2)

D_x(w)-D_x'(w)
= -8x_01x_12x_20
  (-(q_0+q_1+q_2)w^2-q_0q_1q_2
    +q_0x_12^2+q_1x_20^2+q_2x_01^2).                 (3)
```

Consequently:

1. if `x_01x_12x_20=0`, both `P` and `D` are unchanged by the edge flip;
2. if all three edges are nonzero, then `D_x(w)≠D_x'(w)` for `w=0` or `w=1`.

## Paper proof

Laplace expansion of `det(wI-A_x)` gives `(1)`.  Only its triangle monomial changes sign under
`x_01↦-x_01`, proving `(2)`.  Apply `(1)` at `w` and `-w`, multiply, subtract the flipped product,
and collect terms to obtain `(3)`.

The forest claim follows immediately when the cycle product vanishes.  For detection, set

```text
c=-q_0q_1q_2+q_0x_12^2+q_1x_20^2+q_2x_01^2.
```

If `c≠0`, `(3)` is nonzero at `w=0`.  If `c=0`, its bracket at `w=1` is
`-(q_0+q_1+q_2)`, nonzero because every `q_i>0`.  The edge product and scalar factor `-8` are also
nonzero.  Hence one of the two test points detects the cycle.  ∎

No numerical experiment or divisor data enters the proof.

## General flat-gauge theorem `[PROVED HERE]`

Let `G` be a finite connected graph, let `A` be a real matrix whose off-diagonal support lies in
`G`, and let `c` be a symmetric Boolean edge field.  Assume the XOR sum of `c` on every finite
closed walk is zero.  The formalized Boolean flatness criterion gives `epsilon:V→Bool` such that

```text
c(i,j)=epsilon(i) XOR epsilon(j)
```

on every edge.  Put `s_i=(-1)^epsilon(i)` and `S=diag(s_i)`.  Edge twisting by `c` is exactly
`A_c=SAS`: this holds on edges by the XOR product law, on the diagonal because `s_i²=1`, and away
from the support because both entries vanish.  Moreover

```text
wI-A_c = S(wI-A)S.
```

Taking determinants and using `det(S)²=prod_i s_i²=1` proves

```text
det(wI-A_c)=det(wI-A).
```

Applying the equality at `w` and `-w` proves paired blindness.  Hence nontrivial closed-walk
holonomy is necessary for determinant-visible sign orientation on every finite packet, not only a
triangle.  This is the signed-graph balance mechanism composed with determinant similarity; both
parents are classical.

## Trace-cumulant theorem `[PROVED HERE]`

For the three-label packet above, write `T_m(x)=Tr(A_x^m)` and

```text
T_m^pair(x)=T_m(q,x)+T_m(-q,-x).
```

Direct closed-walk expansion gives

```text
T_2(x)=T_2(x'),
T_3(x)-T_3(x')=12x_01x_12x_20,
T_4(x)-T_4(x')=16(q_0+q_1+q_2)x_01x_12x_20,

T_3^pair(x)=0,
T_4^pair(x)-T_4^pair(x')
  =32(q_0+q_1+q_2)x_01x_12x_20.                       (4)
```

For `m=2`, every closed walk traverses each nonloop edge with even total parity.  For `m=3`, the
six oriented triangle walks contribute `6x_01x_12x_20`, so the edge flip changes the trace by
`12x_01x_12x_20`.  For `m=4`, a sign-sensitive closed walk traverses the triangle and inserts one
diagonal step.  Each diagonal vertex contributes eight rooted oriented walks, giving
`8(q_0+q_1+q_2)x_01x_12x_20`; the flip doubles it.  The negative sector cancels odd powers and
doubles even powers, proving `(4)`.

When every `q_i>0` and every edge is nonzero, the right side of `(4)` is nonzero.  Therefore the
quadratic regularized-determinant cumulant is blind, cubic is reflection-cancelled, and quartic is
the first reflection-even trace cumulant retaining triangle orientation.

## Completed unit--double source instantiation `[PROVED HERE]`

Let `R(p,q)` be the existing real symmetric completed unit--double physical pair response at the
prime-log nodes and put

```text
H(p,q,r)=R(p,q)R(q,r)R(r,p).
```

This is a source-defined triangle coordinate and is invariant under cyclic permutation and every
swap because `R` is symmetric.  Substituting the three edges
`(R(p_0,p_1),R(p_1,p_2),R(p_2,p_0))` into `(2)` and `(4)` gives exactly

```text
P_x(w)-P_x'(w)=-4H(p_0,p_1,p_2),

T_4^pair(x)-T_4^pair(x')
 =32(q_0+q_1+q_2)H(p_0,p_1,p_2).                       (5)
```

No nonvanishing claim is made: `(5)` identifies what must be estimated.

For a finite prime packet `P`, source row marginals force the balanced diagonal

```text
C_P(p,p)=j(p)-sum_(s in P\{p})R(p,s),
```

while `C_P(p,q)=R(p,q)` off diagonal.  Hence off-diagonal entries are packet-independent.  If a
new prime `r` is inserted, finite-sum insertion gives

```text
C_(P union {r})(p,p)-C_P(p,p)=-R(p,r)
```

for every old `p`, and summing absolute values gives the exact `ell1` shell law

```text
sum_(p in P)|C_(P union {r})(p,p)-C_P(p,p)|
 =sum_(p in P)|R(p,r)|.                                (6)
```

Thus finite marginal balancing is not itself compression-compatible.  Equation `(6)` is the
precise analytic debt for any trace-norm limit; the present theorem neither proves nor assumes
that debt.

## Route consequence

Diagonal corrections and forests cannot carry switching-invariant determinant orientation.
Centered-Xi evenness does not remove this obstruction: reflection pairing still detects closed
cycle holonomy through the positive Riemann--von Mangoldt background.  Therefore any surviving
Route K trace-class relocation must derive compatible closed prime--Gamma cycles from source data.
This is a necessary finite boundary, not the missing infinite construction or an RH proof.

## Lean certificate

Modules:
`formal/GaloisForLFunctions/RHTower/XiPrimeMarkedCycleRelocation.lean`.
`formal/GaloisForLFunctions/RHTower/XiPrimeMarkedCycleGauge.lean`.
`formal/GaloisForLFunctions/RHTower/XiPrimeMarkedUnitDoubleCycleCandidate.lean`.

Declarations:

```text
routeKThreePrimeRelocationMatrix_transpose
routeKThreePrimeCharacteristic_eq
routeKThreePrimeCharacteristic_sub_edgeFlip
routeKThreePrimePairedCharacteristic_sub_edgeFlip
routeKThreePrimeCharacteristic_edgeFlip_eq_of_cycle_eq_zero
routeKThreePrimePairedCharacteristic_edgeFlip_eq_of_cycle_eq_zero
exists_routeKThreePrimePairedCharacteristic_ne_edgeFlip
routeKFiniteCharacteristic_signGauge_eq
exists_routeKGraphEdgeTwist_eq_diagonalSignGauge_of_flat
routeKFiniteCharacteristic_graphEdgeTwist_eq_of_flat
routeKFinitePairedCharacteristic_graphEdgeTwist_eq_of_flat
routeKThreePrimeTracePower_two_edgeFlip_eq
routeKThreePrimeTracePower_three_sub_edgeFlip
routeKThreePrimeTracePower_four_sub_edgeFlip
routeKThreePrimePairedTracePower_three_eq_zero
routeKThreePrimePairedTracePower_four_sub_edgeFlip
routeKThreePrimePairedTracePower_four_ne_edgeFlip
routeKUnitDoubleTriangleHolonomy_cycle
routeKUnitDoubleTriangleHolonomy_swap
routeKUnitDoubleThreePrimeCharacteristic_sub_edgeFlip
routeKUnitDoubleThreePrimePairedTracePower_four_sub_edgeFlip
xiUnitDoubleCompletedBalancedResponseCoupling_offDiagonal_packet_independent
xiUnitDoubleCompletedBalancedResponseCoupling_insert_diagonal_sub
sum_abs_xiUnitDoubleCompletedBalancedResponseCoupling_insert_diagonal_sub
```

`lake env lean GaloisForLFunctions/RHTower/XiPrimeMarkedCycleRelocation.lean` passes.  The missing
module object was then built with
`lake build GaloisForLFunctions.RHTower.XiPrimeMarkedCycleRelocation`; target build passes.
`lake env lean GaloisForLFunctions/RHTower/XiPrimeMarkedCycleGauge.lean` and its targeted module
build also pass.  `#print axioms` for all headline determinant, flat-gauge, and cumulant theorems
reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The unit--double candidate source check and targeted build pass; its seven headline source-cycle
and shell theorems have the same standard-axiom audit.

Umbrella:
`formal/GaloisForLFunctions/RHTower.lean` imports the module.

## Log

- 2026-08-01 — determinant and reflection-paired laws proved on paper.
- 2026-08-01 — theorem formalized unconditionally; target source check, module build, umbrella, and
  standard-axiom audit passed; promoted through Stage 2 to Stage 3.
- 2026-08-01 — general flat-switching determinant theorem and exact quadratic/cubic/quartic paired
  trace-cumulant boundary proved and formalized; second target build and axiom audit passed.
- 2026-08-01 — literal unit--double source cycle instantiated and exact packet-insertion diagonal
  shell obstruction formalized; third source check, target build, umbrella, and axiom audit passed.

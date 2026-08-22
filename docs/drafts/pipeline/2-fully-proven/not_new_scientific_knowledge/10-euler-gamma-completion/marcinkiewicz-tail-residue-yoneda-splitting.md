# Marcinkiewicz tail--residue Yoneda pairing splits

- **ID:** `marcinkiewicz-tail-residue-yoneda-splitting`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ROUTE-D NO-GO (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Inputs:** `logarithmic-marcinkiewicz-prime-tail-boundary.md`;
  `prime-shift-residue-closability-criterion.md`

## Statement

Let

```text
0 -> M_0 -> M_log -> Q_log -> 0                              (E)
```

be the logarithmic Marcinkiewicz prime-tail extension, and let `u=[one]` be the nonzero unit Euler
class in `Q_log`.

1. The pullback of `(E)` along `i_u:C->Q_log`, `lambda |-> lambda u`, is a split Banach extension.
2. For every bounded linear reader `ell:M_0->C`, the pushout of `(E)` along `ell` is a split Banach
   extension.
3. Consequently every ordinary Banach-Yoneda pairing of `u` with a bounded vanishing-tail reader is
   zero.
4. Replacing the bounded reader by the canonical prime-shift residue functional does not produce an
   unconditional unbounded Fredholm pairing: that functional is closable exactly when RH holds.  On
   RH it is the zero functional; off RH it has no closed graph and therefore supplies no unbounded
   Fredholm or `KK` cycle.
5. In every unital operator-algebra or `C*`-algebra extension modeling the same quotient, the
   `K`-theory connecting map annihilates the Euler unit class, and annihilates every boundary phase
   class having an actual unitary prime-field lift.

Thus the missing joint source--divisor incidence cannot be the connecting class of the evident
Banach exact sequence, nor the graph class of its canonical residue reader.  A live construction must
introduce a different source-forced singular category or a different closed operator whose
closedness is not already equivalent to RH.

## Pullback splitting

Let `q:M_log->Q_log` be the quotient map.  The pullback space is

```text
P_u={(b,lambda) in M_log x C : q(b)=lambda u}.
```

Since `q(one)=u`, the bounded linear map

```text
s_u:C->P_u,
s_u(lambda)=(lambda one,lambda)
```

is a right inverse to the projection `P_u->C`.  Hence

```text
0 -> M_0 -> P_u -> C -> 0
```

splits continuously.  In particular the distinguished arithmetic class `u` creates no nontrivial
one-dimensional pullback extension.  The split is not chosen by Hahn--Banach: the actual unit Euler
field is already a distinguished lift.

## Pushout splitting

Let `ell:M_0->C` be bounded.  By Hahn--Banach it extends to a bounded linear functional

```text
L:M_log->C.
```

Write the pushout as

```text
E_ell=(M_log direct_sum C)/{(m,-ell(m)):m in M_0}.
```

The map

```text
[b,c] |-> (q(b),c+L(b))
```

is well defined: replacing `(b,c)` by `(b+m,c-ell(m))` changes the second component by
`-ell(m)+L(m)=0`.  It is a bounded linear isomorphism

```text
E_ell ~= Q_log direct_sum C
```

compatible with the quotient and scalar-inclusion maps.  Thus the pushed-out extension splits.
Pulling this split extension back along `i_u` remains split, proving the vanishing of every such
Banach-Yoneda pairing.

## Canonical residue graph

The prime-shift residue card constructs a canonical densely defined functional

```text
R_res:D_res subset M_0 -> C
```

with

```text
R_res(tau_z)=-ord_z(zeta),       1/2<Re(z)<1.
```

It proves the equivalence

```text
R_res is closable  <->  R_res=0  <->  RH.                (C)
```

If RH holds, the graph operator is zero and any index pairing made directly from it is trivial.  If
RH fails, `(C)` says its graph is not closable.  A nonclosable operator has no closed extension with
that graph and cannot be the unbounded operator in an ordinary Fredholm module, spectral triple, or
unbounded `KK` cycle.  Declaring such a cycle to exist would therefore insert the RH side of `(C)` as
an analytic regularity hypothesis.

This is not merely the failure of one norm.  The sequence witnessing nonclosability is explicit: a
right-half zero `z` gives finite truncations of `tau_z` tending to `tau_z` in `M_0`, while their
residue values are zero and `R_res(tau_z)` is the nonzero multiplicity.  Any repair must change the
operator, its domain, or its topology by additional source data.

## Lifted `K`-classes have zero boundary

Suppose a unital operator-algebra extension

```text
0 -> J -> A -> B -> 0
```

is chosen to represent a multiplicative completion of the tail quotient.  Exactness of the six-term
`K`-theory sequence says that every class in the image of `K_*(A)->K_*(B)` has zero connecting
class.  The quotient unit is the image of the unit of `A`; hence

```text
delta([1_B])=0.
```

Likewise a critical boundary phase `p |-> p^(-it)` is already a bounded unitary prime field.  In
every realization containing that unitary as a lift, its quotient `K_1` class also has zero boundary.
The same conclusion holds equivariantly whenever the displayed lift respects the chosen Real or
reflection structure.

Thus a nonzero connecting index cannot be extracted from the unit tail or a lifted phase orbit by
changing only the homology theory.  Its symbol must fail to lift for a reason constructed jointly
from the source and divisor.  Declaring that failure to be the off-line zero count would again put
the target into the symbol unless an independent source construction proves it.

## Exact route boundary

- `[CLOSED]` Pulling the tail extension back to the unit Euler line gives a split extension.
- `[CLOSED]` Pushing it out through any bounded scalar reader gives a split extension.
- `[CLOSED]` The canonical residue graph cannot itself be an unconditional unbounded index cycle.
- `[CLOSED]` Ordinary and equivariant connecting maps vanish on the lifted unit/phase classes.
- `[OPEN CORE]` A viable secondary invariant must use a different closed source construction whose
  regularity is proved before divisor residues are read.  Merely renaming nonclosability as an
  anomaly, extension class, or index does not qualify.

## Novelty audit

One-dimensional pullbacks of Banach quotients split after choosing a lift, scalar pushouts split by
Hahn--Banach, and closedness is required for unbounded Fredholm theory.  The theorem is a direct
functional-analytic audit of the project interface and is not new scientific knowledge.

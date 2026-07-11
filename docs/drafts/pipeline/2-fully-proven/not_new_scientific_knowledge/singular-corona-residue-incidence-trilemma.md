# Singular corona--residue incidence trilemma

- **ID:** `singular-corona-residue-incidence-trilemma`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Statement:** Multiplying the actual unit tail by a right-strip prime character gives a canonical
  source-defined residue incidence, but it cannot produce a protected corona charge.  If the
  incidence descends continuously through `Q_log`, it is zero on the entire vanishing-tail layer.
  If it detects an off-line zero, it is necessarily nonclosable; its closed-graph vertical defect
  is then all of `C`, so multiplicity and integer count are erased.  The current singular
  corona--divisor proposal is therefore either zero, RH-equivalent, or nonquantized.

## Goal

After continuous joint source/germ invariants and finite algebraic corona expressions are removed,
the remaining Route A proposal is a singular pairing between

```text
[one] in Q_log=M_log/M_0
```

and the canonical prime-shift residue graph on `M_0`.  The desired output is an even nonnegative
integer measuring off-line divisor content.

This card constructs the canonical incidence that actually exists and proves that its graph defect
cannot carry such an integer.

## Gates

- [x] 0 -> 1: bounded shift multiplier and residue pullback isolated
- [x] 1 -> 2: complete paper proof; no open dependency
- [x] parent-theory attack: bounded diagonal multipliers, the dense-kernel graph lemma, and the
  vertical-fibre dichotomy are standard functional analysis, so the result is `[BRIDGE]`
- [ ] 2 -> 3: no isolated Lean formalization selected; the abstract graph-fibre lemma is routine,
  while the prime-tail analytic continuation is already the paper-level bottleneck

## 1. Tail spaces and the canonical residue graph

The logarithmic Marcinkiewicz prime-tail space is

```text
||b||_M = sup_(X>=2) 1/log X *
            sum_(p<=X) (log p)/p |b_p|.
```

Let `M_0` be the closure of finite-support fields and put

```text
Q_log=M_log/M_0.
```

The actual unit field `one_p=1` lies in `M_log\M_0` and gives the nonzero class `[one]`.

For `z` in the open right strip

```text
S_+={z : 1/2<Re z<1},
```

define

```text
tau_z(p)=p^(1/2-z).                                      (1)
```

Every `tau_z` lies in `M_0`.  The canonical prime-shift residue functional

```text
R_res : D_res=c00 direct_sum span{tau_z:z in S_+} -> C   (2)
```

satisfies

```text
R_res(tau_z)=-ord_z(zeta).                               (3)
```

It vanishes on `c00` and is closable on `M_0` if and only if RH holds.

## 2. Shift multiplication carries the corona into the vanishing layer

For `z in S_+`, define the diagonal multiplier

```text
(S_z b)_p=tau_z(p)b_p.                                  (4)
```

Write `epsilon=Re z-1/2>0`.  Then

```text
S_z : M_log -> M_0                                      (5)
```

is bounded.

### Proof

Put

```text
alpha_p=(log p)/p |b_p|,
K=||b||_M.
```

On the dyadic block `2^k<p<=2^(k+1)`,

```text
sum alpha_p p^(-epsilon)
  <= 2^(-k epsilon) sum_(p<=2^(k+1)) alpha_p
  <= K (k+1)(log 2) 2^(-k epsilon).                     (6)
```

The right side is summable in `k`.  Hence

```text
sum_p (log p)/p |(S_z b)_p| < infinity,                 (7)
```

continuously in `||b||_M`.  Weighted absolute summability implies membership in `M_0`, proving
(5).  QED.

In particular,

```text
S_z(one)=tau_z,
R_res(S_z(one))=-ord_z(zeta).                            (8)
```

Thus a canonical source-to-divisor incidence already exists on the distinguished representative
`one`.  Finite Euler changes do not alter it: if `f in c00`, then `S_z f in c00` and

```text
R_res(S_z(one+f))=R_res(tau_z)=-ord_z(zeta).             (9)
```

The issue is not construction of a residue pairing.  The issue is whether it descends from the
representative `one` to its corona class and carries a protected sign or integer.

## 3. Continuous descent cannot detect a zero

Suppose a linear incidence at `z` extends to a continuous functional

```text
Lambda_z : M_log -> C
```

which is invariant under `M_0`, equivalently factors through `Q_log`.  Then

```text
Lambda_z|_(M_0)=0.                                      (10)
```

Since `S_z(M_log) subset M_0`, every continuously descended pairing of the form

```text
b |-> Lambda_z(S_z b)
```

is identically zero.  In particular it cannot take the nonzero residue value in (8).

Therefore a corona pairing that detects an off-line zero cannot be continuous on the quotient.  It
must use the nonclosable graph of `R_res` after the shift has entered `M_0`.

## 4. The full shifted residue kernel is already the divisor

For `z,w in S_+`, whenever the translated point avoids the source pole, the prime series of
`S_z(tau_w)` is shifted twice:

```text
S_z(tau_w)=tau_(z+w-1/2),
R_res(S_z(tau_w))=-ord_(z+w-1/2)(zeta).                 (11)
```

Thus the bivariate singular incidence kernel is

```text
K_res(z,w)=-ord_(z+w-1/2)(zeta).                        (12)
```

It is a Hankel kernel in the additive shift variables, but it is exactly the continued prime-zeta
divisor read after translation.  No sign law has been gained.

For fixed `z` with `sigma=Re z`, omit from the character domain the single `w` for which
`z+w-1/2=1`, so that the known source pole is not counted as an RH defect.  On this pole-excised
domain, the restriction of the pulled-back residue graph to `M_0` is closable exactly when zeta has
no zero with real part greater than `sigma`.

Indeed, if `rho` is such a zero, choose

```text
w=rho-z+1/2.
```

Then `w in S_+`, equation (11) gives a nonzero residue, and finite truncations of `tau_w` produce
the standard null sequence witnessing nonclosability.  Conversely, every nonzero value in (11)
comes from a zero at `z+w-1/2`, whose real part is greater than `sigma`.

Letting `sigma` decrease to `1/2` recovers the existing equivalence

```text
all shifted residue graphs closable <-> RH.              (13)
```

The singular incidence is therefore an exact zero-free-region filtration, not an independent
positivity mechanism.

## 5. A nonclosable scalar graph has no integer defect

Let `L:D->C` be any densely defined linear functional on a topological vector space.  Define the
vertical fibre of its graph closure by

```text
V_L={c in C : (0,c) lies in closure(Graph L)}.           (14)
```

### Theorem: scalar vertical-fibre dichotomy

```text
V_L={0}  if L is closable,
V_L=C    if L is not closable.                           (15)
```

### Proof

The set `V_L` is a closed complex-linear subspace of the one-dimensional complex vector space
`C`.  Hence it is either `{0}` or `C`.  By definition, `L` is closable exactly when the vertical
fibre is `{0}`.  QED.

Apply this to `R_res` or any shifted pullback in Section 4.  A single off-line zero gives one
nonzero vertical value, hence the entire scalar line.  The graph closure forgets:

- the residue magnitude;
- zero multiplicity;
- the number of off-line zeros; and
- the even FE--Schwarz quartet count.

Thus nonclosability can encode the binary predicate “some off-line zero exists,” but it cannot be
the proposed even nonnegative integer charge.

## 6. The trilemma

Every incidence built from the present corona and residue graph falls into one of three cases.

### Continuous quotient incidence

It annihilates `M_0`.  Since every right-strip shift of `[one]` lands in `M_0`, the incidence is
zero and detects no zero.

### Canonical residue incidence

It is the kernel (12), hence reads the zeta divisor directly.  Proving its vanishing or closability
is exactly RH or a zero-free-region restatement.

### Nonclosable graph defect

Its vertical fibre is all of `C`, so it carries no protected sign, multiplicity, or integer count.

Therefore the current conjectural pairing

```text
[one] in Q_log  x  FE--Schwarz divisor
    -> even nonnegative off-line integer                (16)
```

does not arise from the existing linear corona/residue interface.

## 7. Route consequence

The singular linear corona--divisor route is closed as a mechanism.

Together with `fe-schwarz-prime-corona-horizontal-grade-collapse.md`, this excludes:

1. finite algebraic quartet-character expressions;
2. norm-continuous or holomorphic boundary-character families;
3. bounded quotient pairings;
4. the canonical shifted residue kernel as an independent theorem; and
5. integer charge extracted from nonclosability of the scalar residue graph.

`[OPEN CORE]` A surviving weighted-tail version of Route A would need a new nonlinear or
higher-dimensional singular object whose defect retains quantized multiplicity before graph
closure, while not reconstructing the divisor and then applying an RH-equivalent sign test.  No
such object is present in the current source, corona, or Lean interfaces.

## Scientific status

This is `[BRIDGE]`, not new scientific knowledge.  The multiplier estimate is a dyadic summability
argument; the shifted kernel is analytic-continuation bookkeeping; and the vertical-fibre
dichotomy is elementary graph theory for a scalar functional.  The contribution is the exact
closure of the proposed singular linear corona charge, not a new parent theorem.

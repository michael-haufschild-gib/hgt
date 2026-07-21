# Suzuki anchored Euler--Wronskian elimination of linear escape

- **ID:** `suzuki-anchored-euler-wronskian-escape-elimination`
- **Stage:** 3-formalized
- **Type:** THEOREM / REPRESENTATION CHANGE / PRODUCER FRONTIER
- **Scientific status:** `[LEAN-PROVED] [PAPER-PROVED] [SOURCE-SPECIFIC] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `suzuki-residual-overcrowding-entire-pair-closure`,
  `suzuki-donoghue-defect-spectral-measure-law`,
  `suzuki-neumann-clock-annihilator`
- **RH used:** no
- **Computation used:** no

## Exact corpus frontier

**Semantic correction (2026-07-21).** This theorem applies to Suzuki's canonical Donoghue ratio,
which is odd and anchored at `i`. Suzuki's displayed reciprocal-logarithmic `R_eta` is instead a
one-phase characteristic target. The algebraic Lean connector computing `E[R_eta]` is valid, but
the anchor does not identify a Donoghue ratio with `R_eta`. The zero fibre is the unique odd member
of the shifted pencil; see `suzuki-opposite-shift-parity-harmonic-recovery`.

After exact Neumann-clock annihilation, corpus still asks independently for

```text
common-gauge entire-pair normality
  + zero linear Nevanlinna mass
  + Xi/de Branges pair identification.
```

The second demand is a cofinal escape problem, even though every finite Suzuki Donoghue function
has zero linear term.  The residual theorem proves that once common-gauge normality removes
interior overcrowding, the only remaining discrepancy has form `alpha*z`.

## Competing conjectures and attacks

### C1: one scalar tightness selector forces `alpha=0` `[FALSIFIED AS A GENERIC MECHANISM]`

A non-extremal scalar statistic of a probability does not control all tails.  For example, a
prescribed value of `int (1+t^2)^(-1) dnu` can be retained by adjusting one finite symmetric atom
while a separate positive mass moves to `+-infinity`.  A one-number shift normalization therefore
cannot prove tightness without an additional source rigidity theorem.  This is not selected.

### C2: common-gauge pair normality forces `alpha=0` `[FALSIFIED]`

The corpus's ground-edge sequence has common entire-pair convergence to the Cayley carrier and
limit Donoghue function `m(z)=z`, whose linear coefficient is one.  Pair normality and endpoint
tightness are genuinely independent.  This is not selected.

### C3: anchored Euler--Wronskian elimination `[PAPER-PROVED]`

For a meromorphic carrier `m`, define its degree-one Euler defect

```text
E[m](z)=z*m'(z)-m(z).                                  (1)
```

Then `E[m+alpha*z]=E[m]`.  If `m=-i*A/B`, define the homogeneous pair invariant

```text
P[A,B](z)=z*(A'(z)B(z)-A(z)B'(z))-A(z)B(z).            (2)
```

The conjectured exact package is

```text
E[-i*A/B]=-i*P[A,B]/B^2,                               (3)
P[gA,gB]=g^2*P[A,B],                                   (4)
E[m]=E[n] on H and m(i)=n(i)  =>  m=n on H.            (5)
```

For Donoghue's probability kernel `K_z(t)=(tz+1)/(t-z)`, the same defect is

```text
K^E_z(t)=z*partial_z K_z(t)-K_z(t)
        =[t(z^2-1)+2z]/(t-z)^2,                        (6)
K^E_z(+infinity)=K^E_z(-infinity)=0.                   (7)
```

Equation `(4)` makes `(3)` invariant under the common zero-free entire gauges required by the
Suzuki pair topology.  Equations `(6)--(7)` show that compactified weak convergence passes the
Euler transform automatically even when positive probability reaches either endpoint.  Equation
`(5)` uses the source normalization `m(i)=i` to restore the one-dimensional kernel, so no
information is discarded.

## Proposed frontier replacement

If `(3)--(5)` hold, the producer wall can be reformulated as

```text
intrinsic non-erasing schedule
  -> common-gauge normality of the annihilated parity pair
  -> pass the endpoint-vanishing Euler kernel through compactified convergence
  -> identify its gauge-invariant Euler--Wronskian defect with a correctly constructed two-phase
     Xi/de Branges Donoghue ratio
  -> Donoghue anchor reconstructs the full carrier
  -> zero linear mass follows, rather than being a separate premise.
```

This does not make Xi identification automatic.  It deletes one independent asymptotic premise
and presents the remaining source identity in a form simultaneously insensitive to finite
Neumann clocks and cofinal linear escape.

## Complete paper proof

### 1. Linear escape is exactly the Euler kernel

Let `m` be holomorphic on an open set and let `c` be constant.  Direct differentiation gives

```text
E[m+cz]
 =z(m'+c)-(m+cz)
 =zm'-m
 =E[m].                                                  (8)
```

Conversely, suppose `E[m]=E[n]` on the upper half-plane `H`.  Put `h=m-n`.  Since `z!=0` on `H`,
the quotient `r(z)=h(z)/z` is holomorphic there and

```text
r'(z)=[zh'(z)-h(z)]/z^2=0.                              (9)
```

The upper half-plane is connected, so `r` is constant.  Hence `m-n=cz`.  If additionally
`m(i)=n(i)`, then `ci=0`, so `c=0` and `m=n` throughout `H`.  This proves `(5)` and shows that the
anchor is both sufficient and necessary: without it the full kernel is exactly the linear mode.

### 2. Pair formula and common-gauge covariance

At a point where `B!=0`, the quotient rule gives

```text
(-i A/B)'=-i(A'B-AB')/B^2.
```

Therefore

```text
E[-iA/B]
 =-i[z(A'B-AB')-AB]/B^2
 =-i P[A,B]/B^2,                                        (10)
```

which proves `(3)`.  For a holomorphic common gauge `g`, expand both product derivatives:

```text
(gA)'(gB)-(gA)(gB)'
 =(g'A+gA')gB-gA(g'B+gB')
 =g^2(A'B-AB').                                         (11)
```

Also `(gA)(gB)=g^2AB`; substituting in `(2)` proves `(4)`.  Where `gB!=0`, division by
`(gB)^2=g^2B^2` shows that the quotient in `(10)` is exactly common-gauge invariant.

### 3. Endpoint-vanishing Donoghue kernel

For real `t` and `z` off the real pole, quotient differentiation gives

```text
partial_z K_z(t)=(t^2+1)/(t-z)^2.                       (12)
```

Consequently

```text
z partial_z K_z(t)-K_z(t)
 =[z(t^2+1)-(tz+1)(t-z)]/(t-z)^2
 =[t(z^2-1)+2z]/(t-z)^2,                                (13)
```

proving `(6)`.  Numerator in `(13)` has degree one in `t` and denominator degree two, so the limit
at both real ends is zero.  This proves `(7)` without a moment or endpoint-coefficient bound.

### 4. Weak-limit passage without tightness

Let `sigma_n` be the compactified Suzuki spectral probabilities and suppose
`sigma_n => sigma` on `R union {+-infinity}`.  For fixed `z` in `H`, extend `(13)` to both endpoints
by zero.  The extension is continuous.  If `z` ranges over a compact subset of `H`, its distance
from the real axis is positive; `(13)` and its `z`-derivatives are then jointly continuous and
uniformly bounded on that compact set times the compactified real line.  Weak convergence and a
finite-net argument therefore give locally uniform convergence

```text
E[m_n](z)
 =int K^E_z(t) d sigma_n(t)
 ->int K^E_z(t) d sigma(t).                              (14)
```

Writing endpoint mass as `alpha` and interior pullback as `nu_int`, endpoints contribute zero to
`(14)`.  Equivalently, the ordinary Donoghue limit is

```text
m(z)=alpha*z+int K_z(t)dnu_int(t),
```

while

```text
E[m](z)=int K^E_z(t)dnu_int(t).                          (15)
```

Thus Euler-defect convergence needs neither tightness nor a separate proof that `alpha=0`.

### 5. Anchored reconstruction and Suzuki consequence

Suppose source analysis identifies the limit in `(14)` with `E[m_*]`, where `m_*` is a
separately constructed normalized two-phase Xi/de Branges Donoghue ratio and `m_*(i)=i`. This
hypothesis must not be replaced by `m_*=R_eta`: nonzero fibres are not odd, and even `R_0` is a
one-phase target with no automatic Donoghue anchor. Every finite Suzuki Donoghue function satisfies
`m_n(i)=i`; local holomorphic convergence retains `m(i)=i`.  Step 1 then gives `m=m_*` on `H`.
Uniqueness of the Nevanlinna representation forces their linear coefficients and interior
measures to agree.  In particular, when the target has zero linear coefficient, `alpha=0` follows
as a conclusion.

Steps 2--4 show why this is producer-facing rather than an arbitrary reformulation: the defect is
computed from a homogeneous common-gauge pair, and its kernel passes compactified source limits
while annihilating exactly the remaining endpoint boundary mode.

## Hostile audit

1. **Anchor is essential.** `m` and `m+cz` have identical defects; `(5)` would be false without
   `m(i)=n(i)`.
2. **No claim that the defect is Herglotz.** Positivity is used only for the compactified
   probability representation; the Euler defect itself need not map `H` to `H`.
3. **No pole division.** Pair identity `(10)` is asserted where `B!=0`; its meromorphic extension
   carries the same statement globally.
4. **Gauge zeros.** Polynomial covariance `(4)` holds even at zeros of `g`.  Quotient invariance is
   used only where `gB!=0`, exactly the common zero-free-gauge regime.
5. **No hidden tightness.** Endpoint probability is retained in `sigma`; the new kernel simply has
   exact value zero there.
6. **Interior residual remains real work.** Endpoint annihilation does not kill bounded-window
   escaped-label overcrowding.  Common-gauge pair normality or an equivalent source theorem is
   still required.
7. **Not an RH criterion presented as proof.** Equality with a correct two-phase Xi/de Branges
   Donoghue defect is still open. The one-phase shifted target cannot fill this role directly.
   Advance is deletion of a separate zero-linear-mass limit theorem and replacement by an
   endpoint-insensitive transform that the compactified source topology passes automatically.
8. **No numerical evidence.** Every identity is exact and unconditional.

## Remaining open core

`[OPEN CORE]` Construct the correct two-phase Xi/de Branges Donoghue ratio from Suzuki's concrete
boundary-annihilated source and prove equality of its Euler--Wronskian defect with the limiting
canonical Donoghue defect. In parallel, identify the one-phase zero-shift characteristic target
through the corrected exterior channel. Common-gauge normality remains needed to eliminate
interior overcrowding; zero linear mass no longer remains an independent premise for the ratio.

## Lean formalization

Exact module:

```text
formal/GaloisForLFunctions/RHTower/SuzukiAnchoredEulerWronskian.lean
```

Formal capstones:

```text
suzukiEulerDefect_add_linear
suzukiEulerWronskian_commonGauge
suzukiEulerDefect_div
suzukiEulerWronskianQuotient_commonGauge
suzukiEulerDefect_suzukiShiftedXiTarget
suzukiEulerDefect_donoghueKernel
tendsto_suzukiDonoghueEulerKernel_atTop
tendsto_suzukiDonoghueEulerKernel_atBot
eqOn_upperHalfPlane_of_suzukiEulerDefect_eq_of_eq_I
```

`suzukiEulerDefect_suzukiShiftedXiTarget` is only an exact algebraic derivative formula for the
one-phase target. It is not an identification of that target with the anchored Donoghue ratio.

Direct Lean check, exact module build, formal lint, and axiom audit pass.  Axiom output contains only
`propext`, `Classical.choice`, and `Quot.sound`.

## Internal and external collision audit

- `[CORPUS]` `suzuki_twoAngle_common_gauge_cancels` proves quotient gauge cancellation, but no
  Euler--Wronskian invariant or anchored kernel classification.
- `[CORPUS]` `tendsto_suzukiDonoghueKernel_atTop/atBot` identifies endpoint escape as `alpha*z`.
- `[CORPUS]` `suzukiNeumannBoundaryAnnihilator_fourierDefect_eq_zero` eliminates finite endpoint
  clocks before the aperture limit.
- `[LITERATURE]` Nevanlinna representation theory identifies a nonnegative linear coefficient;
  meromorphic-inner uniqueness theory records phase/Clark data.  Targeted searches found no
  Suzuki-specific use of the anchored Euler defect `(1)` or pair covariant `(2)`.
- Algebraic Euler homogeneity and quotient Wronskians are classical.  Candidate novelty, if the
  proof closes, is the source-specific two-boundary elimination and removal of zero linear mass as
  an independent Suzuki producer premise.  Priority remains unverified.

## Gates

- [x] exact corpus wall stated
- [x] incompatible conjectures and falsifiers recorded
- [x] internal declaration audit
- [x] preliminary current-literature collision audit
- [x] dependency-complete paper proof of `(3)--(7)` and weak-limit passage
- [x] hostile audit
- [x] exact unconditional Lean formalization and axiom/lint/build audit
- [x] shifted-Xi target connector and SOTA/handover frontier update

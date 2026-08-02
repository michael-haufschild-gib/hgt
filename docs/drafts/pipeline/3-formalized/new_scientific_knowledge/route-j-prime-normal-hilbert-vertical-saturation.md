# Route J prime-normal Hilbert vertical saturation

- **ID:** `route-j-prime-normal-hilbert-vertical-saturation`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / CLASS NO-GO / POSITIVE SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [SOURCE-SPECIFIC CANDIDATE NEW] [CLASSICAL CYCLICITY INPUT] [EXTERNAL PRIORITY UNVERIFIED] [NOT RH]`
- **Parent:** `../../1-in-progress/route-j-semilocal-prolate-odd-harmonic-activation-law.md`
- **Source:** `../../4-publication-ready/source-horizon-riemann-divisor/main.tex`

## Frontier question

The source-horizon theorem proves maximal verticality for the complete prime-normal reader in
the product topology on `C^N`. That argument uses the nonsquare-summable packet

```text
P_0=(1,1,...)
```

and finite-coordinate approximation. It does not imply the corresponding theorem in the
strictly stronger Hilbert topology. A closed relation in

```text
X × l2(N,C)
```

need not be closed in `X × C^N`, so product-topology saturation cannot be imported.

The hard question is whether the square-summable packets

```text
P_j=(p_i^(-j))_(i>=0),  j>=1,
```

still force maximal verticality in `l2`, including after subtraction of an arbitrary proposed
Hilbert-space value at the collapsed source horizon.

## Theorem — prime-normal packets are Hilbert-cyclic

Put

```text
x_i=p_i^(-1),                 0<x_(i+1)<x_i<=1/2,
H=l2(N,C),
P_j=(x_i^j)_(i>=0),           j>=1.
```

Then:

1. `P_j` belongs to `H` for every `j>=1`;
2. `P_j -> 0` in `H` as `j->infinity`;
3. the complex linear span of `{P_j:j>=1}` is dense in `H`;
4. for every `y in H`, the span of `{P_j-y:j>=1}` is dense in `H`.

### Square summability and decay

Euler's convergence

```text
sum_i p_i^(-2)<infinity
```

gives `P_1 in H`. Since `0<x_i<=1/2`,

```text
||P_j||_2^2
 =sum_i x_i^(2j)
 <=x_0^(2j-2) sum_i x_i^2
 =4^(1-j)||P_1||_2^2.                                  (HJ1)
```

This proves every membership claim and `P_j->0`.

### Dense-span proof

Let `z in H` be orthogonal to every `P_j`. Suppose `z!=0`, and let `k` be the least index with
`z_k!=0`. Orthogonality gives, with the harmless conjugation determined by inner-product
convention,

```text
0=sum_(i>=k) conjugate(z_i)x_i^j.
```

After division by `x_k^j`,

```text
0=conjugate(z_k)
  +sum_(i>k) conjugate(z_i)(x_i/x_k)^j.                 (HJ2)
```

Set

```text
r_k=x_(k+1)/x_k<1,
C_k^2=sum_(i>k)(x_i/x_k)^2<infinity.
```

For `i>k` and `j>=1`,

```text
(x_i/x_k)^(2j)
 <=r_k^(2j-2)(x_i/x_k)^2.
```

Cauchy--Schwarz therefore gives the geometric tail bound

```text
|sum_(i>k) conjugate(z_i)(x_i/x_k)^j|
 <=||z_(i>k)||_2 C_k r_k^(j-1)
 ->0.                                                   (HJ3)
```

Taking `j->infinity` in `(HJ2)` forces `z_k=0`, a contradiction. Thus the orthogonal complement
of `span{P_j:j>=1}` is zero, proving density.

This density mechanism is classical: it is cyclicity of the compact diagonal operator

```text
D(a_i)=(x_i a_i)
```

with simple nonzero spectrum, for the cyclic vector `P_1`, since
`P_j=D^(j-1)P_1`. No novelty is claimed for this functional-analytic parent theorem.

### Affine-centre independence

Fix `y in H`, and suppose `z` is orthogonal to every `P_j-y`. Then

```text
<P_j,z>=<y,z>                                             (HJ4)
```

for every `j>=1`. By `(HJ1)`, the left side tends to zero. Hence `<y,z>=0`, so `(HJ4)` reduces
to `<P_j,z>=0` for every `j`. Hilbert cyclicity gives `z=0`. Therefore

```text
closure span_C{P_j-y:j>=1}=H                             (HJ5)
```

for every proposed horizon value `y`.

## Theorem — every closed Hilbert carrier is maximally vertical

Let `X` be a complex normed source space and let

```text
R subset X × H
```

be a closed complex linear relation. Fix `y in H`. Suppose that, for every `j>=1`, there are
source representatives `u_(K,j)` such that

```text
u_(K,j)->0,
(u_(K,j),P_j-y) in R                                    (HJ6)
```

for every `K`. Then

```text
mul R=H,
R=dom R × H.                                            (HJ7)
```

### Proof

For fixed `j`, closedness and `(HJ6)` give `(0,P_j-y) in R`. Thus `mul R` contains the span in
`(HJ5)`. The vertical fibre is closed because it is the inverse image of `R` under the
continuous map `v |-> (0,v)`. Hence `(HJ5)` forces `mul R=H`.

If `x in dom R`, choose `(x,v_0) in R`. For arbitrary `v in H`, full verticality gives
`(0,v-v_0) in R`; addition gives `(x,v) in R`. This proves `(HJ7)`.

For the complete Riemann source, take

```text
u_(K,j)=E_K(1/2+j)-e_0.
```

The source-horizon collapse proves `u_(K,j)->0`, and the internal prime peeling identifies the
retained output with `P_j`. Therefore `(HJ7)` is an unconditional source-specific consequence.

## Self-adjoint corollary — pure verticality

If `X=H` and `R` is self-adjoint as a Hilbert linear relation, then `(HJ7)` sharpens to

```text
R={0} × H.                                               (HJ8)
```

Indeed, for `(x,v) in R` and every `z in H`, full verticality gives `(0,z) in R`.
Symmetry implies

```text
<x,z>=<v,0>=0.
```

Thus `x=0`; the domain is trivial, while the multivalued part is all of `H`.

## Exact Route-J consequence

The latest source-horizon paper leaves topology-changing and relation-valued carriers open.
This theorem closes the ordinary norm-conservative Hilbert member of that survivor class:

```text
closed Hilbert relation
+ all square-summable prime-normal samples
+ one common horizon value
=> no output constraint anywhere in its domain.
```

A self-adjoint Hilbert--Polya-style relation retaining those samples is even more rigid: it is
the pure vertical relation `(HJ8)` and has no nonzero operator domain. Multivaluedness alone is
therefore not a repair; useful transport must change more than graph single-valuedness.

## Hostile anti-theatre audit

### HJ-A — use `l2` instead of the product topology

**Conjecture.** Stronger norm topology may make the finite-coordinate prime packets incomplete,
leaving a proper closed vertical fibre on which a selector can act.

**Attack.** `(HJ2)`--`(HJ3)` prove the square-summable packets themselves are total in `l2`.

**Verdict.** Falsified class-completely for the unweighted canonical `l2` target.

### HJ-B — choose a special horizon value

**Conjecture.** A carefully selected `y in l2` makes the differences `P_j-y` incomplete.

**Attack.** `P_j->0`; any annihilator of all differences has constant moments
`<P_j,z>=<y,z>`, whose limit is zero. It then annihilates the dense uncentered packet.

**Verdict.** Falsified for every `y in l2`.

### HJ-C — use a self-adjoint relation instead of an operator

**Conjecture.** A self-adjoint multivalued relation can retain the packet while preserving a
nontrivial operator part.

**Attack.** Maximal verticality plus symmetry forces every domain vector orthogonal to all of
`H`, so the domain is zero.

**Verdict.** Falsified exactly; only the pure vertical relation survives.

## Novelty boundary

Classical ingredients receiving no novelty credit:

1. convergence of `sum_p p^(-2)`;
2. cyclicity/polynomial density for a compact simple-spectrum diagonal operator;
3. orthogonal-complement characterization of dense Hilbert span;
4. closed linear-relation vertical fibres and Cartesian singular parts.

The canonical decomposition of closed Hilbert relations into operator and singular Cartesian
parts is classical; see Hassi--Sebestyén--de Snoo--Szafraniec,
[*A canonical decomposition for linear operators and linear relations*](https://arxiv.org/abs/math/0611045).
General cyclic-vector and spectral-theorem infrastructure is standard functional analysis.

Targeted repository and theorem-level searches found no prior result combining:

1. the positive divisor-faithful complete Riemann source;
2. internal extraction of every prime-normal character;
3. cofinal collapse of all source representatives;
4. Hilbert cyclicity of the square-summable canonical sample packets;
5. affine-center-independent maximal verticality; and
6. pure-vertical collapse of every self-adjoint relation retaining the packet.

Candidate novelty is this exact arithmetic-source classification, not its classical components.
External priority remains unverified.

## Strongest positive survivor

Any useful prime-normal boundary transport must violate at least one proved hypothesis. Live
survivors are:

1. a rigged/distributional target retaining the nonsquare-summable `P_0`;
2. a topology not continuously comparable with canonical product or `l2` completion;
3. an index-dependent renormalization with no common Hilbert horizon value;
4. a nonlinear or partial source-selected reader which does not retain all `j>=1`;
5. an indefinite/Krein carrier where Hilbert orthogonal-complement density is not the governing
   closure law;
6. a singular pre-completion selection acting before the packets enter one closed relation.

These remain Route J work. The semilocal prolate Legendre-wave survivor and its finite-prime,
Sonin, and global descent obligations are untouched. Route J remains open.

## Lean formalization

Module:

```text
formal/GaloisForLFunctions/RHTower/
  CompleteResolutionPrimeNormalHilbertSaturation.lean
```

It proves unconditionally:

1. `P_j in lp (fun _ : N => C) 2` for every positive exponent;
2. `P_j -> 0` in `l2`;
3. norm-dense span of the uncentered packet;
4. norm-dense span after arbitrary `y in l2`;
5. maximal verticality and Cartesian domain factorization for every closed relation;
6. pure verticality for every Hermitian relation retaining the packet.

The module is wired into `GaloisForLFunctions/RHTower.lean`. Direct verification passed with:

```text
lake env lean GaloisForLFunctions/RHTower/
  CompleteResolutionPrimeNormalHilbertSaturation.lean
```

No RH hypothesis, zero hypothesis, computation, unproved density assumption, new axiom, or
product-topology substitution occurs.

## Log

- 2026-08-02 — Product-topology maximality incorporated from updated source-horizon paper.
- 2026-08-02 — Hilbert-cyclic density, affine-centre independence, maximal relation saturation,
  and pure-vertical self-adjoint corollary proved on paper.
- 2026-08-02 — Full theorem formalized unconditionally in Lean; direct module check passed.

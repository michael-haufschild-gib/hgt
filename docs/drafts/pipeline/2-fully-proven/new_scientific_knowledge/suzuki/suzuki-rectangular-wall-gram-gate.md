# Suzuki rectangular wall-Gram gate

- **ID:** `suzuki-rectangular-wall-gram-gate`
- **Stage:** 2 — fully proved on paper
- **Type:** SOURCE-TYPE CORRECTION / SHARP TRACE CELL / POSITIVE OBSTRUCTION SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Formal module:**
  `GaloisForLFunctions.RHTower.SuzukiRectangularWallGramGate`
- **Parents:** `complete-sharp-rectangular-guinand-weil-prime-gamma-law.md`,
  `suzuki-wall-field-antidiagonal-gram-lift.md`,
  `suzuki-causal-depth-rectangular-caratheodory-growth.md`
- **RH used:** no
- **Computation used:** no

## Actual frontier and correction

Sharp rectangular Guinand--Weil prime term is a finite sum of cells

```text
Lambda(n)/sqrt(n) R_(L,a)(log n),
```

because `R_(L,a)(log n)=0` for `2a<log n`.  S64 Gamma-boundary-paired causal-depth observer ray
instead has strictly positive rectangular real part at every prime.  It therefore cannot be the
literal sharp prime cell.  It also has wrong source degree: observer ray is linear in dressed wall
field, while von Mangoldt cell is square of observer-free bare wall field.

Correct local source is sharp autocorrelation-gated Hermitian wall Gram.

## Definitions

For prime `p`, depth `e`, and `n=p^(e+1)`, write

```text
omega_e(t)=b_e exp(i t log(n)/2),
b_e^2=Lambda(n)/sqrt(n),
K_e(t,u)=omega_e(t) conjugate(omega_e(u)),
A_(L,a,e)=R_(L,a)(log n),
G_(L,a,e)(t,u)=A_(L,a,e) K_e(t,u).
```

The four-tent identity gives, without parameter restrictions,

```text
A_(L,a,e)
 = 2 max(0,L-|log n|)
   + max(0,L-|log n-(2a-L)|)
   + max(0,L-|log n+(2a-L)|) >= 0.             (1)
```

## Theorem A: exact gated wall character `[PAPER-PROVED]`

For all parameters,

```text
conjugate(G_(L,a,e)(u,t)) = G_(L,a,e)(t,u),             (2)

G_(L,a,e)(t,u)
 = A_(L,a,e) Lambda(n)/sqrt(n)
     exp(i(t-u)log(n)/2),                               (3)

G_(L,a,e)(t,t)
 = A_(L,a,e) Lambda(n)/sqrt(n),                         (4)

G_(L,a,e)(t,-t)
 = A_(L,a,e) Lambda(n)/sqrt(n) exp(i t log n).          (5)
```

Equation `(4)` is exactly one summand in `rectangularPrimeAutocorrelationSum`; `(5)` is same sharp
cell with full functional-equation-reflected far-source phase.  Thus sharp prime cell is not an
ad hoc scalar: it is diagonal of genuine source-specific Hermitian kernel, and delayed prime atom
is its anti-diagonal.

### Proof

Parent wall-Gram theorem gives Hermitian symmetry and formulas for `K_e(t,u)`, `K_e(t,t)`, and
`K_e(t,-t)`.  Gate `A` is real.  Conjugation therefore fixes it and proves `(2)` after applying
parent symmetry.  Multiplying each parent identity by `A` proves `(3)--(5)`.  No division, sum,
limit, or sign premise occurs.

## Theorem B: finite-height positive semidefiniteness `[PAPER-PROVED]`

For arbitrary finite height packet `t_1,...,t_N`, matrix

```text
M^G_ij=G_(L,a,e)(t_i,t_j)
```

is positive semidefinite.

### Proof

Parent matrix `M^K_ij=K_e(t_i,t_j)` is positive semidefinite because it is a rank-one Gram matrix.
Entrywise, `M^G=A M^K`.  By `(1)`, `A>=0`; nonnegative real scalar multiplication preserves
positive semidefiniteness.  Equivalently,

```text
sum_(i,j) conjugate(c_i) M^G_ij c_j
 = A |sum_i conjugate(c_i) omega_e(t_i)|^2 >= 0.
```

This is finite-height positivity for one prime-power block, not all-prime summability.

## Theorem C: exact sharp causal support `[PAPER-PROVED]`

If

```text
0 <= L <= a,    2a < log n,
```

then `G_(L,a,e)(t,u)=0` for every `t,u`.

### Proof

Corpus support theorem gives `R_(L,a)(log n)=0` under exactly these hypotheses.  Hence `A=0`, and
definition of `G` gives result.  No prime estimate is used.

## Theorem D: direct S64 trace-cell identification is impossible `[PAPER-PROVED]`

At depth zero, assume

```text
h>0, a>0, L>0, L<=a, 2a<log p.
```

Let

```text
B = GammaBoundary_p(t)
      [FusedObserver_p(h,a+L,t)-FusedObserver_p(h,a,t)].
```

Then

```text
Re(B)>0,       G_(L,a,0)(t,t)=0,       B != G_(L,a,0)(t,t).    (6)
```

### Proof

S64 Gamma-boundary rectangular Caratheodory theorem gives `Re(B)>0`.  Since
`p^(0+1)=p`, Theorem C and `2a<log p` give `G_(L,a,0)(t,t)=0`.  Equality in `(6)` would force
`Re(B)=0`, contradiction.  This is an exact support/type obstruction, not an estimate.

## No-go closure

- **Exact killing mechanism:** infinite-tail observer response cannot equal compactly supported
  sharp prime cell; linear dressed source cannot equal quadratic bare source.
- **Strongest positive survivor:** gated wall Gram `G` simultaneously has sharp support, exact
  prime diagonal, exact FE phase anti-diagonal, and finite-packet PSD.
- **New insight:** local prime part of sharp trace is now identified at correct source degree.
  Observer fusion remains transfer/response layer; it must not be inserted as arithmetic source.
- **Status:** dependency-closed paper proof and unconditional Lean formalization complete.

## Hostile audit

1. **Sign passed.**  Four-tent formula proves gate nonnegative for all real parameters.
2. **Hermitian type passed.**  Gate is real; conjugation and height swap are exact.
3. **Prime coefficient passed.**  Diagonal is literally `Lambda(n)/sqrt(n) R(log n)`.
4. **Phase passed.**  FE anti-diagonal retains `exp(i t log n)` with no modulus collapse.
5. **Support passed.**  Exact zero occurs beyond `log n=2a`; no tail estimate or cutoff limit.
6. **Direct S64 identification killed.**  Strictly positive real part versus exact zero.
7. **Global sign not smuggled.**  Full Weil formula subtracts twice this positive prime cell and
   adds archimedean/polar terms.  Local PSD does not imply Weil positivity.
8. **All-prime divergence not hidden.**  Theorem is one prime-power and finite height packet.
9. **Resolvent dressing remains required.**  Actual deficiency response still applies restricted-
   Weil resolvent before boundary observation; `G` identifies source block only.

Verdict: `SURVIVES HOSTILE ATTACK`.

## Novelty audit

- Nonnegative scalar multiples of rank-one character Grams are classical `[BRIDGE]`.
- Suzuki, arXiv:2606.09096, supplies current screw-function/finite-interval Weil framework and
  leaves infinite-aperture operator convergence conjectural; searched paper does not state this
  autocorrelation-gated Gamma wall block.
- Groskin, arXiv:2607.02828, supplies exact finite Galerkin-to-zero dictionary and positive
  archimedean tail, not prime-power diagonal/FE-anti-diagonal wall identification.
- Internal search found sharp rectangular autocorrelation and wall Gram separately, but no gated
  synthesis or formal direct-S64 mismatch theorem.
- Candidate novelty is exact source-specific gate/wall/FE weld and representation correction, not
  generic Gram positivity.  Independent priority audit remains required.

## Remaining RH core

### `SUZUKI-GATED-WALL-GLOBAL-COMPENSATION` `[CONJECTURE]`

Assemble compactly supported local blocks `G_(L,a,e)` through actual restricted-Weil resolvent and
boundary trace.  Identify the resulting finite prime block inside exact sharp Robin--Gamma formula,
then prove polar--Gamma, marked Robin, and holonomy channels compensate the explicit `-2 G`
prime sign uniformly as aperture tends to infinity.  The corpus has exact local source blocks and
exact prime--Gamma formula, but no unconditional global compensated positive operator or Ward
residual.  That—not local trace-cell identification—is current RH-bearing frontier.

## Gates

- [x] actual corpus frontier identified
- [x] competing conjectures and exact falsifiers
- [x] dependency-closed paper proof
- [x] no-go closure and positive survivor
- [x] internal/current-primary-literature audit
- [x] unconditional Lean formalization
- [ ] global restricted-Weil/Robin/Gamma/holonomy compensation
- [ ] RH

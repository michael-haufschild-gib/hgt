# Route R graded `det2` scalar-descent counterboundary

- **ID:** `route-r-graded-det2-scalar-descent-counterboundary`
- **Stage:** 3 — formalised in Lean 4
- **Type:** REGULAR/SINGULAR CONNECTING CLASS / EQUAL-GRADE SCALAR COUNTERBOUNDARY
- **Status:** `[LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Parents:**
  - `../3-formalized/new_scientific_knowledge/route-r-essential-edge-occupation-det2-bv-relative-class.md`;
  - `../3-formalized/new_scientific_knowledge/route-r-prime-depth-bv-wold-curved-source-differential.md`;
  - `../3-formalized/new_scientific_knowledge/route-r-resolved-bv-wold-source-frame-annihilation.md`;
  - `route-r-five-program-polarized-descent-frontier.md`.

## Frozen candidate

For a prime/depth cell `i`, write

```text
v_i=(m_i,lambda_i),
theta(i,j)=m_i lambda_j-m_j lambda_i,
kappa(i,j,k)=theta(i,j)+theta(j,k)-theta(i,k).
```

For an oriented edge define source increments

```text
dm(i,j)=m_j-m_i,
dl(i,j)=lambda_j-lambda_i.
```

Let `Q` be the actual essential-edge occupation Hilbert--Schmidt operator and

```text
q=Tr(Q^2)=zeta(2) != 0.
```

On the graded double `H^+ ⊕ H^-`, define the two even diagonal polarized edge operators

```text
A_a(i,j)^+ = (a dm(i,j)/q) Q,
A_a(i,j)^- = (a dl(i,j)/q) Q,

B(j,k)^+   = dl(j,k) Q,
B(j,k)^-   = dm(j,k) Q.
```

Their graded quadratic contraction is

```text
Str(A_a(i,j) B(j,k))
  = a (dm(i,j) dl(j,k)-dl(i,j) dm(j,k))
  = a kappa(i,j,k).                                      (1)
```

Define the normalized graded Hilbert--Carleman anomaly boundary

```text
Anom_a(i,j,k)=exp(-Str(A_a(i,j) B(j,k))).                (2)
```

For scalar Route-R transport `U_a(i,j)=exp(a theta(i,j))`, `(1)` gives

```text
U_a(i,j) U_a(j,k) U_a(i,k)^(-1) * Anom_a(i,j,k)=1.       (3)
```

For a scalar zero-cochain `f`, define the equal-grade additive counterboundary

```text
Boundary_a(f)(i,j,k)
  = U_a(i,j) U_a(j,k) (Anom_a(i,j,k)-1) f(k).            (4)
```

The exact target is

```text
(D1_a D0_a f)(i,j,k)+Boundary_a(f)(i,j,k)=0              (5)
```

for every real `a`, every `f`, and every labelled triangle.  Equation `(4)` is defined from the
crossed regular/singular determinant anomaly, not as the negative of `D1 D0`; equality `(5)` must
be proved from `(1)--(3)`.

## Actual Xi landing

At `rho : XiDivisorSupport`, specialize

```text
a=a_rho=2 Re(rho)-1,
f(rho,i)=XiC^(multiplicity(rho))(z_rho) != 0.
```

The counterboundary acts on the same nonzero leading Xi conormal as the existing scalar square.
On the exact three-depth witness, its vanishing is equivalent to `a_rho=0`, hence to the critical
line.  Therefore `(5)` is an unconditional corrected-square identity, but the statement
`Boundary=0` remains RH-equivalent.

## Why this candidate is independent

1. Definition `(2)` uses the actual occupation operator `Q`, its regular quadratic trace, and
   crossed increments of the singular BV mass and Wold clock.
2. Neither `theta`, `kappa`, Xi zeros, nor `D1 D0` occurs in the definition of the graded
   contraction.
3. The equality with curvature is a theorem: the symplectic area of two consecutive source
   increments equals the triangle defect.
4. The two parity channels are forced by the ordered source records `(BV mass, Wold clock)`;
   ordinary ungraded trace would give the symmetric sum and would not cancel curvature.

## Dependency-closed proof

### 1. Nonzero operator normalization

The existing occupation theorem gives

```text
q=Tr(Q^2)=zeta(2).
```

Since `Re(2)>1`, the Euler half-plane nonvanishing theorem gives `zeta(2)!=0`.  Thus every
coefficient divided by `q` in the frozen construction is defined.  Scalar multiples of the
Hilbert--Schmidt operator `Q` are Hilbert--Schmidt, and products of two such multiples are trace
class.

### 2. Consecutive-increment area

Direct expansion gives

```text
dm(i,j) dl(j,k)-dl(i,j) dm(j,k)
 = (m_j-m_i)(lambda_k-lambda_j)
   -(lambda_j-lambda_i)(m_k-m_j)
 = m_i lambda_j-m_j lambda_i
   +m_j lambda_k-m_k lambda_j
   -(m_i lambda_k-m_k lambda_i)
 = theta(i,j)+theta(j,k)-theta(i,k)
 = kappa(i,j,k).                                         (6)
```

This is the symplectic area of the two consecutive source increments.  It uses neither a divisor
nor scalar transport.

### 3. Graded quadratic contraction

The four operator products have ordinary traces

```text
Tr(A_a(i,j)^+ B(j,k)^+)
  =(a dm(i,j)/q) dl(j,k) Tr(Q^2),

Tr(A_a(i,j)^- B(j,k)^-)
  =(a dl(i,j)/q) dm(j,k) Tr(Q^2).
```

Subtracting the odd trace from the even trace and using `Tr(Q^2)=q`, `q!=0`, and `(6)` proves

```text
Str(A_a(i,j)B(j,k))=a kappa(i,j,k).                      (7)
```

The operators are parity-preserving block diagonals on `H^+ ⊕ H^-`.  No Berezinian of an odd
operator is invoked.

### 4. `det2` anomaly realization

For Hilbert--Schmidt `A,B`, the regularized Fredholm product formula is

```text
det2((I-A)(I-B))
 =det2(I-A) det2(I-B) exp(-Tr(AB)).                      (8)
```

Apply `(8)` separately to the even and odd blocks and divide the two identities wherever the
local determinant ratios are defined.  The graded quotient anomaly is

```text
exp(-Tr(A^+B^+)+Tr(A^-B^-))
 =exp(-Str(AB)).                                         (9)
```

Equation `(2)` is the entire exponential continuation of `(9)`, so the boundary itself has no
small-parameter restriction.  Combining `(7)` and `(9)` gives

```text
Anom_a(i,j,k)=exp(-a kappa(i,j,k)).                       (10)
```

### 5. Inverse scalar holonomy

By definition of scalar transport and real exponential addition,

```text
U_a(i,j)U_a(j,k)U_a(i,k)^(-1)
 =exp(a(theta(i,j)+theta(j,k)-theta(i,k)))
 =exp(a kappa(i,j,k)).                                   (11)
```

Equations `(10)` and `(11)` prove `(3)`.

### 6. Equal-grade corrected square

The existing covariant-square identity is

```text
(D1_a D0_a f)(i,j,k)
 =(U_a(i,j)U_a(j,k)-U_a(i,k))f(k).                       (12)
```

From `(3)`,

```text
U_a(i,j)U_a(j,k)Anom_a(i,j,k)=U_a(i,k).                 (13)
```

Adding `(4)` to `(12)` and using `(13)` leaves zero.  This proves `(5)` for every scalar
zero-cochain and every labelled triangle.  The counterboundary is a degree-two cochain, exactly
the grade of the curved square.

### 7. Actual Xi landing and sharpness

The existing cofinal source theorem lands at

```text
c_rho=XiC^(multiplicity(rho))(z_rho)!=0.
```

Specialize `a=a_rho=2 Re(rho)-1` and `f(i)=c_rho`.  Equation `(5)` proves corrected annihilation
on this actual nonzero landing.  On the witness triangle,

```text
kappa=-log(2)/8 !=0.
```

Every scalar transport is positive and `c_rho!=0`, so `(4)` vanishes there exactly when
`Anom=1`.  Its exponent is real; injectivity of the real exponential and nonzero witness
curvature give

```text
Boundary_(a_rho)(c_rho)=0
  <-> a_rho=0
  <-> Re(rho)=1/2.                                       (14)
```

Thus the counterboundary is non-vacuous and its global triviality remains equivalent to RH.

## Lean realization

Formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldGradedDet2ScalarDescentBoundary.lean`.
The module proves:

1. consecutive source-increment area equals scalar Route-R curvature;
2. actual occupation quadratic trace is `zeta(2)` and is nonzero;
3. crossed graded occupation supertrace equals `a * curvature`;
4. graded `det2` anomaly is exact inverse scalar holonomy;
5. `D1 D0 + Boundary = 0` for every cochain and triangle;
6. the same corrected square vanishes on the actual leading Xi conormal;
7. boundary vanishing on the exact witness is equivalent to the critical line;
8. global boundary triviality is equivalent to RH.

Targeted `lake build` passed.  `#print axioms` on all frontier theorems reports only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.  The module contains no `sorry`,
`admit`, `axiom`, `opaque`, or `unsafe` declaration and is imported by the `RHTower` umbrella.
Repository-wide lint remains red only because unrelated pre-existing owned modules are not wired
into their umbrellas; this module is reachable and appears in no lint error.

## Hostile proof audit

1. **Odd-operator version rejected.**  `I-A` for an odd complex-linear operator is not an even
   super-automorphism with an ordinary graded determinant.  The final construction uses even
   parity-preserving blocks and is well typed.
2. **Tautological exponential divided difference rejected.**  The boundary is not defined from
   `D1D0`, `theta`, `kappa`, or inverse holonomy.  Those equalities are consequences of the
   occupation trace and consecutive-increment area identity.
3. **Ungraded anomaly rejected.**  Ordinary trace gives the symmetric cross term
   `dm*dl+dl*dm`; only the source-ordered parity difference gives oriented curvature.
4. **No fake annihilation.**  Corrected square vanishes for every `a`; original scalar square and
   the anomaly boundary separately vanish only at `a=0` on the witness.
5. **No target fitting.**  Operators, parity, normalization, and edge increments exist before Xi
   specialization.  Xi enters only when the already constructed nonzero conormal is evaluated.

Verdict: `SURVIVES PRELIMINARY ATTACK` as an exact equal-grade counterboundary.  It is not a proof
of boundary trivialization or RH.

## External boundary

The Hilbert--Schmidt `det2` product formula `(8)` is parent operator theory; see Britz--Carey--
Gesztesy--Nichols--Sukochev--Zanin,
<https://arxiv.org/abs/2007.12834>, and the higher-product treatment of Koutsonikos-Kouloumpis--
Lesch, <https://arxiv.org/abs/2202.12923>.  Supertrace as the difference of traces on a
parity-preserving block decomposition is also parent mathematics.  Targeted searches found no
exact construction joining the Route-R BV mass/clock increment area, normalized essential-edge
occupation trace, scalar holonomy, and actual Xi conormal.  This is noncollision evidence, not an
independent priority certificate.

## Hostile falsifiers

1. Reject if the actual occupation kernel does not have nonzero quadratic trace.
2. Reject if the supertrace sign gives `-a kappa` rather than `a kappa` after fixed orientation.
3. Reject if the construction needs Xi specialization before the anomaly exists.
4. Reject any proof defining `Boundary=-D1D0` or `Anom` as inverse holonomy.
5. Do not infer original scalar flatness from corrected flatness.
6. Do not call invertible anomaly cancellation annihilation of the anomaly itself.
7. On the witness, prove that boundary vanishing is still equivalent to the critical line.

## Open core after construction

Even if `(1)--(5)` are proved, RH still requires a source Stokes/Cartier theorem trivializing this
explicit anomaly boundary on the actual Xi conormal.  The present construction narrows the missing
object from an unspecified equal-grade term to one canonical graded determinant anomaly.

## Gates

- [x] exact statement frozen
- [x] internal Route-R collision audit
- [x] external parent-theory and exact-collision audit
- [x] dependency-closed paper proof
- [x] hostile proof audit
- [x] unconditional Lean formalization
- [ ] boundary trivialization on Xi conormal
- [ ] RH

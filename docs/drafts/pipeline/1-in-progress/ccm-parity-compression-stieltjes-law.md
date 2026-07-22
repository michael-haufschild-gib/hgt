# CCM parity-compression and boundary--central Stieltjes law

- **ID:** `ccm-parity-compression-stieltjes-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / CANDIDATE-NEW UNIVERSAL LAW
- **Scientific status:** `[PROVED ON PAPER] [LEAN CORE IN PROGRESS] [NOVELTY AUDIT OPEN]`
- **Parent sources:** Connes--Consani--Moscovici, *Zeta Spectral Triples*, Lemmas 5.1--5.2;
  finite-dimensional spectral theorem; Cauchy interlacing; finite Stieltjes transforms.
- **Statement:** Every finite CCM Weil matrix has an exact odd/even characteristic-determinant
  quotient equal to one mixed boundary--central resolvent entry. Positivity of the associated mixed
  moment Hankel form is equivalent to a unique positive commuting metric and forces strict
  even/odd spectral alternation; in particular the full ground state is simple and even.

## Goal and scientific role

CCM require the smallest eigenvalue of each truncated Weil matrix to be simple with an even
eigenvector. Their matrix already satisfies two source-defined identities:

```text
Gamma Q = Q Gamma,
D Q-Q D = |beta><eta|-|eta><beta|,                       (1)
```

where `Gamma e_j=e_(-j)`, `D e_j=j e_j`, `eta=sum_j e_j` is the Dirichlet boundary vector,
and `beta` is odd. The theorem below uses `(1)` to eliminate the odd block exactly. It replaces a
two-sector eigenvector assertion by one scalar resolvent and one finite mixed-moment orientation
law. No Xi zero, RH assumption, limiting determinant, or numerical observation enters.

This is not yet a proof of the CCM source condition. The open arithmetic theorem is positivity of
the boundary--central moment form at the actual von-Mangoldt--Gamma coefficient point. Unlike an
arbitrary ground-state criterion, that condition is a finite list of explicit source-polynomial
inequalities and can fail without deciding RH.

## Setup

Let

```text
V=R^{ {-N,...,N} },
V_+=ker(Gamma-I),                 dim V_+=N+1,
V_-=ker(Gamma+I),                 dim V_-=N.
```

Let `e_0` be the central clock vector. Normalize `eta^T e_0=1`. Since `D` anticommutes with
`Gamma`, it exchanges `V_+` and `V_-`. Put

```text
L=V_+ intersect ker(eta^T),
P=I-e_0 eta^T : V_+ -> L.                                  (2)
```

Thus `P` is the oblique projection onto `L` along `R e_0`. Write `Q_+` and `Q_-` for the parity
restrictions of `Q`.

## Theorem A: displacement forces oblique parity compression

`[PROVED]` The restriction

```text
J=D|_L : L -> V_-                                             (3)
```

is an isomorphism and intertwines `Q_-` with the oblique compression

```text
C=P Q_+|_L : L -> L:
Q_- J=J C.                                                    (4)
```

### Proof

The kernel of `D|_{V_+}` is `R e_0`, which meets `L` trivially because `eta^T e_0=1`. Hence
`D|_L` is injective. Both spaces have dimension `N`, so it is an isomorphism.

For `x in L`, parity gives `beta^T x=0` and the definition of `L` gives `eta^T x=0`. Applying
`(1)` to `x` therefore gives

```text
D Q_+ x=Q_- D x.                                             (5)
```

Since `D e_0=0`, equation `(2)` gives `D P=D` on `V_+`. Consequently

```text
J Cx=D P Q_+x=D Q_+x=Q_-Dx=Q_-Jx,
```

which proves `(4)`.

## Theorem B: universal parity determinant quotient

`[PROVED]` For every `z` outside the spectrum of `Q_+`,

```text
 det(Q_--zI)
---------------- = eta^T (Q_+-zI)^(-1)e_0.                  (6)
 det(Q_+-zI)
```

The polynomial form, valid for every complex `z`, is

```text
det(Q_--zI)
 =eta^T adj(Q_+-zI)e_0.                                      (7)
```

### Proof

Use the direct sum `V_+=L direct_sum R e_0`. The functional `eta^T` extracts the `e_0`
coordinate, while `P` extracts the `L` coordinate. Therefore the upper-left block of `Q_+-zI` in
this generally nonorthogonal decomposition is `C-zI`. Its `(e_0,eta)` cofactor is
`det(C-zI)`. Theorem A gives

```text
det(C-zI)=det(Q_--zI).                                       (8)
```

The adjugate identity yields `(7)`, and multiplication by `det(Q_+-zI)^(-1)` yields `(6)`.

## Theorem C: Stieltjes, commuting-metric, moment, and interlacing equivalence

Define the mixed boundary--central moments

```text
m_k=eta^T Q_+^k e_0,
H_N=(m_(r+s))_(0<=r,s<=N).                                  (9)
```

`[PROVED]` The following are equivalent.

1. `H_N` is positive definite.
2. The mixed spectral measure
   ```text
   mu_(eta,e0)=sum_(j=0)^N w_j delta_(lambda_j),
   w_j=(eta^T u_j)(u_j^T e_0),                              (10)
   ```
   has `N+1` distinct atoms and every `w_j` is positive.
3. There is a unique positive-definite operator `W` such that
   ```text
   WQ_+=Q_+W,       W e_0=eta.                              (11)
   ```
4. The even and odd spectra are simple and strictly alternate:
   ```text
   lambda_0^+<lambda_0^-<lambda_1^+<...<lambda_(N-1)^-<lambda_N^+.
                                                                    (12)
   ```

Under these conditions the smallest eigenvalue of the full CCM matrix is simple and its
eigenvector is even.

### Proof: `(1) <-> (2)`

The spectral theorem gives

```text
c^T H_N c
 =eta^T p(Q_+)^2e_0
 =sum_lambda mu_(eta,e0)({lambda}) p(lambda)^2,             (13)
```

where `p(t)=sum_(r=0)^N c_r t^r`. If the measure has `N+1` distinct positive atoms, a nonzero
polynomial of degree at most `N` cannot vanish at every atom, so `(13)` is positive.

Conversely, if `H_N` is positive definite, `(13)` forbids a negative atom: Lagrange interpolation
can choose `p` equal to one at that atom and zero at every other distinct eigenvalue. It also
forbids a zero atom. Positive definiteness on an `(N+1)`-dimensional polynomial space forces at
least `N+1` support points. Since `dim V_+=N+1`, there are exactly `N+1`; hence the even spectrum
is simple and every weight is positive.

### Proof: `(2) <-> (3)`

Write `Q_+u_j=lambda_j u_j`. Positivity of `w_j` implies both components in `(10)` are nonzero and

```text
alpha_j=(eta^T u_j)/(u_j^T e_0)>0.                          (14)
```

Define `W u_j=alpha_j u_j`. Then `W` is positive definite, commutes with `Q_+`, and `We_0=eta`.
Conversely `(11)` gives

```text
w_j=<W e_0,u_j><u_j,e_0>
   =alpha_j |<u_j,e_0>|^2>0.                               (15)
```

The `N+1` support condition makes `e_0` cyclic for `Q_+`; a commuting operator is determined by
its value on a cyclic vector, proving uniqueness.

Geometrically, `(11)` straightens the oblique projection. In the inner product

```text
<x,y>_W=<x,Wy>,                                            (16)
```

one has `L=(R e_0)^(perp_W)`, `P` is the orthogonal projection onto `L`, and `Q_+` remains
self-adjoint because it commutes with `W`. Thus the odd block is similar to a genuine codimension-one
self-adjoint compression of the even block.

### Proof: `(2) <-> (4)`

By `(6)` and the spectral theorem,

```text
R(z)=det(Q_--zI)/det(Q_+-zI)
    =sum_(j=0)^N w_j/(lambda_j^+-z).                       (17)
```

If every `w_j>0`, then `R` is strictly increasing on each complementary interval, tends from
`-infinity` to `+infinity` between consecutive even poles, and is positive below the lowest even
pole. Its `N` zeros are therefore simple and occur exactly as in `(12)`. By `(6)`, those zeros are
the odd eigenvalues.

Conversely, strict alternation determines the signs of the residues of the monic determinant
quotient. They are all positive, and their sum is `eta^T e_0=1`, proving `(2)`.

## Corollary: exact parity spectral tomography

When the equivalent conditions hold, the two parity spectra recover every boundary--central
weight:

```text
w_j
 = Res_(z=lambda_j^+) [-R(z)]
 = det(Q_--lambda_j^+ I)
   / product_(k!=j)(lambda_k^+-lambda_j^+),                 (18)
```

with the orientation fixed by `sum_j w_j=1`. Hence the parity spectra determine every mixed
moment by

```text
m_k=sum_j w_j (lambda_j^+)^k.                               (19)
```

This is an inverse spectral law, not only a ground-state certificate.

## Exact CCM source conjecture exposed by the theorem

For the actual CCM truncated Weil matrix `Q_(lambda,N)`, define `H_(lambda,N)` by `(9)` using the
actual finite Euler product through `p<=lambda^2`, the archimedean term, and the polar correction.

> **Boundary--central Stieltjes conjecture.** There is a source-defined cofinal regime
> `(lambda,N(lambda))` in which `H_(lambda,N(lambda))` is positive definite, with a smallest
> eigenvalue margin sufficient to pass to the continuous restricted-Weil ground state.

Finite positive definiteness already proves simple-evenness at that truncation, unconditionally.
The cofinal margin and continuous passage remain open. The conjecture is stronger than the minimum
needed by CCM because it predicts complete parity alternation, and is therefore independently
falsifiable.

## Scientific-method tests

### Predictions

1. Every actual finite CCM parity spectrum in the claimed regime strictly alternates.
2. Residues reconstructed from `(18)` are positive and sum to one.
3. The mixed Hankel minors `det(m_(r+s))_(0<=r,s<=k)` are positive for every `k<=N`.
4. A unique positive commuting metric `W_(lambda,N)` exists and maps the central clock mode to the
   boundary Dirichlet vector.
5. Loss of simple-evenness must be preceded by one of two exact events: a mixed residue reaches
   zero, or two even eigenvalues collide and destroy central cyclicity.

### Kill conditions

- The determinant quotient `(6)` fails for a matrix satisfying the exact CCM displacement law.
- A published source already proves the full equivalence `(1)`--`(4)` for the CCM matrix family.
- Actual CCM matrices systematically violate the mixed Hankel sign before any relevant cofinal
  regime, leaving no positive asymptotic survivor.
- The continuous passage requires an assumption equivalent to RH rather than source-uniform
  control of the explicit moment functional.

## Novelty audit through 2026-07-22

The parent pieces are classical: cofactor-resolvent identities, Cauchy interlacing for orthogonal
compressions, rational Stieltjes transforms, Krylov moment matrices, and low-displacement-rank
matrices. The CCM papers provide `(1)` and use it to construct the rank-one perturbed scaling
operator, but do not state `(4)`, `(6)`, the mixed Hankel criterion `(9)`, or the commuting-metric
equivalence `(11)`. Targeted searches found literature on each parent component but no theorem
combining reflection-graded rank-two displacement with boundary--central Stieltjes positivity to
identify the opposite parity block. Novelty is therefore candidate-level pending expert and
bibliographic review.

## Lean plan

Formalize without any RH hypothesis or source computation:

1. principal-minor/adjugate polynomial identity underlying `(7)`;
2. positive-weight rational Stieltjes monotonicity and unique-zero interlacing;
3. `[FORMALIZED]` finite mixed-moment positivity from distinct positive atoms;
4. the displacement-to-oblique-compression intertwiner in finite modules;
5. an explicit connector theorem whose hypotheses are exactly CCM's `(1)`.

Do not formalize the open boundary--central Stieltjes conjecture as a wrapper.

## Gates

- [x] 0 -> 1: source-pure statement, exact implication chain, predictions, and kill tests
- [x] complete paper proof of the universal finite-dimensional law
- [x] preliminary corpus and external collision search
- [ ] independent expert novelty audit
- [ ] Lean theorem for the complete universal law
- [x] Lean determinant/central-resolvent core
- [x] Lean positive-distinct-atomic Hankel direction
- [ ] instantiate the exact finite CCM matrix definitions in Lean
- [ ] prove source positivity/cofinal margin for actual von-Mangoldt--Gamma coefficients
- [ ] continuous restricted-Weil passage
- [ ] standalone preprint and final citation audit

## References

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- A. Connes, W. D. van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral
  Action*, arXiv:2511.23257.

## Log

- 2026-07-22 -- Derived the parity oblique-compression similarity directly from the CCM
  displacement identity. Closed determinant quotient, mixed Stieltjes measure, positive commutant
  metric, complete parity interlacing, and inverse spectral tomography on paper. Classified
  source positivity and cofinal passage as open; no RH claim.
- 2026-07-22 -- Formalized the universal determinant/central-resolvent identity and the strict
  finite atomic Hankel law in `CCMParityCompressionDeterminant.lean`. This freezes determinant
  algebra and positive-atom Vandermonde arguments; actual von-Mangoldt--Gamma source positivity,
  full interlacing equivalence, and cofinal passage remain open.

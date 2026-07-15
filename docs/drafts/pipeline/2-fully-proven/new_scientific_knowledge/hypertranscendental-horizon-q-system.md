# The hypertranscendental horizon caustics form a nonvanishing Q-system

- **ID:** `hypertranscendental-horizon-q-system`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / INFINITE STATIC CONSTRAINT LATTICE
- **Scientific status:** `[PROVED ON PAPER] [NOVEL SYNTHESIS] [SIGNIFICANCE CANDIDATE]`
- **Formal status:** first two ranks and zero propagation formalized
- **Parents:** `projective-horizon-rectangular-schur-caustic`,
  `projective-horizon-logarithmic-vacuum-duality`, `hypertranscendental-function-jet-freeness`
- **Lane:** source-pure hypertranscendental geometry; static integrable topology

## Theorem

Let `K` be a differential field of characteristic zero and let `x` be hypertranscendental over
`K`.  Write the universal ordinary Taylor jet and its reciprocal as

```text
X(t)=sum_(k>=0) x_k t^k,       Y(t)=X(t)^-1,
Z(t)=Y(t)/Y(0),                h_k=[t^k] Z(t)^2.             (1)
```

Thus `h_0=1`.  For `m,n>=0`, define the normalized horizon amplitude

```text
tau_(m,n)(x)=det(h_(n-i+j))_(1<=i,j<=m),                    (2)
```

using `h_k=0` for `k<0` and the empty determinant `tau_(0,n)=1`.  Then:

1. For every `m,n>=1`, `tau_(m,n)` is the normalized mass determinant of the critical
   `(m,n)` projective-horizon logarithmic vacuum.  Its zero locus is exactly the rectangular Schur
   caustic where finite source reconstruction acquires a zero mode.

2. The complete array satisfies the static `A_infinity` Q-system

   ```text
   tau_(m,n)^2 =
     tau_(m,n-1) tau_(m,n+1) +
     tau_(m-1,n) tau_(m+1,n),                               (3)
   ```

   with boundary values `tau_(0,n)=tau_(m,0)=1`.

3. Every `tau_(m,n)(x)` with `m,n>=1` is a nonzero element of the differential function field.
   Equivalently, a hypertranscendental source is algebraically off every finite horizon caustic.

4. Caustic incidence propagates.  Over a domain, if two adjacent amplitudes in one direction
   vanish, for example

   ```text
   tau_(m,n)=tau_(m,n-1)=0,                                 (4)
   ```

   then at least one transverse neighbor vanishes:

   ```text
   tau_(m-1,n)=0  or  tau_(m+1,n)=0.                         (5)
   ```

The resolution lattice in `(3)` is not a time evolution.  It is an identity among simultaneous
finite constraint charts of one source.

## Proof

The critical-horizon Schur-caustic theorem gives the raw-to-reciprocal Jacobian

```text
J_(m,n)=-y_0^2 (h_(n+r-i))_(0<=r,i<m).                      (6)
```

Its determinant differs from `(2)` only by the nonzero scale `(-1)^m y_0^(2m)`, proving part 1.

For part 2, apply the Desnanot--Jacobi identity to the `(m+1) x (m+1)` Jacobi--Trudi matrix for
`tau_(m+1,n)`.  Deleting both outer rows and columns gives `tau_(m-1,n)`.  The two principal
`m x m` minors are both `tau_(m,n)`, while the two crossed minors are `tau_(m,n-1)` and
`tau_(m,n+1)`.  Hence

```text
tau_(m+1,n) tau_(m-1,n)
  =tau_(m,n)^2-tau_(m,n-1)tau_(m,n+1),                      (7)
```

which is `(3)`.  When `n=0`, the Jacobi--Trudi matrix is lower unitriangular, giving the stated
boundary value.

For part 3, reciprocal inversion is a triangular birational change from
`x_0,...,x_(m+n-1)` to `y_0,...,y_(m+n-1)`.  After dividing by `y_0`, the further change

```text
h_k=2 z_k+polynomial(z_1,...,z_(k-1))                       (8)
```

is triangular with invertible diagonal because the characteristic is zero.  Hypertranscendence
makes every finite raw jet algebraically independent, so `h_1,...,h_(m+n-1)` are algebraically
independent over `K(y_0)`.  The rectangular Schur polynomial in `(2)` is nonzero: under the standard
specialization to complete symmetric functions in `m` variables it becomes the nonzero rectangle
character `s_((n^m))`.  It therefore cannot vanish at the generic independent tuple `(h_k)`.

Finally, substitute `(4)` into `(3)`.  The product of the transverse neighbors is zero, and a
domain has no zero divisors.  This proves `(5)`.  `QED`

## What this says about the nature of hypertranscendence

The finite constraint geometry has a canonical physical description:

```text
finite horizon fiber     = critical scheme of a logarithmic potential,
finite invisible mode    = zero of its Hessian determinant,
all horizon determinants = one A_infinity Q-system,
hypertranscendence       => the generic source misses every finite zero-mode divisor.
```

Thus the emergent physical object is neither a carrier nor a flow.  It is an exact Lagrangian
vacuum constraint at each polarization, glued across all depth polarizations by the Pluecker
relation `(3)`.  The Q-system is the static integrable topology of those constraint charts.

This does not say that every everywhere-noncaustic source is hypertranscendental; the rectangular
determinants are a distinguished family of differential polynomials, not all differential
polynomials.  The proved direction is the strong, source-pure implication from hypertranscendence
to simultaneous algebraic noncausticity.

## Novelty and significance audit

Desnanot--Jacobi, Jacobi--Trudi, rectangular Schur functions, and the Kirillov--Reshetikhin
Q-system are classical.  Hankel determinant tau-functions in integrable systems are classical as
well.  None of those parent identities is claimed as new.

The candidate new scientific content is the conjunction forced by the HT horizon theory: the
mass determinants of every complementary finite observation pair of a hypertranscendental source
are exactly one nonvanishing `A_infinity` Q-system, and its zero patterns are the propagation rules
for loss of finite reconstructibility.  Targeted searches found the parent Q-system and
Grassmannian theories but no source-jet horizon theorem of this form.

This supplies an infinite-depth invariant and a rigorous physical/topological description absent
from the individual finite-level theorems.  The subsequent full-symmetric-monodromy theorem now
provides the global classification of every finite cover: the Q-system survives all tail
deformations while the pure-tail subset labels do not.  An application or classification of the
infinite source itself is still required before any medal-level claim.

## RH impact

Riemann zeta is unconditionally hypertranscendental, so every `tau_(m,n)(zeta)` is a nonzero
differential function: no rectangular horizon mass determinant vanishes identically.  This does
not exclude isolated numerical zeros after evaluation, locate zeta zeros, or orient the critical
line.  The Q-system is still target-translation blind.  An RH application would require an Euler
marking that imposes a sign, reality, or vanishing-cycle orientation compatible with `(3)`.

## Formal verification

`ProjectiveHorizonCausticQSystem.lean` proves the all-rank Desnanot--Jacobi engine for an arbitrary
two-border matrix with invertible central block, proves `(3)` at ranks one and two directly from
the actual rectangular Toeplitz determinants, including the first `3 x 3` instance, and proves the
general domain-theoretic propagation `(4)--(5)` from a Q-system relation.  Reindexing the general
two-border identity as the rectangular Jacobi--Trudi identity and the algebraic-independence
argument remain paper-level.  A targeted leaf build passes; no full build was run.

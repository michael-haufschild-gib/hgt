# Route J joint-depth off-diagonal countertransport

- **ID:** `route-j-joint-depth-offdiagonal-countertransport`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), CLASS-CLOSING NO-GO + POSITIVE COUNTERTRANSPORT
- **RH used:** no
- **Xi zero used:** only as quantified support in final unconditional equivalence
- **Computation used:** no
- **Parent:** `../1-in-progress/route-j-principal-relative-julia-current.md`, Sections 55--57

## Frontier statement

Reflection-diagonal pairing of the primitive joint-depth source erases horizontal displacement.
The remaining regular candidate is its off-diagonal incidence before codiagonalization.  This
card computes that incidence exactly, constructs its canonical inverse-log-clock
countertransport, proves reflected-Hodge preservation, and classifies its cofinal capacity.

## Source theorem

For prime-depth labels `i=(p,e)`, put

```text
n_i = p^(e+1),
lambda_i = log n_i.
```

The literal reflected source/co-source incidence is

```text
P_(eps,a)(i,j)
 = L_(eps+a)(i) conjugate(R_(eps-conjugate(a))(j)).
```

It has exact factorization

```text
P_(eps,a)(i,j) = P_(eps,0)(i,j) H_a(i,j),
H_a(i,j) = exp(a (lambda_j-lambda_i)).
```

All base coefficients are nonzero, hence `H_a` is the normalized actual source incidence.  It is
an exact coboundary:

```text
H_a(i,j) H_a(j,k) = H_a(i,k),
H_a(i,j) H_a(j,k) H_a(k,i) = 1.
```

Every normalized finite cycle is therefore displacement-blind.  This closes the entire
separable multiplicative-cycle class, not only one chosen loop.

More strongly, for the diagonal vertex gauge

```text
G_a(q)=diag_i(exp(a lambda_(q_i))),
```

every finite literal incidence matrix satisfies

```text
P_(eps,a)[q]=G_a(q)^(-1) P_(eps,0)[q] G_a(q).
```

Thus all finite characteristic polynomials, determinants, and traces of every matrix power are
independent of horizontal displacement.  This closes every similarity-invariant finite
Julia/spectral consumer of this source incidence, not only explicit cycle products.

## Burnol and reflected-Hodge bridge

For distinct labels,

```text
H_a(i,j) = H_(-conjugate(a))(i,j)  <->  Re(a)=0,
H_a(j,i) = conjugate(H_a(i,j))     <->  Re(a)=0.
```

At an actual centered divisor displacement,

```text
H_(rho-1/2)(i,j)
 = burnolCoPoissonCenteredConormalCharacter(lambda_j-lambda_i,rho).
```

Thus the doubled Burnol window is exactly the log-clock edge of the retained Euler source, not an
externally chosen analogy.

## Countertransport

For every injective finite packet `q : Fin N -> Primes x Nat`, let `D_q` be the diagonal log-clock
and let `P_q` be the source incidence matrix.  Define

```text
K^P_q(i,j) = 0                                  if i=j,
             P_q(i,j)/(lambda_(q_i)-lambda_(q_j)) otherwise.
```

Then

```text
[D_q,K^P_q] = P_q - diagonal(P_q).
```

The same construction for `H_q` gives

```text
[D_q,K^H_q] = H_q - I.
```

If `Re(a)=0`, then

```text
(K^H_q)^* = -K^H_q,
[D_q,K^H_q]^* = [D_q,K^H_q].
```

This is the operator-level reflected-Hodge preservation requested of the depth-nonlocal
countertransport.

## Uniform capacity theorem

Define

```text
UB(a) := exists C, forall i j, ||H_a(i,j)|| <= C.
```

Then unconditionally

```text
UB(a) <-> Re(a)=0.
```

At `Re(a)=0`, every norm is one.  For positive real part, same-prime edges from depth `0` to depth
`e` at prime `2` diverge exponentially.  For negative real part, reverse the edge orientation.
Consequently

```text
exists C, forall rho in XiDivisorSupport, forall i j,
  ||H_(rho-1/2)(i,j)|| <= C
  <-> RiemannHypothesis.
```

This capstone is an unconditional equivalence, not a proof of the capacity premise.

## No-go closure and novelty audit

- **Exact killing mechanism:** normalized off-diagonal incidence is a vertex-potential quotient;
  all cycle holonomies equal one for every displacement.
- **Strongest positive survivor:** canonical finite inverse-clock countertransport, exact Burnol
  identification, skew-Hermitian reflected-Hodge preservation, and sharp all-oriented-depth
  capacity iff `Re(a)=0`.
- **Prior overlap:** `5-failed/orbitwise-source-divisor-seam-obstruction.md` already proved the
  first-prime transport to be a coboundary and predicted coordinatewise flatness on the full
  prime-power grading.  General inverse-gap commutator algebra is classical.  This card therefore
  does not claim novelty for flatness itself.
- **Strict extension:** exact computation for the literal primitive/co-source joint-depth
  incidence, exact Burnol conormal bridge, actual and normalized finite commutators, operator Hodge
  theorem, and the two-oriented cofinal capacity phase boundary.
- **Open survivor:** genuinely nonseparable, non-coboundary prime/depth--divisor incidence carrying
  an independent arithmetic annihilation law.  It remains in Route J.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  EulerPrimitiveJointDepthOffDiagonalCountertransport.lean
```

Capstones:

- `xiGammaEulerPrimitiveReflectedOffDiagonalIncidence_factor`;
- `xiGammaEulerPrimitiveReflectedNormalizedIncidence_eq_holonomy`;
- `xiGammaEulerPrimitiveReflectedNormalizedIncidence_triangle`;
- `xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_similarity`;
- `xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_charpoly`;
- `xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_det`;
- `xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_trace_pow`;
- `xiGammaEulerPrimitiveReflectedFiniteOffDiagonalCountertransport_commutator`;
- `xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport_commutator`;
- `xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport_conjTranspose_eq_neg`;
- `xiGammaEulerPrimitiveReflectedFiniteNormalizedCountertransport_commutator_isHermitian`;
- `xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_eq_burnolCenteredConormalCharacter`;
- `eulerPrimitiveReflectedOffDiagonalHolonomyUniformlyBounded_iff`;
- `xiGammaEulerPrimitiveReflectedOffDiagonalHolonomyUniformCapacity_iff_riemannHypothesis`.

## Gates

- [x] 0 -> 1: literal source object and exact attack
- [x] 1 -> 2: dependency-closed paper proof in Route J Section 57
- [x] 2 -> 3: unconditional Lean module
- [ ] 3 -> 4: integrate class-closing result into publication paper after final audit

## Log

- 2026-08-03 -- exact source factorization, countertransport, Hodge law, and capacity formalized.

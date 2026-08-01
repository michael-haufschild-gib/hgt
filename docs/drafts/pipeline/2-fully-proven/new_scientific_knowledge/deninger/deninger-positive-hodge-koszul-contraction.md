# Positive Hodge--Koszul contraction

- **ID:** `deninger-positive-hodge-koszul-contraction`
- **Stage:** 2-fully-proven
- **Type:** FINITE-STAGE DERIVED HODGE THEOREM
- **Label:** `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION`
- **Parent:** `deninger-unit-amalgamation-derived-lagrangian-enhancement`
- **Statement:** the derived critical locus of a positive quadratic
  Calderón action restricted to any finite linear Milnor-incidence
  space is the ordinary origin; its Koszul cdga has only the constant
  class.

## Theorem

Let \(B\) be a finite-dimensional real Hilbert space,
\(A:B\to B\) self-adjoint and strictly positive, and
\(L\subseteq B\) a linear subspace.  Define
\[
 q(x)=\tfrac12\langle x,Ax\rangle,\qquad x\in L,
\]
and let
\[
 g:L\longrightarrow L^*,\qquad
 g(x)(y)=\langle Ax,y\rangle.                                 \tag{1}
\]
The gradient-derived zero locus of \(q|_L\) is represented by the
Koszul chain cdga
\[
 K_g
 =
 \operatorname{Sym}(L^*)\otimes\Lambda^\bullet L,              \tag{2}
\]
with
\[
 d_g(f\otimes v_1\wedge\cdots\wedge v_p)
 =
 \sum_{j=1}^{p}(-1)^{j-1}
 f\,g(v_j)\otimes
 v_1\wedge\cdots\widehat v_j\cdots\wedge v_p.                 \tag{3}
\]

`[PROVED HERE] [DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION]`

The augmentation at the origin
\[
 \epsilon:K_g\longrightarrow\mathbb R
\]
is a quasi-isomorphism:
\[
 H_0(K_g)=\mathbb R,\qquad H_p(K_g)=0\quad(p>0).               \tag{4}
\]
Equivalently, the positive graph--Milnor-conormal intersection has no
finite-stage derived excess.

### Proof

Strict positivity makes \(g\) injective: if \(g(x)=0\), then
\[
 0=g(x)(x)=\langle Ax,x\rangle,
\]
so \(x=0\).  Finite dimensionality makes \(g\) an isomorphism.

Choose a basis \(e_1,\ldots,e_n\) of \(L\) and use
\[
 x_i=g(e_i)
\]
as a basis of \(L^*\).  Then `(3)` is the standard Koszul
differential
\[
 d=\sum_i x_i\,\iota_{e_i^*}.                                \tag{5}
\]
On \(\operatorname{Sym}^r(L^*)\otimes\Lambda^pL\), define
\[
 h=\sum_i \frac{\partial}{\partial x_i}\,
       (e_i\wedge-).                                          \tag{6}
\]
The polynomial derivative relation
\(\partial_i x_j=x_j\partial_i+\delta_{ij}\) and the exterior
creation--annihilation relation
\[
 \iota_i(e_j\wedge-)+(e_j\wedge-)\iota_i=\delta_{ij}
\]
give
\[
 dh+hd=(r+p)\operatorname{id}.                               \tag{7}
\]
The differential preserves total degree \(r+p\).  On every
positive-total-degree summand,
\[
 s=\frac{1}{r+p}h
\]
is therefore a contraction.  The only total-degree-zero summand is
the constant copy of \(\mathbb R\), where \(d=0\).  This proves `(4)`.

The construction is basis-independent at the level of the resulting
quasi-isomorphism: a different basis merely conjugates the displayed
contracting homotopy.  For complex Fourier packets, apply the theorem
to the underlying real Hilbert space with
\(\operatorname{Re}\langle-,-\rangle_{\mathbb C}\).

## Arithmetic specialization

On every finite nonconstant Kummer Fourier packet,
\[
 A=|D_\ell|>0.
\]
The linearized finite Milnor relative-cell constraints define a
tangent subspace \(L\).  The derived intersection of the exact
Poisson graph with the corresponding conormal is the derived critical
locus of \(q|_L\).  Formula `(4)` proves its complete
position--momentum fibre is quasi-isomorphic to the constant fibre,
not only that its tangent spaces are transverse.

This upgrades
`DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY` from a tangent theorem to
an explicit finite-stage cdga contraction.

## Exact global consequence

Finite algebraic Hodge enhancement adds no cohomology to the source
coefficient.  Any nontrivial arithmetic middle group must survive the
following non-finite operations:

1. removal of no uniform spectral gap as packets grow;
2. strict nuclear completion before cohomology;
3. coarse invariant-sheaf descent;
4. smooth suspension and the infinite Poisson flow sum;
5. restricted prime/real Rost--Schmid totalization.

The homotopies in `(6)` divide by total degree but, through the
coordinate choice \(x_i=g(e_i)\), their operator bounds also involve
\(g^{-1}\).  Thus they need not be equicontinuous when the smallest
positive eigenvalue of \(|D_\ell|\) tends to zero.  Algebraic
finite-stage contraction therefore does not justify commuting the
homotopy with nuclear completion or coarse derived sections.

## Hostile audit

- Positivity, not RH, gives invertibility of the finite Hessian.
- The augmentation/constant mode must be removed; otherwise \(g\) has
  a kernel.
- A nonlinear Milnor chart requires its own regularity theorem; this
  card proves the exact linear/tangent packet.
- Finite-stage quasi-isomorphism does not imply a strict
  quasi-isomorphism of the nonuniform nuclear limit.
- No zeta zero, spectral divisor, CCM object, or numerical
  computation enters.

## Lean status

`RHTower.deninger_exact_of_scaled_chainContraction` formalizes the
abstract implication
\[
 dh+hd=a\,\mathrm{id},\ a\ne0
 \Longrightarrow
 \ker d\subseteq\operatorname{im}d.
\]
The explicit symmetric/exterior Euler identity `(7)` remains to be
formalized.

## References

- `DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY`.
- `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`.
- `DAC_UNIT_AMALGAMATION_DERIVED_LAGRANGIAN_ENHANCEMENT`.
- Standard Koszul resolution of the origin by a coordinate regular
  sequence.

## Log

- 2026-07-27 — Proved explicit Euler contracting homotopy for every
  positive finite Calderón--Milnor critical packet.

### The exterior half of `(7)` landed

`formal/GaloisForLFunctions/HTGeometry/ExteriorEulerIdentity.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `ExteriorAlgebra.ι_mul_ι_add_swap_eq_zero` — two exterior generators anticommute, and
  `ι_mul_ι_mul` is the form used below: moving a creation past another creation flips the sign.
- `sum_ι_mul_contractLeft_listProd` — **the exterior Euler identity**:

  `∑ᵢ eᵢ ∧ ι_{eᵢ*}(v₁ ∧ ⋯ ∧ v_k) = k · (v₁ ∧ ⋯ ∧ v_k)`,

  i.e. summing creation against contraction over a basis multiplies a product of `k` generators
  by `k`.  The induction is on the list of generators: the creation--annihilation relation
  `CliffordAlgebra.contractLeft_ι_mul` splits off the head, the basis expansion
  `∑ᵢ eᵢ*(a)·eᵢ = a` reassembles it, and anticommutation moves the head past the remaining
  creations so the inductive hypothesis applies.  Since `ExteriorAlgebra.ιMulti_span_fixedDegree`
  says `Λ^k` is spanned by such products, this is the identity on `Λ^k`.

This is the exterior half of the Koszul Euler identity `dh + hd = (r + p)·id`.  The symmetric half
is mathlib's `MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`, so what remains for `(7)` is the
tensor-product bookkeeping on `Sym(L*) ⊗ Λ L` — mathlib has no Koszul complex, so the bigraded
differential and homotopy have to be assembled by hand.

Recorded for the next session: `CliffordAlgebra.contractLeft` is the contraction operator (the
exterior algebra is the Clifford algebra of the zero form), and `Module.Basis` — not `Basis` — is
the current mathlib name.

# Real Arakelov divisor endpoint

- **ID:** `deninger-real-arakelov-divisor-endpoint`
- **Stage:** 2-fully-proven
- **Type:** LITERATURE THEOREM / PAPER SPECIALIZATION
- **Label:** `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`
- **Parent:** `deninger-coarse-invariant-sheaf-rost-schmid-descent`
- **Statement:** the real-linearized principal-divisor/Rost--Schmid
  row of a number field has one-dimensional cokernel, canonically the
  Arakelov degree orientation.

## Number-field theorem

Let \(K\) be a number field.  Write
\[
 \operatorname{Div}_{\mathrm{Ar}}(K)_{\mathbb R}
 =
 \left(\bigoplus_{v\nmid\infty}\mathbb R[v]\right)
 \oplus
 \left(\bigoplus_{v\mid\infty}\mathbb R[v]\right),
\]
with the standard local-degree convention at complex places.  The
principal divisor of \(\alpha\in K^\times\) consists of finite
valuations and negative archimedean logarithms.  The product formula
makes its Arakelov degree zero.

`[PROVED HERE] [DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT]`

After quotienting roots of unity and tensoring with \(\mathbb R\),
\[
 0\longrightarrow
 (K^\times/\mu_K)\otimes_{\mathbb Z}\mathbb R
 \xrightarrow{\operatorname{div}_{\mathrm{Ar}}}
 \operatorname{Div}_{\mathrm{Ar}}(K)_{\mathbb R}
 \xrightarrow{\deg_{\mathrm{Ar}}}
 \mathbb R
 \longrightarrow0                                                \tag{1}
\]
is exact.

## Proof

The product formula gives
\(\deg_{\mathrm{Ar}}\operatorname{div}_{\mathrm{Ar}}=0\).
If a real principal combination has zero finite and archimedean
coordinates, its finite part is a real combination of units and its
archimedean logarithm is zero.  Dirichlet's unit theorem makes the
logarithmic unit map injective after quotienting torsion and tensoring
with \(\mathbb R\), proving injectivity on the left.

For a degree-zero real Arakelov divisor, finiteness of the ideal class
group implies that its finite part becomes principal after real
linearization.  Subtract that principal divisor.  The remaining vector
is archimedean of weighted sum zero.  Dirichlet's unit theorem says
real logarithms of units span exactly that hyperplane, so the remainder
is principal.  This proves exactness in the middle.  An archimedean
basis vector has nonzero degree, giving surjectivity.

## \(\mathbb Q\)-coordinate model

For \(K=\mathbb Q\), identify the finite divisor space with
\[
 D_f=\bigoplus_p\mathbb R[p].
\]
Let
\[
 W(d)=\sum_p d_p\log p.
\]
The full Arakelov divisor space is \(D_f\oplus\mathbb R_\infty\), with
\[
 \operatorname{principal}(d)=(d,-W(d)),\qquad
 \deg(d,a)=W(d)+a.                                                  \tag{2}
\]
Then
\[
 \ker\deg=\operatorname{range}(\operatorname{principal}),          \tag{3}
\]
the principal map is injective, and degree is surjective.  Equations
`(2)`--`(3)` are written unconditionally in
`RHTower/DeningerArithmeticRealArakelovEndpoint.lean`.

By `DAC_ADELIC_PLACE_AVERAGE_RESIDUE`, the finite coordinates in `(2)`
are exactly the place-average Kummer residues.  Thus `(1)` is the
source residue/signature endpoint row required by the coarse
two-column complex.

## Consequence and scope

The cokernel \(\mathbb R\) is the candidate
\(\mathbb R(-1)\) orientation in arithmetic degree two.  This proves
the endpoint of the algebraic residue row.  It does not prove that the
analytic invariant-sheaf totalization has the same cokernel: that still
requires `DAC_FINITE_CORRESPONDENCE_ANALYTIC_REALIZATION`, internal
amplitude, and closed reduced comparison.

It also produces no nontrivial middle spectrum.  For
\(\operatorname{Spec}\mathbb Z\), real-linearized finite divisors are
already principal; spectral \(H^1\) must arise from nonproper
coarse-sheaf/coherence defects.

## Gates

- [x] number-field paper proof
- [x] unconditional Lean source for the \(\mathbb Q\)-coordinate
  exactness core
- [ ] direct Lean check after external build saturation
- [ ] analytic invariant-sheaf endpoint comparison

## References

- Jürgen Neukirch, *Algebraic Number Theory*, product formula, ideal
  class group, and Dirichlet unit theorem.
- Daniel Allcock and Jeffrey D. Vaaler, *A Banach space determined by
  the Weil height*: https://arxiv.org/abs/0808.1038

## Log

- 2026-07-26 — Combined place-average residues with the
  real-linearized Arakelov divisor exact sequence.

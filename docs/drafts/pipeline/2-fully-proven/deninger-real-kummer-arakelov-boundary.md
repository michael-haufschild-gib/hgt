# Real Kummer--Arakelov boundary

- **ID:** `deninger-real-kummer-arakelov-boundary`
- **Stage:** 2-fully-proven
- **Type:** SOURCE BOUNDARY THEOREM
- **Labels:** `DAC_REAL_KUMMER_ARAKELOV_BOUNDARY`,
  `DAC_ARAKELOV_BOUNDARY_SHEAF`
- **Parent:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Statement:** the real logarithmic Kummer functional is a strict
  codimension-one boundary on the cofinite arithmetic base, and
  together with finite valuations its cokernel is the unique
  Arakelov orientation line.

## Arakelov boundary sheaf

Let
\[
 S=\operatorname{Spec}\mathbb Z,\qquad
 \overline S=S\sqcup\{\infty\}
\]
with the usual Arakelov convention that every nonempty cofinite
arithmetic open \(U_N\subset S\) is enlarged to
\(\overline U_N=U_N\sqcup\{\infty\}\).

Define the real boundary sheaf on \(S\) by
\[
 \mathscr B_\infty^S(U_N)=\mathbb R(-1),\qquad
 \mathscr B_\infty^S(\varnothing)=0,                              \tag{1}
\]
with identity restrictions between nonempty opens.  Equivalently,
`(1)` is the direct image of the skyscraper
\(i_{\infty,*}\mathbb R(-1)\) from \(\overline S\).

`[PROVED HERE] [DAC_ARAKELOV_BOUNDARY_SHEAF]`

The prescription `(1)` is a flasque sheaf of complete real vector
spaces.  Hence
\[
 R\Gamma(S,\mathscr B_\infty^S)
 \simeq\mathbb R(-1)[0].                                         \tag{2}
\]

### Proof

Every restriction between nonempty opens is the identity and every
restriction to the empty open is surjective.  Thus all restrictions
are surjective, so `(1)` is flasque.  Flasque sheaves are acyclic,
which proves `(2)`.

## Real Kummer boundary

For \(a\in\mathbb Q^\times/\{\pm1\}\), define
\[
 \partial_\infty(a)
 =
 -\log|a|_\infty.                                                 \tag{3}
\]
If
\[
 a=\prod_p p^{n_p},
\]
then
\[
 \partial_\infty(a)
 =
 -\sum_p n_p\log p.                                               \tag{4}
\]
After tensoring with \(\mathbb R\), `(3)` is a linear map from the
real Kummer line to \(\mathbb R(-1)\).

`[PROVED HERE] [DAC_REAL_KUMMER_ARAKELOV_BOUNDARY]`

The finite and real Kummer boundaries assemble to
\[
 \partial_{\mathrm{Ar}}:
 (\mathbb Q^\times/\{\pm1\})\otimes\mathbb R
 \longrightarrow
 \left(\bigoplus_p\mathbb R[p]\right)
 \oplus\mathbb R_\infty,
                                                                    \tag{5}
\]
\[
 \partial_{\mathrm{Ar}}(a)
 =
 \left(
   (\operatorname{ord}_p a)_p,\,
   -\sum_p\operatorname{ord}_p(a)\log p
 \right).                                                        \tag{6}
\]
It is injective, its image is the kernel of
\[
 \operatorname{tr}_{\mathrm{Ar}}(d,x)
 =
 \sum_p d_p\log p+x,                                              \tag{7}
\]
and `(7)` is surjective.  Therefore
\[
 \operatorname{coker}\partial_{\mathrm{Ar}}
 \cong\mathbb R(-1).                                              \tag{8}
\]

The map `(3)` is continuous for the mixed Kummer norm because
\[
 |\partial_\infty(a)|
 \leq
 \sum_p\log p\,|\operatorname{ord}_p(a)|.                         \tag{9}
\]
It consequently extends uniquely to the strict \(L^1/L^2\)
completion.

### Proof

Unique factorization identifies
\[
 (\mathbb Q^\times/\{\pm1\})\otimes\mathbb R
 \cong\bigoplus_p\mathbb R[p]
\]
by the finite valuation map.  Formula `(4)` is the product formula.
It gives
\(\operatorname{tr}_{\mathrm{Ar}}\partial_{\mathrm{Ar}}=0\).
Conversely, if `(7)` vanishes on \((d,x)\), then
\[
 x=-\sum_p d_p\log p,
\]
so \((d,x)=\partial_{\mathrm{Ar}}(d)\) under the valuation
identification.  Finally \((0,r)\) maps to \(r\), proving
surjectivity.  Inequality `(9)` is the triangle inequality.

## Square-zero Milnor extension

Let \(K_{\mathbb R}^M(\mathbb Q)\) be the real Milnor algebra.  Rank
gives an augmentation
\[
 s_\infty:K_{\mathbb R}^M(\mathbb Q)\longrightarrow\mathbb R
\]
which is the identity in degree zero and zero in positive degrees.
There is a degree-minus-one \(s_\infty\)-derivation
\[
 \delta_\infty:
 K_{\mathbb R}^M(\mathbb Q)\longrightarrow\mathbb R(-1)[-1]       \tag{10}
\]
equal to `(3)` in Milnor degree one and zero in every other degree.
Equivalently,
\[
 s_\infty\oplus\delta_\infty:
 K_{\mathbb R}^M(\mathbb Q)
 \longrightarrow
 \mathbb R\oplus\mathbb R(-1)[-1]                                \tag{11}
\]
is a map of graded square-zero algebras.

Indeed, the augmentation kills every positive-degree factor.  The
graded Leibniz rule therefore forces the derivation to vanish on
products of two positive-degree classes, exactly as `(10)` does.
It is compatible with Steinberg relations because those lie in
degree two.  Thus the real logarithm is not an ad hoc additive
functional: it is the weight-one square-zero boundary of the
realified Milnor algebra.

By `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`, any analytic
Kummer-boundary lift agreeing with `(3)` extends through every
relative Tate--Milnor cell.  The remaining source gate is not the
Milnor relation.  It is construction of that analytic real Betti
lift on Deninger's coarse generic coefficient and proof of its
flow/correspondence compatibility.

## Strict completed endpoint

Let \(D_{\mathrm{fin}}\) be the strict packet residue space.  Its Haar
splitting is
\[
 D_{\mathrm{fin}}
 =
 D_{\mathrm{val}}\widehat\oplus D_{\mathrm{pkt},0}.               \tag{12}
\]
The theorem above proves the trace-kernel identity on
\[
 D_{\mathrm{val}}\widehat\oplus\mathbb R_\infty.                  \tag{13}
\]
Local log-toric Poincaré residue is surjective onto each finite-stage
mean-zero packet space.  Therefore the full completed endpoint reduces
to one exact analytic assertion:
\[
 D_{\mathrm{pkt},0}
 \subset
 \operatorname{im}\partial_{\mathrm{fin}}
\quad\text{strictly after all-prime completion}.                  \tag{14}
\]
If `(14)` holds, `(8)` upgrades to the full boundary space.

## Boundary of the theorem

- The Kummer generator, real sheaf, continuity, product formula, and
  scalar endpoint are complete.
- The analytic real Betti lift on the entire coarse generic
  coefficient is not yet constructed.
- Strict completed surjectivity onto packet mean-zero modes is `(14)`,
  not a consequence of scalar unique factorization.
- The real orientation does not provide Hodge positivity or the
  archimedean fixed-point exponent.

## References

- Daniel Allcock and Jeffrey D. Vaaler,
  *A Banach space determined by the Weil height*:
  https://arxiv.org/abs/0808.1038
- `DAC_ADELIC_PLACE_AVERAGE_RESIDUE`
- `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`
- `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`
- `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`

**Verdict:** `FULLY PROVEN ON PAPER FOR THE REAL KUMMER BOUNDARY AND
SCALAR ARAKELOV ENDPOINT; FULL ANALYTIC REAL-BETTI LIFT AND STRICT
MEAN-ZERO SURJECTIVITY REMAIN OPEN`.

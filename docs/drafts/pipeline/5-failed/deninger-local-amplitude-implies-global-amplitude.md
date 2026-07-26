# Local coefficient amplitude automatically bounds global arithmetic cohomology

- **ID:** `deninger-local-amplitude-implies-global-amplitude`
- **Stage:** 5-failed
- **Type:** RETIRED INFERENCE
- **Parent:** `deninger-algebraic-cyclotomic-milnor-amplitude`

## Retired claim

The real coefficient on every cyclotomic character chart has amplitude
\([0,1]\); therefore its derived global sections on Deninger's flow space
automatically have amplitude \([0,2]\).

## Failure

Stalkwise or local amplitude does not bound sheaf-cohomological degree.
For any sheaf \(\mathscr F\) concentrated in degree zero,
\[
 H^n(R\Gamma(X,\mathscr F))=H^n(X,\mathscr F),
\]
which can be nonzero in arbitrarily high degree when the site has
correspondingly large cohomological dimension.  Deninger's
rational-Witt dynamical approximation is infinite-dimensional, and his
primary paper explicitly says that no analytic structure has yet been
defined on it.  Hence neither finite covering dimension nor a fine/soft
leafwise resolution is presently available.

The implication is false without an additional theorem controlling the
chosen coefficient sheaves.

## Positive survivor

`DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE` gives the sharp replacement.
It is enough to construct either:

1. length-one, global-section-acyclic Rost--Schmid resolutions for the
   degree-zero and degree-one geometric coefficient sheaves;
2. one global-section-acyclic real orientation sheaf supported at the
   zero-dimensional archimedean boundary.

or, without any stalkwise amplitude assertion:

1. a two-level arithmetic localization/hypercover model for derived global
   sections;
2. generic and prime-packet derived-section columns of amplitude
   \([0,1]\);
3. one real orientation summand in total degree two.

The resulting total complex has exactly three terms.  This survivor is fully
proved on paper in
`deninger-two-column-hypercohomology-amplitude`.

## Second-pass audit

Ordinary smooth-foliation arguments do not repair the failed inference.
They use smooth manifolds, partitions of unity, and leafwise differential
forms.  Deninger's present space is an infinite-dimensional topological
approximation and is not proved to possess those structures.  The required
acyclicity must therefore be constructed for the actual
rational-Witt/Galois/residue sheaves.

**Verdict:** `FAILED; POSITIVE SURVIVOR PAPER-PROVED`.

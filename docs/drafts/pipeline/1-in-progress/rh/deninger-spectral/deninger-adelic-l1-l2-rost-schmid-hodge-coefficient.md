# Adelic \(L^1\!\cap L^2\) Rost--Schmid Hodge coefficient

- **ID:** `deninger-adelic-l1-l2-rost-schmid-hodge-coefficient`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE
- **Label:** `DAC_ADELIC_L1_L2_ROST_SCHMID_HODGE_COEFFICIENT`
- **Parent:** `deninger-coarse-invariant-sheaf-rost-schmid-descent`
- **Statement:** the logarithmic Kummer part of Deninger's analytic
  Tate--Milnor coefficient admits a mixed \(L^1/L^2\) completion that
  retains the product formula and Milnor residues while supplying the
  positive local energy used by the leafwise Hodge metric; the
  Milnor--Witt signature is added only at the real boundary.

## Forced source topology

Use the Allcock--Vaaler place space \((Y,\lambda)\) and let
\(\mathcal F\) be the rational span of logarithmic Kummer functions
\(f_\alpha(y)=\log\|\alpha\|_y\).  Define
\[
 E_{\mathrm{Kum}}
 =
 \overline{\mathcal F}^{\,
   \|f\|_{\mathrm{mix}}=\|f\|_1+\|f\|_2}
 \subset L^1(Y,\lambda)\cap L^2(Y,\lambda).                         \tag{1}
\]
Then the integral/product formula remains continuous, while
\[
 B_2(f,g)=\int_Yfg\,d\lambda                                       \tag{2}
\]
is a positive form.  This is the minimal source correction forced by
`DAC_NAIVE_ADELIC_L2_KUMMER_COMPLETION_NO_GO`.

For each rational place \(v\), the component \(Y_v\subset Y\) has
finite measure and
\[
 a_v(f)=\int_{Y_v}f\,d\lambda                                      \tag{3}
\]
is continuous on `(1)`.  On Kummer functions, the finite components
are normalized valuation/residue coordinates and their total sum,
including the archimedean component, is zero.

More precisely, `DAC_ADELIC_PLACE_AVERAGE_RESIDUE` proves for a number
field \(K\), a finite place \(v\), and \(\alpha\in K^\times\) that
\[
 \int_{Y(K,v)}f_\alpha\,d\lambda
 =-\frac{\operatorname{ord}_v(\alpha)}{[K:\mathbb Q]}\log Nv.       \tag{4}
\]
It also proves that normalized field norms are contractions for both
\(L^1\) and \(L^2\), hence for the mixed norm.  Thus the \(K_1\)
residue formula and field-norm continuity are no longer conjectural.

Bare completion in `(1)` is still only a coefficient construction.  It
does not identify its cohomology with Deninger's reduced leafwise
cohomology and does not create the zeta spectrum.

`DAC_ADELIC_KUMMER_GELFAND_TRIPLE` proves that `(1)` has the canonical
rigged-Hilbert form
\[
 E_{\mathrm{Kum}}\hookrightarrow L^2(Y,\lambda)
 \hookrightarrow E_{\mathrm{Kum}}'.
\]
Thus product formula and residues belong to the source test topology,
positive energy belongs to the Hilbert middle, and distributional
traces may live in the dual.  Extending this triple to the full
Steinberg-corrected Milnor sheaf remains open.

The locally constant refinement
`DAC_ADELIC_KUMMER_NUCLEAR_TEST_SCALE` further gives
\[
 \mathcal S_{\mathrm{Kum}}\subset E_{\mathrm{Kum}}\subset L^2
 \subset E_{\mathrm{Kum}}'\subset\mathcal S_{\mathrm{Kum}}',
\]
with \(\mathcal S_{\mathrm{Kum}}\) nuclear.  This types the source
distribution space but does not by itself prove trace-class flow.

## Conjecture

`[CONJECTURE] [DAC_ADELIC_L1_L2_ROST_SCHMID_HODGE_COEFFICIENT]`

There is a Tate-graded transfer sheaf
\(\mathscr E_{\mathrm{mix}}\) on the standard finite-correspondence
category used by `DAC_FINITE_CORRESPONDENCE_ANALYTIC_REALIZATION`
satisfying:

1. **Kummer realization.**  On every algebraic generic chart, its
   weight-one logarithmic Kummer summand is the pullback of `(1)`.
   The chart transition maps agree with Galois pullback and normalized
   field norm.
2. **Product-formula boundary.**  The \(L^1\) channel extends the
   product-formula functional and the real-place boundary.  Its kernel
   is closed and contains the image of the global principal-divisor
   differential.
3. **Rost--Schmid residues.**  The component functionals `(3)` extend
   to a continuous Milnor
   residue differential
   \[
     \partial_{\mathrm{RS}}:
       \mathscr E_{\mathrm{mix},\eta}
       \longrightarrow
       \prod_p' i_{p,*}\mathscr E_{\mathrm{mix},p}.                 \tag{5}
   \]
   Its closure is compatible with specialization and the
   finite-correspondence projection formula.  The real endpoint has a
   separate Milnor--Witt determinant/signature refinement.
4. **Two-channel realization.**  The \(L^1\) channel controls descent,
   trace, and the archimedean product formula; the \(L^2\) channel
   controls the positive energy `(2)`.  The comparison map is
   cohomologically faithful after quotienting the explicitly
   regulator-null acyclic subcomplex.  On the Kummer part it restricts
   to `DAC_ADELIC_KUMMER_GELFAND_TRIPLE`.
5. **Power law.**  Under Deninger's \(s\)-twist, power maps act on the
   Kummer channel by \(n^{1-s}\).  At \(s=\tfrac12\), `(2)` scales by
   \(n\), while the \(L^1\) product-formula kernel is preserved.
6. **Defect completion.**  The local Frobenius homotopy defects
   \([c_{m,n}]\) extend in the mixed residue topology.  Their closed
   span, together with the Rost--Schmid residues, is the orthogonal
   complement of the scalar Kummer sector in reduced middle
   cohomology.
7. **Hodge comparison.**  The reduced complex obtained from `(5)` is
   isomorphic to the harmonic complex of
   `DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION`; under this
   comparison `(2)` is the Kummer restriction of the cup--Hodge
   pairing.

## Step-by-step construction

1. Construct `(1)` and its Galois action directly from the
   Allcock--Vaaler measure.
2. Use `DAC_ADELIC_PLACE_AVERAGE_RESIDUE` for normalized Milnor
   \(K_1\) residues and field-norm compatibility.
3. Extend that identity from \(K_1\) to the full Milnor homotopy
   module and verify the residue projection formula; construct the
   Milnor--Witt determinant/signature comparison only at the real
   endpoint.
4. Sheafify on the finite-correspondence topology; prove that mixed
   completion commutes with the quotient-adapted hypercover.
5. Close `(5)` without replacing the \(L^1\) boundary topology by bare
   \(L^2\).
6. Prove the scalar Kummer sector is removed from the nontrivial
   centered spectrum and identify the defect quotient.
7. Compare the resulting positive form with the Kähler leafwise area
   pairing.

## Falsifiers

- If field norms fail to preserve `(1)` or `(3)`, this is not a
  correspondence coefficient.
- If the product formula becomes dense rather than closed after
  completion, the construction has fallen back to the retired bare
  \(L^2\) route.
- Positivity of `(2)` does not imply positivity on the defect quotient;
  clause 7 is mandatory.
- The scalar Kummer sector cannot be declared to contain zeta
  eigenvectors: its centered power action is the identity.
- A metric or defect class defined using Xi zeros, Weil positivity, or
  RH is circular.

## Current status

- Allcock--Vaaler \(L^1\) hyperplane and \(L^2\) density: literature
  theorem.
- Kummer \(L^2\) positivity, field independence, Tate scaling,
  normalized field-norm contraction, and the local \(K_1\) residue
  formula: literature/paper-proved.
- Mixed Kummer test/Hilbert/distribution triple: paper-proved.
- Nuclear locally constant Kummer test scale: paper-proved.
- Mixed sheafification, Milnor residue closure, real signature
  comparison, defect completion, and Kähler comparison: open source
  construction.

**Verdict:** `ACTIVE SOURCE COEFFICIENT; REPLACES BARE HILBERT
COMPLETION`.

## References

- Daniel Allcock and Jeffrey D. Vaaler, *A Banach space determined by
  the Weil height*: https://arxiv.org/abs/0808.1038
- Paul Fili and Zachary Miner, *Orthogonal decomposition of the space
  of algebraic numbers and Lehmer's problem*:
  https://arxiv.org/abs/0911.1975
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §§10, 12: https://arxiv.org/abs/1807.06400
- Christopher Deninger, *Rational Witt vectors and associated sheaves*:
  https://arxiv.org/abs/2508.05329

## Log

- 2026-07-26 — Created from the positive survivor of the naive adelic
  \(L^2\) no-go.

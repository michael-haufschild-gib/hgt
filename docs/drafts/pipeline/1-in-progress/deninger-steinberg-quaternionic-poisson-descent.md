# Steinberg quaternionic Poisson descent

- **ID:** `deninger-steinberg-quaternionic-poisson-descent`
- **Stage:** 1-in-progress
- **Type:** ALL-NUMBER-FIELDS EXTENSION CONJECTURE
- **Parent:** `deninger-poisson-relevant-complex-comparison`
- **Statement:** a mod-two theta-group quotient of the selective
  Steinberg bar--residue extension supplies the genuinely quaternionic
  coefficient twist required by the Poisson--zeta complex.

## Forced input

Three established facts determine the shape of the missing descent.

1. `deninger-rectangular-quaternionic-hodge` gives a positive local
   odd \(K_{\mathbb R}\) atom intertwined by centered power maps.
2. `deninger-rectangular-untwisted-real-descent-obstruction` proves
   that the untwisted real power cocycle also descends coordinatewise
   conjugation and is therefore forbidden.
3. `deninger-quaternionic-transition-no-real-atom` gives explicit
   \(Q_8\)-holonomy preserving the positive atom and proves that no
   compatible square-one anti-linear real structure exists.

The remaining problem is not linear algebra.  It is construction of
the \(Q_8\)-type holonomy from arithmetic correspondence data.  This is
required for a theory functorial over all number fields.  It is not a
blocker for the isolated \(\mathbb Q\)/Riemann-zeta Hodge comparison,
where an additional real form is allowed.

## Conjecture

`[CONJECTURE] [DAC_STEINBERG_QUATERNIONIC_POISSON_DESCENT]`

Let \(\mathscr M_{\mathrm{St}}\) be the selective positive-degree
Steinberg bar--residue envelope surviving
`deninger-a1-localized-rational-witt-coefficient`.  On the
rational-Witt finite-correspondence groupoid there exists:

1. a functorial rank-two mod-two local system
   \(\Lambda_{\mathrm{St}}\) with a nondegenerate alternating residue
   pairing
   \[
     e_{\mathrm{St}}:
     \Lambda_{\mathrm{St}}\times\Lambda_{\mathrm{St}}
       \longrightarrow\mu_2;
   \]
2. its theta-group central extension
   \[
     1\longrightarrow\mu_2\longrightarrow
     \widetilde\Lambda_{\mathrm{St}}\longrightarrow
     \Lambda_{\mathrm{St}}\longrightarrow1,                         \tag{1}
   \]
   whose commutator is \(e_{\mathrm{St}}\);
3. local symplectic bases whose lifts \(i,k\) satisfy
   \[
     i^2=k^2=-1,\qquad ik=-ki,
   \]
   so the corresponding finite holonomy subgroup is \(Q_8\);
4. a Morita quaternionic line
   \(\mathscr S_{\mathrm{arith}}\) for `(1)` whose transition
   representation is the explicit positive
   `DAC_QUATERNIONIC_TRANSITION_NO_REAL_ATOM`;
5. a power-equivariant action for which centered Frobenius maps are
   unitary and intertwine the rectangular Hodge operators;
6. a theta/Poisson descent section making
   \[
     Z=\sum_{n\ge1}F_n^{-1}
   \]
   equivariant on the logarithmic Schwartz domain;
7. a strict derived pushforward comparison
   \[
     R\alpha_*
       \bigl(\mathscr M_{\mathrm{St}}
         \mathop{\otimes}^{\mathbb L}
         \mathscr S_{\mathrm{arith}}\bigr)
       \simeq C^\bullet_{\mathrm{PZ}}                               \tag{2}
   \]
   preserving flow, cup, trace, endpoints, and topology.

The quaternionic line in `(2)` is a Morita/gerbe twist, not an
additional tensor factor in cohomology.  Under the comparison it
organizes the upper/lower conjugate Meyer spectral directions into one
quaternionic block.  It must not double zero multiplicities.

## Why the theta-group form is forced

For a rank-two \(\mathbb F_2\)-module with nondegenerate alternating
pairing, a theta group has lifts whose commutator is the nontrivial
central sign.  Choosing lifts with square \(-1\) gives \(Q_8\), and its
standard complex representation is exactly the proved transition
atom.  Conversely, a split extension has commuting lifts and retains a
real reduction.  Thus nontriviality of `(1)` is precisely the missing
parity datum, not an optional metaplectic decoration.

The use of a selective Steinberg envelope is also forced.  Full
\(\mathbb A^1\)-localization contracts the rational-Witt coordinate,
while a bare Hilbert-symbol \(\mu_2\)-quotient forgets the higher
Steinberg coherences needed for residues and Poisson gluing.  The
universal positive-degree extension must be constructed first; `(1)`
is only its coefficient representation.

## Proof obligations

1. Construct \(\Lambda_{\mathrm{St}}\) sheafwise from normalized
   multiplicative bar faces and MW residue maps.
2. Prove \(e_{\mathrm{St}}\) is alternating, nondegenerate, and
   compatible with finite correspondences.
3. Construct `(1)` before taking derived global sections and prove its
   local \(Q_8\) presentation.
4. Prove the power action preserves `(1)` and the positive rectangular
   metric after half-density centering.
5. Derive the theta section and Poisson equivariance from the real
   Betti Fourier boundary and adelic product formula.
6. Prove `(2)` chainwise, including strict closed range.
7. Prove the Morita comparison pairs upper/lower spectral directions
   without multiplicity doubling.

## Falsifiers

- If the mod-two residue pairing is degenerate or zero, `(1)` cannot
  produce genuine quaternionic holonomy.
- If `(1)` splits on the transversal groupoid, coordinatewise
  conjugation returns and Deninger's no-real theorem excludes the
  model.
- If the twist is attached only after derived sections, it is a
  spectral decoration rather than \(R\alpha_*\mathcal G\).
- If the complex rank-two atom tensors \(M_\zeta\) instead of Morita
  pairing conjugate directions, zero multiplicities double.
- If Poisson equivariance uses zeta zeros or Weil positivity, the
  comparison is circular.

## Current status

- Quaternionic transition representation and no-real theorem:
  paper-proved; Lean written, direct check pending system capacity.
- Selective Steinberg envelope: survivor conjecture from a proved
  \(\mathbb A^1\)-contraction no-go.
- Arithmetic mod-two residue pairing, theta extension, and comparison
  `(2)`: open.

**Verdict:** `ACTIVE ALL-NUMBER-FIELDS EXTENSION CONJECTURE; NOT ON THE
\(\zeta_{\mathbb Q}\)-TO-RH CRITICAL PATH`.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400.
- Christopher Deninger, *There is no "Weil-"cohomology theory with
  real coefficients for arithmetic curves*, arXiv:2204.02714.
- Moulay-Tahar Benameur and James L. Heitsch, *The twisted higher
  harmonic signature for foliations*, arXiv:0711.0352.
- Classical theta-group construction: the commutator of the central
  extension is the underlying alternating Weil pairing.

## Log

- 2026-07-27 — Extracted the conjecture from the proved untwisted
  real-reduction obstruction and explicit \(Q_8\) no-real transition
  atom.  Separated universal Steinberg descent from its quaternionic
  coefficient representation and made no-multiplicity-doubling an
  explicit gate.

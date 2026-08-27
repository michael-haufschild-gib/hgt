# FZZ puncture polynomial-incidence minor classification

- **ID:** FZZ-PIM
- **Stage:** 3-formalized
- **Type:** SINGULAR-PENCIL RIGIDITY / EXACT CLASSIFICATION
- **Parent:** FZZ-RPP / FZZ-P
- **Frontier-map policy:** read only

## Frozen conjecture

Let `A(z)` be an arbitrary fixed `R×N` complex polynomial matrix encoding all
finite interior equations and coupling constraints.  A dark mode at real energy
`E` is a nonzero vector in `ker A(E)`.

Prove the equivalence:

1. `A(E)` has a nonzero kernel vector for every positive real zero `E` of `XiC`;
2. every `N×N` column-maximal minor of `A` vanishes identically;
3. `A(z)` has a nonzero kernel vector for every complex `z`.

Thus a fixed finite polynomial incidence model cannot select exactly the zeta
zero set.  If it catches every positive real Xi zero, its dark branch persists
at every energy.

## Corpus basis

- FZZ-RPP: positive real XiC zero packets of arbitrary finite size.
- `HTGeometry.MvPolynomialMatrixRankDefect`:
  rectangular complex `mulVec` is injective iff some column-maximal minor is
  nonsingular, and polynomial rank defect is the common zero locus of those
  minors.
- Polynomial evaluation commutes with determinant; a nonzero univariate
  polynomial has at most `natDegree` roots.

## Paper proof

For each row selection `rows : Fin N → Fin R`, a dark vector at `E` lies in the
kernel of the selected square submatrix, so the corresponding minor polynomial
vanishes at `E`.  Xi-completeness supplies, for a hypothetically nonzero minor
of degree `d`, an injective Hardy packet of `d+1` positive real roots, impossible.
Hence every maximal minor is the zero polynomial.

Conversely, if all maximal minors vanish identically, all their evaluations
vanish at every `z : ℂ`.  The rectangular maximal-minor injectivity criterion
then says `A(z).mulVec` is noninjective, equivalently it has a nonzero kernel
vector.  This holds at every complex energy and implies Xi-completeness.

## Lean theorem package

Module:
`GaloisForLFunctions.RHTower.FZZCigarPuncturePolynomialIncidenceMinorClassification`

- `eval_fzzPuncturePolynomialIncidenceMinor`
- `fzzPuncturePolynomialIncidenceDarkMode_iff_not_injective`
- `fzzPuncturePolynomialIncidenceDarkMode_isRoot_minor`
- `not_fzzPuncturePolynomialIncidenceXiComplete_of_minor_ne_zero`
- `fzzPuncturePolynomialIncidence_minors_eq_zero_of_XiComplete`
- `fzzPuncturePolynomialIncidence_universallyDark_of_minors_eq_zero`
- `fzzPuncturePolynomialIncidence_xiComplete_iff_minors_eq_zero`
- `fzzPuncturePolynomialIncidence_xiComplete_iff_universallyDark`

The last two theorems are the exact classification.  They include every finite
polynomial interior/coupling system representable by stacking its equations as
rows, including rectangular overdetermined systems and identically singular
square pencils.

## Novelty status

Provisional `[NEW]`: polynomial-eigenvalue literature treats singular pencils,
normal/minimal rank, and separation of true from fake eigenvalues after
regularization.  FZZ literature treats first-order reductions, winding
condensates, and puncture criticality.  No checked source states the
Xi-completeness-to-all-energy-darkness collapse for a finite polynomial
FZZ/puncture incidence matrix.  Priority remains provisional pending expert
review.

Primary sources checked:

- arXiv:2406.16832, singular polynomial eigenvalue problems and regularization
- arXiv:1712.05742, minimal ranks and Kronecker structure of matrix pencils
- arXiv:2411.16669, higher-dimensional FZZ puncture/first-order reduction
- arXiv:2010.14681, higher-rank FZZ dualities

## Exact new insight and surviving boundary

Xi-completeness is not merely compatible with algebraic singularity: in this
finite polynomial class it is **equivalent** to universal rank defect.  Therefore
no such model can distinguish Xi zeros from nonzeros.  A selective FZZ endpoint
must escape at least one frozen hypothesis: finite column dimension, finitely
many polynomial incidence rows, fixed coefficients, or polynomial energy
dependence.  Infinite-dimensional/non-polynomial/moving-domain dynamics survive.

## Verification

- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarPuncturePolynomialIncidenceMinorClassification.lean`
- Targeted build:
  `lake build GaloisForLFunctions.RHTower.FZZCigarPuncturePolynomialIncidenceMinorClassification`
- Principal theorem axiom audit: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Umbrella import wired in `GaloisForLFunctions/RHTower.lean`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.
- Repository lint was run.  It recognized this module as umbrella-reachable but
  exited nonzero on unrelated concurrently present unreachable Sieve and
  HTGeometry modules; none of the reported errors names this theorem package.

## Status

- Mandatory corpus and primary-literature searches complete.
- Paper proof dependency-closed.
- Lean proof complete; direct check and targeted build passed.
- Exact singular finite-polynomial boundary classified.

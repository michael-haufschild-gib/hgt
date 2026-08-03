# Galois sheet-pair coarea universal law

- **ID:** galois-sheet-pair-coarea
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** Douçot, *New nonabelian Hodge graphs from twisted irregular connections*, Lemmas 2.1--2.2; cyclic conductor/discriminant mechanism
- **Statement:** Every type-A Stokes loop and edge multiplicity is the normalized coarea of loss of equality among a pair of cyclic Galois sheet torsors; complementary contact is the survival integral of the same filtration.

## Goal

Supply the missing two-orbit Puiseux source bridge and identify the common law behind the paper:

`cyclic sheets -> equality-mass filtration -> conductor/coarea -> complementary contact -> tomography/energy`.

The first arrow must be actual complex root-of-unity algebra, not a decorated-core certificate.

## Gates

- [x] 0 → 1  in-progress: exact common-level kernel and fission layer isolated
- [x] 1 → 2  fully-proven: complete proof below; no open mathematical dependency
- [x] 2 → 3  formalized: `StokesPairPuiseuxSourceLaw.lean`; targeted build and axiom audit passed
- [ ] 3 → 4  publication-ready: manuscript integration, novelty audit and hostile review

## Exact theorem

Let `R,S>0`.  A common exponent `k=n/d` is reduced, with `d|R,S`; its numerators in the two
denominators are `m=(R/d)n` and `m'=(S/d)n`.  For sheets
`a in Z/R`, `b in Z/S`, their coefficients at this common exponent agree iff `a=b (mod d)`.

For common exponents `k_i=n_i/d_i` in decreasing order put

`D_i=lcm(d_0,...,d_i)`, `D_(-1)=1`.

Assume every `D_i` divides `R,S`, as it does for a common truncation.  Let `E_i` be the set of sheet
pairs agreeing through the first `i` common exponents.  Then

`|E_i|=R S/D_i`,

and the pairs first separating at `k_i` number

`R S/D_(i-1)-R S/D_i = R(S/D_(i-1)-S/D_i)`.

If the different part of the `R`-orbit has leading numerator `s_d`, so fission slope is `s_d/R`,
every pair remaining in `E_t` separates there.  Consequently

`Irr(Hom(I,J))
 = sum_i m_i(S/D_(i-1)-S/D_i) + s_d S/D_t`,

and

`B_(I,J)=Irr(Hom(I,J))-RS`.

For `I=J`, replace the pair torsor by `Z/R` relative shifts.  This specializes to

`Irr(End(I))=sum_i beta_i(e_(i-1)-e_i)` and
`B_(I,I)=Irr(End(I))-R^2+1`.

Thus both published formulas are shadows of one law: if `M(h)` is the number of sheet pairs still
equal above height `h`, irregularity is the Stieltjes coarea integral

`Irr = integral h d(-M(h))`,

while complementary contact is its affine normalized survival integral.  The tomography and
energy-tree theorems depend only on this survival profile.

## Dependency-closed proof

`[PROVED HERE]` For one reduced common exponent, actual phases are

`zeta_R^(a m)=exp(2 pi i a n/d)` and
`zeta_S^(b m')=exp(2 pi i b n/d)`.

Their equality is equivalent to `d | n(a-b)`, and coprimality of `n,d` cancels `n`, giving
`a=b mod d`.

For any `D|R,S`, reduction defines surjections `Z/R -> Z/D` and `Z/S -> Z/D`.  The map

`delta_D : Z/R x Z/S -> Z/D`, `(a,b) |-> a-b`,

is surjective.  Its kernel is the equality set modulo `D`.  The first isomorphism theorem, or direct
finite-group cardinality, gives

`|ker(delta_D)|=|Z/R x Z/S|/|Z/D|=RS/D`.

Agreement at all exponents `d_0,...,d_i` is simultaneous congruence modulo their lcm `D_i`; hence
`E_i=ker(delta_(D_i))`.  Nested-set subtraction gives the stated layer sizes.  Multiplying a layer
size by its slope `m_i/R` cancels `R`; multiplying the final surviving mass `RS/D_t` by the fission
slope `s_d/R` gives `s_d S/D_t`.  Summation and the published `-RS` normalization prove the edge
formula.  The relative-shift diagonal specialization is the already paper-proved and formalized
cyclic stabilizer coarea law.  Finite Stieltjes coarea is exactly this sum over jumps of `M`, proving
the universal formulation.

## Novelty and hostile audit

- **Local formula verdict:** `[BRIDGE / REDISCOVERED]`; it reorganizes published formulas and the
  classical conductor-discriminant mechanism.
- **Universal-law verdict:** `[CANDIDATE NEW SYNTHESIS]`, not yet an accepted novelty claim.  Search
  found Eggers--Wall contact complexity and tree/contact interpretations, but no source presenting
  the full factorization from cyclic sheet-equality mass through complementary contact to exact
  hierarchy tomography, strict tree energy, four-point law, strict negative type and canonical
  squared embedding.
- **Falsifier:** a source proving this complete factorization and consequences with the same
  diagonal/off-diagonal normalization reclassifies it as rediscovered.
- **Theatre test:** Lean must contain `delta_D`, prove its kernel cardinal, prove the complex common
  phase criterion, and derive the edge coarea.  Assuming a contact profile does not pass.

## Log

- 2026-08-03 — exact two-torsor kernel route isolated after one-orbit source module passed.
- 2026-08-03 — paper proof dependency-closed; promoted directly to 2-fully-proven.
- 2026-08-03 — formalized complex common phases, quotient-difference kernel cardinal, LCM
  filtration, exact pair coarea, zero-common/unramified specializations and diagonal/off-diagonal
  master law; all promoted theorems use only `propext`, `Classical.choice`, `Quot.sound`.

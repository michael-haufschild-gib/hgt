# Source-normal valuation-coframe transgression

- **ID:** `source-normal-valuation-coframe-transgression`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / PRODUCER TARGET
- **Status:** `[OPEN] [NOT RH] [ANTI-CIRCULARITY GATES ACTIVE] [NO LEAN WRITTEN]`
- **Parent theorem:**
  `../../2-fully-proven/constraint-relativity/prime-valuation-cyclic-coframe-and-diagonal-dagger-defect-law.md`

## Problem

Current arithmetic source has complete valuation cyclic coframe

\[
 \phi_\ell([u_p])=-\delta_{\ell p},
\]

and physical dagger defect is diagonal off line. Faithful completion of old differential cannot
annihilate it. Missing event must make valuation cocycles transgress under genuinely new,
source-generated boundary operation before choosing Xi divisor.

## Central conjecture VCT

Construct from literal rational-adelic/Gamma/co-Poisson source, before divisor specialization:

1. source-normal complex `N_src` extending current signed cyclic complex;
2. extensions `tilde phi_ell` of all valuation cocycles;
3. source-generated prime--infinity or cross-grade law cells `mathfrak U_(p,s)`;
4. one divisor-independent boundary operation `d_src`;

such that on open pre-divisor spectral domain

\[
 d_{\mathrm{src}}^*\widetilde\phi_\ell
   (\mathfrak U_{p,s})
 =\delta_{\ell p}
  \bigl(1-p^{2\Re s-1}\bigr)C(s),
 \tag{VCT}
\]

with `C(s)` actual nonzero completed-theta/Xi source jet before selecting zero.

An independent source identity making left side zero on every Xi divisor would then force each
radial factor to vanish. Equation alone is receiver, not selector; independent vanishing theorem
is mandatory.

## Why this is first viable law event

- Old cyclic differential leaves every `phi_ell` closed and is radially equivariant.
- Cross-prime cancellation is impossible coordinatewise.
- Holomorphic one-leg compensation is impossible.
- Mixed opposite charge has exact separation rank two.
- Rank-minimal fitted compensation is contractible.

Therefore new operation must be non-`Gamma_c`-equivariant, genuinely mixed/two-legged,
noncontractible, source-generated, and singular enough that old valuation cocycles cease to be
closed only through controlled transgression.

## Conjecture loops

### VCT-1: archimedean Kummer closure

Try extend finite valuation family by infinity valuation and use product formula. **Failed:**
principal-idèle relation is invariant under every radial character `|.|^c`; it cancels all `c`,
not only zero.

### VCT-2: sum valuation cocycles

Try scalar Kummer `sum log(ell) phi_ell`. **Failed:** it is one covector, loses prime coordinates,
and remains radial-gauge invariant.

### VCT-3: complete prime span

Try Hilbert/nuclear completion. **Failed under faithful extension:** each extended `phi_ell`
continues to separate prime coordinates; diagonal off-line defect stays injective.

### VCT-4: force a cross-grade line

Algebraically, line spanning two distinct total grades has trivial radial stabilizer. **Partial:**
correct selector normal form, but adjoining such line by hand is circular. Need canonical source
production and physical dagger landing.

### VCT-5: source-star mismatch at infinity

Candidate survivor: ordinary source dagger reverses Kummer orientation and is blind. Seek secondary
operation comparing finite-prime valuation coframe with archimedean analytic adjoint without
reversing prime class. This is nonprincipal prime--infinity boundary anomaly. Construction open.

## Fatal anti-theatre tests

Any candidate fails if:

1. defined after choosing `rho`;
2. inserts `Re rho=1/2`, `delta=1`, null-homology, or equivalent normality;
3. equation holds only after logarithmic contraction, not prime-by-prime;
4. erases first nonzero Xi jet or trace-one prime atom;
5. cone differential is defined to be desired multiplier;
6. operation is homogeneous under total radial grade;
7. new compensator splits as contractible fitted pair;
8. source relation is not canonical under rational-adelic symmetries;
9. generalized-prime countermodels satisfy every stated premise off line.

## First exact subproblem

Construct on two primes `p!=q` and infinity an honest source exact triangle in which:

\[
 [d_{\mathrm{src}},\partial_p]
 \quad\text{and}\quad
 [d_{\mathrm{src}},\partial_q]
\]

are nonzero, independent, and land on same rank-one Stokes orientation port, while diagonal radial
combination has trivial stabilizer. Prove relation before any Xi zero enters.

## Falsifier

Prove every source-natural extension of current rational-adelic cyclic complex commuting with
finite adèles and actual Xi coordinate action remains `Gamma_c`-equivariant. That would rule out
VCT inside present source category and force pivot to a larger source law (likely nonprincipal
prime--infinity/holographic completion).

## Lean-return note

No Lean until dependency-closed paper construction exists. Later inspect files listed in parent
Stage-2 card; do not write or build now.

## Log

- 2026-08-08 — opened after valuation-coframe theorem and radial-gauge no-go.

# Arithmetic conormal socle-gauge frontier (2026-08-03)

Research card: `docs/drafts/pipeline/1-in-progress/riemann-arithmetic-conormal-socle-gauge-law.md`.

Universal law isolated:
- Let `N_Xi^src` carry centered rational-dilation action.
- Atomic socle locus is union of one-dimensional G-character submodules, not their span.
- A G-invariant finite-weight domain containing that locus with an absolutely homogeneous gauge q, positive on every nonzero character line, forces all retained characters unitary.
- At a multiplicity-m Xi divisor, the top local jet `(s-rho)^(m-1)` is an exact eigenline with character `g^(rho-1/2)`; invariance for one prime already forces Re rho=1/2, hence every existing horizontal defect D_rho vanishes and RH follows.

Concrete independent producer law (open):
- Construct singular relative Rees *-algebra from Wold ideal + Gamma determinant + BV first trace + co-Poisson source point.
- Construct divisor-independent equivariant conormal map j_src and source-pointed positive weight Omega_src.
- Weight must be invariant, finite, and strictly positive on every exact conormal character line; it may be unbounded elsewhere.
- q(x)=Omega(jx* jx)^(1/2).
- Ordinary bounded boundary states erase anomalies; finite Rees order preserves flat radical; singular infinite source-normal weight is necessary.

New sharpening:
- Full injectivity is unnecessary.
- Separation of sums of character lines is unnecessary.
- Lower jets, global positivity, Hilbert space, all-prime estimates are unnecessary.
- Minimal target: one fixed prime invariance + non-erasure of each top character line.

Corpus already closes finite-stage half:
`deningerTopConormalPowerPullback_comp`,
`inner_deningerTopConormalEmbedding`,
`deningerTopConormalResidue_embedding`,
`deningerRamifiedFiniteStageToAlgebraic_injectiveOn_admittedSector`,
`iteratedDeriv_gammaCoPoissonIntervalCell_self_ne_zero`,
`deningerOneSidedFramedCurvature_two_eq_zero_iff`,
`deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_framedCurvaturePolarization`.
Existing `completeResolution_sourceCharacter_selection` proves vectorwise erasure-or-neutrality. Exact remaining theorem is global, divisor-independent atomic non-erasure through singular source-normal completion.

Honest status: source law open; no RH proof; no new Lean module because formalizing another conditional interface would be theorem-wrapper theater.
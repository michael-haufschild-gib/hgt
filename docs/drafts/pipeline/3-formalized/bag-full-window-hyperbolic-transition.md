# BAG full physical-window hyperbolic transition

- ID: C28.56ag.4, continuation01a9.
- Route: complete signed physical BAG cubic.
- Paper: ../2-fully-proven/bag-full-window-hyperbolic-transition.md.
- Parent: ../1-in-progress/bag-complete-hyperbolic-transition-action.md.
- Status: two production leaves, all19 public declarations audited.

For every positive r the complete two-coordinate oscillatory kernel equals
the full bilinear Fourier multiplier at (-r*y,-r*x), with factor r*e(-r*x*y).
Both Schwartz amplitudes and every edge transition remain. The literal
Gaussian/logarithmic slices are proved Schwartz to every order. Full-line
Mellin inversion of the actual physical window then gives an absolutely
convergent assembly, with no omitted Mellin tail or assumed analytic estimate.
The unconditional capstone `exists_bagCubicFullWindowTransitions` constructs
the actual family while retaining the established negligible sharp/smooth
cubic comparison. The comparison is inherited from the existing corpus.

`ChiHyperbolicFourierTransition` (6 declarations) passed production59166;
`ChiPrimeGaussianCubicWindowTransition` (13 declarations) passed41307.
Both commands were `lake --old env lean <leaf> -o <olean>`; logs are empty.
All19 names passed axiom56220: only propext, Classical.choice, Quot.sound.
Index35593 passed. Generated LEAN_API lists18 names; the same-line attributed
`bagCubicMellinSlice_apply` is absent from that generated list but was included
in the successful explicit19-name Lean axiom audit. Both umbrella imports
occur exactly once. Lint11175 reports26 unrelated unreachable modules;
no proof-debt or new-leaf finding. Global lint is not clean.

Search67634 was nonpartial65681/65681, with incomplete background refresh
and source-only/pending compiler metadata. All20 candidate and20 source
statements/methods, empty proof ideas and proposed ingredients were inspected.
The lexical smoothness search found only the existing C2 cutoff theorem;
its actual explicit derivative was used to prove C-infinity. Concrete
mathlib API names were probed in /tmp. No numerical experiments, new axioms,
resource increases, subagents, commits, full or umbrella builds occurred.

This closes the exact CONTINUUM two-coordinate slice only. It proves no
signed cubic saving. Complete lattice Poisson transfer, the r-variable,
both literal contraction projectors and the critical atom tensor still
need assembly. Their signed near-cone and transverse-tail aggregate at
o(N/log(N)^2), growing moments, moving cofactors, common-height self-return
and RH remain open. Goal ACTIVE.

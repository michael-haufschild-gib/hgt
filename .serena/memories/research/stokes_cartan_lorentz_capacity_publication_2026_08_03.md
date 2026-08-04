# Stokes--Cartan Lorentz-capacity law completed (2026-08-03)

New theorem: every type-A genus-zero nonabelian Hodge Cartan form is finite, affine, or Lorentzian. For rooted contact data,
C = I + Σ_e ell_e u_e u_e^T - (H-1) r r^T.
Capacity gap Omega=(r^T P^{-1}r)^{-1}-(H-1) gives exact trichotomy, determinant, affine kernel, and root-extension invariant. Corona pruning is series-parallel effective resistance. Arbitrary type-A legs preserve one-defect law. Graph corollary: lambda_2(B) <= 2; higher Kac--Moody signatures excluded in stated class.

Publication artifacts:
- docs/drafts/manuscripts/stokes-cartan-lorentz-law/main.tex
- docs/drafts/manuscripts/stokes-cartan-lorentz-law/output/pdf/stokes-cartan-lorentz-law.pdf
- CLAIM_TRACE.md, LITERATURE_AUDIT.md, HOSTILE_REVIEW.md
- pipeline card: docs/drafts/pipeline/4-publication-ready/stokes-cartan-lorentz-capacity-law.md

Formal modules:
- StokesCartanLorentzCapacity.lean
- StokesCartanTypeALegs.lean
- StokesCartanCoronaCapacity.lean
All targeted lake builds pass; forbidden declarations absent; imports wired into HTGeometry umbrella. Global lint currently red only from unrelated concurrent unwired RHTower modules and two unrelated HTGeometry modules. No owned Lean/lake process left.

Closest novelty collision audited: Nabben arXiv:2607.27221 (July 2026), no inertia/Lorentz/Stokes theorem. Prior contact tomography is input, not claimed new.
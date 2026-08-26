# BM projective Hawking–Matsubara response (2026-08-25)

## Result
The conjecture that the physical mixed causal response is logarithmically singular at the Birmingham–Mokhtari Hawking–Matsubara frequency is false. BM Eq. (34) gives forbidden and decaying boundary coefficients
[
S=\Gamma(c)\Gamma(1/2)/(\Gamma(A)\Gamma(B)),\qquad
V=\Gamma(c)\Gamma(-1/2)/(\Gamma(A-1/2)\Gamma(B-1/2)).
]
Their normalization-invariant response is
[
\mathscr R=V/S=-2\frac{\Gamma(A)}{\Gamma(A-1/2)}
\frac{\Gamma(B)}{\Gamma(B-1/2)}.
]
The common \(\Gamma(c)\) pole cancels.

For mixed frequency \(\Omega_{+-}=-i(2n+2k+3)\) and real BM momentum \(\chi\),
[
\mathscr R_{+-}=-2\left|
\frac{\Gamma(-n-k-3/4+i\chi/2)}
{\Gamma(-n-k-5/4+i\chi/2)}
\right|^2<0.
]
Quarter shifts avoid all Gamma poles, including \(\chi=0\). Thus response is finite, nonzero, strictly negative real, and has zero imaginary part. A logarithmic finite part belongs only to a chosen horizon-normalized Frobenius representative/first jet, not the projective boundary response. The zero of reciprocal forbidden coefficient \(1/S\) at \(c\in-\mathbb N\) is a normalization zero, not physical vanishing.

The exact ++ formula is
[
\mathscr R_{++}=-2
\frac{\Gamma(-2n-3/4-i\chi/2)}{\Gamma(-2n-5/4-i\chi/2)}
\frac{\Gamma(-2n-3/4-3i\chi/2)}{\Gamma(-2n-5/4-3i\chi/2)}.
]

## Formalization
Created:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMProjectiveCausalResponse.lean
- import added to formal/GaloisForLFunctions/RHTower.lean
- corrected active card docs/drafts/pipeline/1-in-progress/hawking-bm-augmented-einstein-mode-evaluation.md

Direct Lean source check and exact target build passed. Every public declaration reports only standard Mathlib axioms [propext, Classical.choice, Quot.sound]. Lint has only pre-existing unreachable-module errors; new module is reachable. Scratch files and generated target artifacts removed. No git operation.

## Remaining open core
This solves scalar normalization-invariant BM boundary response, not sourced nonlinear Einstein operators. Full total (++-) cokernel still requires:
- gauge-fixed Kodama–Ishibashi metric reconstruction;
- angular harmonic product coefficients;
- augmented bulk/horizon/outer-boundary second and third jets;
- sourced radial Green integrals and stationary constraint completion;
- adjoint target projection of the complete causal convolution.

Novelty status: novel to audited local corpus and audited primary literature, globally unverified.

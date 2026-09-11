# Route L: original circle observations on all integrable sources

- **ID:** L-C47
- **Date:** 2026-09-11
- **Stage:** 1-in-progress
- **Type:** original Green-domain classification / source correction test
- **Depends on:** [C46 complete damped Xi packet](../3-formalized/route-l-damped-complete-xi-packet.md); `HTGeometry.FourierUniquenessL1`; `HTGeometry.L1PeriodizationFourier`
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. C46 admits the full damped Xi field and original
Tate graph family for fixed a>1, while retaining the original physical
critical-line discriminator. The hard remaining step is a source-forced
comparison or domain change. This card tests the admissible correction
class before proposing such a change.

## Conjecture → paper proof under verification

For integrable f, all Fourier coefficients of its original periodizations
along any positive periods L_n tending to infinity determine f almost
everywhere. No smoothness, exponential decay, analytic continuation, or
Xi placement is needed.

The corpus coefficient law identifies coefficient m with
`(1/L_n) * Fourier(f)(m/L_n)`. For each real frequency w, set
`m_n=floor(w*L_n)`. Then `0 <= w-m_n/L_n < 1/L_n`, so the sample frequency
tends to w. L1 Fourier continuity transports vanishing of all circle
coefficients to every frequency. The corpus L1 uniqueness theorem then
gives f=0 almost everywhere. Applying the same continuous-sampling argument
to the difference of two Fourier transforms gives the equality version.

For an infinite set of original primes, an injective enumeration tends to
infinity and so do its positive logarithms. Thus all those original circle
observations are jointly injective on L1.

A second obligation is the actual original Green range: if
`f(x)=g_p(x)-g_p(x+log(p))` almost everywhere with integrable g_p, the exact
Fourier translation character is one at every integer/log(p) sample.
All those samples vanish. Hence common integrable original-prime Green
admission over infinitely many primes should force f=0. A nonzero survivor
would require a non-L1 primitive/domain change, or a proved alteration of
the source equations. That conclusion is limited to these original
translation differences, not every possible singular Green construction.

## Corpus evidence and status

Read `DeningerTomographyInjective`: its existing proof uses exponential
Schwartz decay and the analytic identity theorem at one accumulating
harmonic. That proof cannot be applied to general L1. The replacement uses
all harmonics and continuity. Read the exact L1 periodization coefficient
law and L1 Fourier uniqueness statements and their domain requirements.
The terminal deep and hybrid reports are audited below. The complete
179-line module `DeningerL1CofinalPrimeTomography` passed scratch check4
and its initial leaf build. A final statement audit is checking the literal
original orientation `Delta_L = 1 - translation_L`; reversing the sign
preserves the existential range, but the public theorem must retain the
original source formula.


## Search and cross-field transfer audit

`route_l_c47_l1_tomography_deep.json` is terminal: 20 candidates, no source
arguments or proof ideas, one proposed ingredient group. Generation 876411;
inventory snapshot 56955/56955 files; semantic coverage not measured.
Text/source/semantic retrieval are partial. The proposed Bohr-orbit group
requires a totally bounded orbit and does not establish the L1 density
step. No such assumption was imported. All candidates and the group were
inspected.

Because the deep report lacked methods, the hybrid query
`Fourier translation periodization --any` was run separately. Its terminal
report `route_l_c47_translation_methods.json` has 20 candidates and 20
source arguments, all inspected; generation 876439, no unfinished retrieval
stages, semantic coverage not measured and background source refresh still
incomplete. The actual scaling/coefficient and translation-character
methods apply; exponential Schwartz lattice arguments and L2 unitarity
alone do not replace the required L1 proof.

Broad arXiv `renewal` search found
[Geometric Analysis of Doppler-Based Navigation with Low Earth Orbit Satellites](https://arxiv.org/abs/2609.11296),
submitted 10 September 2026. Sections 4–5 retain the source clock column:
under full rank, its Schur complement is the squared orthogonal residual,
and the inverse Gram gains a positive rank-one term. The strict sign
constraint depends on its stated orbital model. This does not provide
Route L's missing source equation or a cancellation law; a positive
finite-dimensional Gram matrix cannot be assumed for the original
boundary. No numerical example was used. The independent `sampling`
search page failed to load; no paper from it was adopted.

# Route L: original circle observations on all integrable sources

- **ID:** L-C47
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** original Green-domain classification / source correction test
- **Depends on:** [C46 complete damped Xi packet](../3-formalized/route-l-damped-complete-xi-packet.md); `HTGeometry.FourierUniquenessL1`; `HTGeometry.L1PeriodizationFourier`
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. C46 admits the full damped Xi field and original
Tate graph family for fixed a>1, while retaining the original physical
critical-line discriminator. The hard remaining step is a source-forced
comparison or domain change. This card classifies the admissible correction
class before proposing such a change.

## Closed proof and positive classification

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

The actual original Green range uses its unchanged sign: if
`f(x)=g_p(x)-g_p(x+log(p))` almost everywhere with integrable g_p, the exact
Fourier translation character is one at every integer/log(p) sample.
All those samples vanish. Hence common integrable original-prime Green
admission over infinitely many primes forces f=0 almost everywhere. A nonzero survivor
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
179-line module `DeningerL1CofinalPrimeTomography` passes scratch check5
with the literal original orientation `Delta_L = 1 - translation_L`.
Its eight public theorems are wired into the umbrella. The final
`lake build GaloisForLFunctions.RHTower.DeningerL1CofinalPrimeTomography`
audit of that exact orientation passed, building only this leaf (42 seconds;
other dependency results replayed). Formal lint passed and indexing
completed; all eight public declarations are present in `formal/LEAN_API.md`.
Logs: `/tmp/route_l_c47_l1_circle_check5.log`,
`/tmp/route_l_c47_l1_circle_build2.log`,
`/tmp/route_l_c47_l1_circle_lint2.log`,
`/tmp/route_l_c47_l1_circle_index.log`.


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


## Exact Lean results

- `deningerCofinalLattice_frequency_tendsto`: every real frequency is a limit of actual integer harmonics at the original periods.
- `deningerCofinalLattice_continuous_ext`: all such samples determine any continuous scalar response.
- `deningerL1CofinalCircle_coefficients_injective`: complete circle coefficients at cofinal periods determine an L1 source almost everywhere.
- `deningerL1PrimeCircle_coefficients_injective`: the same result over every infinite set of original primes.
- `deningerL1PrimeCircle_periodizations_injective`: equality almost everywhere on each original cell suffices.
- `deningerL1OriginalGreen_fourier_lattice_zero`: the literal integrable original translation primitive kills every lattice sample.
- `deningerL1CofinalOriginalGreen_eq_zero`: common original Green admission at unbounded periods forces the source to vanish almost everywhere.
- `deningerL1PrimeOriginalGreen_iff_zero`: exact common-domain classification over every infinite original-prime subset, with the zero-source converse proved too.

`lake env lean /tmp/route_l_c47_l1_circle.lean` check5 passed without
diagnostics. No numerical experiment or axiom-print command was used.
The next [literal local Green boundary attack](../1-in-progress/route-l-l1-local-green-boundary-jump.md)
constructs the non-L1 primitive and retains its full two-ended jump before
any comparison with the fixed physical reader. RH remains unproved.

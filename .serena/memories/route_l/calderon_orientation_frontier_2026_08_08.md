# Route L authoritative frontier — source Calderón orientation (2026-08-08)

## Carrier closed

Actual arithmetic coefficient remains the constructed pro-Stein residue fibre with strict Poisson model
`C0=C⊕Hcap`, `C1=H_-⊕P_Q`, `C2=D_Ar,Q`, and strict cohomology
`H0=C`, `H1=M_zeta`, `H2=C(-1)`.
Do not rebuild coefficient or revive raw coarse endpoint-only full-Cauchy fibre.

## Newly retired false frontier

`DAC_RELEVANT_GREEN_PAUGAM_CHAIN_TRANSGRESSION` is ill-typed.

Paugam scalar pairing is
`psi(F,G)=Tr(F*JG-G*JF | H^1_{d,+})`
after discrete spectral suspension and an oriented upper/lower half.
It is not a scalar degreewise cocycle on raw `C_PZ`.

For
`A_rho=Fhat(rho) Ghat(1-rho)-Ghat(rho) Fhat(1-rho)`,
`A_(1-rho)=-A_rho`.
Hence the reflection-complete Meyer virtual character cancels the wedge identically. Meyer's common-cutoff
`Z`/Fourier corrections compute the full character but cannot construct Paugam's half-sector.
Swapping halves negates the scalar pairing, so an orientation-free scalar lift is zero.

Failed card:
`docs/drafts/pipeline/5-failed/deninger-relevant-green-paugam-chain-transgression.md`.

Generic involution-odd sum cancellation is already formalized as
`HTGeometry.AbstractSpectralFamily.tsum_eq_zero_of_inv_odd`; do not write another abstraction.

## New dependency-closed source layers

Three paper theorems now precede the old global relation gap:

1. `DAC_PRIME_LOG_HEIGHT_KOTHE_CALDERON_SOURCE`: on `Γ=Z^(P)`, weights `H(m)^k` make a nuclear Fréchet convolution source. Prime-log generator and Green inverse are continuous with one integer height-step estimate; Poisson/DtN, Hodge sign, Hardy projectors, reflection, powers, and centered Mellin jets are continuous.
2. `DAC_BALANCED_WORD_HEIGHT_BAR_STRICT_CONTRACTION`: product-of-letter height plus every exponential word-length seminorm gives a nuclear entire two-sided bar source. All arithmetic-character sectors are split strictly exact. Green contracts nonzero total character; extra degeneracy contracts balanced total character zero.
3. `DAC_LINEARIZED_MILNOR_FIRST_SULLIVAN_STRICT_PRIMITIVE`: existing Lean Sullivan tower's canonical set-indexed primitive is non-linear. Linearize first attachment by using completed `Λ²E` itself. Normalized exterior `2+(r-2)` coproduct gives a canonical continuous primitive for the full completed base Milnor ideal, preserving character/height and working on balanced zero without Green division.

Paper cards:
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-prime-log-height-kothe-calderon-source.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-balanced-word-height-bar-strict-contraction.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-linearized-milnor-first-sullivan-strict-primitive.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-euler-depleted-meyer-periodization-extension.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-cofinal-prime-periodization-tomography-instability.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-half-density-floquet-euler-boundary-dichotomy.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-cofinal-floquet-secondary-poisson-graph.md`
- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/deninger-mobius-right-inverse-poisson-range-classification.md`

Fourth theorem supersedes the earlier frontier ordering:

4. `DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION`: for each prime `p`,
   `Delta_p=1-tau_(log p)` is a strict isomorphism from Meyer's two-ended rapid target onto the
   zero-periodization kernel, `Z^(p)=Delta_p Z`, and
   `0 -> M_zeta -> M_zeta^(p) -> C^infty(R/log(p)Z) -> 0` is split strict. Therefore one prime
   already gives exact carrier admission and boundary conservativity. Every form factoring through
   the full compact prime-circle trace is zero on all of the admitted `M_zeta` sector.

5. `DAC_DENINGER_COFINAL_PRIME_PERIODIZATION_TOMOGRAPHY`: every infinite prime family separates
   Meyer cochains by entire Mellin/Fourier uniqueness; every finite family has a nonzero finite
   Euler-difference kernel. Ordinary product range is nonclosed. The existing half-density
   seminorm localizes by the Euler Green inverse and controls the explicit translated escape.
6. `DAC_DENINGER_HALF_DENSITY_FLOQUET_EXACT_SEQUENCE`: weighted periodization
   `sum_j p^(j/2)h(t+j log p)` is the unique prime Floquet trace of weight one. Its `p^-2`
   all-prime square sum is continuous and positive definite on Meyer cochains; ordinary Euler
   depletion is bounded below and extends invertibly on every completed cross-prime fiber. Exact leakage is
   `Per_(p,1/2) Delta_p=(1-p^-1/2) Per_(p,1/2)`. Matching twisted depletion kills the whole
   admitted sector. The uncorrected Hilbert Poisson quotient retains exactly critical zeta zeros
   coinciding with prime Floquet Mellin nodes, and loses nonresonant modes plus higher jets.
7. `DAC_DENINGER_BOUNDED_FLOQUET_CORRECTION_RESONANCE_NO_GO`: every boundary-annihilating
   correction bounded in the raw Floquet Hilbert norm factors through that same resonance-only
   quotient. Missing correction must be nuclear-topology singular or add another source channel.
8. `DAC_DENINGER_COFINAL_FLOQUET_SECONDARY_POISSON_GRAPH`: the already-formalized physical/Fourier
   two-collar regulator has a canonical full-circle lift. Its all-prime radical is exactly the
   reflected Calderón graph `h_+(t)=exp(-t)h_-(-t)`. This graph strictly contains the literal
   boundary range `{(Zf,Z(Fourier f))}`.
9. Classical/project-specific `DAC_DENINGER_MOBIUS_POINTWISE_RIGHT_INVERSE`: for every Meyer cochain, canonical Möbius
   inversion converges pointwise on the positive radial line and Poisson summation returns the
   original cochain. The literal Poisson range is exactly the cochains whose Möbius preimage
   extends as an `H_cap` function. On the reflected graph this is the exact boundary incidence.

Lean corpus was audited read-only; no Lean file/build belongs to this work.

## Current first open source object

`DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`, now sharply:

1. construct `DAC_DENINGER_CORRECTED_TATE_FLOQUET_POISSON_DESCENT` before Hilbert closure:
   a singular Gamma/co-Poisson Green--Stokes realization of the canonical Möbius preimage's
   endpoint/Fourier regularity defect, with kernel exactly the literal Poisson boundary range and
   transported to `Delta_p Z(H_cap)`;
2. preserve the proved weight-one cochain energy through the correction and prove real-Fourier
   compatibility; cochain auxiliary-prime compatibility is already strict;
3. obtain Hodge-symmetric nuclear almost-involution `S` and prove Green-energy
   radical/chirality-kernel exactness;
4. then polar sign, oriented Paugam trace comparison, and resolvent-faithful Hodge-Schwartz core.

Cofinal Sullivan/pro-Stein completion is an optional construction of the correction, not the first
hard frontier. Scalar compact trace is zero on the admitted sector. Half-density Floquet trace
fixes weight and ambient positivity but leaks boundaries; its uncorrected Hilbert quotient is
exactly classified and too small. Relative harmonic/Gamma/co-Poisson correction before completion
is load-bearing.

## Optional methods and endpoints

Full-packet Cauchy/Bessel conservativity is only an optional proof of Green-energy radical.
Calderón-Witt incidence remains transverse degree-two data and endpoint witness, not middle Hodge metric.
`XI_BV_GREEN_STOKES_STRICT_DESCENT` and fixed two-prime boundary remain RH-equivalent endpoint tests, not source premises.

## Primary-source reason

Meyer arXiv:math/0412277: cutoff almost-sections and Toeplitz traces yield full prime-plus-real character; no upper spectral projector.
Paugam arXiv:0803.0199: supertrace uses conjugation-exchanged decomposition; number-field scalar formula is upper-half trace; positivity is RH-conditional.

Do not rediscover coefficient, full character, Paugam pairing, odd-sum cancellation, polar-sign
algebra, endpoint detectors, carrier admission, half-density source norm, or ambient positive
Floquet energy, bounded Hilbert repairs, the full reflected Calderón graph, or set-theoretic range
classification. Hard frontier is Gamma/co-Poisson realization of the singular Möbius regularity
defect before Hilbert closure.

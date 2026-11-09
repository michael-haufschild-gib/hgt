# Euler–FE transport theory

- **ID:** euler-fe-transport-theory
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** obstacles-summary §2.10, with §2.5 and §3.
- **Scope:** Additional programme alongside ExactEventTheory; both remain required.
- **Target:** Resolve the Euler–FE replication mechanism, its defect-classification branch,
  the five milestones below, and all tools and questions in the foundational README.
- **Home:** `formal/GaloisForLFunctions/EulerFETransportTheory/README.md`.

## Mathematical obligations

1. M1 proved: Beurling rigidity for integrable or square-integrable defects in the explicit Hamburger strip class (B122).
2. M2 proved in that class: both nonclassical defect costs `∫⁻‖g‖ₑ` and `∫⁻‖g‖ₑ²` are infinite, hence infinite layer cost (B84).
3. M3: same-depth replication of one exceptional quartet of ζ.
4. M4: an actual finite-slope law `LinAt C`.
5. M5: AAL; retain the distinction between arbitrarily small depth loss and exact replication.

Required constructions: FE-to-transport operator; quantitative recurrence of the rigid
oscillation; resonant identities coupling `γ` to `(2k+1)γ`; defect calculus for conditionally
convergent prime discrepancies; the same-depth replication law. All must act on the actual
infinite Euler product, pass the stated fake-class calibrations, and recover finite-rank
local squares.

## Classification pillar

`../3-formalized/exact-event-decaying-fourier-defect-rigidity.md` gives the proof and exact
analytic scope. Boundary decay and atomic recurrence force unit-gap vanishing; the origin
sinc-squared pairing forces integer support. Pole reality and exclusion of empty prime
systems complete the rational-prime classification. The terminal Lean theorems are
`EulerFETransportTheory.beurlingSystem_rigidity_of_integrable_defect` and
`EulerFETransportTheory.nonclassical_beurling_defect_cost_eq_top`; both pass direct checks
with the three standard axioms only.

`../3-formalized/euler-fe-finite-energy-rigidity.md` proves the square-integrable
variant without pointwise boundary regularity. Its terminal theorems are
`beurlingSystem_rigidity_of_finiteEnergy_defect` and
`nonclassical_beurling_defect_energy_eq_top`, with the same direct checks and axiom audit.
`../3-formalized/euler-fe-finite-energy-defect-annihilation.md` further proves that
the finite-energy defect is zero almost everywhere in the theta formulation and
pointwise in the original strip identity, with the same axiom audit.

M1–M2 remove nonclassical finite-defect perturbations from these classes. M3–M5 require an
exact identity of ζ producing height transport. The classification does not decide whether
ζ itself has an exceptional finite layer. Both research programmes remain incomplete.

## Gaussian source constraint

Finite quartet surgery already preserves positive source and seed, exact outward
Euler resolvents, smooth reflection and every real zero. The literal Gaussian
seed equation and all-prime-deletion complete monotonicity distinguish the
deformations. Those exclusions do not imply replication for undeformed ζ.
`../3-formalized/euler-fe-gaussian-causal-defect.md` proves reconstruction of an
admissible complex causal tail from the Gaussian differential defect on one open
interval. The domain includes every measurable exponential-order kernel. Its
exact invisible directions are scalar identity terms; an infinite causal repair
must cancel the entire non-scalar kernel. Both modules pass direct Lean checks
and standard-axiom audits. This extends the source constraint beyond finite
rational surgery without settling M3–M5.

`../3-formalized/euler-fe-atomic-causal-repair.md` extends reconstruction to full
causal measures with finite Gaussian-weighted mass, including infinite atomic
sources and infinite undamped mass. Atomic and continuous parts are separately
visible. The domain is closed under convolution and contains every causal source
with some convergent Laplace transform. A normalized positive atomic operator
repairs continuous Gaussian surgery only when the operator is the identity and
the signed continuous correction vanishes.
`../3-formalized/euler-fe-signed-atomic-gaussian-repair.md` extends the exclusion
to normalized real signed atomic operators by cancelling the common measure
after Gaussian weighting. The positive survivor is complete local source
reconstruction, convolution admission and valid cancellation at infinite
undamped mass. All four modules pass direct checks and standard-axiom audits.
These statements do not establish height transport.

## Height reflection and boundedness domains

`../3-formalized/euler-fe-gaussian-finite-part.md` identifies the unscaled
finite part of the full Gaussian prime discrepancy throughout `0<σ≤1`.
Subtracting the Gamma zero field gives `A(σ)−ξ′/ξ(σ)`; the sum of reflected
finite parts is `A(σ)+A(1−σ)`. If all complementary zeros lie strictly left
of the observation line, finitely many modes suffice without a uniform gap.
The actual `¬AAL` top layer supplies this subtraction throughout the interval
between top and tail. Direct checks and standard-axiom audits pass. The
reflected infinite field cannot be truncated on the strength of this result.

`../3-formalized/euler-fe-two-scale-zero-multiplicity.md` extends the calculus
to every actual complex zero. The full nonresonant Gamma field is absolutely
admitted; the resonant logarithm has exact divisor multiplicity. Comparing
scales `y` and `cy` cancels the finite part and gives `−mρ log(c)/2` for every
`c>0`, without rightmostness or simplicity. Direct checks and standard-axiom
audits pass. Divisor-defined counterterms remain in this observable.

`../3-formalized/euler-fe-prime-only-top-multiplicity.md` removes these
counterterms from the observable at any actual rightmost zero:
`Gρ(e^(−u))/u→−mρ/2`. The full nonresonant field is uniformly bounded,
without a finite-layer or uniform-gap hypothesis. The actual finite top
under `¬AAL` supplies an off-line point satisfying this law. Direct checking
and both standard-axiom audits pass. No new height or contradiction follows.

`../3-formalized/euler-fe-height-uniform-archimedean-damping.md` proves
`|A_y,c(s)−e^(−y)A(s)|≤ye^(−y)/Re s`, uniformly at every height in the
right half-plane. The renormalized error tends uniformly to zero on
`Re s≥σ₀>0`; `e^(−y)` is the unique scalar leaving bounded vertical error.
The full trivial-zero series and four terminal standard-axiom audits pass.

`../3-formalized/euler-fe-joint-height-damping-finite-part.md` controls the
complete Gamma-subtracted prime current by `Cy(1+y)(1+log Im s)` away from
the divisor. The logarithmically weighted error tends uniformly to zero;
absolute error vanishes along every regular path with `y(1+log Im s)→0`.
The actual `¬AAL` layer supplies a whole high strip satisfying the law whose
left boundary lies below an exceptional abscissa. Six terminal standard-axiom
audits pass.

`../3-formalized/euler-fe-finite-layer-joint-damping.md` removes the infinite
Gamma counterterm when a finite exceptional set has complementary abscissa
`θ<σ`. The remaining error is `O((y+y^((σ−θ)/2))(1+log Im s))`, uniformly
on the regular high strip. The actual `¬AAL` layer supplies that strip with
left boundary below an exceptional abscissa. Four terminal standard-axiom audits pass.
Only the finite exceptional modes remain in the subtraction.

`../3-formalized/euler-fe-counterterm-free-high-gaussian-passage.md` removes
those modes at damping `1/Im s`. The continuum vanishes too, so the literal
infinite von Mangoldt sum approaches `−ζ′/ζ(s)`, uniformly
on an interior high strip supplied by `¬AAL`. The tail, exceptional modes
and continuum have explicit vanishing bounds; scalar and polar corrections
are `O((1+log Im s)/Im s)`. Five terminal standard-axiom audits pass.
No new zero height follows.

`../3-formalized/euler-fe-fixed-damping-dyadic-passage.md` strengthens this to
one damping scale `1/T` throughout `T≤Im s≤2T`. The entire prime current
approaches `−ζ′/ζ` uniformly on the interior strip. Five terminal axiom
audits are standard. This matches the arithmetic mean's observation scale.

`../3-formalized/euler-fe-infinite-conditioned-gaussian-recurrence.md` proves
the exact mean-square law for the entire rough Gaussian current under any
fixed smooth head probe, with damping `1/T` on both `[0,T]` and `[T,2T]`.
The literal von Mangoldt tail is admitted for every `σ>1/2`; its variance
vanishes as the prime cutoff grows. The error retains explicit weighted
head dependence. Seven terminal standard-axiom audits pass. Matching this
mean to the continued current and obtaining same-depth replication remain open.

`../3-formalized/euler-fe-height-reflection-normalization.md` proves the actual
conductor-normalized reflected-height law, with uniform error `C_D t^(−1/4)`
on bounded parts of the open strip. It also proves that, for any escaping
sequence, connected upper-half-plane domains meeting `Re s>1` and supporting
locally bounded ζ-translates lie strictly right of `½`. No phase alignment is
needed. Whole-quadrant boundedness is impossible; the normalized law is the
positive survivor. Both terminal laws have standard-axiom audits. New-height
replication, `LinAt C`, and AAL remain open.

## Local identification

The actual theta kernel on any open interval `(a,b)`, `0<a<b`, determines every
measurable polynomially bounded uncompleted defect almost everywhere. This does
not require finite mass or energy: Gamma damping gives strip analyticity in
logarithmic scale, followed by Fourier injectivity. After integrable arithmetic
classification, Jacobi's theta law therefore annihilates the original defect;
the strip identity makes this pointwise. Proof and formalization:
`../3-formalized/euler-fe-local-defect-identification.md`.

## Defect energy

`../3-formalized/euler-fe-boundary-energy.md` proves the exact Hamburger boundary law
`∫ |J_g(iy)|² dy = π⁻¹∫ |g(t)|² dt` for `g ∈ L¹ ∩ L²`, including square integrability.
The complementary Mellin weights on the two rays sum to `4`.
`../3-formalized/euler-fe-finite-energy-boundary.md` constructs the unique continuous
extension to all `L²`, preserves its exact norm, and proves agreement on the original
integral domain. `../3-formalized/euler-fe-hardy-source-classification.md` identifies
the actual transform for every `L²` defect with the Laplace transform of an explicit
scaled-unitary Mellin source. These transforms exhaust the right-half-plane Hardy
class; their limiting vertical energy is `π⁻¹‖g‖²`.
`../3-formalized/euler-fe-hardy-laplace-transport.md` proves strong convergence of
the actual vertical traces to the canonical boundary, weak `L²` test pairings, and
the exact Hardy boundary range. The normalized boundary map is unitary onto that range.
`../3-formalized/euler-fe-finite-energy-tent-transport.md` proves the actual
arithmetic tent identity, the two-width recurrence law and almost-everywhere
unit-gap vanishing. Reflection and the origin Fejér identity force integer support;
zero radial defect residues then recover the full integer spectrum and prime labels.

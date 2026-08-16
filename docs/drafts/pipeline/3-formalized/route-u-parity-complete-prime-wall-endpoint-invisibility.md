# Route U: parity-complete prime-wall endpoint invisibility

Status: `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Question

Existing Route-U work proved that the von Mangoldt atom entering at a prime-power wall is invisible
to every admitted odd state.  Is this an odd-parity accident, or does exact endpoint saturation
annihilate the even sector too?

## Exact theorem

At the `n`th hard-edge wall, let

`b = log(n) / (4 pi)`.

The entering source atom has physical frequency `log(n) = 4 pi b`.  If the real even states
`g(x)=H(x²)` and `k(x)=K(x²)` lie in `L²` and their unitary Fourier transforms vanish almost
everywhere outside `[-b,b]`, then

`integral g(x) k(x) cos(x log(n)) dx = 0`.

After exact squared-variable transport, this says that the full bilinear even prime-jump response
vanishes:

`routeUHardEdgePrimeJumpEvenResponse n H K = 0`.

Therefore the even hard-edge Gram form is unchanged across the wall on the whole admitted
endpoint band.  In particular, incoming nonnegativity implies wall nonnegativity for every
admitted even state.  Together with the earlier odd theorem, every admitted parity Gram entry is
unchanged at every prime-power wall.

The mechanism is exact.  Fourier supports of the two factors have extreme difference frequency
`2b`; after the repository's Fourier normalization this is the entering frequency `4 pi b`.
At equality, translated supports intersect only at one Lebesgue-null endpoint, so there is no
boundary mass capable of coupling to the atom.

## Conjecture loop

### U-NK1 — infinitely many simple roots force an infinite null kernel

Conjecture: divide an actual first-contact limit by each of its infinitely many simple roots;
the resulting independent quotient family should be null and contradict finite negative index.

Result: false.  The corpus's parity-jet law makes nonterminal repeated-root descendants null, but
a quotient at a simple root is a terminal channel whose even energy need not vanish.  Distinct
terminal channels can be orthogonal without belonging to the null radical.  This route cannot
supply strictness.

### U-EP1 — endpoint invisibility is odd-specific

Conjecture: the factor `x` in odd states is essential to killing the incoming prime atom.

Result: false.  The underlying endpoint orthogonality theorem is bilinear and parity-blind.
Applying it to `H(x²)` and `K(x²)` proves the missing even response is zero.

### U-EP2 — an even first contact can be created by a prime jump

Conjecture: although odd packets cannot lose sign at a wall, an admitted even state may couple to
the entering atom and create the first negative direction.

Result: false.  The exact even jump law is incoming form minus the new response, and the new
response vanishes on the entire admitted endpoint band.  Every even Gram entry is unchanged.

### U-EP3 — first contact is arithmetic jump orientation

Conjecture: Route U should orient the next prime-power atom to exclude first contact.

Result: false for genuinely admitted endpoint states.  Both parity sectors are spectrally blind
to that atom at the instant it enters.

Positive survivor: Route U's remaining strictness theorem is wholly an interior domain-entry
problem.  The density is constant inside a cutoff chamber, while the Paley--Wiener source space
expands continuously with aperture.  Any genuine first contact must arrive through that expanding
domain boundary, not through a change of arithmetic density at a prime wall.

## Higher principle

At Nyquist saturation, an absolutely continuous Paley--Wiener state has no endpoint atom.  A
discrete source event located exactly at the extreme difference frequency is therefore invisible
to every bilinear Gram entry, independently of parity.  Arithmetic jumps and analytic domain
growth are transverse mechanisms: the former changes density but is endpoint-null; only the
latter can create Route U's first-contact state.

This sharpens the open core.  Searching for a sign of the entering von Mangoldt atom is dead work.
Needed theorem must prove strict positivity of the fixed chamber form on each newly admitted
boundary layer, or prove that the source-selected Laguerre--Pólya limit cannot enter through that
layer.

## Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeEvenPrimeWallEndpointInvisibility.lean`

Principal declarations:

- `routeUHardEdgePrimeJumpEvenResponse`
- `routeUHardEdgeEvenForm_log_nat_half_eq_incoming_sub_primeJumpResponse`
- `routeUHardEdgePrimeJumpEvenResponse_eq_zero_of_two_bandSupports`
- `routeUHardEdgePrimeJumpEvenResponse_eq_zero_of_bandSupport`
- `routeUHardEdgeEvenForm_log_nat_half_nonneg_of_incoming_and_bandSupport`
- `routeUHardEdgePrimeJumpEvenResponse_eq_zero_of_two_suzukiHlogAdmissions`
- `routeUHardEdgeEvenForm_log_nat_half_eq_incoming_of_two_suzukiHlogAdmissions`

The module is imported by `formal/GaloisForLFunctions/RHTower.lean` immediately after the odd
endpoint-invisibility module.

Verification performed:

- scratch: `lake env lean /tmp/RouteUEvenPrimeWall.lean`
- direct module check:
  `lake env lean GaloisForLFunctions/RHTower/XiShiftedHardEdgeEvenPrimeWallEndpointInvisibility.lean`
- exact leaf audit:
  `lake build GaloisForLFunctions.RHTower.XiShiftedHardEdgeEvenPrimeWallEndpointInvisibility`
- scratch `#print axioms` audit: capstones use only `propext`, `Classical.choice`, and `Quot.sound`
- forbidden-token scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`

No umbrella or full-project build was run.

## External novelty audit

Targeted search checked current primary literature on Suzuki's Weil-distribution Hilbert space and
screw-function formulation, including arXiv:2301.00421, arXiv:2209.04658, and arXiv:2606.09096.
Those works supply the surrounding Weil/Hilbert framework.  No searched source stated the exact
finite-prime hard-edge wall law, parity-complete endpoint invisibility, or its consequence that
all first contact must be interior domain entry.  This is not an external priority claim; novelty
remains unverified pending specialist review.

## Remaining open core

Prime-wall birth is now excluded in both parity sectors, but chamber-interior source-space growth
remains uncontrolled.  Need unconditional strictness of fixed-density form on every newly admitted
Paley--Wiener boundary layer, or a source-specific exclusion of the actual Laguerre--Pólya
first-contact state.  RH is not proved.

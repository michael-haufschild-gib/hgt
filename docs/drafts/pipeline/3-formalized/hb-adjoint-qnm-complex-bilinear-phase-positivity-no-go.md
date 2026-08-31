# HB adjoint-QNM complex-bilinear phase/positivity no-go

- **ID:** HB-ADJOINT-QNM-BILINEAR-PHASE-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB surviving radiative `++` causal-cut/sign premise
- **Statement:** A complex-bilinear adjoint-QNM diagonal cannot both descend through common source phase and carry a nonzero sign-definite HB causal orbit; phase descent forces its diagonal to vanish, and universal HB landing is therefore equivalent to RH rather than a producer of RH.

## Goal
Kill the surviving proposal

`complex-bilinear adjoint Teukolsky period positivity -> nonnegative full-cokernel orbit -> extinction -> source-FE unit-clock covariance -> RH`.

Exact chain contribution: `hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut` is already the negative of a strictly positive susceptibility times clock-defect energy, and universal extinction is RH.  If a physical adjoint-QNM diagonal were sign-definite and common-phase invariant, the proposed sign would follow.  The conjecture says that premise is structurally impossible unless the orbit has already vanished.

Non-circularity passport: proof may use only complex bilinearity, the phase rotation `x -> I • x`, and already-proved pointwise/global zero-locus theorems for the canonical full-cokernel orbit.  It may not assume RH, physical incidence, completeness of QNMs, or a positive Hermitian replacement.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `d4HBAdjointQNMDiagonalPositivityRouteKilled`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Paper proof

`[PROVED HERE]`
For a complex-bilinear form `B`, its diagonal obeys

`B(I • x, I • x) = -B(x,x)`.

Hence equality of both phase representatives with one physical scalar `K` gives `K=-K`, so `K=0`.  More generally, if one fixed phase calibration makes every diagonal value real and nonnegative, applying it to `x` and `I • x` forces every diagonal value to vanish; if `B` is symmetric, polarization then forces `B=0`.

For phase landing, if both ray representatives equal `K`, then `K=-K`; torsion-freeness of `ℂ` gives `K=0`.  Conversely, the zero bilinear form lands exactly when `K=0`.  Therefore existence of a projectively descended complex-bilinear diagonal landing at `K` is equivalent to `K=0`.

For fixed-phase positivity, suppose for nonzero `alpha` that every `alpha B(x,x)` is a nonnegative real.  Apply this to `x` and `I x`.  The two real energies are nonnegative and sum to zero, hence both vanish.  Since `alpha` is nonzero, `B(x,x)=0` for every `x`.  If `B` is symmetric, apply the diagonal identity to `x+y`; symmetry gives `2B(x,y)=0`, hence `B=0`.

Instantiate `K` by the complete target-independent HB full-cokernel orbit.  Its zero locus equals the source-FE clock-defect zero locus, which is exactly the critical wall.  Thus fibrewise phase-descended diagonal landing is equivalent to the critical wall, and universal landing is equivalent to RH.  Combine this with the existing finite-KMS/Hermitian polarity no-go: complex-bilinear diagonals fail phase descent, while Hermitian diagonals erase the required phase and produce the already-known wrong polarity.  Surviving producer must therefore be genuinely off-diagonal/polarized, with independently transformed source and left-QNM legs.

Falsifiers checked:

- Retaining a charged, phase-covariant value instead of a scalar on source rays evades the no-go; it does not supply physical scalar positivity.
- Restricting amplitudes to a real cone evades the `I` rotation; QNM eigenspaces and the source gauge are complex.
- Sesquilinear/Hermitian pairing evades the sign flip, but is covered by existing Hermitian/KMS wrong-polarity results.
- Literature's Teukolsky QNM form is complex-linear in both arguments, symmetric, not positive definite, and QNM-only expansions omit continuum/branch-cut contributions; no literature identity supplies the forbidden positivity.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** `B(Ix,Ix)=-B(x,x)` forces every projectively phase-descended diagonal value to vanish; fixed-phase positive symmetric complex-bilinear forms are identically zero.  HB landing is pointwise criticality and globally RH.
- **Strongest positive survivor:** Weight-two phase covariance of the complex-bilinear diagonal; a nonzero survivor must remain a charged polarized section rather than descend to a scalar optical energy.
- **New insight:** Completed positive flux and adjoint-QNM projection cannot be identified on the diagonal without inserting an antilinear left leg; doing so moves the route into the already-killed Hermitian/KMS class.  Physical work must target an off-diagonal source/left-QNM reciprocity law.
- **Status:** Internal corpus novelty search and primary-literature audit complete through 2026-08-31; dependency-closed paper proof and Lean formalization complete in `ThetaCuspHawkingHBAdjointQNMComplexBilinearPositivityNoGo.lean`; umbrella wired; axioms only `propext`, `Classical.choice`, `Quot.sound`.

## Conjecture loop
- **C0 — literal positive completed period equals the nonlinear Peierls cut:** failed.  Corpus defines the positive period separately; physical cut identification still requires response-incidence and Einstein--Green reciprocity premises.  Literature gives a complex-bilinear, indefinite QNM form rather than a positive Hilbert product.
- **C1 — complex-bilinear diagonal positivity can orient the HB orbit:** frozen target; expected false by the `I`-phase obstruction.
- **C2 — projective phase landing is exactly criticality/RH:** frozen strongest classification and intended route-kill capstone.

## Log
- 2026-08-31 — created directly in 1-in-progress after corpus and primary-literature novelty/falsifier audit.
- 2026-08-31 — C1 proved; strongest C2 pointwise/global classification proved; moved to 2-fully-proven.
- 2026-08-31 — formalized, targeted module build passed, axiom audit passed, moved to 3-formalized.

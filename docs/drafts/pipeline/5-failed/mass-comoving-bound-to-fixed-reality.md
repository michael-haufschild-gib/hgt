# Co-moving mass boundedness does not recover fixed spectral reality

- **ID:** mass-comoving-bound-to-fixed-reality
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../../../reports/mass-shifted-spectral-trace-route.md · §9.3 Exact open core
- **Statement:** A uniform trace bound obtained by choosing mass aperture `a(u) ≥ |u|` forces the underlying spectrum to be real.

## Goal

Test whether the unconditional co-moving prime cone can be fed directly into existing fixed-family
vertical rigidity, without a separate aperture-recovery theorem.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: conjecture falsified instead
- [x] no-go closure: explicit countermodel and strongest positive survivor are Lean-proved

## Failed conjecture C13

If a family satisfies a uniform bound along `sigma+iu` after assigning a mass `a(u)≥|u|`, then all
original displacements vanish.

This conjecture is false.  Co-moving boundedness is a universal consequence of admissibility plus
the height floor `base≥1/2`; it contains no reality selector.

## Exact killing theorem/mechanism

Let `offRealPairFamily` consist of the conjugate points `1+i/4` and `1-i/4`, with base `1`.  It is
an admissible abstract spectral family and its first point has nonzero imaginary part.  Nevertheless,
for the minimal aperture `a(u)=|u|+1/2` and every `sigma>1/2`, Lean proves

`‖(offRealPairFamily.mass a(u)).traceC (sigma+iu)‖`

`≤ offRealPairFamily.traceReal (sigma-1/2)`.

Thus a nonreal spectrum satisfies the same co-moving cone bound.  Existing vertical rigidity
requires one fixed family; changing mass with `u` destroys its hypothesis.

## No-go closure

- **Exact killing theorem/mechanism:** `offRealPairFamily_nonreal` together with
  `offRealPairFamily_comoving_bound` is an unconditional finite countermodel.
- **Strongest positive survivor:** first aperture rescaling recovers conserved displacement charge.
  If `p=R+iJ`, its mass image is `M+iK`, `a≥1/2`, and `base≥1/2`, then

  `a |aK-RJ| ≤ R |RJ|`.

  Hence `aK` approaches `RJ` at explicit `O(1/a)` scale.  Unscaled cone values are blind, but a
  first mass jet or charge-normalized observation retains the lost off-real information.
- **New insight:** fixed-mass recovery must be transverse in aperture, not merely a bound along one
  co-moving graph.  Repeated fixed-aperture failures are the shadow of discarding the conserved
  first aperture scale.
- **Status:** paper proof dependency-closed and formalized in
  `HTGeometry.AbstractSpectralComovingBlindness`; direct Lean check and targeted build pass.

## Paper proof of positive survivor `[PROVED HERE]`

The mass laws give `MK=RJ`, `M>a`, and `M≤R+a`.  Therefore `0≤M-a≤R`.  Taking absolute values in
the charge law gives `M|K|=R|J|=|RJ|`.  Also

`|aK-RJ|=|aK-MK|=(M-a)|K|`.

Since `a≤M` and `M-a≤R`,

`a |aK-RJ| = a(M-a)|K| ≤ MR|K| = R|RJ|`.

No limit theorem is needed; the estimate is pointwise in every admissible `a`. ∎

## Lean certificate

- `HTGeometry.AbstractSpectralFamily.mass_rescaled_im_error`
- `HTGeometry.offRealPairFamily_nonreal`
- `HTGeometry.offRealPairFamily_comoving_bound`

Verification:

- `lake env lean GaloisForLFunctions/HTGeometry/AbstractSpectralComovingBlindness.lean` — PASS.
- `lake build GaloisForLFunctions.HTGeometry.AbstractSpectralComovingBlindness` — PASS
  (`2748/2748`).
- `#print axioms` on all three declarations — only `propext`, `Classical.choice`, `Quot.sound`.
- Module wired into `GaloisForLFunctions.HTGeometry` umbrella.

## Log

- 2026-08-05 — C13 proposed after formalizing the literal co-moving Xi prime cone.
- 2026-08-05 — falsified by explicit conjugate two-point family; quantitative rescaled-charge
  survivor proved on paper and compiled in scratch.
- 2026-08-05 — no-go and survivor formalized; targeted build and axiom audit pass.

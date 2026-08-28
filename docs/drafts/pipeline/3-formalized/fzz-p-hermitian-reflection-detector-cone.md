# FZZ-P Hermitian reflection detector cone

- **ID:** FZZ-P-HC3
- **Stage:** 3-formalized
- **Type:** THEOREM / sharp coefficient classification
- **Source:** FZZ-P-HC1/HC2 + centered Mellin-character reflection law
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityHermitianReflectionDetectorCone`
- **Statement:** A fixed Hermitian quadratic reporter separates every positive nonunit radial-phase
  carrier from reciprocal-radius reflection exactly when its coefficients lie in the punctured
  Lorentz cone `d != 0` and `b^2+c^2 <= d^2`.

## Main classification

For `r>0` and `x^2+y^2=1`, set

`u(r,x,y)=(1,r(x+i y))`.

For the Hermitian block `[[a,b+ic],[b-ic,d]]`, define universal radial-reflection separation by

`H(u(r,x,y)) != H(u(r^-1,x,y))`

for every `r != 1` and every unit phase.  Then

`universal separation <-> d != 0 and b^2+c^2 <= d^2`.

The coefficient `a` is invisible to radial reflection.  The nonzero lightlike boundary
`b^2+c^2=d^2` remains strictly separating; the admissible set is therefore the full punctured
closed Lorentz cone, not merely its interior.

## Exact defect and paper proof

Direct expansion gives

`H(u(r))-H(u(r^-1))`

`= (r-r^-1) [d(r+r^-1)+2(bx-cy)]`.

For sufficiency, put `t=bx-cy`.  Cauchy--Schwarz gives

`t^2 <= (b^2+c^2)(x^2+y^2) <= d^2`.

If the bracket vanished, squaring would give

`d^2(r+r^-1)^2 = 4t^2 <= 4d^2`.

Because `d != 0`, this contradicts `(r+r^-1)^2>4` for positive `r != 1`.  Since the other factor
is also nonzero, every off-unit carrier is separated.

Necessity is constructive.  If `d=0` and `(b,c)=(0,0)`, every phase is blind.  Otherwise choose the
unit phase perpendicular to `(b,-c)`, so `bx-cy=0`; taking `r=2` kills the bracket.  If
`d^2<b^2+c^2`, put `B=sqrt(b^2+c^2)>|d|`.  Choose phase parallel or antiparallel to `(b,-c)` so
`bx-cy=-sign(d) B`, then choose the positive root `r>1` of
`r+r^-1=2B/|d|`.  The bracket vanishes at an explicit nonunit carrier.  These cases exhaust the
complement of the cone.

## Mellin reflection consequence

Every nonzero complex number has the radial-phase decomposition used above.  For the centered
dyadic FZZ Mellin character, critical-line reflection preserves phase and inverts radius.  Its
radius is one exactly when `rho.re=1/2`.  Consequently every reporter in the cone satisfies the
pointwise detector law

`H(M(rho)) = H(M(reflect rho)) <-> rho.re=1/2`.

Universal reporter matching on all open-strip parity-Mellin divisor modes is therefore equivalent
to the Riemann hypothesis.  This is an endpoint equivalence, not an RH proof: remaining burden is
to derive matching from interacting FZZ/GFZZ dynamics without assuming RH or zero placement.

## New route knowledge

- diagonal norm reporters are interior examples of a complete coefficient family;
- phase-robustness has an exact Lorentz-cone geometry;
- lightlike reporters remain valid detectors despite saturating Cauchy--Schwarz;
- every reporter outside the cone has a constructive off-critical false positive;
- chiral-only reporters detect source orientation but cannot universally detect radial reflection;
- any proposed FZZ dynamical matching law must produce a cone-valued reporter or impose extra phase
  control.

## Corpus audit

Mandatory searches on 2026-08-28:

- `scripts/formal_tools.py research "FZZ Mellin character Hermitian quadratic reporter reflection equality critical line classification"`
- `scripts/formal_tools.py research "centered modular character Hermitian observable reflection radial phase cancellation cone"`
- `scripts/formal_tools.py research "Mellin carrier quadratic form conjugate inverse reflection iff real part one half"`
- `scripts/formal_tools.py research "FZZ diagonal Hermitian norm reflection critical line detector"`

Corpus contained individual norm-one and normalized-crossing detectors, but no coefficient-complete
Hermitian reflection cone or sharp outside-cone witness.

## Literature boundary

Primary neighboring literature checked includes:

- Hikida--Schomerus, FZZ duality and correlation matching, arXiv:0805.3931:
  https://arxiv.org/abs/0805.3931
- Pakman, FZZ scattering, arXiv:hep-th/0606067:
  https://arxiv.org/abs/hep-th/0606067
- Ashok--Troost, cigar continuum spectral asymmetry, arXiv:1101.1059:
  https://arxiv.org/abs/1101.1059
- Kapitula--Kevrekidis--Yan, Krein matrix and signature theory, arXiv:1212.2951:
  https://arxiv.org/abs/1212.2951
- Kollar--Miller, graphical Krein signatures and Evans--Krein functions, arXiv:1209.3185:
  https://arxiv.org/abs/1209.3185

Exact-object searches for reciprocal-radius Hermitian reporters and Lorentz-cone classification
located no matching theorem.  Status is “no collision located,” not an absolute priority claim.

## Lean closure

Main declarations:

- `fzzCigarParityHermitianRadialPhase_reflection_sub`
- `fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_cone`
- `not_fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_d_eq_zero`
- `not_fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_sq_lt`
- `fzzCigarParityHermitianUniversalRadialReflectionSeparating_iff`
- `fzzCigarParityMellinCharacterCarrier_reflection_eq_reciprocalRadialPhase`
- `fzzCigarParityMellinCharacterHermitianReading_eq_reflection_iff`
- `fzzCigarParityMellinHermitianReflectionMatched_iff_riemannHypothesis`

Verification on 2026-08-28:

- direct `lake env lean` passed;
- targeted module build passed;
- axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`;
- scoped banned-token and `git diff --check` audits passed;
- module wired into `GaloisForLFunctions.RHTower` umbrella;
- frontier map untouched.

## Gates

- [x] 0 -> 1 in-progress: corpus-led sharp conjecture frozen
- [x] 1 -> 2 fully-proven: dependency-closed classification and witnesses
- [x] 2 -> 3 formalized: unconditional Lean theorem package and audit
- [ ] 3 -> 4 publication-ready: independent specialist priority/physics audit

## Log

- 2026-08-28 — Conjectured from HC2 and exact Mellin reflection geometry.
- 2026-08-28 — Sharp iff, explicit outside-cone witnesses, pointwise detector, and RH endpoint
  equivalence proved and formalized.

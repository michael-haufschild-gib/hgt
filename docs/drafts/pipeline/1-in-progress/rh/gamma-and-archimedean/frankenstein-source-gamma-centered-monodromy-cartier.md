# Source/Gamma centered-monodromy Cartier producer

- **ID:** frankenstein-source-gamma-centered-monodromy-cartier
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** cross-corpus synthesis of theta prime translation, Hurwitz monodromy, rational Cartier dilation, and source/Gamma shared-ghost descent
- **Statement:** A coefficient-faithful descent of the FE/Schwarz orientation quotient of the genuine theta/Gamma source would make the actual centered Xi grade an integral monodromy weight; the open critical strip then forces grade zero and constructs the rational Cartier and shared-ghost reporters.

## Goal

For every retained Xi divisor support `rho`, construct the source/Gamma descent rather than assume
it.  Let

```text
t_rho = 2 Re(rho) - 1,
E_rho(L) = exp(-t_rho L).
```

Target is literal `2*pi*I` descent `E_rho(L+2*pi*I)=E_rho(L)`.  Hurwitz monodromy makes this
equivalent to `t_rho in Z`; Xi's open strip makes it equivalent to `t_rho=0`.  Existing rational
Cartier valuation and `(2,3)` source/Gamma reporter theorems then construct both requested
producers and close RH.

Non-circularity requirement: descent must be derived from the pre-spectral theta/Gamma source and
must retain prime label, first nonzero Xi jet, divisor multiplicity, and both FE/Schwarz
orientations.  Postulating periodicity, equality of reflected samples, or vanishing of the known
Euler/Hurwitz seam is forbidden because each is already RH-strength.

## Gates

- [x] 0 → 1 in-progress: well-posed source-pure target and exact cross-corpus consumer chain
- [ ] 1 → 2 fully-proven: construct coefficient-faithful orientation-quotient descent
- [ ] 2 → 3 formalized: Lean producer and unconditional RH capstone
- [ ] 3 → 4 publication-ready: standalone proof and Lean certificate

## Conjecture / hostile-test loop

### Conjecture 1 — raw theta spin descent forces grade integrality

Complexify one literal theta-cusp atom:

```text
a_n(z) = exp(z/2) 2*pi (2*pi (n exp z)^4 - 3 (n exp z)^2)
         exp(-pi (n exp z)^2).
```

Then `a_n(z+2*pi*I)=-a_n(z)` and `a_n(z+4*pi*I)=a_n(z)`, with integer label `n` retained.

**FAIL.**  Mellin/Fourier kernel has compensating spectral monodromy.  At
`rho=1/2+I*w`, the complete integrand acquires `exp(-2*pi*I*rho)`, not the unit character.
Moreover the Gaussian series converges only in Stokes sectors; a `2*pi*I` contour turn crosses
growing sectors and has nonzero Stokes flux.  Raw half-density spin therefore does not trivialize
the spectral local system.

### Conjecture 2 — local L1/BV source regularity kills that Stokes flux

**FAIL.**  Corpus proves exact strict-frontier source wall is non-`L1` on every right neighborhood
of an occupied frontier.  Its all-frontier local-integrability assertion is equivalent to RH.
Ordinary theta-source smoothness is on a different real chart and supplies no domination across
the complex Gaussian Stokes sectors.  This is a mathematical pole/Stokes obstruction, not a
missing declaration.

### Conjecture 3 — two reflected orientations cancel height and leave integral grade

For `rho' = 1-conj(rho)`, the ratio of Hurwitz characters is

```text
monoScalar(rho) / monoScalar(rho') = monoScalar(2 Re(rho)-1).
```

Thus a single-valued identification of the two orientations on one coefficient-faithful source
line gives `t_rho in Z`, hence `t_rho=0`.

**OPEN CORE.**  Reality of source only makes two presentations conjugate; conjugation-invariant
norm or determinant scalarization erases the phase.  Functional-equation reflection exchanges
the presentations.  Neither identifies them on one fixed source line.  Exact calibrated
prime-two Euler/Hurwitz seam measures this failure and has positive norm-square proportional to
the Xi Hurwitz orientation defect.

### Pivot 4 — Gamma/Witt descent of orientation quotient

Construct one source-derived rational-Witt/Gamma line over the common archimedean base whose two
pullbacks are the FE and Schwarz presentations.  Prove their tensor-square equality before
scalarization.  Field-equalizer descent then makes the orientation quotient base-defined; geometric
prime dilation converts its character to the rational Cartier degree lattice.  Required theorem
must be fibre-selected and non-equivariant: global/equivariant descent is blocked by corpus no-gos.

## Strongest positive survivor

The following dependency-closed laws are to be formalized as one bridge module:

1. literal complex theta atom has exact anti-period `2*pi*I` and period `4*pi*I`;
2. actual centered Xi log character has multiplier `monoScalar(t_rho)` under `2*pi*I`;
3. its descent is equivalent to `t_rho in Z`;
4. on Xi support this is equivalent to `t_rho=0`;
5. the same descent is equivalent to coefficient-faithful rational Cartier landing and to
   existence of the genuine `(2,3)` source-natural Gamma reporter.

This corrects the stale claim that corpus has no integral lattice for exact grade.  It does: the
rational Cartier valuation theorem already proves it.  Missing producer is now a precise
orientation-quotient descent, not integrality infrastructure.

## Novelty / circularity audit

- Existing corpus has centered complex modular character and Hurwitz orientation laws, but search
  found no theorem connecting `2*pi*I` descent of actual centered grade simultaneously to rational
  Cartier landing and source/Gamma reporter existence.
- Existing external symplectic/functional-equation constructions exchange `rho` and `1-rho`; they
  do not supply fixed-source FE/Schwarz identification.  Global real polarization is RH-strength.
- Escaping-quartet corpus countermodels preserve fixed nonzero modular weight while local jets,
  bounded Ward windows, and trace-class energy lose it.  Hence local regularity alone cannot prove
  descent.

## Log

- 2026-08-16 — stale “no integral lattice” claim falsified by
  `ccmRationalAdelicPrimeXiRationalCartierLanding_centeredRate_eq_int`.
- 2026-08-16 — raw theta spin conjecture failed on explicit spectral monodromy and Gaussian Stokes
  flux; local-L1 repair failed against exact strict-frontier pole theorem.
- 2026-08-16 — isolated live producer as coefficient-faithful FE/Schwarz orientation-quotient
  Gamma/Witt descent and proved bridge lemmas in scratch Lean.
- 2026-08-16 — **Conjecture 4 failed by exact countermodel:** Gauss cover composition supplies
  `(mn)^(-t)=m^(-t)n^(-t)` for every real `t`.  At `t=1/2`, the `(2,3)` composition is coherent
  while the fitted prime-two and prime-three ghosts are provably unequal.  Ordinary Gamma
  multiplication naturality therefore cannot create a prime-independent reporter.
- 2026-08-16 — **Pivot 5 proved:** replaced cover coherence by source-selected two-orientation
  unital scale-zero descent.  If forward and reflected coefficient-faithful characters extend
  continuously to one collapsed source scale and both retain its unit, the forward extension
  gives `t<=0` and the reflected extension gives `-t<=0`; hence `t=0`.  Formalized in
  `FrankensteinGammaCompositionScaleZeroDescent.lean`, including unconditional constructors from
  this descent to rational Cartier landing and the genuine source-natural Gamma reporter.

## Current open core after Pivot 5

Construct the two scale-zero extensions from the literal multiplicity jet of the shifted theta
source, before divisor scalarization.  This is strictly stronger than Gauss cover composition and
strictly more local than global/equivariant Gamma descent.  Required analytic statement must show
that the normalized first nonzero Xi jet retains the common unit at collapsed scale in both
FE/Schwarz orientations.  Raw shifted source values do not suffice: their zeroth Xi coefficient
vanishes, so the construction must divide at exact support multiplicity before taking scale zero.

# Hedenmalm--Euler reflection-admission fracture

- **ID:** RH-Hedenmalm-Euler-admission-fracture
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and formal certificate)
- **Source:** `XiHedenmalmThetaBorelHilbert` and `EulerPrimitiveCommonTestPolarizedReflectionRigidity`
- **Statement:** The Hedenmalm Borel reflection family is Hilbert-admissible throughout the centered open half-strip, whereas the Euler/Hardy polarized reflection family is admissible only at zero displacement; hence no finite-energy-faithful transport can intertwine the two families at any nonzero strip parameter.

## Goal

Produce first nontrivial cross-route consequence of relative admission-spectrum functoriality.
This must explain why a genuine Hedenmalm Hilbert source does not supply the sharp orientation
selection already present in the Euler/Hardy source, and why any bridge between them must be
singular or source-nonfaithful.

## Gates

- [x] 0 -> 1 in-progress: exact statement, source-pure definitions, complete proof, circularity audit
- [x] 1 -> 2 fully-proven: hostile proof/significance audit and `[PAPER-PROVED]`
- [x] 2 -> 3 formalized: exact Lean spectrum and no-transport theorems; direct check and axiom
  audit passed
- [ ] 3 -> 4 publication-ready: integrate as explicit cross-route corollary of universal law

## Status labels

- `[CORPUS]` Every Borel holonomy vector with `|Im alpha|<1/2` lies in the fixed source `L2` space.
- `[CORPUS]` Euler/Hardy reflection-odd tail energy is integrable iff displacement is zero.
- `[PAPER-PROVED]` The spectrum comparison and faithful-transport no-go below.
- `[NOVELTY UNVERIFIED]` Literature audit deferred by user instruction.

## Definitions

Fix a Borel basepoint `x`.  For real displacement `a`, put

```text
H_a(t) = holonomy(i a,x,t) - holonomy(-i a,x,t),
E_a(t) = exp(a t) - exp(-a t).
```

The Hedenmalm profile includes the square root of its positive Borel source density.  Its
admissibility predicate is

```text
AH_x(a) : H_a belongs to L2((0,infinity),dt).
```

The Euler profile is measured in the actual escaping Hardy-tail weight
`w(t)=1-exp(-t)`:

```text
AE(a) : integral_0^infinity w(t)|E_a(t)|^2 dt < infinity.
```

Define the admission spectra `SigmaH(x)={a|AH_x(a)}` and `SigmaE={a|AE(a)}`.

## Main theorem

### Theorem HEF

For every real `x`:

1. `(-1/2,1/2) <= SigmaH(x)`.
2. `SigmaE={0}`.
3. `SigmaH(x) != SigmaE`.
4. More strongly, fix `a != 0` with `|a|<1/2`.  Absorb the actual Hardy-tail weight into
   `W_a(t)=sqrt(1-exp(-t)) E_a(t)`.  There is no linear raw-profile transport `T` satisfying both

   ```text
   T(H_a)=W_a
   ```

   and even the one-way regularity condition

   ```text
   H_a in L2  implies  T(H_a) in L2.
   ```

Consequently no chain transport inducing an injective relative-admission quotient map can
intertwine the two reflection families on any nonzero centered strip.  Any such bridge must change
domain, lose relative information, or be singular before Hilbert completion.

## Complete proof

Let `|a|<1/2`.  The two parameters `i a` and `-i a` both have imaginary part of absolute value
`|a|`.  The existing Borel Hilbert theorem puts each holonomy profile in `L2`.  A normed linear
space is closed under subtraction, so `H_a` is in `L2`.  This proves part 1.

For the Euler family, the exact polarized reflection theorem gives

```text
AE(a) iff a=0.
```

Thus `SigmaE={0}`, proving part 2.  Taking `a=1/4`, part 1 puts `1/4` in `SigmaH(x)`, while part 2
excludes it from `SigmaE`; hence the spectra differ.

For part 4, assume `T` has the two asserted properties at a nonzero `a` with `|a|<1/2`.  Part 1
gives `H_a in L2`.  One-way domain preservation makes `T(H_a)` square integrable.  Intertwining
replaces it by `W_a`; its squared norm is exactly `w(t)|E_a(t)|^2`.  Part 2 forces `a=0`,
contradicting the hypothesis.  No injectivity, boundedness estimate, inverse, or global
faithfulness assumption is used.

Finally, relative admission-spectrum functoriality proves that an injective induced quotient map
preserves the parameter spectrum.  Since the two spectra differ on every nonzero point of the
centered half-strip, no source-faithful chain transport can intertwine them there.

## Hostile audit

### Objection: the no-go is tautological because faithfulness says membership is preserved

The logical step is short, but the nontrivial content is the unconditional computation of two
different spectra for two independently constructed arithmetic source carriers.  It is a genuine
route-to-route obstruction: a bridge cannot even map admitted vectors to admitted vectors while
intertwining the reflected character family.  The conclusion is stronger than failure of one
proposed kernel or lack of an inverse.

### Objection: the Hedenmalm and Euler coordinates differ

The theorem compares the common centered modular parameter, not pointwise time coordinates.
An intertwiner is required to map the actual source profiles.  Coordinate changes are allowed
inside `T`; the no-go still applies if they preserve finite-energy admission.

### Objection: perhaps an unbounded transport works

Yes.  The theorem does not exclude a singular densely defined transport whose domain shrinks the
Hedenmalm spectrum.  It proves such singularity is necessary.  This identifies, rather than solves,
the missing bridge.

### Objection: this proves RH

No.  The sharp Euler source has admission spectrum `{0}`, but unconditional source-derived landing
of every Xi fibre in that source remains unproved.  The theorem removes the possibility of obtaining
that landing by a regular Hilbert transport from the permissive Hedenmalm carrier.

## Positive survivor

The obstruction supplies a new invariant: **reflection admission spectrum**.  Regular
source-faithful transports conserve it.  Hedenmalm and Euler/Hardy sources occupy different
admission classes, so their difference is structural, not missing bounded-operator technology.

## Log

- 2026-08-02 — exact cross-route theorem and dependency-closed proof written; external novelty
  deliberately unverified.
- 2026-08-02 — hostile proof audit passed.  The claim is retained as a sharp cross-route no-go,
  not advertised as zero exclusion; promoted to Stage 2.
- 2026-08-02 — strengthened after formal feedback: reverse faithfulness and injectivity are
  unnecessary; one-way preservation of the admitted Hilbert domain already contradicts
  intertwining at every nonzero strip displacement.
- 2026-08-02 — exact certificates added in
  `RHTower/HedenmalmEulerReflectionAdmissionFracture.lean` and
  `RHTower/RiemannRelativeAdmissionSpectrumUniversalityLaw.lean`; direct checks passed and all
  load-bearing theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

# Virasoro--Shapiro double-copy differential boundary

- **ID:** `virasoro-shapiro-double-copy-differential-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / CANDIDATE NEW SCIENTIFIC KNOWLEDGE
- **Source:** closed-bosonic-string four-tachyon amplitude; Euler reflection; the existing
  Veneziano Gamma-orbit classification
- **Statement:** After removing the fixed crossed-channel factor, every one-channel
  Virasoro--Shapiro slice is a nonzero differentially algebraic reflection gauge times the square
  of the corresponding reduced Veneziano amplitude.  It is differentially algebraic exactly at
  integer crossed-channel separation and hypertranscendental everywhere else.

## Goal

Close the open/closed-string Gamma-amplitude surfaces by an exact differential-algebraic law.  The
result must reuse the existing meromorphic Gamma, Euler-reflection, Veneziano, power, and gauge
theorems, not postulate a new string carrier or infer complexity from the name "closed string".

This theorem is about differential complexity in a complexified kinematic channel.  It is not a
claim about time evolution, quantum gravity phenomenology, or the Riemann hypothesis.

## Gates

- [x] 0 -> 1 in-progress: source formula, exact reduction, paper proof, corpus consumer, and
  falsifiers identified
- [x] 1 -> 2 fully-proven: hostile formula review and external novelty review completed
- [x] 2 -> 3 formalized: exact Lean module, direct `lake env lean` check, axiom audit, generated
  index refresh, lint, and final exact module build
- [ ] 3 -> 4 publication-ready: standalone exposition and independent string-amplitude review

## Physics formula

For the closed bosonic string, the four-tachyon Virasoro--Shapiro amplitude has Gamma core

```text
Gamma(x) Gamma(y) Gamma(z)
---------------------------------,                       (1)
Gamma(1-x) Gamma(1-y) Gamma(1-z)
```

with `x+y+z=1`.  In standard Mandelstam variables,

```text
x=-1-alpha'*s/4,  y=-1-alpha'*t/4,  z=-1-alpha'*u/4,
s+t+u=-16/alpha'.
```

Fix `y=b` and write the variable argument as `x=w+a`; then `z=1-w-a-b`.  Removing the
nonzero-or-meromorphic fixed factor `Gamma(b)/Gamma(1-b)` leaves the reduced channel element

```text
VS(a,b) = Gamma(w+a) Gamma(1-w-a-b)
          --------------------------------.              (2)
          Gamma(1-w-a) Gamma(w+a+b)
```

The physical formula is classical.  A current primary reference which writes the closed-string
four-point Gamma amplitude and its deformations is Cheung--Hillman--Remmen,
*Uniqueness Criteria for the Virasoro-Shapiro Amplitude*, arXiv:2408.03362.  The original source is
M. Virasoro, *Alternative constructions of crossing-symmetric amplitudes with Regge behavior*,
Phys. Rev. 177 (1969), 2309--2311.  The open/closed-string relation is also the four-point instance
of the Kawai--Lewellen--Tye construction.

## Theorem and proof

`[PROVED HERE]` Define

```text
V(a,b) = Gamma(w+a)/Gamma(w+a+b),
G(a,b) = R(1-a-b)/R(1-a),
R(c)   = pi/sin(pi*(-w+c)).
```

Euler reflection gives

```text
Gamma(1-w-a-b) = R(1-a-b)/Gamma(w+a+b),
Gamma(1-w-a)   = R(1-a)/Gamma(w+a).
```

Substitution into `(2)` yields the exact closed/open double-copy normal form

```text
VS(a,b) = G(a,b) * V(a,b)^2.                            (3)
```

Both reflection gauges are nonzero meromorphic elements satisfying a second-order linear
differential equation, so `G(a,b)` is nonzero and differentially algebraic over `C(w)`.

The existing Veneziano theorem proves

```text
V(a,b) is DA  iff  b is an integer,
V(a,b) is HT  iff  b is not an integer.                 (4)
```

If `b` is an integer, closure of differential algebraicity under squares and multiplication
proves `VS(a,b)` is DA.  If `b` is not an integer, `(4)` makes `V(a,b)` HT; every positive power of
an HT element is HT, and multiplication by a nonzero DA gauge preserves HT.  Hence

```text
VS(a,b) is DA  iff  b is an integer,
VS(a,b) is HT  iff  b is not an integer.                (5)
```

Equivalently, the reduced open and closed channels are DA together and HT together.  This is the
direct theorem connector, not merely a comparison of two separately classified parameter sets.

This proof is unconditional once the already-formalized meromorphic Gamma theorems are imported.
The fixed factor omitted from `(2)` can be restored on any physical parameter domain where it is
finite and nonzero; as a constant DA gauge it cannot alter `(5)`.

## Stronger universal law

Equation `(3)` says that the closed-string double copy doubles the nonzero Gamma-orbit charge but
does not move the cancellation lattice.  The open and closed four-point amplitudes therefore have
the same exact DA/HT phase boundary in a fixed crossed channel, despite their different pole
multiplicities and crossing presentation.

This is stronger than merely observing that both amplitudes contain Gamma functions: arbitrary
products of HT Gamma factors can cancel.  The theorem computes the exact cancellation locus and
proves that the reflection/KLT square introduces no new cancellation sector.

## Corpus application

- Reuse `reducedVenezianoAmplitudeMero` and its exact integer/noninteger boundary.
- Reuse the genuine meromorphic reflection gauge and its nonzero DA certificate.
- Reuse `hypertranscendentalOver_pow_of_pos` rather than creating a square-specific wrapper.
- Reuse `hypertranscendentalOver_mul_differentialAlgebraic_iff` for the closed-string gauge.
- Add one HTGeometry module with the physical reduced amplitude, exact normal form, DA
  equivalence, HT equivalence, and direct open/closed DA and HT equivalences.
- Import that module from the HTGeometry umbrella and expose it through the generated API.

There is no RHTower theorem asking for a Virasoro--Shapiro amplitude, so no zeta wrapper is
justified.  The direct strengthening is within general HTGeometry: the existing open-string
classification becomes an open/closed-string invariant law.

## Novelty and hostile audit

The Gamma formula, Euler reflection, KLT/double-copy interpretation, and differential-algebra
closure lemmas are parent knowledge.  The candidate new statement is the exact differential-
algebraic classification `(5)` and the assertion that open/closed double copy preserves the
integer cancellation lattice while doubling Gamma-orbit charge.

Focused web searches on 2026-07-20 for the combinations
`Virasoro-Shapiro differentially algebraic`, `Virasoro-Shapiro hypertranscendental`,
`Virasoro-Shapiro differential transcendence`, and `closed string amplitude differential algebra
Gamma` found amplitude bootstrap, Regge, KLT, and transcendental-weight literature, but no
differential-algebraic or hypertranscendence classification.  This is negative search evidence,
not a priority proof.  A broader formula-level review and independent expert check remain required
before promotion to `new_scientific_knowledge` or publication language.

Falsifiers:

1. an omitted variable-dependent kinematic factor which is not a nonzero DA gauge;
2. a mass-shell convention which changes `x+y+z=1` for the claimed tachyon amplitude;
3. an existing differential-algebraic classification of this exact slice in the literature;
4. a failure of the meromorphic normal form at poles (as opposed to equality in the meromorphic
   function field);
5. a Lean proof which needs an added hypothesis beyond the displayed parameters.

### Hostile formula result

The formula survived the convention attack.  Firrotta, arXiv:2402.16183, writes the closed
bosonic four-state Gamma core with

```text
Gamma(-alpha's/4-1) Gamma(-alpha't/4-1) Gamma(-alpha'u/4-1+sum N_l)
----------------------------------------------------------------------------,
Gamma(alpha's/4+2) Gamma(alpha't/4+2) Gamma(alpha'u/4+2-sum N_l)
```

and the mass-shell relation `alpha'(s+t+u)/4=sum N_l-4`.  On the four-tachyon sector
`sum N_l=0`, the substitutions in this card give `x+y+z=1` and denominators
`Gamma(1-x)Gamma(1-y)Gamma(1-z)` exactly.  The same source gives the four-point KLT form as a sine
gauge times two open-string amplitudes.  Thus no variable-dependent non-DA kinematic factor was
omitted from the reduced one-channel core.

The crossed-channel constant `Gamma(b)/Gamma(1-b)` requires care: it can be restored only where it
is finite and nonzero.  At its poles or zeros the theorem is intentionally the classification of
the reduced meromorphic channel, not a pointwise classification of an ill-defined fixed physical
normalization.  Equality `(3)` is an equality of meromorphic functions, so channel poles do not
invalidate it.

The external search was repeated against current bootstrap and KLT literature, including
Cheung--Hillman--Remmen, arXiv:2408.03362, Firrotta, arXiv:2402.16183, and the 2026 dispersive
bootstrap of Xu, arXiv:2606.19283.  Those works treat uniqueness, Regge behavior, spectra,
factorization, KLT relations, or low-energy coefficient bounds; the focused searches found no differential-
algebraic classification of the exact reduced slice.  This remains negative priority evidence,
not a proof that no prior statement exists.

## Log

- 2026-07-20 -- internal corpus search found Veneziano, reflected-Gamma, thermal-CFT, QED, and
  Bogoliubov applications but no Virasoro--Shapiro or closed-string differential boundary; exact
  normal form `(3)` isolated and paper proof completed before Lean edits.
- 2026-07-20 -- the mass-shell convention, Gamma numerator/denominator shifts, crossed-channel
  normalization, meromorphic pole interpretation, and four-point KLT factor were checked directly
  against arXiv:2402.16183.  Focused current-literature searches found no exact differential-
  algebraic collision.  The Lean module and all five capstones passed direct checks and an axiom
  audit with only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-20 -- the declaration surface is exposed in the generated API, generated-file
  consistency and repository lint pass, and the exact final module build succeeds.  The card is
  promoted to stage 3 under `needs-audit`: the mathematical theorem is formalized, while priority
  and publication language still require independent expert review.

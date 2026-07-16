# Complete period-source reconstruction uncertainty

- **ID:** `period-gauge-attainment-complementarity`
- **Stage:** 3-formalized
- **Type:** GENERAL HT SOURCE PHASE CLASSIFICATION / BARE-SOURCE NO-GO
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [CLASSICAL-BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [SIGNIFICANT ARCHITECTURAL RESULT] [NOT RH]`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/PeriodGaugeComplementarity.lean`
  - `formal/GaloisForLFunctions/HTGeometry/DiscretePeriodGaugeClassification.lean`
- **Unified parent:**
  `../../1-in-progress/hypertranscendental-source-fracture-hypercube.md`

## Complete theorem `[PROVED; LEAN-FORMALIZED]`

Let `L <= C` be any integral translation source. Let `M_L` be its complete regularized
period-incidence multiplier, and let `Fix_mero(L)` be the global meromorphic fraction-field
elements fixed by every translation in `L`. Lean proves the exact equivalences

```text
L is discrete
  <-> M_L has a continuous left inverse
  <-> Fix_mero(L) contains a nonconstant element.                    (1)
```

It also proves the complementary form

```text
M_L has no continuous left inverse
  <-> every element of Fix_mero(L) is constant.                      (2)
```

Consequently every period source lies in exactly one obstruction phase:

```text
discrete:
  uniform incidence attainment + nonconstant gauge ambiguity;

nondiscrete:
  incidence nonattainment + maximal meromorphic gauge rigidity.      (3)
```

In particular,

```text
not (uniform bare-source effectivity and fixed-gauge rigidity modulo constants). (4)
```

Equation `(4)` is the exact period-source reconstruction uncertainty theorem. A bare translation
source can solve the existence/effectivity problem or eliminate every nonconstant gauge, but never
both. In the nondiscrete phase a separate scalar calibration is still required.

## Constructive proof of the missing converse

The new Lean module proves the previously open implication

```text
L discrete -> Fix_mero(L) contains a nonconstant element               (5)
```

by classifying the integral rank of `L` inside the real plane `C`.

1. **Rank zero.** `L=0`; any nonconstant entire exponential is fixed.
2. **Rank one.** If `L=Z omega`, then
   `exp(2 pi i z / omega)` is a nonconstant global meromorphic fixed gauge.
3. **Rank two.** A real-linearly independent basis is rescaled and oriented to periods
   `(1,tau)`, `Im(tau)>0`. A nonlattice translate of `theta'/theta` gives a nonconstant elliptic
   theta-defect gauge. Lean constructs the scaling automorphism of the global meromorphic field,
   proves its conjugacy with translation, and transports the normalized gauge back to `L`.

The reverse implication in `(1)` is the small-period rigidity theorem: a nondiscrete integral
source contains nonzero periods tending to zero, and invariance under them forces a global
meromorphic germ to be constant. The middle equivalence in `(1)` is the previously formalized
bounded-below criterion for the diagonal incidence multiplier.

## Meaning of the Gamma counterexample

The Gamma pair

```text
Gamma(z),  exp(2 pi i z) Gamma(z)
```

is not an isolated pathology. It is the rank-one instance of the discrete half of `(3)`.
Conversely, irrational rank-three period sources are instances of the nondiscrete half: their
fixed gauge has collapsed to constants, but their complete incidence map has nonclosed-range
nonattainment.

Thus adding periods does not monotonically improve reconstruction. It moves the obstruction from
degree `-1` (automorphisms/gauges) to degree `0` (attainment/completion).

```text
[NO-GO]
The same bare period source can be uniformly effective and rigid modulo scalar calibration.

[POSITIVE]
The two failures are exhaustive adjacent phases. A viable reconstruction theorem must add
transverse data: gauge-separating reporters in the discrete phase, and an independent completion
producer in the nondiscrete phase.                                            (6)
```

Source-derived observables cannot supply the transverse datum after the source has forgotten it;
the exact common-kernel criterion remains the conservativity gate for any reporter family.

## Novelty and anti-theatre verdict

The external parent theory already contains the decisive ingredients:

- the period group of a nonconstant meromorphic function is discrete;
- discrete subgroups of the complex plane have ranks `0`, `1`, or `2`;
- exponentials and elliptic functions provide nonconstant invariants in ranks `1` and `2`;
- a diagonal multiplication operator has a continuous inverse exactly when its symbol is bounded
  away from zero.

The exact equivalence `(1)` does not appear verbatim in the targeted search because `M_L` is this
project's incidence representation. But it is a direct synthesis of those parents. That is not a
credible novelty basis for a standalone paper.

- `[NOVELTY GATE -- FAIL AS NEW SCIENCE]` The theorem is a classical bridge in a new notation.
- `[SIGNIFICANCE GATE -- PASS ARCHITECTURALLY]` It rules out an entire reconstruction strategy and
  replaces two apparently unrelated obstructions by one exhaustive phase law.
- `[DUAL GATE -- FAIL]` Significant-but-derivable is not a new scientific result.
- `[ANTI-THEATRE -- PASS]` The card is classified as not-new despite the complete Lean theorem.

Useful external checks include the standard period-group proposition and lattice classification
in Joachim Wehler's *Modular Forms* notes, the MIT elliptic-function notes on rank-two period
modules, and standard closed-range multiplication-operator criteria. Absence of the project's
combined vocabulary from search results is not evidence of mathematical novelty.

## The genuinely new target: gauge-attainment transgression

The theorem suggests a higher object rather than another equivalence.

> **[CONJECTURE -- SOURCE DEFECT COMPLEX.]** A natural HT source `S` has a functorial two-degree
> bornological defect complex `D(S)` whose degree `-1` cohomology is the normalized joint-fixed
> gauge and whose degree `0` cohomology is the completed incidence nonattainment defect. For period
> sources, `(3)` says that exactly one of these adjacent cohomology objects is nontrivial.

The paper-worthy statement is not the existence of two labels. It is a transgression theorem in a
degenerating natural family:

> **[CONJECTURE -- GAUGE/ATTAINMENT WALL CROSSING.]** When discrete period sources converge in the
> Chabauty topology to a nondiscrete source, normalized nonconstant gauges escape every compact
> meromorphic family at exactly the rate at which the norm of the incidence inverse diverges.
> After projectivized jet or spherical-derivative renormalization, the escaping gauge class maps
> canonically to the degree-zero nonattainment class of the limiting source defect complex.

This is falsifiable and not supplied by the classical equivalence `(1)`. It asks for a canonical
comparison map and a quantitative conservation law, not parallel observations.

## Where to look next

1. Prove a quantitative model for `L_n=(1/n)Z -> R`: inverse-norm blow-up versus derivative or
   spherical-energy escape of normalized exponential gauges.
2. Prove the rank-two cusp analogue using the rescaled theta-defect gauges already in Lean.
3. Construct the two-term defect complex and the wall-crossing map before adding more obstruction
   channels.
4. Test whether positivity, monodromy, continuation, and spectral incompleteness become real,
   integral, or functorial twists of the same two-degree complex.
5. Only then apply the object to a natural Gamma/Barnes/elliptic-Gamma family; zeta remains a
   downstream pressure test.

## Lean certificate

Lean proves unconditionally:

- the complete rank `0/1/2` construction for every discrete `L <= C`;
- exact discreteness iff existence of a nonconstant global meromorphic fixed gauge;
- exact left-invertibility iff existence of such a gauge;
- exact non-left-invertibility iff all fixed gauges are constant;
- the exclusive two-phase dichotomy and bare-source uncertainty theorem;
- scaling covariance and orientation independence of the rank-two theta construction.

The exact target module build and direct source-file check pass. No full build was run. The area
umbrella's direct check remains blocked by the unrelated missing cached module
`NormalizedMomentQuantumVariance`; no build of that module was attempted.

## Gates

- [x] full converse for every discrete integral submodule
- [x] exact three-way equivalence
- [x] exhaustive and exclusive phase dichotomy
- [x] no-go paired with a nontrivial positive classification
- [x] unconditional Lean formalization
- [x] external parent mechanisms identified
- [x] anti-theatre reclassification to not-new
- [ ] quantitative gauge-escape/inverse-blow-up theorem
- [ ] functorial source defect complex
- [ ] canonical wall-crossing transgression
- [ ] natural HT family with a nontrivial transferred theorem

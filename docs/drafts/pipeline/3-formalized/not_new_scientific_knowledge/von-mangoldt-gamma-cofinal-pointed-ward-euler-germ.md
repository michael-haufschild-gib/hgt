# Von Mangoldt--Gamma cofinal pointed Ward reconstruction of the Euler germ

- **ID:** `von-mangoldt-gamma-cofinal-pointed-ward-euler-germ`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean), COFINAL SOURCE/EULER ANALYTIC RECONSTRUCTION
- **Scientific status:** `[PROVED] [LEAN-VERIFIED] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `von-mangoldt-gamma-pointed-ward-bianchi-gram.md`
- **Normalization no-go child:**
  `von-mangoldt-gamma-factorial-normalization-positivity-no-go.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaInfinitePointedWard.lean`

## Theorem

For `x>0`, logarithmic order `a`, and `n>=0`, define the pointed raw atom

```text
r_(x,a)(n)
 = Lambda(n+2)/(n+2) exp(-x log(n+2)) log(n+2)^a.        (1)
```

Lean proves the termwise analytic identity

```text
r_(x,a)(n)
 = term(vonMangoldtLogCoeff(a), x+1, n+2),               (2)
```

after the real atom is embedded in `C`.  The series is absolutely summable and its first two
omitted `LSeries` terms vanish.  Consequently

```text
sum_(n>=0) r_(x,a)(n)
 = LSeries(vonMangoldtLogCoeff(a),x+1)
 = vonMangoldtLogMoment(a,x+1).                          (3)
```

The first equality is complex-valued; the second line records its real form.  Thus the cofinal
pointed source is not an abstract completion: it reconstructs the existing analytic Euler germ
exactly.

For a finite exponent packet `a_i`, put

```text
G_x(i,j)=sum_(n>=0) r_(x,a_i+a_j)(n).                    (4)
```

Every finite-aperture raw Gram converges entrywise to `G_x`, and Lean proves

```text
G_x>=0,
G_x(i,j)=vonMangoldtLogMoment(a_i+a_j,x+1).              (5)
```

For arbitrary Gamma-depth labels `b_i` satisfying

```text
b_i+b_j<a_i+a_j,
```

the parent theorem identifies the finite adjacent-depth anomaly Bianchi matrix with the finite
raw Gram.  Therefore every such Bianchi entry converges to `(5)`.  The depth labels disappear in
the limit because the pointed Ward boundary reconstructs the same raw source before aperture is
sent to infinity.

## What this closes

The finite source-effectivity chain is now cofinal and analytic:

```text
finite Gamma anomaly
  -> pointed adjacent-depth Bianchi current
  -> finite raw von Mangoldt Gram
  -> cofinal positive Gram
  -> analytic logarithmically weighted Euler germ.       (6)
```

Every arrow in `(6)` is unconditional and Lean-verified.  In particular, there is no remaining
finite-to-infinite gap on the absolute-Euler side and no unproved interchange of limit and source
sum.

## RH boundary and anti-theatre gate

Equation `(6)` does not prove RH.  It reconstructs values and finite-packet positivity at
`Re(s)>1`; RH requires positivity or coercivity after inverse translation to the critical
normalization.  The inverse half-translation is expansive on the resolved prime channels, and the
positive resolved diagonal energy is divergent.  Hence `(5)` cannot simply be transported as a
diagonal Hilbert norm.

The normalization no-go child sharpens this further: the literal factorial trace normalization
already sends a positive cofinal odd source Gram to a matrix with eventually negative determinant
in the far-right half-plane.  Thus the direct source-Gram-to-normalized-Hankel arrow fails before
inverse-critical transport.  A coupled correction must act before that normalization, or the
critical realization must be changed.

A concurrently formalized observability theorem sharpens the obstruction: on an
infinite-dimensional residual gauge, a compact injective reporter has normalized approximate-null
vectors and cannot satisfy a uniform lower bound.  Therefore a smoothing completion of `(6)` is
structurally incapable of producing the critical all-scale coercivity needed for RH.  The next
producer must be a genuinely transverse noncompact coupled channel in which the Gamma, polar, and
critical-Mellin cross terms are retained before taking the norm.

The remaining chain is

```text
cofinal pointed Gamma--Euler reconstruction                         PROVED
analytic finite-packet Gram positivity                              PROVED
direct factorial normalization preserves positivity                 DISPROVED
  -> [OPEN] noncompact coupled inverse-critical reporter
  -> [OPEN] positive compression retaining polar/Mellin cross terms
  -> normalized prime--Gamma/Xi Hankel positivity
  -> RH.                                                            (7)
```

No target Xi positivity, zero-free hypothesis, or RH-equivalent premise occurs in the theorem.

## Novelty gate

Absolute convergence, partial-sum convergence, and closure of positive semidefinite matrices
under entrywise limits are classical.  The exact project-specific dictionary from the pointed
Gamma anomaly current to the analytic Euler germ is useful corpus infrastructure, but it is not
claimed as new scientific knowledge.  The candidate-new theorem remains the noncompact coupled
critical completion in `(7)`.

## Lean certificate

Principal declarations:

- `infiniteVonMangoldtGammaRawAtom_ofReal_eq_term`;
- `summable_infiniteVonMangoldtGammaRawAtom`;
- `infiniteVonMangoldtGammaRawMoment_ofReal_eq_weightedLSeries`;
- `infiniteVonMangoldtGammaRawMoment_eq_vonMangoldtLogMoment`;
- `tendsto_finiteVonMangoldtGammaRawMoment`;
- `infiniteVonMangoldtGammaRawGram_posSemidef`;
- `infiniteVonMangoldtGammaRawGram_eq_cofinalBianchiGram`;
- `vonMangoldtGammaCofinalBianchiGram_posSemidef`;
- `tendsto_finiteVonMangoldtGammaAnomalyBianchiMixedGram_apply`.

Verification:

- exact target build passed;
- direct touched-file Lean check passed silently;
- axiom audit: `propext`, `Classical.choice`, and `Quot.sound` only;
- no numerical computation;
- no RH or target-positivity hypothesis;
- repository lint found no defect in this module or its umbrella import, but the global gate remains
  red because concurrent unrelated new modules are not yet reachable from their area umbrellas.

## Gates

- [x] actual infinite von Mangoldt--Gamma atom defined
- [x] absolute summability at every positive displacement
- [x] termwise identification with the Euler `LSeries`
- [x] exact analytic moment reconstruction
- [x] finite-aperture convergence
- [x] cofinal Gram positivity
- [x] cofinal Bianchi-to-Euler convergence
- [x] unconditional Lean formalization and axiom audit
- [ ] noncompact transverse critical reporter
- [ ] coupled Gamma/polar/Mellin positive compression
- [ ] critical Xi Hankel positivity
- [ ] RH

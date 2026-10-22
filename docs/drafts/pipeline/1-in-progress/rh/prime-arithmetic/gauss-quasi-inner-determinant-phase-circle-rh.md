# Gauss quasi-inner determinant phase to circle RH

- **ID:** `gauss-quasi-inner-determinant-phase-circle-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Source theorem:** `../2-fully-proven/new_scientific_knowledge/gauss-component-quasi-inner-residue-hierarchy.md`
- **Circle consumer:** `irrational-circle-sem-holonomy-collapse.md`
- **Operator no-go:** `../../../5-failed/completed-source-window-index-amplifier.md`

## Claim

The Gauss-component quasi-inner operators carry more information than their positive weak-Schatten
residues.  Before replacing a component `E_(m,k,p)` by the positive operator
`|E_(m,k,p)|^(2m)`, retain the moving Fourier phase

```text
conj(d_(n+j))/conj(d_n)
  = exp(-2 pi i j delta_n) + o(1),
delta_n = log(n/L)/(mL) mod 1.                              (1)
```

Use `(1)` to construct a canonical phase-sensitive relative determinant or eta class in `R/Z`.
Assemble the `m` Gauss components for a finite set of places before taking the all-place limit.  The
resulting right-half window anomaly should agree with the single-prime SEM order charge

```text
[completed SEM contour index * log p] in R/Z.               (2)
```

If the completed finite-place system gives a source homotopy closing this relative phase, the
irrational-circle criterion forces the contour index to vanish and proves RH.

## Full chain

```text
finite-place archimedean-compensated quasi-inner factors
  -> Gauss decomposition into E_(m,k,p)
  -> exact moving Fourier phases delta_n in R/Z
       [PROVED PAPER INPUT]
  -> phase-sensitive relative determinant / eta class
       [OPEN CORE A: determinant-class construction]
  -> coherent product over all Gauss components and finite places
       [OPEN CORE B: multiplicative phase assembly]
  -> secondary all-place window anomaly before ratio collapse
       [OPEN CORE C: renormalized cofinal limit]
  -> identify window holonomy with [SEM index * log p]
       [OPEN CORE D: source-to-contour comparison]
  -> completed source homotopy closes the relative phase
       [OPEN CORE E: source annihilation]
  -> SEM index = 0 by irrational prime-log faithfulness
  -> no right-half Xi zero
  -> RH.
```

The final three implications are already formalized.  The detour is long because it tries to
construct the missing oriented circle character from an existing phase-bearing source operator,
not from the Xi divisor.

## Why the proved positive residue is insufficient

The proved endpoint theorem computes the critical weak-Schatten residue of

```text
|E_(m,k,p)|^(2m).
```

This operation removes the phase in `(1)`.  The residue is positive and independent of `k`, which is
excellent for coherent magnitude assembly but fatal for orientation: it cannot distinguish a
right-half window defect from its reflected partner and gives no zero exclusion by itself.

## Positive statement from the phase-loss no-go

The moving-translation lemma identifies exactly what must be retained:

> the determinant-line successor must be built from the unsquared Gauss components and must record
> their `R/Z` translation phase; the positive Dixmier residue may control its magnitude/ideal class
> but cannot replace its phase.

The unexpected `k`-independence of the positive residue is still useful.  It suggests a common
critical ideal and common counterterm for all components, against which the component phases can be
compared relatively.

## Firewalls

### The full Gauss product is not yet proved

The source theorem treats one paired component.  Even the exact residue for the product over all
`m` Gauss components is not yet established.  Phase assembly is strictly harder because ordering,
commutators, and determinant anomalies matter.

### Positive powers erase the target datum

Any construction factoring only through singular values, `|E|`, `|E|^(2m)`, Dixmier traces, or
positive weak-Schatten residues is circle-phase blind and cannot feed `(2)`.

### Ordinary all-place multiplication collapses

The completed local-factor ratio regularizes to `1`.  Taking that scalar limit before compression
or before forming the relative determinant yields the identity and zero anomaly.  The invariant
must measure noncommutation of finite-place compression/renormalization with the cofinal limit.

### Determinant phase must be canonical

A regularized determinant or eta invariant can change under spectral cuts and local counterterms.
The allowed counterterm class and its cancellation across Gauss components must be fixed by the
source.  Choosing a cut or subtraction after inspecting the Xi divisor is forbidden.

### Same circle is not the same character

The explicit Gauss phase is

```text
delta_n = log(n/L)/(mL) mod 1,
```

whereas the RH consumer needs `index * L mod 1`, with `L=log p`.  Their common target `R/Z` does not
identify them.  A valid comparison must prove a transgression or spectral-flow formula in which the
regularized moving phase accumulates exactly one `L`-unit per oriented window crossing.  Without
that theorem, the Gauss phase is merely adjacent circle-valued data.

### Right-half orientation is essential

A phase theorem valid at every Xi zero would wrongly annihilate genuine critical-line orders.  The
window polarization must distinguish the anti-fixed right-half defect while leaving fixed-line
zeros outside the annihilation statement.

## First falsifiable subclaims

1. `[CONJECTURE]` The unsquared component admits a canonical relative phase in `R/Z` with respect to
   the common critical weak-Schatten magnitude model.
2. `[CONJECTURE]` The phase difference between Gauss components is trace-class stable even though
   the individual components are only in the critical weak ideal.
3. `[CONJECTURE]` The product phase over `k=0,...,m-1` is independent of Gauss decomposition choices
   and compatible under adjoining a finite place.
4. `[CONJECTURE]` The cofinal finite-place phase has a secondary window limit although the ordinary
   all-place multiplier is `1`.
5. `[CONJECTURE]` The resulting boundary character is `(2)` with no complementary-character or
   gamma counterterm.
6. `[CONJECTURE]` The completed source supplies a right-half homotopy proving that character zero.

Failure of 1 or 2 kills the determinant-phase realization.  Failure of 3 or 4 leaves only local
phase data.  Failure of 5 leaves a source invariant with no RH consumer.  Failure of 6 leaves an
exact target reader but no proof.

## Status

- `[PROVED PAPER INPUT]` exact component magnitude and moving phase asymptotics;
- `[PROVED PAPER INPUT]` phase-blind positive residue is independent of the Gauss index;
- `[PROVED LEAN CONSUMER]` one prime-circle SEM closure is equivalent to RH;
- `[OPEN]` phase-sensitive determinant/eta construction;
- `[OPEN]` full Gauss and finite-place assembly;
- `[OPEN]` secondary all-place limit and source closure.

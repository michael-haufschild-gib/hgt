# Same-Hamiltonian local recurrence--collision capstone

- **ID:** `qubit-path-recurrence-collision-capstone`
- **Stage:** 3-formalized
- **Type:** theorem / local many-body quantum recurrence
- **Date:** 2026-08-23

## Statement

For every open qubit path with \(n\ge 3\) sites, use the full real coefficient space of traceless
one-site and nearest-neighbour two-site Pauli terms. On every nonempty connected open
simple-spectrum chart, for Lebesgue-almost every coefficient vector, one and the same static
Hamiltonian has all following properties. Writing \(D=2^n\):

1. balanced integer spectral relation lattice is trivial, equivalently projective rank is \(D-1\);
2. first simultaneous return of all \(D-1\) anchored gap phases to radius \(r\) has logarithmic
   exponent \(D-1\);
3. after using first positive gap as clock, first return of remaining \(D-2\) gap ratios has
   logarithmic exponent \(D-2\);
4. for every strictly positive spectral weight and every replica order, collision mass equals
   unavoidable permutation floor;
5. every long-time survival-fidelity moment converges to same floor.

## Proof

Exact Pauli path family has a maximally projective witness, so its non-maximal set is Lebesgue null.
It escapes every nonzero homogeneous balanced real spectral relation. Because family is linear,
linear-family affine-escape theorem upgrades this to escape of every affine level. Sorted-gap and
sorted-gap-ratio extremality theorems give \(D-1\) and \(D-2\) first-hit exponents almost everywhere
on every nonempty preconnected simple-spectrum chart. Intersect these conull events with
maximal-projectivity event. Maximal projectivity is equivalent to all-order replica rigidity;
collision decomposition and symmetric-time dephasing identity give items 4 and 5 for same
coefficient vector.

## Scope

- Exact family: full traceless onsite-plus-nearest-neighbour two-qubit Hamiltonian space.
- Static, deterministic Hamiltonian after coefficient selection.
- Genericity: Lebesgue almost everywhere on every nonempty connected open simple-spectrum chart.
- First exponent is stroboscopic; second is clock-normalized winding exponent.
- No claim about unrestricted continuous-time first-return distribution.

## Closure

- [x] dependency-closed paper proof
- [x] same-object claim, not intersection of separately packaged path witnesses
- [x] every-chart strengthening
- [x] direct source check
- [x] targeted module build
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] no placeholders or custom axioms in new modules
- [x] publication claim trace

## Declarations

- `qubitPath_everyChart_sameDraw_recurrenceCollisionLaw`
- `qubitPath_sameDraw_recurrenceCollisionLaw`
- `chainPauliFin_spectrumEscapesAffineRelations`
- `SpectrumEscapesRealRelations.linearFamily_toAffine`

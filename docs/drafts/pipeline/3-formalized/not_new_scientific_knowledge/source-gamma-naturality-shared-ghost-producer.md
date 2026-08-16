# Source/Gamma naturality shared-ghost producer

- **ID:** RH-SOURCE-GAMMA-NATURAL-SHARED-GHOST
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Calderón--Witt oriented source cohomology + Gamma inverse character + shared-ghost Ward descent
- **Statement:** Prime and archimedean orientation presentations define the same retained Calderón--Witt top class. If an arbitrary reporter has the prescribed inverse-Gamma values at prime presentations, a positive real archimedean readout, and is natural on the two selected prime--archimedean Green boundaries at labels `2` and `3`, its archimedean readout is forced to be a prime-independent ghost satisfying both local Ward equations.

## Goal

Replace bare shared-ghost existence by a genuine source theorem. Local countercharacters
`c_p = p^(-t)` exist for every grade and contain no information. Required producer must explain
why two local values are components of one source cohomology reporter. It must use actual source
boundaries, retain prime labels, and avoid global/equivariant descent.

## Gates

- [x] 0 → 1 in-progress: exact source carrier and two selected Green boundaries identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile audit
- [x] 2 → 3 formalized: targeted Lean module, leaf build, lint, and axiom audit
- [ ] 3 → 4 publication-ready: not claimed

## Conjecture / fail / pivot log

1. **Affine Kummer--Gamma commutator. FAIL.** Genuine first jet of `p^t` is
   `p^t log p`; deleting `p^t` creates false curvature. Full jet representation commutes for all
   `t`.
2. **Big-Witt base-ring naturality. FAIL.** Existing naturality changes coefficient rings. Prime
   label enters as an external ghost index, so it does not identify components at `2` and `3`.
3. **Adelic product formula supplies common ghost. FAIL.** Product formula cancels finite
   `log p` with an archimedean term depending on the same `p`. Total modulus is one for every `t`
   and therefore cannot produce the local inverse Ward equation.
4. **CCM prime atoms become equal in cyclic homology. FAIL.** Retained tensors are not Hochschild
   cycles, and genuine cyclic coinvariants retain rather than identify their prime labels.
5. **Calderón--Witt prime--archimedean orientation naturality. SURVIVES.** Every normalized prime
   orientation and the single archimedean orientation have trace one. Their difference is a
   literal boundary with a canonical Green primitive. This supplies the missing common source
   carrier without erasing either endpoint.

## Paper construction

Let `C` be the all-prime Calderón--Witt top cochain space, `d : C1 → C` its oriented boundary,
and `Tr : C → ℂ` its orientation trace. Existing exactness gives `im d = ker Tr`. For each prime
`p`, let `e_p ∈ C` be the normalized prime orientation and let `e_∞ ∈ C` be the independent
archimedean orientation. Existing normalization gives

```text
Tr(e_p) = 1 = Tr(e_∞).
```

Hence `e_p - e_∞ ∈ ker Tr = im d`. More precisely, the canonical top Green lift gives an
explicit primitive `w_p` with

```text
d(w_p) = e_p - e_∞.                         (1)
```

Let `F : C → ℂ` be an arbitrary source/Gamma reporter whose selected prime coefficients are

```text
F(e_p) = p^(-t),  p ∈ {2,3},
```

and whose archimedean readout is real and positive. Define, rather than assume, the candidate
shared ghost by

```text
c := Re F(e_∞) > 0.
```

Its reality gives `F(e_∞)=c`. Source naturality `F(d w_p)=0` and `(1)` now force

```text
0 = F(e_p-e_∞) = p^(-t)-c.                     (2)
```

Thus `c=2^(-t)=3^(-t)`. This is the producer direction: no proposed common scalar occurs in the
source-natural reporter datum.

For the converse and exact classification, define the canonical coefficient-faithful reporter

```text
G_(t,c)(z,u) = Σ_p p^(-t) tr_p(z_p) + c u,      (2)
```

where every input has finite prime support and `c > 0` is one archimedean component. Equations
`(1)` and `(2)` give, without quotient scalarization,

```text
G_(t,c)(d w_p) = p^(-t) - c.                     (3)
```

The canonical reporter proves the converse: a shared ghost makes the selected source squares
natural. Existing local Ward classification says a positive `c`
satisfies

```text
c D_p(t) = c^(-1) D_p(-t),  D_p(t) = -p^t,
```

iff `c = p^(-t)`. Thus the same `c` satisfies both Ward equations. Conversely a shared Ward ghost
has those two forced values, so its reporter annihilates both selected source boundaries.

Therefore

```text
selected source/Gamma naturality
  ⇔ prime-independent shared ghost at (2,3)
  ⇔ t = 0.                                      (4)
```

For `t = 2 Re rho - 1`, `(4)` is `Re rho = 1/2`; quantified over Xi divisor supports it is
equivalent to RH. This is a producer classification, not proof that selected naturality holds.

## Why this is not excluded repair theatre

- **Not prime-local:** one archimedean coefficient `c` occurs in both source boundary equations.
- **Not contractible-ghost erasure:** `e_p` and `e_∞` each have trace one and represent same
  nonzero top class; only their presentation difference is exact.
- **Not common determinant correction:** reporter is defined before determinant comparison on
  finite-prime plus archimedean source coordinates. Reflection inverse is derived from local Ward
  uniqueness, not imposed as same-orientation multiplication.
- **Not global/equivariant descent:** only canonical `2–∞` and `3–∞` Green boundaries are
  required. Global boundary blindness is unnecessary.

## Hostile audit

- Dropping common archimedean coordinate recovers vacuous family `p ↦ p^(-t)`.
- Allowing separate archimedean coordinates at `2` and `3` also makes naturality automatic and is
  rejected as prime-local fitting.
- Replacing `e_∞` by zero makes boundary contractible and destroys retained orientation class.
- Requiring only difference boundary `e_2-e_3` proves equality but hides source of shared value;
  two prime--archimedean boundaries construct value itself.
- Full boundary blindness would force factorization through canonical orientation trace by
  existing `deningerCalderonWittGlobalOrientationConsumer_factorization_unique_iff`; selected
  theorem extracts minimal RH-strength fragment.

## Novelty audit

- **Internal:** orientation Green boundaries and universal trace factorization were already
  formalized; inverse-oriented Ward uniqueness was already formalized. New knowledge is exact
  cross-corpus producer: two prime--archimedean boundary naturality squares construct one shared
  ghost directly.
- **External:** Connes--Consani--Marcolli formulate RH as positivity of an adelic cyclic-homology
  trace pairing, while Paugam's unconditional spectral pairing implements functional-equation
  exchange. Neither checked source supplies this selected coefficient-faithful prime--archimedean
  inverse-Gamma descent. No external novelty claim is made.

## Lean target

- Module: `GaloisForLFunctions.RHTower.SourceGammaNaturalitySharedGhostProducer`
- Boundary construction: `deningerCalderonWittGlobalOrientedBoundary_primeArchWitness`
- Exact reporter readout: `deningerCalderonWittInverseGammaGhostReporter_primeArchBoundary`
- Non-circular reporter datum: `PrimeGammaTwoThreeSourceNaturalReporter`
- Producer extracting its archimedean readout: `primeGammaTwoThreeSharedGhost_of_naturalReporter`
- Canonical converse: `primeGammaTwoThreeNaturalReporter_nonempty_of_sourceNaturalInverseGhost`
- Equivalence: `primeGammaTwoThreeSourceNaturalInverseGhost_iff_sharedGhost`
- RH endpoint: `everyFrankensteinSourceGammaNaturalSharedGhostDescends_iff_riemannHypothesis`

## Log

- 2026-08-16 — five-conjecture loop completed; prime--archimedean cohomology pivot survived hostile audit.
- 2026-08-16 — dependency-closed paper proof completed.
- 2026-08-16 — non-circular formulation formalized: shared scalar extracted as real
  archimedean readout of arbitrary coefficient-faithful natural reporter.
- 2026-08-16 — exact leaf build and formal lint passed; main declarations use only
  `propext`, `Classical.choice`, and `Quot.sound`; module wired into `RHTower.lean` without an
  umbrella build.

# Differential-algebraic-relative source conservativity

- **ID:** `da-relative-source-conservativity`
- **Stage:** 3-formalized
- **Type:** EXACT QUOTIENT-CONSERVATIVITY GATE / DA CONTROL
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [PARENT ALGEBRA]`
  `[ANTI-THEATRE CORRECTION] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/DARelativeSourceConservativity.lean`
- **Parents:**
  - `joint-source-realization-common-kernel-criterion.md`
  - `../../1-in-progress/hypertranscendental-conormal-integrability-correspondence.md`

## Exact quotient theorem

Let `S` be a commuting difference-differential source on `K`, let `R_r` be a labelled family of
linear reporters, and put

```text
F(x)=((sigma_i-1)x)_i x (R_r x)_r.                         (1)
```

Let `D <= K` be a gauge submodule already invisible to `(1)`, so that `D <= ker F`.  Then `F`
descends to a linear map

```text
F_bar:K/D -> source boundary x reporter family.            (2)
```

Lean proves the exact criterion

```text
F_bar injective
  iff ker F <= D
  iff every z fixed by all sigma_i and killed by every R_r lies in D.   (3)
```

Together with the descent hypothesis, `(3)` says that `D` is exactly the gauge forgotten by the
complete observation.  This is the correct quotient version of the earlier zero-common-kernel
theorem.

## HT/DA phase theorem

Assume every member of `D` is differentially algebraic over the base differential field.  Lean
also proves

```text
x-y in D  ->  (x is HT iff y is HT).                        (4)
```

Consequently, if the jointly fixed common reporter kernel is contained in `D`, equality of the
complete fingerprints determines the exact HT/DA phase even when it does not determine the
primitive:

```text
F(x)=F(y)  ->  (x is HT iff y is HT).                       (5)
```

Thus the maximal HT-relevant conservativity condition is not

```text
joint fixed common kernel = 0,
```

but

```text
joint fixed common kernel is differentially algebraic.     (6)
```

An invisible non-DA class is the genuine obstruction to HT-phase reconstruction.

## Differentially algebraic control

Put

```text
f(z)=exp(z),
g(z)=exp(2 pi i z) exp(z).                                  (7)
```

Lean proves that both functions are differentially algebraic, distinct, agree at `z=1`, and obey
the same source equation

```text
F(z+1)=exp(1) F(z).                                         (8)
```

Therefore pointed source non-effectivity and periodic-gauge inertia occur already in a DA family.
They cannot characterize hypertranscendence.  The Gamma collision is an HT instance of a general
source-kinematic phenomenon, not by itself the HT invariant.

## Positive successor

The correct reconstruction target is the source class modulo DA gauge.  For a source-operator
algebra `R`, ambient source module `M`, DA submodule `M_DA`, and source class

```text
q=[f] in M/M_DA,                                            (9)
```

the HT-relevant information is the pointed cyclic module `(R q,q)`, its exact annihilator, and any
source-canonical conormal or derived-critical lift.  This target can distinguish Gamma from the
DA exponential control while refusing the impossible task of choosing one analytic representative
inside a bare source fibre.

The quotient gate `(3)`--`(6)` is parent linear and differential algebra.  Candidate novelty lies
only in proving that natural HT quotient modules admit source-canonical conormal lifts, reconstruct
their source laws, and have conservative analytic/spectral/positive/monodromy realizations.

## Novelty and anti-theatre gate

Parameterized difference Galois theory studies differential relations of solutions, and the DA
elements of a differential extension are closed under field operations.  Kernel quotients and
injectivity of a descended linear map are elementary algebra.  The exact theorem here is therefore
not new scientific knowledge.

The literature attack located the expected parents, including Hardouin's rank-one difference
Galois theory and Adamczewski--Dreyfus--Hardouin's general hypertranscendence theorems for linear
difference equations.  It did not locate the stronger source-polarity conjecture recorded in the
active conormal-integrability card, but absence from search is not a priority certificate.

- `[ANTI-THEATRE -- PASS]` The DA control falsifies an HT-characterization claim rather than being
  hidden.
- `[NOVELTY -- PARENT]` Equations `(3)`--`(6)` are a load-bearing bridge only.
- `[POSITIVE -- SIGNIFICANT ARCHITECTURAL]` The theorem replaces impossible germ reconstruction by
  exact HT-phase reconstruction modulo DA gauge.
- `[RH BOUNDARY]` No zeta source, zero set, positivity theorem, or RH conclusion occurs.

## Lean certificate

The module proves:

- `CommutingDifferenceDifferentialField.familyRealizedBoundaryLinearMap`;
- `CommutingDifferenceDifferentialField.mem_ker_familyRealizedBoundaryLinearMap_iff`;
- `CommutingDifferenceDifferentialField.quotientFamilyRealizedBoundaryLinearMap`;
- `CommutingDifferenceDifferentialField.quotientFamilyRealizedBoundaryLinearMap_injective_iff`;
- `CommutingDifferenceDifferentialField.quotientFamilyRealizedBoundaryLinearMap_injective_iff_jointFixed`;
- `hypertranscendentalOver_iff_of_sub_mem_daGauge`;
- `CommutingDifferenceDifferentialField.fingerprint_determines_hypertranscendence_mod_daGauge`;
- the complete pointed DA exponential collision and DA certificates.

All imported module caches existed, so no build was run.  The touched file passes direct
`lake env lean` verification.  No computation is used.

## Gates

- [x] exact quotient descent constructed
- [x] quotient injectivity characterized by residual common kernel modulo `D`
- [x] HT/DA phase shown constant on DA gauge classes
- [x] fingerprint phase-reconstruction theorem formalized
- [x] explicit pointed DA source collision formalized
- [x] source non-effectivity demoted from HT invariant to source kinematics
- [x] parent-algebra novelty verdict recorded
- [ ] source-canonical DA submodule constructed for a nonlinear analytic category
- [ ] one non-Gamma natural HT quotient module shown conservatively observable
- [ ] source-polarity/full-faithfulness conjecture proved

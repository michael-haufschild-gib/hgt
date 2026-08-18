# G-CE exact-debt physical-cancellation dichotomy

- **ID:** `g-ce-exact-debt-physical-cancellation-dichotomy`
- **Stage:** 3 — formalized in Lean 4
- **Type:** theorem / no-go survivor / source-controller classification
- **Route:** G-CE inside Route G
- **Inputs:** `MobiusGammaXiCoupledErrorSingularGraphGlobalWall.lean`,
  `MobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport.lean`,
  `coupled-floor-mobius-complementary-shift-incidence-law.md`
- **Date:** 2026-08-18
- **RH used:** no
- **Computation used:** no
- **Scientific status:** `[CORPUS-FIRST] [LEAN-FORMALIZED] [UNCONDITIONAL]`
  `[CANDIDATE NEW ROUTE CLASSIFICATION] [NOT AN RH PROOF]`

## 1. Exact problem

Write

```text
d = continuedXiAntiCausalWardResponse(1/2),
D = |d|^2.
```

The actual G-CE boundary vector is the four-unit Fisher vector plus the orthogonal zero-node
component `d k_0`.  Its minimum positive budget is `4+D`; the uncompleted wall has sharp floor
`-D`; and `D=0` iff RH.

The question is whether a physical boundary controller can cancel `d k_0` without first proving
`d=0` and without erasing the source channel.

## 2. Corpus and literature audit

Corpus search was run before conjecturing.  Existing results already exclude:

1. paying a smaller positive Hilbert budget: the exact minimum is `4+D`;
2. scalar Julia/unitary slack: it hides the defect at first order but does not force it to vanish;
3. Gamma-sewn first-jet recovery: it is transparent to `d`;
4. co-moving prime extinction: it is source-insensitive;
5. Krein/theta signed cancellation: it cancels signed current while retaining positive Euclidean
   defect;
6. a regular source contraction through the existing graph map: its critical source gain blows up;
7. a scalar singular relation: one nonzero vertical output makes the scalar vertical fibre all of
   `C`, hence destroys source selection.

Suzuki's 2026 finite self-adjoint/Friedrichs construction and Connes--Consani--Moscovici finite
spectral triples do not prove the critical source convergence/nonexpansiveness needed here.  Their
finite realizations therefore do not remove `D`.

## 3. Conjecture/failure/pivot loop

### C1 — orthogonal zero-mode projection

Because `k_0` is the zero-node Cauchy feature and the Fisher score vanishes at zero,

```text
<k_0,F>=0,
P_(k_0 perp)(F+d k_0)=F,
||F+d k_0||^2-||F||^2=D.
```

This is an exact target-independent dissipative cancellation.

**Failure.**  It erases the only RH-bearing coordinate.  Positivity after this projection is the
unperturbed four-unit Hardy--Fisher Gram for every value of `d`; it cannot imply RH.

### C2 — coherent opposite port

Add a controller carrying `-d`.  The visible sum is zero.

**Failure.**  A conservative two-port mixer cannot destroy norm.  The controller itself costs
`D`, and the antisymmetric output carries the complete two-port energy.  Cancellation is transfer,
not elimination.

### C3 — source-selective linear controller

Let `T:C -> C` be any complex-linear bounded controller and suppose

```text
d+T(d)=0.                                                (1)
```

Perhaps `T` can cancel this actual arithmetic value while remaining nontrivial on other source
values.

**Pivot theorem.**  This is impossible in one complex dimension.  If `d != 0`, every `z` is a
complex multiple of `d`, so complex linearity and `(1)` give

```text
T(z)=-z for every z.                                    (2)
```

Thus cancellation of the actual channel has exactly two branches:

```text
d+T(d)=0
  iff RH
      or T=-I on the entire scalar boundary channel.    (3)
```

The second branch is universal source erasure, not a source-selective physical cancellation.

## 4. Exact energy accounting

On the erasing branch `T(d)=-d`, so

```text
|T(d)|^2=D,
d+T(d)=0,
d-T(d)=2d.
```

The normalized sum/difference mixer obeys the parallelogram identity

```text
(1/2)(|d+T(d)|^2+|d-T(d)|^2)
  = |d|^2+|T(d)|^2
  = 2D.                                                  (4)
```

Hence visible cancellation pays one additional debt `D` and transfers total two-port energy
`2D` into the antisymmetric port.  No positive conservative completion eliminates `D`.

## 5. Surviving RH-bearing obligation

Equation `(3)` removes physical cancellation as an independent escape hatch.  A lawful G-CE
producer must do one of two harder things:

1. prove `d=0` from a source-defined nonexpansive lift before scalarization; or
2. retain a higher-dimensional marked output and prove its complementary port vanishes by source
   admission, rather than discarding it.

The complementary floor/Mobius incidence identifies the only plausible pre-scalar carrier, but
its Gamma boundary renormalization and nonexpansive continuation remain open.  Installing `-I` on
the scalar Ward value is not that theorem.

## 6. Lean formalization

`MobiusGammaXiCoupledErrorDebtCancellationDichotomy.lean` formalizes unconditionally:

- scalar complex-linear controller normal form;
- cancellation iff RH or universal erasure;
- nonerasing cancellation iff RH;
- controller energy equals exact G-CE debt on erasing branch;
- exact balanced-port energy transfer;
- controlled wall at residual coefficient zero is the ordinary four-unit Hardy--Fisher Gram and
  is positive, explicitly classified as the erasing branch.

## Gates

- [x] corpus audit before conjecture
- [x] current literature audit
- [x] three conjecture/fail/pivot rounds
- [x] dependency-closed paper proof
- [x] Lean formalization
- [x] targeted module check and target-only build
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] forbidden-token scan
- [x] umbrella wiring

Global formal lint currently reports unrelated dirty-tree modules missing from their umbrellas; it
does not report this module.  The new module itself passes `lake env lean`, target-only
`lake build`, and the forbidden-token scan.

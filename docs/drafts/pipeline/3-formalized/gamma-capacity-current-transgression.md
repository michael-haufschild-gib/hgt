# Gamma's opposite-variance capacity current is exactly rank one

- **ID:** `gamma-capacity-current-transgression`
- **Stage:** 3-formalized
- **Type:** GAMMA SOURCE-CONORMAL / BOUNDARY-CURRENT IDENTIFICATION
- **Scientific status:** `[LEAN-FORMALIZED FINITE SKELETON] [SIGNIFICANT BRIDGE] [SOURCE-GALOIS IDENTIFICATION OPEN]`
- **Parents:**
  - `../1-in-progress/hypertranscendental-mackey-corona-field.md`
  - `../1-in-progress/gamma-opposite-variance-weyl-seam.md`
- **Statement:** Pairing Gamma's incoming coordinate-prolongation defect with its outgoing Taylor
  curvature gives the factorial-tail conormal boundary vector with nonzero rank one at every clock
  layer.

## Theorem

At level `n`, let

```text
beta_n  = outgoing Taylor curvature,
gamma_n = incoming coordinate-prolongation defect.
```

Their paired current is `C_n=beta_n gamma_n`. For `a` in the first `n+1` raw jets and
`0<=i<=n`, Lean proves

```text
(C_n a)_i=(n+1) a_n/(n+1-i)!.                             (1)
```

Consequently

```text
C_n(a)=((n+1)a_n) v_(n+1),
v_(n+1)(i)=1/(n+1-i)!,                                    (2)
range(C_n)=C v_(n+1),
rank(C_n)=1.                                               (3)
```

The same factorial coefficients occur in the differentiated Gamma shift conormals
`D^i(exp(D)-1)`. Thus `(1)` is the exact finite boundary-symbol transgression from the cyclic
source conormal into the newest algebraic clock direction. It is independent of `z`.

## No-go and positive statement

The equality “one new jet generator equals rank one” is only dimension counting and is rejected as
an index theorem. The positive nontrivial content is the exact pairing `(1)`: the source-selected
incoming and outgoing variance defects pair to the same factorial conormal symbol at every level.

This remains a finite skeleton. Proving that it is the transgression of the minimal parameterized-
Galois conormal module, rather than only the explicit Gamma jet matrices, is open.

## Lean declarations

`GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona` contains:

- `gammaClockPairedBoundaryCurrent`;
- `gammaClockPairedBoundaryCurrent_apply`;
- `gammaClockPairedBoundaryCurrent_eq_outerProduct`;
- `range_gammaClockPairedBoundaryCurrent`;
- `finrank_range_gammaClockPairedBoundaryCurrent`.

The touched file passed direct Lean checking. The declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. Its cached object existed, so no module or full build was run.

## Gates

- [x] exact paired-current formula Lean-formalized
- [x] exact rank-one range Lean-formalized
- [x] current coefficient identified with differentiated shift-conormal boundary symbol
- [ ] finite Weyl seam proved equal to the negative paired current in Lean
- [ ] minimal source-Galois conormal module constructed
- [ ] source-Galois transgression identified with this finite current

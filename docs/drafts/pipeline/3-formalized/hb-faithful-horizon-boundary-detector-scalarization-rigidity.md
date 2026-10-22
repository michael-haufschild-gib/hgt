# HC93 — Faithful horizon/boundary detector scalarization rigidity

Status: formalized

Route: HB, with shared FZZ-P / RBH / PW-B Ward relevance

## Hard frontier question

HC92 proves common diagonal gauge cannot erase relative horizon/boundary source-FE holonomy. The
frontier map leaves a stronger possible escape: fixed nonscalar or singular detector data might mix
the two physical readouts and see one common gain even off the critical line.

This card attacks arbitrary linear detector compression, not only diagonal gauge or invertible
matrix changes.

## Corpus basis

Mandatory searches:

- `scripts/formal_tools.py research "horizon boundary relative gain common detector locality radiation map source independent normalization transfer cocycle"`
- `scripts/formal_tools.py research "complete pre-divisor augmented-source evaluation fixed pre-transport reflection-real nonscalar singular data copywise darkness HB"`
- `scripts/formal_tools.py research "canonical left action covariance endpoint two branch functional equation reflection sends branches augmented source"`

Corpus facts:

- HC92 supplies actual nonzero horizon and boundary cocycles and proves their equality exactly on
  the critical line for every common diagonal gauge.
- Canonical BM Peierls incidence is already realized unconditionally; its untransported branch
  equality is extinction/RH, while genuine channel Schwarz transport remains nonzero off line.
- Copy-dependent, division-free, and singular response compensators can cancel reflected currents.
  Therefore detector faithfulness—not regularity or nonscalarity alone—is the unresolved invariant.

## Frozen conjecture HC93

Let `D(q)` be the diagonal linear operator on the two-detector carrier `C^2` with eigenvalues the
actual horizon and boundary source-FE cocycles. For any complex-linear detector map `L : C^2 -> V`
and scalar `c`, define scalarization by

`L(D(q)x) = c L(x)` for every `x`.

Prove:

1. If `L` is injective and scalarizes `D(q)`, then the horizon and boundary cocycles are equal, so
   `Re(q)=1/2`.
2. Conversely, on the critical line the identity detector scalarizes `D(q)`.
3. Off line, every scalarizing detector kills the horizon basis vector or the boundary basis
   vector. This classifies all singular escape: scalarization is possible only by deleting at least
   one physical channel.
4. Existence of a globally faithful (even copy-dependent) detector scalarization is equivalent to
   `RiemannHypothesis`.
5. Package all statements as one closed unconditional Lean theorem.

## Kill criterion and survivor

- If a faithful linear detector can scalarize an off-line cocycle, HC92's relative invariant is
  basis-dependent and the common-gain route is dead.
- If conjecture holds, arbitrary nonscalar and singular linear mixing is exhausted. Only rank-loss
  projections evade the obstruction, and they do so by discarding a physical horizon/boundary axis.
  Remaining HB producer is then literal augmented-source dynamics forcing faithful copywise
  darkness, not detector choice.

## Literature audit (through 2026-08-28)

- Birmingham–Mokhtari (arXiv:hep-th/0609028) supplies exact gauge-invariant hypergeometric
  gravitational modes and distinct horizon/AdS boundary data.
- Green et al. (arXiv:2210.15935v3) derives reflection-based conserved bilinear forms and QNM
  excitation projections.
- Sberna et al. (arXiv:2112.11168) distinguishes horizon amplitude from boundary-normalized QNM
  response and emphasizes their nontrivial proportionality.
- Targeted searches for horizon/boundary detector-channel scalarization and faithful linear mixing
  found no statement of this classification or RH equivalence. This is a bounded novelty audit.

## Formal result

Module:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRadiativeSourceFEFaithfulDetectorScalarizationRigidity`

The closed theorem `hbXiRadiativeFaithfulDetectorScalarizationRigidity` proves all five clauses of
HC93 for the actual HC92 source-FE horizon/boundary cocycles. In particular:

- any injective detector that scalarizes the two-channel cocycle forces `Re(q) = 1 / 2`;
- off the critical line, a linear detector scalarizes the cocycle if and only if it kills the
  horizon basis vector or kills the boundary basis vector;
- local faithful scalarizability is equivalent to the critical-line condition; and
- existence of a copy-dependent globally faithful detector scalarization is equivalent to
  `RiemannHypothesis`.

Thus arbitrary nonscalar and singular linear detector compression is exhausted. Rank loss is the
only off-line scalarization mechanism, and it works precisely by deleting one complete physical
channel. The live HB burden is now literal augmented-source dynamics / pre-divisor source law
forcing faithful copywise darkness, not detector normalization or channel mixing.

Audit: direct Lean check passed; targeted build passed 13,098/13,098; `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`; formal lint reports no HC93 finding (its failures are
pre-existing unreachable modules outside this card).

## Lean audit checklist

- [x] Foreground scratch proof with `lake env lean /tmp/hc93.lean`
- [x] No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [x] Closed theorem and `#print axioms` audit
- [x] Add module and wire `GaloisForLFunctions.RHTower`
- [x] Targeted module build only
- [x] Formal lint has no HC93 finding
- [x] Promote to `3-formalized`

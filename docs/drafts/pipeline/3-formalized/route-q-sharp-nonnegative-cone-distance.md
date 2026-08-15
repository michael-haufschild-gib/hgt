# Route Q sharp nonnegative-cone distance

- **ID:** `route-q-sharp-nonnegative-cone-distance`
- **Stage:** 3-formalized
- **Type:** THEOREM / exact quantitative obstruction
- **Routes:** Q primary; U odd-sector comparison
- **Source:** cofinal separated-source sign gate and Xi--Hurwitz negative Weil sector

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Question

The cofinal sign gate proves that a source-nonnegative separated packet sequence cannot converge
to a nonzero Hurwitz orientation vector.  Is this only an asymptotic sign fact, or is there an
exact metric gap between the orientation vector and the entire nonnegative Weil cone?

## Theorem Q-DIST

Let `J` be the unconditional critical-line reflection on the multiplicity-exact Xi Hilbert
carrier, let

```text
Q(v) = Re <Jv,v>,
w = xiHurwitzOrientationVector,
Jw = -w,
||w||^2 = xiHurwitzOrientationEnergy.
```

Then every `v` with `Q(v)>=0` satisfies

```text
xiHurwitzOrientationEnergy <= 2 dist(v,w)^2.                 (1)
```

The constant is exact.  Define the phase-forgetting vector coordinatewise by

```text
e(q) = |w(q)|.
```

Lean proves `Je=e` and `||e||=||w||`.  The balanced even--odd vector

```text
b = (w+e)/2
```

lies on the null boundary `Q(b)=0` and attains

```text
xiHurwitzOrientationEnergy = 2 dist(b,w)^2.                 (2)
```

For every pairwise-separated finite continued-Cauchy prime--Gamma packet `P`, exact source-energy
reconstruction specializes `(1)` to

```text
0 <= sourceEnergy(P)
  -> xiHurwitzOrientationEnergy
       <= 2 dist(evaluation(P), xiHurwitzOrientationVector)^2.  (3)
```

All statements are unconditional.

## Heavy conjecture loop

### Q-D1 — false-RH trapping is only qualitative

**Conjecture.** Continuity gives eventual negativity but no uniform geometric obstruction.

**Attack.** Split an arbitrary `v` into reflection-even and reflection-odd channels.  `Q(v)>=0`
means its even Hilbert energy dominates its odd Hilbert energy.  Since `w` is entirely odd,
parallelogram geometry forces

```text
||w||^2 <= 2 ||v-w||^2.
```

**Verdict:** false.  Replaced by exact inequality `(1)` and proved in Lean.

### Q-D2 — the factor two is proof slack

**Conjecture.** Triangle inequalities make `(1)` nonsharp.

**Attack.** Sign-forgetting produces an equally long reflection-even companion `e`.  The midpoint
of `w` and `e` has equal even and odd energies, hence zero Weil square.  Orthogonality of the two
reflection sectors gives equality `(2)`.

**Verdict:** false.  Factor two is optimal, with a canonical equality witness.

### Q-D3 — the equality witness supplies the missing packet

**Conjecture.** Approximate the boundary witness `b` by separated prime--Gamma packets and obtain
the cofinal nonnegative producer.

**Attack.** `b` is defined using absolute values of divisor-side orientation coordinates.  Density
can approximate it only through target-side Hilbert closure, and continuity does not preserve the
sign of approximants at a null boundary.  This is precisely the information-losing selection
mechanism already ruled out by the monotone plateau wall.

**Verdict:** failed.  The boundary vector classifies the obstruction but is not source-first.
The positive survivor is the literal packet inequality `(3)`.

## Dependency-closed proof

For a general involutive complex-linear isometry `J`, the exact channel identity is

```text
4 Q(v) = ||v+Jv||^2 - ||v-Jv||^2.                           (4)
```

Thus `Q(v)>=0` implies `||v-Jv||^2 <= ||v+Jv||^2`.  Put `a=v-w`.  Since `Jw=-w`,

```text
a+Ja = v+Jv,
a-Ja = (v-Jv)-2w.
```

The parallelogram law gives

```text
4||a||^2 = ||v+Jv||^2 + ||(v-Jv)-2w||^2
          >= ||v-Jv||^2 + ||(v-Jv)-2w||^2
          >= 2||w||^2.
```

The last inequality is the midpoint form of the parallelogram law.  This proves `(1)`.

For sharpness, `e(q)=|w(q)|` is square-summable because its coordinate norms equal those of `w`.
Reflection negates `w` but preserves coordinate norm, so `Je=e`.  Applying `(4)` to
`b=(w+e)/2` gives `Q(b)=0`; applying the channel parallelogram law to `b-w` gives `(2)`.
Finally `sourceEnergy(P)=Q(evaluation(P))` turns `(1)` into `(3)`.

## Higher universal principle

**A negative orientation state is separated from a nonnegative source chamber by half its odd
Hilbert mass, exactly.**  Continuity is not the real mechanism; orthogonal reflection sectors are.
This recasts Route Q as a metric incidence problem.  A source-first construction cannot approach
orientation through nonnegative packets unless orientation energy vanishes.

Route U has the same lawful pattern only after odd-sector admission: if its first-contact limit is
identified with a reflection-odd source state and finite nonnegative states converge to it in the
same Hilbert norm, an exact exclusion radius forces that odd state to vanish.  Current U corpus has
compactness and smaller-aperture positivity but not this source-specific odd-sector identification;
the theorem isolates that missing bridge rather than assuming it.

## Significance and positive survivor

The preceding Q gate asked for arbitrarily late nonnegative packets.  Q-DIST adds a quantitative
falsifier for every candidate source section:

```text
nonnegative source energy at scale n
  -> approximation error_n^2 >= orientationEnergy/2.
```

Therefore any source theorem forcing both nonnegative recurrence and errors tending to zero is
enough, while a proposed construction whose error lower bound saturates `(3)` cannot be improved by
abstract Hilbert geometry.  Progress must exploit prime--Gamma incidence before target closure.

## External novelty audit

- Krein/indefinite-inner-product literature classically describes positive, negative, and null
  cones; an early source is Aronszajn's *Generalized Vector Spaces I*,
  <https://doi.org/10.4153/CJM-1949-010-1>.
- Suzuki studies Hilbert spaces arising from the Weil distribution and RH-dependent positivity,
  <https://arxiv.org/abs/2301.00421>.
- Targeted searches on 2026-08-16 found no external statement identifying the exact Hilbert
  distance from the Xi--Hurwitz orientation vector to the unconditional nonnegative Weil cone, no
  canonical absolute-coordinate equality witness, and no finite prime--Gamma packet inequality
  `(3)`.  Novelty remains unverified and is not claimed.

## Gates

- [x] 0 -> 1: quantitative conjecture, sharpness attack, source-producer falsifier
- [x] 1 -> 2: dependency-closed proof and external novelty audit
- [x] 2 -> 3: unconditional Lean theorem, direct check, exact leaf build, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Module:
`formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationSharpNonnegativeConeDistance.lean`.

Capstones:

- `orientationEnergy_le_two_mul_packet_dist_sq_of_sourceEnergy_nonnegative`;
- `exists_weilBoundaryVector_at_exact_orientationRadius`;
- `xiHurwitzOrientation_exact_nonnegativeCone_radius`.

Direct `lake env lean` and exact leaf `lake build` succeeded.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  Forbidden declaration scan is clean.  Module is imported by
`RHTower.lean`; no umbrella or full-project build was run.

## Log

- 2026-08-16 — Qualitative trapping conjecture replaced by exact cone-distance bound.
- 2026-08-16 — Canonical sign-forgetting equality witness formalized; factor two proved optimal.
- 2026-08-16 — Literal separated-packet source inequality formalized and axiom-audited.

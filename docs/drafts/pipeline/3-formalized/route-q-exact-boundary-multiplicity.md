# Route Q exact boundary multiplicity

- **ID:** `route-q-exact-boundary-multiplicity`
- **Stage:** 3-formalized
- **Type:** THEOREM / equality-locus classification
- **Routes:** Q primary
- **Source:** sharp Xi--Hurwitz nonnegative-cone distance

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Question

Xi--Hurwitz orientation vector has an explicit closest zero-energy boundary point. Can uniqueness
or canonical metric projection select missing source packet, or does sharp cone-distance equality
locus retain uncontrolled phase?

## Theorem Q-MULT

Let `J` be a complex-linear isometric involution, `Jw=-w`, and `Je=e` with `||e||=||w||`. Then

```text
v_e = (w+e)/2
```

has zero `J`-quadratic energy and attains sharp cone radius:

```text
Q(v_e)=0,
||w||^2 = 2 ||v_e-w||^2.                                   (1)
```

For unconditional Xi carrier, absolute-coordinate even companion `e=|w|` and its negative yield
two explicit exact boundary points. If orientation energy is positive, they are distinct. In fact
Lean proves premise-free equivalence

```text
(there exists a unique exact closest zero-energy boundary point) <-> RH. (2)
```

Thus false RH forces multiplicity of sharp equality witnesses, while RH collapses exact boundary
locus to zero.

## Heavy conjecture loop

### Q-M1 — canonical equality witness is unique

**Conjecture.** Absolute-coordinate midpoint from sharp-distance theorem is unique closest
null-cone point and may therefore be characterized intrinsically.

**Attack.** Forget coordinate formula. Split Hilbert space into fixed and anti-fixed reflection
sectors. Every fixed vector `e` with `||e||=||w||` balances odd vector `w` at `(w+e)/2` and
saturates same inequality.

**Verdict:** false. Equality has an entire same-norm fixed-sector family whenever that sector is
nontrivial.

### Q-M2 — Xi source may still distinguish positive absolute companion metrically

**Conjecture.** Although generic equality is nonunique, concrete Xi carrier has only canonical
positive companion.

**Attack.** Use `e` and `-e`. Both are reflection-fixed, equally long, and produce exact boundary
points. Their midpoint difference is exactly `e`; positive orientation energy makes `e` nonzero.

**Verdict:** false. Two explicit Xi equality witnesses exist under false RH.

### Q-M3 — boundary uniqueness is a weaker source-free route to RH

**Conjecture.** Prove uniqueness by strict convexity or abstract projection, then derive RH.

**Attack.** Null boundary of an indefinite quadratic cone is not a convex metric-projection
target. Equality-family theorem shows uniqueness already collapses orientation vector. Lean proves
uniqueness iff RH, so any unconditional proof of uniqueness contains full missing arithmetic
content.

**Verdict:** failed as intermediate mechanism. Positive survivor is exact classification
`(1)`--`(2)` and requirement that source incidence choose even phase before target closure.

## Dependency-closed proof

For `v=(w+e)/2`, involution identities give

```text
v+Jv=e,
v-Jv=w.
```

Exact channel identity

```text
4 Q(v) = ||v+Jv||^2 - ||v-Jv||^2
```

and `||e||=||w||` prove `Q(v)=0`. Applying parallelogram identity to `v-w` gives distance equality
in `(1)`.

In Xi carrier, coordinatewise absolute value is fixed by reflection and has same norm as anti-fixed
orientation vector. Both signs therefore satisfy `(1)`. Positive orientation energy makes absolute
vector nonzero, so two points differ. Conversely, RH makes orientation energy and orientation
vector zero; distance equality then forces every exact boundary point to have norm zero. This
proves `(2)`.

## Higher universal principle

**Sharp indefinite-cone distance forgets fixed-sector phase.** Balancing determines norm of even
component but not its direction. What looked like a canonical closest point is one gauge choice on
a reflection-even sphere. Route Q is stuck because target Hilbert geometry has already discarded
exactly phase that prime--Gamma incidence must supply.

This unifies plateau no-go and sharp-distance theorem: scalar transport forgets source rank; cone
projection forgets even phase. Both become canonical only after erasing arithmetic incidence.
Lawful next theorem must constrain even component of finite separated packets before target-space
closure.

## Significance and positive survivor

Q-MULT eliminates plausible but circular shortcut: uniqueness of canonical sharp boundary witness
cannot be proved by abstract geometry, because it is itself RH-equivalent. Any useful source
recurrence must do more than approach sharp cone radius; it must select compatible fixed-sector
phase through literal theta/prime--Gamma data.

Strongest positive survivor is full fixed/anti-fixed balancing law `(1)`, together with exact Xi
uniqueness equivalence `(2)`. This gives a concrete diagnostic for future packets: near-saturation
without phase control is kinematic and cannot close Route Q.

## External novelty audit

- Reddy--Kurmayya study cone invariance for Gram matrices in indefinite inner-product spaces,
  <https://arxiv.org/abs/1502.00382>; its abstract does not state Xi-specific sharp equality locus
  or RH-equivalent uniqueness theorem.
- Targeted searches on 2026-08-16 found general indefinite-cone literature but no theorem joining
  Xi--Hurwitz orientation vector, two explicit absolute-coordinate boundary witnesses, and
  uniqueness of exact closest zero-energy point with RH.
- No external novelty claim is made; this is an unsuccessful collision search, not priority
  evidence.

## Gates

- [x] 0 -> 1: uniqueness conjecture falsified; equality-locus survivor isolated
- [x] 1 -> 2: dependency-closed proof and external novelty audit
- [x] 2 -> 3: unconditional Lean theorem, direct check, exact leaf build, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Module:
`formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationExactBoundaryMultiplicity.lean`.

Capstones:

- `CliffordWeil.balanced_fixed_antiFixed_boundary`;
- `xiHurwitzOrientationBoundaryPlus_exact`;
- `xiHurwitzOrientationBoundaryMinus_exact`;
- `xiHurwitzOrientationBoundaryPlus_ne_minus_of_energy_pos`;
- `xiHurwitzOrientation_exactConeBoundary_unique_iff_rh`.

Direct `lake env lean` and exact leaf `lake build` succeeded. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden declaration scan is clean. Module is imported by
`RHTower.lean`; no umbrella or full-project build was run.

## Log

- 2026-08-16 — Canonical-boundary uniqueness conjecture falsified by fixed-sector balancing.
- 2026-08-16 — Two explicit Xi equality witnesses and uniqueness iff RH proved in Lean.
- 2026-08-16 — Exact leaf built, axiom-audited, and wired without umbrella build.

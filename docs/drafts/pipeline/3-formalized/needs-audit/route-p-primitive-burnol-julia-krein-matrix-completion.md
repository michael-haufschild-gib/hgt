# Route P primitive Burnol Julia--Krein matrix completion

- **ID:** `route-p-primitive-burnol-julia-krein-matrix-completion`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105C]`
- **Parents:** `route-p-fourth-depth-copoisson-julia-krein-pivot.md`,
  `../../1-in-progress/prime-gamma-signed-permutation-eulerian-rh.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolJuliaKreinMatrixCompletion.lean`

## Goal

Decide whether P-G105B's one-vector Julia--Krein pivot is only a diagonal normalization identity,
or preserves P-G186's full finite prime/depth/ordinate incidence without fitted cross coefficients.

## Conjecturing loop

### Conjecture 1 — one-vector norm law already closes finite matrix

P-G105B proved child energy, pivot energy, cross, determinant, and shorting for one vector in
`evenSubspace`. Reading those identities independently over each primitive label was tempting.

**Failed as matrix argument.** Diagonal norms do not determine off-diagonal Gram entries. This
could silently replace P-G186's nonorthogonal feature incidence by an orthogonal direct sum,
destroying signed-permutation curvature.

**Positive survivor:** polarize Julia--Krein law for two arbitrary vectors before specializing
prime labels.

### Conjecture 2 — use existing even-`L2` logarithmic unitary

Corpus has an even-`L2` to whole-line Sonin unitary, suggesting transport of aperture features into
P-G105B's physical co-Poisson type.

**Pivoted before claiming theorem.** P-G186's feature family lives in `routePBurnolHalfLineL2`;
P-G105B lives in `evenSubspace`. No source-defined half-line-to-even map is proved to intertwine
these features, fourfold dilation, aperture labels, and Gamma/Stokes incidence simultaneously.
Treating carriers as identical would be theatre.

**Positive survivor:** Julia coefficients are scalar, so define completion directly over actual
half-line carrier without any unproved carrier identification.

### Conjecture 3 — universal Julia block tensorizes over actual P-G186 Gram

For arbitrary `f,g` in `routePBurnolHalfLineL2`, define

```text
c = 1/8,
d = sqrt(1-c^2) = sqrt 63 / 8,
x_f = (c f,0),
p_f = (sqrt 63 f,8 f).
```

Conjectured signature pairings were

```text
[x_f,x_g] = (1/64)<f,g>,
[x_f,p_g] = d<f,g>,
[p_f,x_g] = d<f,g>,
[p_f,p_g] = -<f,g>.
```

**Proved.** These are polarized identities, not diagonal norm formulas. For every finite P-G186
packet with Gram `G`, complete channel Gram is exactly

```text
B tensor G,
B = [[1/64,d],[d,-1]].
```

Every off-diagonal prime/depth/ordinate interaction survives as same Gram entry times universal
channel coefficient.

### Conjecture 4 — completion can create or hide finite degeneracy

An indefinite lift could conceivably acquire new null directions when source Gram is nonsingular.

**Falsified, with exact positive survivor.** Julia identity gives `det(B)=-1`. Kronecker determinant
law yields, for an `N`-feature packet,

```text
det(B tensor G) = det(B)^N det(G)^2 = (-1)^N det(G)^2.
```

Completed matrix is nonsingular exactly when original P-G186 Gram is nonsingular. Completion
neither creates nor conceals finite degeneracy.

## Paper proof

Sesquilinearity and reality of `c`, `sqrt 63`, and `8` give first three polarized formulas. For
pivots,

```text
[p_f,p_g] = 63<f,g> - 64<f,g> = -<f,g>.
```

Specialize `f,g` to arbitrary P-G186 window features `f_i,f_j`. Already proved literal half-line
Gram theorem gives `<f_i,f_j>=G_ij`. Four channel choices are therefore exactly four entries of `B`
times `G_ij`, definition of `B tensor G`.

Finally,

```text
det(B) = -(1/64)-d^2 = -(1/64)-(63/64) = -1.
```

Exact Kronecker determinant identity gives displayed factorization. Since `(-1)^N` is nonzero and
a complex square vanishes exactly when its base vanishes, finite nondegeneracy equivalence follows.
`QED`

## Novelty and anti-theatre audit

Kronecker determinants and Julia/Halmos coefficients are standard. New route-specific knowledge is
their coefficient-faithful interaction with corpus's literal P-G186 half-line feature Gram:

```text
P-G186 full incidence G
  -> universal fourth-depth Julia--Krein channel block B
  -> exact completed incidence B tensor G
  -> determinant (-1)^N det(G)^2.
```

This is stronger than repeating P-G105B per label: it proves every off-diagonal feature pairing and
uses no orthogonality, label separation, or fitted coefficient. It changes open core from `N^2`
Gamma/Stokes pairing identities to one label-natural channel identification: if literal co-source
realizes universal pivot map, all finite Gram incidences follow functorially.

It does **not** identify universal negative channel with literal Gamma/Stokes data, prove signed-word
insertion, identify cofinal determinant with Xi, or prove RH.

## Formal status

Lean proves unconditionally, without theorem premises:

- four polarized child/pivot pairings for arbitrary half-line vectors;
- universal block determinant `-1`;
- exact Kronecker equality for every finite P-G186 packet;
- determinant factorization `(-1)^N det(G)^2`;
- completed determinant nonzero iff original P-G186 determinant nonzero;
- combined matrix/determinant capstone.

Direct `lake env lean` passes. Target-only
`lake build GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolJuliaKreinMatrixCompletion` passes.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. Targeted forbidden
scan and `git diff --check` are clean. Module is wired into RHTower; no umbrella build was run.

## Strongest positive survivor and refined open core

Full finite P-G186 incidence is closed conditional only on source identity, not pairwise matrix
matching. The next conjecture was source-defined, label-natural realization of

```text
literal Gamma/Stokes co-source channel(f) = (sqrt 63 f,8 f)
```

or equivalent source-exchange statement before target evaluation. P-G105D realizes Gamma cyclic
coefficient/operator exactly, but P-G105E then proves literal joint-depth Xi co-source is not any
constant multiple of source: exact relation is `source(p,e)=log(p) coSource(p,e)`. Therefore stated
constant arithmetic weld is retired. Strongest survivor is variable prime-log operator-valued
Julia block; do not divide by Xi-zero holonomy or fit target.

## Higher universal principle

Earlier failures treated normalization as one scalar per feature and made every off-diagonal
interaction look like another arithmetic burden. Julia environment is a universal channel functor:
it acts on carrier, not labels. Once completed before scalarization, it tensors with every existing
incidence law automatically. Remaining arithmetic problem is source provenance of one negative
channel.

## Log

- 2026-08-16 — P-G105C polarized full-matrix conjecture formulated after carrier mismatch audit.
- 2026-08-16 — Exact Kronecker law, determinant factorization, and degeneracy equivalence
  paper-proved and formalized in Lean.

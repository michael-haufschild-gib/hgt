# Route P fourth-depth co-Poisson Julia--Krein pivot

- **ID:** `route-p-fourth-depth-copoisson-julia-krein-pivot`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105] [P-G105B]`
- **Parents:**
  `route-e-p-sp-e-fourth-depth-julia-defect-krein-completion.md`,
  `route-e-p-sp-e-source-normalization-krein-shorting.md`,
  `route-p-primitive-depth-square-modular-defect.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePFourthDepthCoPoissonJuliaColligation.lean`,
  `formal/GaloisForLFunctions/RHTower/RoutePFourthDepthCoPoissonJuliaKreinPivot.lean`

## Conjecturing loop

### Conjecture 1 — existing Gamma aperture multiplier realizes `1/8`

P-G104 left a coefficient with correct value but only scalar/physical realization. First attempt
was to specialize the existing Gamma-sewn Mobius aperture contraction multiplier to `1/8` and use
its established colligation as literal source.

**Falsified.** Corpus theorem proves that multiplier is strictly greater than `1/2` for every real
aperture. It cannot equal `1/8`. Reparameterizing it would erase physical aperture provenance.

### Conjecture 2 — Burnol fourfold dilation is the literal contraction

P-G179's physical two-step map is

```text
f(r) -> f(4r) / 4.
```

Burnol's normalized dilation `U_4` is unitary and acts as `f(r) -> 2 f(4r)`. Therefore the
physical fourth-depth map is exactly

```text
A = (1/8) U_4.
```

This survives. Its Julia defect is `D=(sqrt 63 / 8)I`, and both `Af` and `Df` stay inside the
two-level co-Poisson aperture ladder.

### Conjecture 3 — sign can be borrowed from Burnol holonomy

Adjacent top-conormal corpus supplies a genuine negative orientation: on a strict-right Xi zero,
the actual Burnol conormal is a negative Fisher multiple of positive holonomy. That proves sign
provenance exists, but its magnitude varies with zero coordinate. Multiplying P-G104's defect by
that carrier does not produce the fixed pivot `-||f||^2` and would require target-dependent
normalization.

**Falsified as exact pivot realization.** Holonomy remains evidence for eventual Gamma/Xi
orientation, not local normalization source.

### Conjecture 4 — Julia data themselves generate the Krein pivot

Let

```text
c = 1/8,
d = sqrt(1-c^2) = sqrt 63 / 8,
U = U_4,
w = ||f||^2.
```

Place fourth-depth child and Julia co-graph pivot in signature `(+, -)`:

```text
x_f = (c U f, 0),
p_f = ((d/c) U f, (1/c) f).
```

This survives and closes P-G103's entire local matrix, not only its cross magnitude.

## Paper proof

Because `U` is unitary and `c^2+d^2=1`,

```text
[x_f,x_f] = c^2 w = w/64.
```

The child--pivot cross is

```text
[x_f,p_f]
  = <cUf,(d/c)Uf>
  = d w
  = (sqrt 63 / 8)w.
```

The pivot energy is

```text
[p_f,p_f]
  = (d/c)^2 w - (1/c)^2 w
  = (d^2-1)/c^2 w
  = -w.
```

Therefore its exact Krein Gram block is

```text
[[ w/64, (sqrt 63 / 8)w ],
 [ (sqrt 63 / 8)w,       -w ]].
```

Its determinant is

```text
(-w)(w/64) - (63/64)w^2 = -w^2,
```

and shorting through the second coordinate gives

```text
w/64 - ((sqrt 63 / 8)w)^2 / (-w) = w.
```

Thus negative pivot, unique cross, strict indefiniteness, and exact restoration are four shadows
of one Julia co-graph construction.

Both pivot coordinates retain physical source membership. If
`f in burnolCoPoissonSourceSpace b`, then `Uf` lies at aperture `b/4`; scalar multiples preserve
membership. Hence

```text
(p_f)_+ in sourceSpace(b/4),
(p_f)_- in sourceSpace(b).
```

Finally, negative signature is not an arbitrary sign declaration. For polar coordinates
`v=(v_+,v_-)`, set unnormalized source/co-source coordinates

```text
H(v) = (v_+ + v_-, v_+ - v_-).
```

The source-exchange form

```text
B((a,b),(c,d)) = <a,d> + <b,c>
```

satisfies

```text
B(Hx,Hy) = 2 (<x_+,y_+> - <x_-,y_->).
```

So `(+, -)` is Hadamard diagonalization of source/co-source exchange, same universal symmetry
already used by the literal joint-depth Euler Krein landing. `QED`

## Novelty and anti-theatre audit

Generic Julia/Halmos dilation and generic Krein Schur complements are standard. The new
route-specific content is the coefficient-faithful identification

```text
literal Burnol fourth-depth map A=(1/8)U_4
  -> Julia defect D=(sqrt 63/8)I
  -> canonical co-graph pivot ((D/A)Uf,A^-1 f)
  -> exact P-G103 Krein block.
```

This is stronger than P-G104: P-G104 sourced only cross magnitude. P-G105 makes contraction and
defect actual co-Poisson operators. P-G105B constructs actual source-space pivot with exact
negative norm, determinant, and restored Schur energy.

No RH premise, Xi-zero coordinate, numerical fitting, or positivity assumption enters these
results. However, this is still local. Calling it Gamma/Stokes identification, cofinal incidence,
Xi determinant equality, or RH would be theatre. Current pivot is canonical inside the
co-Poisson Julia/source-exchange carrier; proof that corpus's literal Gamma/Stokes co-source maps
to it is still absent.

## Formal status

Lean proves unconditionally:

- physical map is `(1/8) • evenDilationCLM 4` and acts a.e. as `f(4r)/4`;
- exact contraction and defect norms;
- source-space descent `b -> b/4` and environment retention at `b`;
- full two-channel Julia energy conservation and source-pair transport;
- source/co-source exchange diagonalizes to twice the diagonal Krein pairing;
- Julia co-graph pivot has coordinates `((d/c)U_4f,(1/c)f)`;
- child energy `w/64`, cross `(sqrt 63/8)w`, pivot energy `-w`;
- determinant `-w^2`, strict negativity for nonzero source, exact restored shorting `w`;
- combined source-membership/Gram/shorting capstone.

Direct `lake env lean` passes for both modules. Exact target-only OLean builds pass. `#print axioms`
on both capstones, diagonalization, and determinant reports only `propext`, `Classical.choice`, and
`Quot.sound`. Forbidden-declaration scan is clean. Both modules are wired into RHTower umbrella;
no umbrella build was run.

## Strongest positive survivor

Local normalization and negative-pivot construction are closed. P-G105C subsequently proves this
same Julia--Krein law tensorizes over P-G186's full finite half-line feature Gram, so remaining first
unproved theorem is one typed natural intertwining statement, not scalar or pairwise matrix identities:

```text
literal Gamma/Stokes co-source channel
  --source-defined intertwiner-->
Julia co-graph pivot p_f,
```

compatible with primitive `(prime,depth)` labels, aperture descent, source/co-source exchange, and
cofinal summation. If no such intertwiner exists, pivot to completed pre-divisor bichamber current;
do not normalize Burnol holonomy by its target value.

## Higher universal principle

Every failed positive repair compressed too early. A strict contraction first loses energy into a
Julia environment; source/co-source exchange then supplies canonical one-negative-index geometry;
Krein shorting returns environment energy with opposite sign. Amplification `8` survives only in
the negative co-graph coordinate `A^-1 f`, where it creates finite normalized pivot rather than a
positive spectral-shell eigenvector. P-G101/P-G102 failed because they demanded same inverse gain
inside positive physical operator after compression.

## Log

- 2026-08-16 — P-G105 literal Burnol co-Poisson Julia colligation formalized.
- 2026-08-16 — P-G105B exact co-graph Krein pivot, exchange diagonalization, determinant, and
  restored shorting formalized.
- 2026-08-16 — P-G105C full P-G186 matrix tensorization moved to
  `route-p-primitive-burnol-julia-krein-matrix-completion.md`.

# Baire-generic Möbius gauges have maximal exponent

- **Stage:** 3-formalized.
- **Type:** THEOREM (Lean).
- **Lean:** `ArithmeticGaugeTheory/TheBaireGenericExponentIsOne.lean`.
- **Wall:** Γ1, measure versus category.
- **Statement:** For every prescribed sequence `b(N)=o(N)`, a residual set of gauges satisfies `|Σ_(n≤N) μ(n)χ(n)|>K b(N)` at arbitrarily large `N`, for every `K>0`. The Baire-generic Möbius exponent is exactly `1`, whereas its Haar-almost-sure value is `1/2`.

## Frontier

The corpus proves a residual exponent bound `≥3/4` and exponent `1` at every finite-coordinate Liouville tail. The exact generic value and arbitrary prescribed sublinear benchmark are stronger. The exponent at the trivial gauge remains open.

## Proof

Write `S_N(x)=Σ_(n≤N) μ(n)χ_x(n)`. Each `S_N` is continuous in the product torus. For integers `K,M≥0`, the set

`U_(K,M)=⋃_(N≥M) {x: |S_N(x)|>K b(N)}`

is open. Every nonempty open cylinder contains a Liouville tail `y` retaining its prescribed coordinates. The proved squarefree-density formula gives `S_N(y)/N→L_y≠0`. Consequently `|S_N(y)|/N→|L_y|>0`, while `K b(N)/N→0`; hence `y∈U_(K,M)`. Each set is dense, and their countable intersection is residual. For a real multiplier `K>0`, use its integer ceiling when `b(N)≥0`; when `b(N)<0`, the desired strict inequality follows from `|S_N|≥0`.

For each rational `q<1`, take `b(N)=N^q=o(N)`. Intersect these residual sets over rational `q<1`. If the gauge exponent were below `1`, choose a rational `q` strictly between it and `1`. Then `q≥0` and a global bound `|S_N|≤C(N+1)^q≤C2^qN^q` for `N≥1` contradicts escape with multiplier `C2^q+1`. The universal bound `|S_N|≤N+1` gives exponent at most `1`. Thus the generic exponent equals `1`.

Its level set is Haar-null because almost every gauge has exponent at most `1/2`. This sharpens the residual `≥3/4` bound to an exact classification; it does not establish typicality of the trivial gauge.

## Gates

- [x] Corpus check: residual `≥3/4`, dense exponent-one tails, no exact residual exponent-one theorem found.
- [x] Dependency-closed paper proof.
- [x] Lean leaf check, transitive axiom audit, umbrella import.

## Certificate

`residual_moebius_exceeds_sublinear`, `moebius_exponent_one_residual`, and
`moebius_exponent_one_residual_and_null` passed the canonical leaf check
`lake --old env lean GaloisForLFunctions/ArithmeticGaugeTheory/TheBaireGenericExponentIsOne.lean`.
Each transitive axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
The module is imported by `ArithmeticGaugeTheory.lean`. Γ1 remains Open.

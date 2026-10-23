# Exact conductor of an affine progression

- **ID:** goldbach-affine-progression-conductor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), known algebraic support result
- **Parent:** [signed-affine audit](../../1-in-progress/goldbach-signed-affine-dispersion-audit.md)
- **Statement:** The affine image of `r+mℤ` under `a↦ba-T` is
  `(br-T)+bmℤ`; its translation periods are exactly `bmℤ`.

## Scope and novelty

This is elementary arithmetic of cosets, not new scientific knowledge.
Its use here is to certify the full modulus in the second Vaughan step.
It supplies no cancellation, prime count, or proof of Goldbach. Neither
this known identity nor the cofactor classification is counted as novel
positive salvage of a failed analytic route. The broader route is active.

The local corpus was searched for affine progression substitution and
modulus products before checking mathlib. Retrieved affine-sieve root
counts do not supply the missing arithmetic cancellation theorem.
Mathlib's `Int.modEq_iff_dvd` identifies integer congruence with divisibility
of the difference; its source statement was checked directly.

## Complete paper proof

For arbitrary integers `b,m,r,T`, put `c=br-T` and

`S={b(r+mk)-T : k∈ℤ}`.

Distributivity gives `b(r+mk)-T=c+(bm)k`. Therefore `h∈S` if and only
if `h-c=(bm)k` for an integer `k`, which is precisely `bm | h-c`.
Equivalently, `h≡c (mod bm)`. Both implications use the same witness `k`.

Now fix any integer `δ`. If translation by `δ` preserves membership in
`S`, then `c∈S` implies `c+δ∈S`, and the first identity yields `bm | δ`.
Conversely, write `δ=(bm)j`. If `h=c+(bm)k`, then
`h+δ=c+(bm)(k+j)`. If `h+δ=c+(bm)k`, then
`h=c+(bm)(k-j)`. This proves membership equivalence in both directions.
When `bm=0`, the same argument says `S={c}` and its only period is zero;
no positivity or nonvanishing assumption was used.

Consequently the exact lattice step is `bm`, with positive generator
`|bm|` when nonzero. Keeping only `m` enlarges the progression unless
`bm | m`; it cannot be justified by describing `b` as fixed.

## Gates

- [x] Exact statement and dependency-closed paper proof.
- [x] Known mathematics identified; no scientific novelty claim.
- [x] Lean compilation and declaration axiom audit.
- [x] Own-area umbrella import.

## Lean certificate

`formal/GaloisForLFunctions/goldbach/AffineProgressionConductor.lean`:
unconditional integer parameters, with no analytic premise or nonzero
assumption. Checked 2026-10-23 with the single foreground command, from
`formal/`:

```sh
lake --old env lean GaloisForLFunctions/goldbach/AffineProgressionConductor.lean
```

Exit 0, no warnings. All three theorem closures were printed:

- `GaloisForLFunctions.Goldbach.mem_affineProgression_iff_dvd`: `[propext]`.
- `GaloisForLFunctions.Goldbach.mem_affineProgression_iff_modEq`: `[propext]`.
- `GaloisForLFunctions.Goldbach.affineProgression_period_iff`:
  `[propext, Quot.sound]`.

The leaf is imported by `goldbach/Main.lean`; no umbrella was compiled.
This certificate checks the arithmetic modulus identity. It supplies no
unproved analytic estimate to any Lean theorem.

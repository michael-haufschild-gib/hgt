# Littlewood Z3: two-regime shape (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletTwoRegimeBound.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `norm_dirichlet_partial_of_blockBound` :
  `‖∑_{Ico 1 (C·2^R)} n^{−1−It}‖ ≤ (1 + log(C−1)) + ∑_{r<R} b r`
  for any family `b` of per-block bounds above `C`.
- `norm_dirichlet_partial_two_regime` : same with split point `A·2^S`, blocks indexed by `Ico S R`:
  `‖∑_{Ico 1 (A·2^R)}‖ ≤ (1 + log(A·2^S − 1)) + ∑_{r ∈ Ico S R} b r`.

## Point worth remembering

The low blocks need **no telescoping**. Applying the harmonic bound once to the whole range below
the split point collapses head + low blocks into the single term `1 + log(A·2^S − 1)`: the head's
`log(A−1)` cancels against the lower endpoint of the trivial tail. The per-block trivial route
(`dirichlet_tail_dyadic_trivial_le`) is not needed for this purpose — it stays useful only when a
genuine block-by-block comparison is wanted (e.g. `norm_dirichlet_block_min_le`).

## The Littlewood estimate is now exactly

Choose the split point `A·2^S ≈ exp(log t/m)`, `m ≈ loglog t`; supply `b r` from
`dirichlet_block_saving_of_small_factorial` on the blocks above it; show
`1 + log t/m + ∑_{r ∈ Ico S R} b r ≤ C·log t/loglog t`.

## Lean notes

- `Finset.sum_Ico_eq_sum_range f m n : ∑_{Ico m n} f = ∑_{range (n−m)} f (m + ·)` — needs `.symm`
  to go from the `range` form the block assembly produces to the `Ico` form.
- `A * 2^S * 2^(j+1) = A * 2^(S+j+1)` needs `Nat.add_assoc` after `mul_assoc, ← pow_add`
  (`S + (j+1)` is not syntactically `S + j + 1` here).

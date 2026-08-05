# Littlewood L4b-i built: kuzminLandau_interval (2026-08-05)

Card: `littlewood-zero-free-region.md` (L1–L3 ✓, L4a ✓, L4b-i ✓).

`RHTower/Sieve/KuzminLandauInterval.lean` — wired, build 3273 jobs, axioms clean, zero
warnings, ONE compile iteration. `kuzminLandau_interval`: g with HasDerivAt g (g' x) x on
Icc x₀ (x₀+(M+1)), g' MonotoneOn, band m+δ ≤ g' ≤ m+1−δ (m : ℤ) ⟹
‖∑_{j≤M} e(g(x₀+j))‖ ≤ 3/(2δ)+1 uniformly in M.

Working recipe (reuse for L5-adjacent wrappers): `exists_hasDerivAt_eq_slope` per unit step
(slope denominator: finish `field_simp; ring`); increment monotonicity via TWO independent
obtains of MVT points + interlacing (ξ_j < x₀+j+1 < ξ_{j+1}) + MonotoneOn — no global
choice; integer phase shift φ j = g(x₀+j) − m·j with `Complex.exp_int_mul_two_pi_mul_I`;
ContinuousOn from HasDerivAt via `.continuousAt.continuousWithinAt`; membership plumbing via
`Set.mem_Icc_of_Ioo`, `Nat.cast_nonneg`, push_cast+linarith.

Remaining in L4b: (ii) monotone-fibre splitting lemma (fibres of monotone K : ℕ → ℤ on
range N are Ico-intervals; #image ≤ K(N−1)−K(0)+1); (iii) D2 assembly with region index
I(y) = ⌊y−δ⌋ + ⌊y+δ⌋ (even ⟺ band [m+δ, m+1−δ), odd ⟺ gap [m+1−δ, m+1+δ); gap fibres
counted by slope λ ≤ g'' at the fibre's integer endpoints — no measure theory). Design in
the L4b-i card entry + littlewood-l2-weyl-chain.md.

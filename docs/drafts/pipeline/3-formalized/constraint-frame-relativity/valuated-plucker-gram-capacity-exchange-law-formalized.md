# Valuated Plücker–Gram capacity exchange law — formalized

- **ID:** `cfr-valuated-plucker-gram-capacity-exchange-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `valuated-plucker-gram-capacity-exchange-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ValuatedPluckerGram` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.FrameFillingCapacity` | new |

Both wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.  A frame is a matrix
`T : Matrix (Fin r) (Fin n) R`; a *column selection* is a map `b : Fin r → Fin n` and
`frameMinor T b = det (T.submatrix id b)`.  Ordered selections replace `r`-subsets throughout: the
exchange relation then carries **no signs**, and every subset is counted `r!` times, which is
exactly the weight appearing in the Cauchy–Binet identity below.

Theorem 2.1(1) — the maximal-minor criterion, card item 1:

1. `frameMinor_ne_zero_iff` — a selection has nonzero minor exactly when the selected columns are
   linearly independent, so the nonzero minors index the bases of the column matroid.

Theorem 2.1(2) — the Plücker relation and the valuated exchange axiom, card `(4)`, `(14)`, `(15)`:

2. `det_updateCol_finsetSum` — linearity of the determinant along one column in a finite linear
   combination, proved by induction from `det_updateCol_add` and `det_updateCol_smul`.
3. `submatrix_update` — replacing one column of a selected submatrix is reselecting.
4. `plucker_exchange` — the **unconditional** Plücker exchange identity
   `p(c)·p(b) = ∑ⱼ p(c[j↦b i])·p(b[i↦c j])`.
   Proof: expand column `i` of `T_b` in the columns of `T_c` with the *Cramer vector*
   `λ = cramer(T_c, T_{·,b i})`; `mulVec_cramer` gives `∑ⱼ λⱼ T_{·,cⱼ} = p(c)·T_{·,b i}`, so
   multilinearity in that column produces `p(c)·p(b)` on one side and `∑ⱼ λⱼ p(b[i↦cⱼ])` on the
   other, while `cramer_apply` identifies `λⱼ = p(c[j↦b i])`.  No invertibility, no field, no
   choice of signs: it holds over any commutative ring.  This is card `(14)`.
5. `valuated_exchange` — card `(4)`: for any `Valuation K Γ`, some `j` satisfies
   `v(p b)·v(p c) ≤ v(p (b[i↦c j]))·v(p (c[j↦b i]))`, i.e. in additive convention
   `ω(b)+ω(c) ≥ ω(b[i↦c j])+ω(c[j↦b i])`.  Proved from step 4 by choosing a maximising `j` and
   applying `Valuation.map_sum_le`; this is card `(15)`.

Theorem 2.1(3) — the initial matroid at the event normal, card `(5)`:

6. `initial_exchange` — if `b` and `c` both attain the extremal value `M ≠ 0` of the minor profile,
   then so do both exchanged selections.  Proof: the exchange inequality sandwiches
   `M·M ≤ x·y ≤ x·M ≤ M·M`, and cancellation in `LinearOrderedCommGroupWithZero` forces `x = y = M`.
   This is exactly "the minimal-depth bases are the bases of the initial matroid", in its
   exchange-axiom form.

Theorem 2.1(4) — the valuation of the minor ideal, card `(6)`:

7. `valuation_integral_combination_le` — every integral combination `∑ a_b p_b` (all `v(a_b) ≤ 1`)
   of the maximal minors has value at most the extremal value of the generators.
8. `valuation_integral_combination_attained` — the extremal value is attained inside the ideal.
   Together: `ν I_r(T) = d`, the valuation of the ideal of maximal minors is the minimal depth.

Theorem 2.1(5) — Cauchy–Binet and the square law, card `(7)`–`(9)`:

9. `frameGram cj T = T · (T.map cj)ᵀ`, `frameGram_apply` — the Gram matrix relative to a
   coefficient ring homomorphism `cj` (the conjugation).
10. `frameMinor_eq_sum`, `map_frameMinor_eq_sum` — the Leibniz expansion of a minor and its
    conjugate.
11. `factorial_mul_det_frameGram` — card `(7)`, **Cauchy–Binet in ordered form**:
    `r! · det(T T*) = ∑_{f : Fin r → Fin n} p_f · cj(p_f)`.
    Proof: expand both minors by Leibniz, swap the sum over selections inside the product with
    `Finset.prod_univ_sum`, recognise the inner sum as a Gram entry, collapse the `τ`-sum into
    `det (G.submatrix σ id) = sign σ · det G` (`det_permute`, `det_transpose`), and use
    `(sign σ)² = 1` to leave `card (Perm (Fin r)) = r!` copies of `det G`.  Mathlib has no
    rectangular Cauchy–Binet; this supplies it.
12. `psConj` — coefficientwise conjugation of a complex power series, a ring homomorphism.
13. `coeff_lt_of_mul_psConj`, `coeff_two_mul_of_mul_psConj` — the Hermitian square of a series of
    depth `≥ d` vanishes below `2d` and has coefficient `|c|²` at `2d`.
14. `coeff_det_frameGram_lt`, `coeff_det_frameGram_two_mul` — card `(9)`: transported to the Gram
    determinant, `r! · coeff_{2d}(det G) = ∑_f |coeff_d(p_f)|²`, a manifestly nonnegative real.
15. `det_frameGram_depth` — card `(8)`: if the minimal depth `d` is attained by some selection,
    `det G` has all coefficients zero below `2d` and a nonzero coefficient at `2d`.  The depth
    doubles exactly; cancellation is impossible because the top coefficients are squared moduli.

Theorem 2.1(6)–(7) — filling energy and the spectral bound, card `(10)`–`(13)`:

16. `frameInner`, `frameNormSq` and their algebra (`frameInner_self`, `frameInner_conj`,
    `frameInner_add_left/right`, `frameNormSq_eq_zero`).
17. `frameInner_conjTranspose` — the adjoint identity `⟪x, T* z⟫ = ⟪T x, z⟫`.
18. `min_filling_energy` — card `(10)`, `(11)`: with `G = T T*` invertible,
    `x₀ = T* G⁻¹ y` solves `T x = y`, its energy is the Gram form `⟪y, G⁻¹ y⟫`, it minimises
    `‖x‖²` over all solutions, and it is the **unique** minimiser.  Proof by the exact Pythagoras
    splitting `‖x‖² = ‖x₀‖² + ‖x - x₀‖²`, whose cross terms vanish by the adjoint identity.
19. `least_ge_prod_div` — card `(13)`: if every eigenvalue lies in `(0, M]` then
    `det G = ∏ λ ≤ λ_{i₀} · M^{r-1}` for every index, in particular for the least one.  This is
    the precise statement that determinant magnitude bounds strict filling capacity only with an
    upper spectral bound.

Theorem 3.1 — positive capacity is a phase quotient, card `(16)`–`(17)`:

20. `frameGram_rephase` — card `(16)`: rephasing the columns by a unimodular `u`
    (`u_k · cj(u_k) = 1`) leaves every Gram entry, hence the whole Gram matrix, the filling
    energies of step 18, and the positive leading packet of step 14, fixed.
21. `frameMinor_rephase` — card `(17)`: every minor is multiplied by `∏_{i} u(b i)`.
22. `gram_erases_phase` — the two together: identical Gram data, different minor packet, so no map
    from unmarked Gram data recovers the phased or oriented Plücker packet.

Theorem 4.1 — cofinal strictness, card `(19)`–`(20)`:

23. `uniform_filling_iff` — card `(19)`: a positive uniform lower bound on the least singular
    values is equivalent to a uniform bound on the filling constants `s_min^{-2}`.
24. `diagonal_not_bounded_below` — card `(20)`: a diagonal frame with every entry nonzero but
    `|λ_j| → 0` has all finite restrictions onto and yet admits no uniform lower bound, so it is
    not bounded below.

Theorem 5.1 — two-axis independence, card items 1–3:

25. `depth_scalar_family` — `t·I_N` has minor `X^N`: all coefficients vanish below `N` and the
    coefficient at `N` is `1`, so its depth is exactly `N`.
26. `depth_constant_family` — `τ·I_N` has minor `τ^N` with nonzero constant coefficient, so its
    depth is `0` regardless of `N`.
27. `diagonal_strictness`, `diagonal_strictness_attained` — the exact Rayleigh bound of a positive
    real diagonal frame is its least entry, attained at a coordinate vector.
28. `depth_strictness_independent` — the capstone: same strictness with different depth, and
    unbounded-below strictness with the same depth, so neither axis determines the other.

## Verification

```
lake build GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ValuatedPluckerGram
lake build GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.FrameFillingCapacity
```

both build clean, no warnings.

```
#print axioms plucker_exchange
#print axioms valuated_exchange
#print axioms initial_exchange
#print axioms factorial_mul_det_frameGram
#print axioms det_frameGram_depth
#print axioms gram_erases_phase
#print axioms min_filling_energy
#print axioms depth_strictness_independent
#print axioms uniform_filling_iff
```

all report `[propext, Classical.choice, Quot.sound]` — no `sorry`, no project axiom.

## Scope

Two deliberate modelling choices, both strengthenings rather than weakenings:

- **Ordered selections instead of `r`-subsets.**  Every statement quantifies over all maps
  `Fin r → Fin n`.  The Plücker relation then has no sign bookkeeping and holds over an arbitrary
  commutative ring; the Cauchy–Binet identity acquires the exact weight `r!`, which is the number
  of orderings of each subset, and is stated over ℤ-torsion-free coefficients so no division is
  used.  Non-injective selections have zero minor and contribute nothing.
- **Power series instead of convergent Puiseux germs.**  Depth doubling and the positive leading
  packet are proved over `PowerSeries ℂ` with coefficientwise conjugation.  Only two properties of
  the coefficient ring are used — a discrete `ℕ`-valued order and a conjugation with
  `z · conj z ≥ 0` — so the argument is the card's, with the fixed ramification index `q` absorbed
  into the choice of uniformiser.

Card item 4 is formalized as the valuation statement `ν I_r(T) = d` (steps 7–8) rather than through
Fitting ideals: mathlib v4.32 has no Fitting-ideal API, and the identification
`Fitt₀(coker T) = I_r(T)` is the definition of the zeroth Fitting ideal of that presentation, not a
separate theorem.

The `ℓ²` closed-range half of card `(20)` is stated in its bounded-below form (step 24); the
equivalence "bounded below ⟺ closed range with trivial kernel" is standard operator theory and is
not part of the card's own novelty.

The card's own remaining gates (external paper integration) are outside the Lean scope.

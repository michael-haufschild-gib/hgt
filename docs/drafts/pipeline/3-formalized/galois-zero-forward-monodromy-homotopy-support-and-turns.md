# The forward monodromy group: homotopy invariance, finite support, the turn on the whole fibre

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Question:** review-1311 §2.19 question 1 (B193: the forward monodromy group; generators);
  §2.11 (whether the turn around a simple central collision moves one pair only).

`H_τ(z)` the heat family. A *forward path* is a continuous `γ : [0,1] → {Re τ > 0}` off the
branch times; `T_γ` its transport of zeros; `G₊(τ)` the group of the transports along forward
loops at `τ`. The *turn* around `τ₀` is the loop `τ₀ + r²e^{2πis}`. `Z_ρ(s)` are the sheets of
a collision `(τ₀, ζ)` of order `m`, `ρ` a root of the Hermite profile `Q_m`.

## Theorems

1. (Smooth part.) The set `S = {(τ, z) : H_τ(z) = 0, H_τ'(z) ≠ 0}` with the map `(τ, z) ↦ τ`
   is a local homeomorphism onto its image in `ℂ`, and it is separated.
2. (Homotopy invariance.) Let `F_u`, `u ∈ [0,1]`, be a continuous family of paths of times
   with common ends, and `w_u` a lift of `F_u` through simple zeros with `w_u(0) = z₀` for all
   `u`. Then `w_u(1) = w_0(1)` for all `u`. The paths may pass through branch times.
3. (Forward paths.) Two forward paths that are homotopic with fixed ends through forward
   times off the branch times have the same transport. A loop in a convex set of forward
   times without branch times has the trivial transport.
4. (The trap along a path.) Over a box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}`, `t₀ > 0`, there is `R` with:
   if a path of times in the box moves by at most `1/12` on parameter intervals of length
   `1/N`, a continuous family of zeros along it that starts at modulus `≥ R + N/2` moves by at
   most `N/2`.
5. (Far zeros return.) For a box and `N` there is `R` such that every loop in the box with the
   modulus of 4 transports every zero of modulus `≥ R` to itself.
6. (Finite support.) Every `σ ∈ G₊(τ)` moves finitely many zeros.
7. (The reflection.) Every fibre over a forward time off the branch times is infinite, and
   `r : z ↦ −z` is not an element of `G₊(τ)`.
8. (The turn on the whole fibre.) Let `Re τ₀ > 0`. There is `r₀ > 0` such that for
   `0 < r < r₀` and every zero `z` of `H_{τ₀+r²}`: the turn transports `z` to `z`, or
   `z = Z_ρ(r)` is a sheet of a collision `(τ₀, ζ)` of order `m ≥ 2` and the turn transports
   it to `Z_{−ρ}(r)`.
9. (Simple central collision.) Let `H_τ₀` have a zero of order two at `0` and no other
   multiple zero. For small `r` the turn exchanges one zero `w ≠ 0` with `−w` and fixes every
   other zero. For every base time `τ`, `G₊(τ)` then contains an element that exchanges one
   zero `p ≠ 0` with `−p` and fixes every other zero.

## Proof

1. Near a simple zero `(τ₀, z₀)` the zero set is the graph of a continuous `ζ(τ)`, and `z₀`
   has a disc in which `ζ(τ)` is the only zero of `H_τ`. `H'` is continuous on `ℂ²`, so
   `ζ(τ)` is simple for `τ` in an open set `W ∋ τ₀`. Chart: source
   `{(τ, z) ∈ S : τ ∈ W, z ∈ disc}`, target `W`, inverse `τ ↦ (τ, ζ(τ))`.
2. `g(s, u) = (F_u(s), w_u(s))` maps the square into `S`. It is continuous in `s` for each
   `u` and constant on `s = 0`. The lifting theorem for separated local homeomorphisms gives
   that `g` is continuous. `u ↦ g(1, u)` is continuous with constant projection `F_u(1)`;
   a local homeomorphism is locally injective, so the map is constant on the connected
   interval.
3. Over forward times off the branch times every zero lifts along every path and is simple
   (forward tameness). Apply 2. For a convex set contract the loop to its base point by
   straight lines.
4. The trap of forward tameness: while the time moves by `≤ 1/12`, a zero that starts at
   modulus `≥ R` moves by `≤ 1/2`. Induction on `k`: up to the parameter `k/N` the zero has
   moved by `≤ k/2`, so it is still at modulus `≥ R` and the trap applies on
   `[k/N, (k+1)/N]`.
5. The straight contraction `(1−u)γ(s) + uγ(0)` stays in the box (convex) and has the same
   modulus. Let `K = {‖z‖ ≥ R₁}`, `R₁` beyond the trap radius and the radius of simplicity
   of far zeros. By 4 a lift of a contraction loop that starts at `‖z₀‖ ≥ R₁ + N/2` stays in
   `K`. Continuation inside a closed set of simple zeros: the lift exists on `[0, 1]` or the
   zero escapes; escape is excluded over forward times. So every contraction loop carries a
   lift of `z₀` through simple zeros, and 2 gives `T_γ(z₀) = z₀`, the lift of the constant
   loop being constant.
6. A forward loop lies in a box and has a modulus `N` (uniform continuity). By 5 it fixes
   the zeros of modulus `≥ R`; the zeros of `H_τ` in a disc are finite in number.
7. `H_t` has infinitely many zeros for real `t > 0`: otherwise `H_t = P e^{Bz}` with a
   polynomial `P`, which does not tend to `0` along the real axis. Transport from the time
   `1/8` is a bijection of fibres. `r` moves every zero except `0`.
8. Three regions for small `r`. *Far:* the circle has diameter `≤ 1/12` and lies in a box, so
   5 with `N = 1` gives `R`. *Near a simple zero `ζ` of `H_τ₀`:* on a disc `D ∋ τ₀` of times
   the chart `f` of `ζ` is a continuous family of simple zeros, and the zeros of `H_τ` in a
   disc around `ζ` are `f(τ)`; the family `f` lifts the contraction of the circle inside `D`,
   so 2 gives `T(f(τ₀+r²)) = f(τ₀+r²)`. *Near a multiple zero `ζ`:* the zeros of
   `H_{τ₀+r²}` in a disc around `ζ` are the sheets, and the turn reflects them (theorem 8 of
   the card `galois-zero-forward-monodromy-group-and-conjugation`); the profile has finitely
   many roots, so one radius serves all sheets. *Rest:* `H_τ₀` has finitely many zeros in
   `‖z‖ ≤ R`; outside the discs around them `H_τ₀ ≠ 0` on a compact set, hence `H_τ ≠ 0`
   there for `τ` near `τ₀`.
9. By 8 a moved zero is a sheet of a collision of order `≥ 2` at `τ₀`, which is the central
   one of order two; `Q₂` has the roots `±√2`, and at the centre `Z_{−ρ} = −Z_ρ`. Conjugate
   the circle to the base time by a forward path.

## Formalization

- `GaloisTheoryOfZeros/TheTransportOfAZeroDependsOnlyOnTheHomotopyClass.lean`: `simpleZeros`,
  `simpleZeroTime`, `exists_simple_zero_chart`, `isLocalHomeomorph_simpleZeroTime`,
  `lift_end_eq_of_homotopy`, `contractPath`, `transports_self_of_contraction`,
  `transports_of_homotopy`, `transports_self_of_convex`.
- `GaloisTheoryOfZeros/EveryForwardMonodromyMovesFinitelyManyZeros.lean`:
  `exists_nat_forall_norm_sub_le`, `exists_forall_norm_sub_le_of_long_zero_path`,
  `exists_forall_transports_self_of_far`, `IsForwardPath.exists_box`,
  `finite_zeros_closedBall`, `finite_setOf_forwardMonodromy_ne`, `infinite_fibre`,
  `fibreNeg_not_mem_forwardMonodromy`; in `RHTower/DeBruijnNewmanStrictBound.lean`:
  `riemannHeat_zeros_infinite`.
- `GaloisTheoryOfZeros/TheTurnAroundABranchTimeMovesOnlyTheSheetsOfItsCollisions.lean`:
  `transports_self_of_section`, `eventually_turn_transports_self_of_far`,
  `eventually_turn_transports_self_of_simple`, `eventually_turn_transports_sheets`,
  `TurnAction`, `eventually_turnAction`, `exists_forall_turnAction`, `eventually_turn_flip`,
  `exists_mem_forwardMonodromy_flip_one_pair`.

## Open

- Generation of `G₊` by the conjugates of the turns, and with 8 the criterion "`G₊` preserves
  every pair iff no collision away from the centre exists at a forward time": card
  `galois-zero-turns-generate-the-forward-monodromy-group`.
- A collision away from the centre at a forward time (B193). A statement that uses only the
  heat equation and the symmetry cannot give it: `(τ−τ₀)^{ν/2} f(z/√(τ−τ₀))`, `f` an even
  solution of `f'' − (y/2)f' + (ν/2)f = 0`, has the sheets `z² = ρ_j²(τ−τ₀)` and no collision
  off the centre.
- A centre time that satisfies the hypothesis of 9: simplicity of a zero of the centre value
  together with the absence of another collision at that time.

# The turns of a proper forward monodromy group obey a parity law

- **ID:** gtz-parity-law-of-the-turns
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** programme card `gtz-galois-theory-of-zeros-programme.md`, question 1.
- **Statement:** `τ₀` a forward time, `k` the order of vanishing of the centre value
  `c(τ) = H_τ(0)` at `τ₀`, `T_r` the turn of radius `r²` around `τ₀`, acting on the zeros of
  `H_{τ₀+r²}`; `W(b)` the permutations of the zeros of `H_b` that commute with `z ↦ −z` and
  move finitely many zeros; `G₊(b)` the forward monodromy group.
  (A) for all small `r`, `T_r` exchanges every zero `z` with a zero `z'`, and `z' = −z` iff `z`
  is one of the `2k` sheets of the collision at the centre; exactly `2k` zeros are carried to
  their negatives; `T_r` is an involution of `G₊(τ₀ + r²)`;
  (B) let `G` be a group of permutations with a fixed-point-free involution `n`, such that
  `w₁ ∈ G` or `w₂ ∈ G` or `w₁w₂⁻¹ ∈ G` for all permutations of finite support commuting with
  `n`, without an exchange of two pairs, and with `ε = 0` if `G` contains the flips of single
  pairs, `ε = 1` if it contains none. An involution `σ` commuting with `n` with `N` moved
  points has `2a` points with `σx = nx`, `N = 2a + 4c`, and `σ ∈ G` iff `c + εa` is even;
  (C) if `G₊(b) ≠ W(b)` there is `ε ∈ {0, 1}` such that every involution of `G₊(b)` with `2a`
  flipped and `2a + 4c` moved zeros has `c + εa` even;
  (D) if `G₊(b) ≠ W(b)` there is `ε ∈ {0, 1}` such that for every forward `τ₀` and all small
  `r` the turn moves `M = 2k + 4c` zeros with `c + εk` even;
  (E) a forward time with `c(τ₀) ≠ 0` whose turns move, for arbitrarily small `r`, a number of
  zeros not divisible by `8` gives `G₊(b) = W(b)` for every `b`; every real time `t > 0` has
  `c(t) ≠ 0`;
  (F) if `G₊(b) ≠ W(b)`, `M mod 8` is one number `m ∈ {2, 6}` at all simple zeros of the centre
  value in the forward half-plane;
  (G) converse: `G₊(b) ≠ W(b)` iff there is `ε ∈ {0, 1}` with `c + εk` even at every forward
  time, and then `G₊(b)` is the kernel of `χ = sgn_pairs · sgn_zerosᵋ` on `W(b)`.
  (H) real collisions: off the branch times the nonreal zeros of `H_t` (`t > 0` real) number
  `4 Q(t)`, `Q` the first-quadrant zeros; if `G₊(b) ≠ W(b)` then `8 ∣ N(t)` for all `t > 0` and
  every real collision time `s > 0` has mass `Σ (m − m mod 2) ≡ 0 (mod 8)`; a real collision of
  mass `≢ 0 (mod 8)` gives `G₊(b) = W(b)`.

## Goal

Turn the last sign of the group of the zeros into a statement on the branch divisor: the
ramification `M = 2k + 4c` of the forward times. `G₊ = ker χ₂` forces `c` even everywhere,
`G₊ = ker χ₁χ₂` forces `c ≡ k`; any time that violates both gives `G₊ = W`.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean (axioms `propext, Classical.choice, Quot.sound`)

## Proof

(A) The zeros of `H_{τ₀+r²}` beyond a radius return under the turn. Near a simple zero of
`H_τ₀` the zero is a continuous section and returns. Near a multiple zero `ζ` of order `m` the
zeros are the sheets `Z_ρ(r) = ζ + r y_ρ(r)`, `ρ` a root of the Hermite profile `Q_m`, and the
turn carries `Z_ρ` to `Z_{−ρ}` and back. The rest of a large disc carries no zero for times
near `τ₀`. If `ζ ≠ 0` both sheets are within `‖ζ‖/2` of `ζ`, so `Z_{−ρ} ≠ −Z_ρ`. If `ζ = 0`,
`m = 2k` and `−Z_ρ(r) = Z_{−ρ}(r)` by the functional equation. Far zeros and zeros near simple
zeros are fixed and not `0`, so they are not flipped. The `2k` central sheets are distinct for
small `r` (`y_ρ(0) = ρ`), and `Q_{2k}` has `2k` roots. Transporting twice returns every zero,
so the element of `G₊(τ₀ + r²)` is an involution.

(B) Induct on `N`. `N = 0`: `σ = 1 ∈ G`, `a = c = 0`. Otherwise pick `z` with `σz ≠ z` and
`T = {z, σz, nz, nσz}`, which `σ` and `n` preserve. Let `τ = σ` on `T`, `1` off `T`, and
`σ' = 1` on `T`, `σ` off `T`; then `σ = σ'τ`, both are involutions commuting with `n`, and
`σ'` moves `N − |T|` points.
If `σz = nz`: `T = {z, nz}`, `τ` is the flip of the pair of `z`, the flipped points of `σ` are
those of `σ'` and `z, nz`. If `ε = 0`, `τ ∈ G` and `σ ∈ G ⟺ σ' ∈ G`; if `ε = 1`, `τ ∉ G`, and
index two gives `σ ∈ G ⟺ σ' ∉ G`. With `a = a' + 1`, `c = c'` the parity of `c + εa` follows.
If `σz ≠ nz`: `|T| = 4`, `τ` is the exchange of the pairs of `z` and `σz`, no point of `T` is
flipped, `τ ∉ G`, so `σ ∈ G ⟺ σ' ∉ G`; `a = a'`, `c = c' + 1`.
(Index two: if `τ ∉ G` and `σ' ∉ G` then `σ'τ⁻¹ = σ'τ ∈ G`; if `σ' ∈ G` and `σ'τ ∈ G` then
`τ ∈ G`.)

(C) `G₊(b)` has index at most two in `W(b)`, and if it contains an exchange it is `W(b)`. A
flip of a single pair is determined by its pair. `G₊(b)` is transitive on the zeros and its
elements commute with `z ↦ −z`, so the conjugate by `g ∈ G₊(b)` with `g a₀ = a` of the flip at
`a₀` is the flip at `a`: all flips lie in `G₊(b)` or none. Apply (B).

(D) By (A) the turn is an involution of `G₊(τ₀ + r²)` with `2k` flipped zeros. The transport
`φ` along a forward path to `b` commutes with `z ↦ −z`; `φ σ φ⁻¹ ∈ G₊(b)` is an involution with
the same numbers of flipped and moved zeros. (C) gives `M = 2a + 4c` with `2a = 2k`.

(G) A permutation of finite support has a sign `finSign` (the sign on any finite set containing
its support; independent of the set, multiplicative). The induced permutation of the pairs of a
signed permutation of finite support has finite support, so `sgn_pairs` is a character too. An
exchange `e` has `sgn_zeros(e) = 1`, `sgn_pairs(e) = −1`; a flip has `−1`, `1`. So `ker χ` is a
subgroup of index at most two without exchanges. A turn with `k` flips and `c` exchanges (an
involution, split as in (B)) has `χ = (−1)^{c + εk}`, so if the parity law holds every conjugated
turn lies in `ker χ`, and by generation `G₊ ≤ ker χ ≠ W`; with index at most two, `G₊ = ker χ`.

(H) Nonreal zeros at real times are simple off the branch times and none is imaginary; `−z` and
`z̄` split them into four equal quadrants. `Q` even (index two, quartet parity theorem) gives
`8 ∣ N`; `N` is constant up to the next collision time and jumps by the collision mass at each
real collision time (`N(s⁻) = N(s) + mass(s)`). ∎

(E) `k = 0`: `M = 4c` with `c` even. At a real time a zero of `c` would be a central collision,
and those have nonreal times. (F) `k = 1`: `M = 2 + 4c`, `c + ε` even, so `M ≡ 2 + 4ε (mod 8)`. ∎

## Lean

| Step | Module | Declaration |
|---|---|---|
| A | `EveryTurnIsAnInvolutionThatFlipsAsManyPairsAsTheOrderOfTheCentreValue` | `exists_isCollision_center_two_mul`, `IsCollision.eventually_turn_center_sheets`, `IsCollision.eventually_injOn_center_sheets`, `eventually_turn_center_sheet_or_exchange`, `eventually_turn_involution_flip_iff`, `eventually_ncard_turn_flipped`, `eventually_exists_turn_mem_forwardMonodromy` |
| B | `TheInvolutionsOfAProperForwardMonodromyGroupObeyAParityLaw` | `exists_split_involution`, `mem_iff_not_mem_of_eq_mul`, `exists_flips_exchanges_parity` |
| C | same | `flip_eq_of_spec`, `flip_mem_forwardMonodromy_of_flip_mem`, `exists_parity_of_not_mem_forwardMonodromy` |
| D | `TheTurnsOfAProperForwardMonodromyGroupObeyAParityLaw` | `ncard_permCongr`, `exists_turn_parity_of_not_mem_forwardMonodromy` |
| E | same | `mem_forwardMonodromy_of_frequently_not_dvd`, `complexHeat_ofReal_center_ne_zero`, `mem_forwardMonodromy_of_real_frequently_not_dvd` |
| F | same | `exists_forall_simple_centre_time_mod_eight` |
| H | `ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation` | `ncard_eq_two_mul_of_involution`, `nonrealZeroCount_eq_four_mul`, `exists_nonrealZeroCount_eq_right`, `eight_dvd_nonrealZeroCount`, `eight_dvd_collisionMass`, `mem_forwardMonodromy_of_not_eight_dvd_collisionMass` |
| G | `APermutationOfFiniteSupportHasAMultiplicativeSign`, `TheSignedPermutationsOfFiniteSupportHaveTwoSignCharacters`, `TheForwardMonodromyGroupIsProperExactlyWhenItsTurnsObeyOneParityLaw` | `finSign`, `finSign_mul`, `pairSign`, `pairSign_mul`, `signedCharacter`, `signedKernel`, `exchange_not_mem_signedKernel`, `flip_mem_signedKernel_iff`, `involution_mem_signedKernel_iff`, `forwardMonodromy_le_signedKernel_of_turn_parity`, `forwardMonodromy_eq_signedKernel_of_not_mem`, `exists_not_mem_forwardMonodromy_iff_exists_turn_parity` |

## Open

The value of the sign. With (G), `G₊ = W` needs one forward time with `c` odd and `k` even, or
two times violating the two laws. The known forward collisions lie in the saddle region; the
two-term model controls the zeros within `|az| ≤ 8` of the centre and the far zeros are simple,
but the zeros in between are not controlled at a model collision time, so the full turn there
(its `c`) is not known. The sign on the zeros of a loop is the parity of the number of centre
times it winds around (each turn contributes `(−1)^k`); the sign on the pairs has no known
holomorphic carrier. The ramification in terms of the collisions,
`M = Σ_ζ 2⌊m_ζ/2⌋` over the multiple zeros `ζ` of `H_τ₀`. The value of the sign: no forward
time is known at which all collisions are known.

## Log
- 2026-11-14 — proved and formalized
- 2026-11-14 — converse (G) proved and formalized

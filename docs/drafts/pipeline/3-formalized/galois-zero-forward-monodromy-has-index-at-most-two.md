# The forward monodromy group has index at most two in the signed permutations

- **ID:** gtz-index-at-most-two
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** programme card `gtz-galois-theory-of-zeros-programme.md`, question 1.
- **Statement:** `b` a forward time off the branch times; `W(b)` the permutations of the zeros
  of `H_b` that commute with `z ↦ −z` and move finitely many zeros; `G₊(b) ≤ W(b)` the
  forward monodromy group.
  (A) for `w₁, w₂ ∈ W(b)`: `w₁ ∈ G₊(b)` or `w₂ ∈ G₊(b)` or `w₁w₂⁻¹ ∈ G₊(b)` — index at most two;
  (B) `G₊(b)` is normal in `W(b)`;
  (C) for the exchange `e` of any two pairs and `w ∈ W(b)`: `w ∈ G₊(b)` or `we ∈ G₊(b)`;
  (D) if `G₊(b)` contains the exchange of two pairs then `G₊(b) = W(b)`;
  (E) at a real time `t > 0` no zero of `H_t` is imaginary, and conjugation of the zeros is the
  product of the exchanges of the two pairs of each quartet `{z, z̄, −z, −z̄}` of nonreal zeros;
  (F) if the number of quartets is odd at one real time `t > 0` off the branch times, then
  `G₊(b) = W(b)` for every `b`; if `G₊(b) ≠ W(b)`, the number of quartets is even at every such
  time.

## Goal

Determine the group of the zeros over the forward times up to one sign. Together with the
card `galois-zero-sign-of-the-zeros-on-the-forward-monodromy`: `G₊(b)` is `W(b)`, or the kernel
of the sign on the pairs `χ₂`, or the kernel of `χ₁χ₂` (`χ₁` the sign on the zeros); never the
kernel of `χ₁`.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean (axioms `propext, Classical.choice, Quot.sound`)

## Proof

`G = G₊(b)` contains every signed 3-cycle and every double flip, and (sign card) the flip `f_p`
of every single pair, or `f_p e_{aa'}` for all triples of pairs. Fix pairs `p₀, a, a'` and
`e = e_{aa'}`; let `w ∈ W(b)`.

1. *Off three pairs.* If `w` moves a zero `x` off the pairs of `p₀, a, a'`: when `wx = −x`
   multiply on the left by the double flip of the pairs of `x` and `p₀`; otherwise by the
   signed 3-cycle `wx → x → u → wx` with `u ∈ {p₀, a}` in a pair other than that of `wx`. Both
   lie in `G`, fix `x` afterwards, and fix every fixed point of `w` off the three pairs (`wx`
   is moved by `w`). The number of moved zeros off the three pairs drops; induct.
2. *On three pairs.* `w` now permutes the six zeros. If the pair of `wp₀` is not that of `p₀`,
   the signed 3-cycle `wp₀ → p₀ → u` (`u` the third pair) returns it. Then `w` maps the pairs
   of `a, a'` to themselves or exchanges them; in the second case replace `w` by `we`. Double
   flips with `p₀` make it the identity on the pairs of `a` and `a'`.
3. *One pair.* What is left is `1` or `f_{p₀}`. If `f_{p₀} ∈ G` it lies in `G`. If
   `f_{p₀}e ∈ G`, then `f_{p₀} = (f_{p₀}e)e` lies in `G` after one more `e` (`e² = 1`).

So `gw ∈ {1, f_{p₀}}` or `gwe ∈ {1, f_{p₀}}` for some `g ∈ G`, which gives (C). (A): if
`w₁, w₂ ∉ G` then `w₁e, w₂e ∈ G` and `w₁w₂⁻¹ = (w₁e)(w₂e)⁻¹`. (B): apply (A) to `wg` and `w`.
(D): `we ∈ G` and `e ∈ G` give `w ∈ G`.

(E) `H_t(iy) = ∫ Φ(x) e^{tx² − yx} dx > 0`. A nonreal zero `z` has `Re z ≠ 0`, so exactly one
of `z, z̄, −z, −z̄` lies in the open first quadrant; conjugation exchanges `z ↔ z̄`,
`−z ↔ −z̄` and fixes the real zeros. For a set `A` of first-quadrant zeros let `c_A` be
conjugation on the quartets of `A` and the identity elsewhere; `c_{A ∪ {a}} = c_A c_{{a}}`, and
`c_{{a}}` is the exchange of the pairs of `a` and `ā`.

(F) Conjugation `c_S` (`S` all first-quadrant zeros, finite since conjugation is an element of
`G₊(t)`) lies in `G₊(t)`. Suppose no `c_{{a}}` lies in `G₊(t)`. By induction on `|A|` and (A):
`c_A ∈ G₊(t)` iff `|A|` is even (if `c_A ∉ G` and `c_{{a}} ∉ G` then `c_A c_{{a}}⁻¹ ∈ G`; if
`c_A ∈ G` then `c_A c_{{a}} ∉ G`). So `|S|` is even. With `|S|` odd some `c_{{a}} ∈ G₊(t)`;
the transport along a forward path from `t` to `b` conjugates it to an exchange in `G₊(b)`,
and (D) applies. ∎

## Lean

| Step | Module | Declaration |
|---|---|---|
| 1 | `ASignedGroupWithTheEvenPermutationsAndAFlipUpToAnExchangeHasIndexAtMostTwo` | `IsWindowedSignedGroup.exists_mul_fix_off_three` |
| 2 | same | `IsWindowedSignedGroup.exists_mul_fix_off_one` |
| 3 | same | `IsWindowedSignedGroup.mem_or_mul_mem_of_fix_off_one`, `exists_pairExchange`, `pairExchange_mul_self` |
| abstract A–D | same | `IsWindowedSignedGroup.mem_or_mem_or_mul_inv_mem`, `.conj_mem`, `.mem_or_mul_mem`, `.mem_of_exchange_mem` |
| input | `TheForwardMonodromyGroupContainsTheFlipOfEveryPairUpToOneExchange` | `exists_pairCoordinate_forall_hasFlip_or_forall_hasFlipExchange` |
| A | `TheForwardMonodromyGroupHasIndexAtMostTwoInTheSignedPermutationsOfFiniteSupport` | `mem_forwardMonodromy_or_mem_or_mul_inv_mem` |
| B | same | `conj_mem_forwardMonodromy` |
| C | same | `mem_forwardMonodromy_or_mul_exchange_mem` |
| D | same | `mem_forwardMonodromy_of_exchange_mem` |
| E | `AnOddNumberOfQuartetsOfNonrealZerosAtARealTimeGivesEverySignedPermutation` | `re_ne_zero_of_complexHeat_ofReal_eq_zero`, `firstQuadrantZeros`, `quartetConj`, `quartetConj_insert`, `quartetConj_firstQuadrantZeros`, `quartetConj_singleton_exchange` |
| F | same | `quartetConj_mem_forwardMonodromy_iff_even`, `exists_quartetConj_singleton_mem_forwardMonodromy`, `mem_forwardMonodromy_of_odd_firstQuadrantZeros`, `even_ncard_firstQuadrantZeros` |

## Open

Which of the three groups: equivalently whether one exchange of two pairs lies in `G₊(b)`. A
forward branch time whose turn is an odd permutation of the pairs decides it, and so does a
real time with an odd number of quartets of nonreal zeros. Under RH conjugation is trivial at
every real time and (F) gives nothing.

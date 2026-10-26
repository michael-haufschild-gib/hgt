# An approximate functional equation determines the primes up to height ‖g‖₁^{-1/2}

- **ID:** approximate-functional-equation-determines-the-primes
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-2510/hard-obstacles-summary.md`, first milestone (6) ("a
  quantitative stability theorem for the theta law in a logarithmic norm") and §4.5 ("measuring how
  far a positive measure with an approximate law lies from integer counting in norms that see the
  logarithm of the transform"); walls ledger 14.12 (discrete Beurling systems ⇒ rational primes).
- **Statement.** Let `B` be a countable Beurling system with `Σ_x |x|^{−3/2} < ∞` whose zeta
  function satisfies the hypotheses of `positive-measures-approximate-functional-equation` with
  critical-line defect `g`; put `M = ‖g‖₁`, `ρ = √(3πM/2)`. If `N ≥ 4` and `400 N² M ≤ 1`:
  1. every generalized integer `x` satisfies `|x| − round|x|| ≤ ρ|x|`;
  2. each `1 ≤ m ≤ N − 2` is within `1/8` of exactly one generalized integer;
  3. there is a bijection from the Beurling primes of norm `< N − 3/2` onto the rational primes
     `≤ N − 2`, moving each prime by at most `ρN`.
  The prime data — the logarithm of the integer data — are fixed by the defect up to height
  `≍ M^{−1/2}`; `M → 0` recovers the exact rigidity `beurlingSystem_rigidity_of_theta_relation`.

## Lean
`GaloisForLFunctions.ArithmeticPositiveDuality.beurling_primes_of_critical_line_defect`
(`formal/GaloisForLFunctions/ArithmeticPositiveDuality/ApproximateFunctionalEquationDeterminesThePrimes.lean`),
with `abs_sub_round_le_of_sinc_sq_le`, `eq_zero_of_round_intNorm_eq_one`, `round_intNorm_add`,
`unitTent_le_indicator`, `cnt_eq_one_of_tent`, `tentConst_le_eight`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`. Wired into `ArithmeticPositiveDuality.lean`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof
1. Atoms. `|sin πu| ≥ 2|u − round u|` (Jordan), so an atom of norm `u` with
   `sinc²(πu) ≤ ∫ sinc² dν ≤ (6/π)M` has `|u − round u| ≤ ρu`. With `400N²M ≤ 1`, `Nρ ≤ 1/8`.
2. No prime near 1. A label `p` with `1 < |p| ≤ 9/8` has a first power `|p|^j ≥ 3/2`, and then
   `|p|^j < 27/16`; that atom is `≥ 5/16` from the integers. So only the empty integer rounds to 1.
3. Counts. Every tent mass at `1 ≤ n ≤ N − 1` is `2Re β` up to `KM ≤ 8M ≤ 1/16`
   (`K = 18/π + 4κ/π²`, `κ ≤ 4` by `Γ(1/4) = 4Γ(5/4) ≤ 4`). With atoms within `1/8` of integers,
   `(7/8)c_n ≤ τ_n ≤ c_n + (c_{n−1} + c_{n+1})/8`, `c₀ = 0`, `c₁ = 1`, `τ₁ ≥ 1`. Hence
   `c₂ ≤ 1`, `2Re β ≤ 9/8 + KM`, every `c_m ≤ 1` (`m ≤ N − 1`) and every `c_m ≥ 1` (`m ≤ N − 2`).
4. Multiplicativity. For generalized integers with `|x + y| ≤ N`,
   `|XY − round X·round Y| ≤ ρXY(2 + ρ)` and `|XY − round XY| ≤ ρXY`, total `< 1`, so
   `round(XY) = round X · round Y`.
5. Primes. A label rounding to `r ≤ N − 2` has `r ≥ 2`; a factorization `r = mk` gives atoms
   `y_m + y_k` of norm `≤ N` rounding to `r`, which by uniqueness equal the singleton — impossible
   by cardinality. A rational prime `q ≤ N − 2` is the round of a unique atom; a nontrivial split
   of that atom would factor `q`. Injectivity is uniqueness at each round.

# The norm index inequality

- **ID:** agz-norm-index-inequality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1211/obstacles-summary.md §2.14 question 4 (A154); gate G4 of
  `agz-artin-reciprocity-law`
- **Statement:** Let `L/K` be an extension of number fields, `𝔪` a modulus of `K`,
  `π : Cl_𝔪 → Q` a homomorphism onto a finite abelian group with `π[P ∩ K] = 1` for every prime
  `P` of `L` with `N(P) = N(P ∩ K)` and `P ∩ K` prime to `𝔪`. Then `|Q| ≤ [L : K]`.

  For `Q = I^𝔪 / P_𝔪 N(I_L^𝔪)`: `[I^𝔪 : P_𝔪 N(I_L^𝔪)] ≤ [L : K]`. `L/K` need not be Galois.

## Goal
The analytic half of the index equality `[I^𝔪 : P_𝔪 N(I_L^𝔪)] = [L : K]` for cyclic `L/K`, on
which the reciprocity law rests.

## Gates
- [x] N1 the primes with `π[v] = 1` have Mertens sum `≤ (log x + O(1)) / |Q|`
- [x] N2 the degree-one primes of `L` are carried by the primes of `K` below them, at most
  `[L : K]` to one
- [x] N3 the inequality

## Approach
`w(𝔞) = log N(𝔞) / N(𝔞)`.

**N1.** For a character `χ` of `Q`, `ψ_χ = χ ∘ π` is a ray class character, `ψ_χ ≠ 1` for
`χ ≠ 1` (`π` is onto). For an integral ideal `𝔞` prime to `𝔪`,
`Σ_χ ψ_χ(𝔞) = |Q|` if `π[𝔞] = 1` and `0` otherwise; for `𝔞` not prime to `𝔪` every `ψ_χ(𝔞) = 0`.
So `Σ_χ Σ_{N(v) ≤ x} ψ_χ(v) w(v) = |Q| · S(x)`, `S(x) = Σ_{N(v) ≤ x, π[v] = 1} w(v)`. The Mertens
sum of `ψ_1` is `log x + O(1)` and that of `ψ_χ`, `χ ≠ 1`, is `O(1)`
(`exists_norm_heckePrimeMertensSum_one_sub_log_le`, `exists_norm_heckePrimeMertensSum_le`).
Hence `|Q| S(x) ≤ log x + B`. ∎

**N2.** Let `P` be a prime of `L` with `N(P) = p` prime, `v = P ∩ K`. `N(P) = N(v)^f` gives
`N(v) = p`. At most `[L : K]` primes of `L` lie above `v` (`Σ e f = [L : K]`). So
`#{P : N(P) = p} ≤ [L : K] · #{v : N(v) = p, v below a prime of the same norm}`, and
`D_L(x) = Σ_{p ≤ x} #{P : N(P) = p} log p / p ≤ [L : K] · S'(x)`, with `S'(x)` the sum of `w(v)`
over the primes `v` of `K`, `N(v) ≤ x`, below a prime of `L` of the same norm. ∎

**N3.** A prime `v` in `S'` is prime to `𝔪`, and then `π[v] = 1` by hypothesis, or it divides
`𝔪₀`; the latter have `N(v) ≤ N(𝔪₀)`: `S'(x) ≤ S(x) + c`. With `D_L(x) = log x + O(1)`
(`exists_abs_degreeOneMertens_sub_log_le`), `n = [L : K]`, `q = |Q|`:
`log x − C ≤ n (S(x) + c)`, `q S(x) ≤ log x + B`, so `(q − n) log x ≤ qC + nB + nqc` for all
`x ≥ 2`. Hence `q ≤ n`. ∎

## Lean
`formal/GaloisForLFunctions/RHTower/Artin/RayClassesBelowDegreeOnePrimesHaveIndexAtMostTheDegree.lean`:
`mertensWeight`, `ClassTrivial`, `classMertensSum`, `sum_heckeValue_comp`,
`sum_heckePrimeMertensSum_comp`, `exists_card_mul_classMertensSum_le` (N1); `IsBelowDegreeOne`,
`degreeOneBelowMertensSum`, `card_filter_under_eq_le_finrank`,
`absNorm_under_eq_of_absNorm_eq_prime`, `degreeOneCount_le_finrank_mul_card`,
`degreeOneMertens_le_finrank_mul` (N2); `mertens_chain_le`, `degreeOneBelowMertensSum_le`,
`card_le_finrank_of_forall_degreeOne_eq_one` (N3).

## Log
- 2026-11-13 — N1–N3 proved and formalized

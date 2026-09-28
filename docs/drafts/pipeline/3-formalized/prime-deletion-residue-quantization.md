# Prime-deletion residue quantization (a rigorous instance of discrete multiplicative uncertainty)

- **ID:** `MC-DMU-DELETION-QUANTIZATION`
- **Stage:** 3-formalized
- **Route:** MC side question: discrete multiplicative uncertainty (DMU, loop cycle 22)
- **Lean:** `GaloisForLFunctions.RHTower.PrimeDeletionResidueQuantization` (axioms: propext, Classical.choice, Quot.sound)

## Theorem (`residue_quantization_complex`; the real case is `residue_quantization`)
Setup:
- `Q ⊆ ℕ` is any set, and `S` is the set of positive integers with no prime factor in `Q`.
- `N_Q(x) = #S∩[1,x]`.
- `ψ_Q(x) = Σ_{n≤x} Λ(n)·[n is a power of a prime in Q]`.

Hypotheses:
- `N_Q(x) = a x + O(x^θ)` with `θ ≥ 0`.
- `ψ_Q(x) = Σ_{ρ∈J} c_ρ x^ρ + O(x^η)` for a finite set `J` of complex exponents.

Conclusion: `ρ c_ρ ∈ ℕ` for every `ρ ∈ J` with `Re ρ > max(θ,η)` and `(ρ−1)ζ(ρ) ≠ 0`. For real `ρ ∈ (max(θ,η), 1)` the nonvanishing condition is automatic.

**Complex corollary** (`not_isBigO_qFreeCount_of_odd_charge`). Suppose a deletion imitates a zero of odd multiplicity `λ` at `ρ`, so that `ψ_Q ∋ (λ/ρ)x^{ρ/2}`, and `ζ(ρ/2) ≠ 0`. Then `β ≥ Re ρ/2`.
- An off-line imitated zero is compatible with DMU-violating integer regularity only if the imitation has even multiplicity, or if `ζ` vanishes at `ρ/2`.
- The second option needs a zero with real part `< ½`, i.e. RH false.
- This parity condition parallels the sub-orthogonality multiplicity law `2·order ≤ k+1`.

**Corollary** (`not_isBigO_qFreeCount_of_odd`). Suppose `ψ_Q(x) = (λ/κ)(x^κ + x^{κ/2}) + O(x^η)` with `λ` odd, `η < κ/2` and `0 < κ < 1`. Then `N_Q(x) − a x ≠ O(x^θ)` for every `θ < κ/2`.

## Proof
1. On `Re s > 1` put `F = L(1_S)/ζ`. Complete multiplicativity gives `(1_S Λ) ⋆ 1_S = log·1_S`, and together with `ζ' = −ζ L(Λ)` this yields `F' = F·L(Λ_Q)`.
2. The counting hypothesis continues `L(1_S) − aζ = s∫_1^∞(N_Q(t) − a⌊t⌋)t^{−s−1}dt` to `Re s > θ`. Dividing by the entire function `(s−1)ζ(s)` continues `F`.
3. The Chebyshev expansion continues `L(Λ_Q) = s(Σ c_ρ/(s−ρ) + ∫R t^{−s−1})` to `Re s > η`, with residue `ρc_ρ` at `ρ`.
4. Clear the denominators: `(Num'·Z − Num·Z')·Π(s−ρ) = Num·Z·[Π(s−ρ)L(Λ_Q)]`. Both sides are analytic on the convex half-plane `Re s > max(θ,η)`.
5. The identity theorem carries the identity from `Re s ≫ 1` across the whole half-plane. No zero-free region of ζ is used.
6. `F(real) > 0`, so `F ≢ 0`. At `ρ₀`, write `F = (s−ρ₀)^m u` with `u(ρ₀) ≠ 0`. Comparing leading terms gives `m = ρ₀c_{ρ₀}`.

## Meaning for DMU (paper, `Θ ≤ max(½, 2β)`)
- **Odd λ.** Deleting primes with counting `λ∫^x t^{κ−1}dt/log t + O(x^{η'})`, `η' < κ/2`, gives the corollary's ψ-shape. The `x^{κ/2}` term comes from the squares of the deleted primes.
  - For odd λ this forces `β(ℙ∖Q) ≥ κ/2`, while `α(ℙ∖Q) ≥ κ` unconditionally. So `2β ≥ α`: the DMU line, with no loss.
  - Under RH, DMU holds on this whole family. DMU(ℕ) = RH implies DMU(ℙ∖Q).
- **Riemann's correction is forced.** Any `Q`-free set whose count has a power saving below `x^{κ/2}` must carry the `−½·li(x^{κ/2})`-type correction in its deleted-prime count. This is the deletion-relative form of Riemann's `R(x)`.
- **Even λ (open).** The branch points move to `κ/k` with `k ∤ λ`. DMU there reduces to a Möbius uncertainty `γ(Q^κ) ≥ ½` for prime-realizable systems, which is Hilberdink–Neamah type. The random selection of Broucke's construction saturates the DMU line in heuristic.
- **Literature.** Broucke (arXiv 2309.01567) conjectures that every `[α,β]` with `max ≥ ½` exists. DMU contradicts that conjecture. The corollary shows that no odd-λ deletion construction can realize `β < α/2`.

## Concrete deletion sets (closed 2026-09-28)
`GaloisForLFunctions.RHTower.PrimeDeletionGreedyConstruction` (axioms: propext, Classical.choice, Quot.sound).
- **Greedy rule.** Delete the prime `p` iff the deleted mass stays at or below `p^κ/κ`. The resulting set satisfies `θ_Q(x) = x^κ/κ + O(x^{κ−1+α} + log x)` whenever the window bound `θ(y+L)−θ(y) ≥ (L−(y+L)^α)/c` holds (`greedy_deficit_eventually`, `greedy_theta_deficit_eventually`).
- **Prime-power splitting** (`deletedChebyshev_eq_sum_deletedTheta`) gives `ψ_Q(x) = (x^κ + x^{κ/2})/κ + O(x^η)` with `η < κ/2`, provided `α < 1 − κ/2` (`greedy_chebyshev_expansion`).
- **Window input.** The corpus `RHTower.Sieve.exists_theta_window_lower` (any `α > 0.701299`, `c = 8192`) is unconditional. It yields `exists_prime_deletion_half_dimension_uncertainty`: for every `κ ∈ (½, 2(1−0.701299)) = (½, 0.597402)` there is a set `Q` of primes such that
  - `ψ_Q = (x^κ+x^{κ/2})/κ + O(x^η)` with `η < κ/2`;
  - the `Q`-free integers have no power saving below `x^{κ/2}`.
- **Scope.** The window exponent is a parameter.
  - A count-form Huxley bound (`α = 7/12+ε`) extends the range to `κ < 5/6`.
  - Baker–Harman–Pintz (`α = 0.525`, lower bound `(9/100)x^{0.525}/log x`) extends it to `κ < 0.95`.
  - See `1-in-progress/baker-harman-pintz-prime-gaps.md`.

## Honest limits
- The mechanism (log-derivative residues are integers) is classical complex analysis. What is new is the DMU reading, the λ-parity dichotomy, and the deletion construction on the DMU line.

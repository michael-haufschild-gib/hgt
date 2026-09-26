# RH in the theta-power family holds exactly at integral exponent of the modular unit

- **ID:** theta-power-exceptional-set-integral-exponent (C7**)
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** 3-formalized/theta-power-transcendental-offline-zeros.md; theta-power-family-hardy-threshold (C7).
- **Statement:** With `g = η(τ/2)η(2τ)/η(τ)²` one has `h = θ₂⁴θ₄⁴/θ₃⁸ = 16 g²⁴` and
  `F_a = θ₃h^{a/4} = 2^a η(τ) g(τ)^{6a−2}`. Conjecture: for `a ∈ (0, 1/2)`, `Λ_a` has no zero with `0 < |Im w| < 1/2`
  only if `6a ∈ ℤ`, i.e. the RH-exceptional set `E` is contained in `{1/6, 1/3}` (where `Λ_a` is L(χ₂₄), L(χ₁₂)).

## Goal
Sharp form of C7: holomorphy at every cusp is irrelevant; RH in the family is equivalent to the exponent of the
modular unit being an integer (Euler product / congruence theta series by Serre–Stark). `E ∋ 1/3` ⟺ GRH-strip for χ₁₂,
so the unconditional content is `E ⊆ {1/6, 1/3}`.

## Proven (Lean)
- Every transcendental `a ∈ (0,1/2)` gives infinitely many zeros with `0 < Im w < 1/2`
  (`thetaPowerXiC_offline_zeros_infinite_of_transcendental`).
- `O = {a : ∃ zero with 0 < Im w < 1/2}` is open (`isOpen_thetaPowerOffLineSet`, via parameter domination
  `|F_a| ≤ |F_{a₁}| + |F_{a₂}|`, weighted-L¹ continuity of the axis tail, `Λ_a(0) > 0`, sphere domination).
- Hence `E = (0,1/2) ∖ O` is closed in `(0,1/2)`, countable, and consists of algebraic numbers
  (`countable_thetaPower_exceptional`, `thetaPower_exceptional_algebraic`).

## Open core
- Algebraic irrational `a`: `log(n + a/4)` may satisfy multiplicative relations in `ℚ(a)`; the Bohr closure is the
  character group of `⟨n + a/4⟩ ⊂ ℚ(a)^×`. Cassels' private-prime indices have density `> 1/2` but the coefficient
  mass `Σ|b_n|(n+α)^{-σ}` over them is not controlled by the coefficient-free inputs (Hecke bound, horocycle mass).
- Rational `a` with `6a ∉ ℤ`: `F_a = η g^k`, `k ∉ ℤ`, is expected to be noncongruence (unbounded denominators by
  Calegari–Dimitrov–Tang); frequencies are logs of integers in one progression; no Kronecker freedom beyond primes.
  Off-line zeros for Mellin transforms of noncongruence forms are not known in general.

## Gates
- [ ] 0 → 1  in-progress: attack idea for one algebraic irrational `a` (Cassels + mass on private primes)
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Log
- 2026-09-26 — created; η-form of the family; transcendental case, openness and countability of `E` in Lean.

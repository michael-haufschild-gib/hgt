# The arithmetic group acts on continued windows of zeros as heat monodromy

- **ID:** gtz-continued-windows-of-simple-zeros
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** programme card `gtz-galois-theory-of-zeros-programme.md`, problem 4 (specialization from forward times to the time `0`; review-1411 §2.19).
- **Statement:** (A) every zero `z₀` of `H_0` is the limit as `t → 0⁺` of zeros of `H_t`.
  (B) `s_i` (`i` in a finite type) zeros of ξ in distinct reflection pairs, `σ ∈ G`, centred
  coordinate `z(ρ) = (ρ − ½)(−i)`.
  There are `w_i, w'_i : ℝ → ℂ` with `w_i(t) → z(s_i)`, `w'_i(t) → z(σ s_i)` as `t → 0⁺`, and
  `t₀ > 0` such that for every real `0 < t < t₀` off the branch times, `w_i(t)`, `w'_i(t)` are
  zeros of `H_t` and some `g ∈ G₊(t)` has `g(w_i(t)) = w'_i(t)` for all `i`.

## Goal

The specialization asked by problem 4, on finite windows that may grow: the arithmetic action
is the limit at the time `0` of forward heat monodromies along the continuation of the zeros.
Combined with the no-go on whole fibres (card `galois-zero-arithmetic-group-versus-heat-monodromy.md`)
this is the exact extent of the comparison.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean (axioms `propext, Classical.choice, Quot.sound`)

## Proof

`H_0(z(ρ)) = ξ(ρ) = 0`. Every zero of `H_0` is a collision of some order `m ≥ 1`; the profile
`Q_m` has `m` roots; the Hermite sheet `Z(s)` of one root is continuous with `Z(0) = z₀` and
`H_{s²}(Z(s)) = 0`; `w(t) = Z(√t)`. Distinct points, not opposite (`z(1 − ρ) = −z(ρ)`, `z` injective), stay
so for small `t` by continuity, for finitely many pairs at once. `G₊(t)` moves finitely many
zeros in distinct pairs to any such zeros. ∎

## Lean

| Step | Module | Declaration |
|---|---|---|
| all | `TheArithmeticGroupActsOnContinuedWindowsOfZerosAsHeatMonodromy` | `complexHeat_zero_xiSpectralPointSupport`, `xiSpectralPointSupport_injective`, `exists_continuation_of_zero`, `exists_forwardMonodromy_eq_on_continued_window` |

(C) If continuations `w_ρ(t)` of all off-line zeros are, on one interval `0 < t < t₀`, nonreal
zeros of `H_t` and pairwise distinct, then only finitely many zeros are off the line: at `t₀/2`
they inject into the finite set of nonreal zeros of `H_{t₀/2}` (Ki–Kim–Lee). Lean:
`AUniformSpecializationOfTheOffLineZerosForcesThemToBeFinite.finite_offLine_of_uniform`.

## Open

Whether finitely many off-line zeros suffice for a uniform `t₀` (non-escape of all zeros near the
time `0`).

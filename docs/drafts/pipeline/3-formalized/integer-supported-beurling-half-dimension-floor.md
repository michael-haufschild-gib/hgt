# Integer-supported Beurling perturbations have integer error Ω(x^{κ/2−ε})

- **ID:** `MC-DMU-INTEGER-SUPPORTED-FLOOR`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, axiom-clean)
- **Source:** MC loop cycle 95 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`). It generalizes `3-formalized/regular-prime-deletion-square-root-floor.md` (cycles 89, 91) and replaces the refuted cycle-22 DMU conjecture (Malliavin 1961, cycle 94) with its correct form.

## Statement
Let `a : ℕ → ℝ` be the integer masses of a Beurling system of positive integers, with `|a n| ≤ 1` and `a 1 = 1`, and let `Λ − e` be the von Mangoldt function of its generators:
`(Λ − e) ⋆ a = a · log`, `|e n| ≤ log n`.

Suppose:
- every nonzero `e n` has `|e n| ≥ log 2`;
- `Σ_{n≤x} e n = Σ_{ρ∈J} c_ρ x^ρ + O(x^η)`, where `J ⊂ ℂ` is finite and `κ ∈ J` is real with `Re c_κ ≠ 0` (either sign);
- `Re ρ < κ ≤ 1` for `ρ ≠ κ`, and `0 ≤ η < κ/2`.

Then `Σ_{n≤x} a n − A x ≠ O(x^θ)` for every `θ < κ/2` and every `A`.

Lean: `RHTower.IntegerBeurling.not_isBigO_count_of_leading_chebyshev` (module `RHTower/PrimeDeletionSquareRootFloor.lean`; base definitions in `RHTower/IntegerBeurlingPerturbation.lean`). It depends only on propext, Classical.choice and Quot.sound.

## Instances
- **Deleted primes** `Q`: `a = 1_S`, `e = Λ_Q ≥ 0`. This is `PrimeDeletion.not_isBigO_qFreeCount_of_leading_chebyshev_complex`, with the real and multiplicity forms as corollaries.
- **Added integer generators** (e.g. composites): `e < 0` on the added generator powers.
- **Mixed modifications**, for any arithmetical semigroup `S ⊂ ℤ⁺` with unique factorization.
  - Here `a = 1_S` and `ℓ = Λ_G`, the generator von Mangoldt function.
  - `|e| ≤ log n` because a generator power `g^k = n` is unique.
  - `|e n| ∈ {0} ∪ [log 2, ∞)` because `e n` is `(1 − m)·log p` or `−log g`.

## Proof (the cycle-89 mechanism, sign-free)
1. `L(a)/ζ` has logarithmic derivative `L(e)` on `Re s > 1` (`deriv_LSeries_div_riemannZeta`).
2. The regular count continues `(s−1)L(a)`, and the expansion continues `L(e)`.
3. The Poisson–Jensen ceiling bounds the continued `L(e)` by `O(log t)` on `Re s = σ < κ/2` above the exponents (`exists_norm_pertLogDeriv_le_log`).
4. Gaussian window `W = u²` at height `T = u⁴`, linearized against the signed head `Σ_{n≤u} e(n) n^{−σ−it}` (`windowed_meanSquare_ge` for real coefficients of either sign). The off-diagonal terms are controlled by the `1/N` log-separation of distinct integers.
5. This caps `Σ_{n≤u} e(n)² n^{−2σ}` by `O(log² u)`.
6. On the other side, `e(n)² ≥ log 2·|e(n)|` and `Σ_{n≤N}|e n| ≥ |Σ_{n≤N} e n| ≥ ½|Re c_κ| N^κ`, so the head mass is `≫ N^{κ−2σ}`. Contradiction.

## Audit
- **Mechanism.** Hilberdink (J. Number Theory 112, 2005) and Broucke–Hilberdink: Borel–Carathéodory for `log ζ_B` plus a mean-square head.
- **Novelty.** The theorem holds with ζ's zeros present, handled by Poisson–Jensen with no zeta lower bounds. It holds for signed, integer-supported perturbations. The exponent is `κ/2`, the square root of the perturbation's dimension.
- **Atomic-noise dichotomy (the scientific content).**
  - The floor comes from integer atoms: each nonzero coefficient has full high-frequency content. Smooth (continuous) perturbations carry none, which is why Diamond–Montgomery–Vorhauer continuous systems escape it.
  - For ℕ itself, ζ's critical zeros cancel the primes' atomic noise, which is exactly `β_ℕ = 0 < ½`.
- **Malliavin.** Malliavin (Acta Math. 106, 1961, §6) constructs Beurling systems with `N = Ax + O(x^ε)` for all `ε` and a real zero near 1. His assertion that such systems exist inside ℤ⁺ is reported by Lagarias, 1997, p. 4.
  - By this theorem, such a ℤ⁺-supported system cannot be ℕ modified by a finite regular expansion: its zeta must have infinitely many new zeros.
- **Significance.** It is a rigorous law for all integer-supported modifications with finite expansions. It carries no information about ζ's zeros: `Z = ζ·exp(P)` is ζ-zero-blind.

## Log
- 2026-09-29 — created and formalized (MC loop cycle 95). Refactor: the three deletion modules are now general in `(a, e)`, and the deletion theorems are instances (no duplicated proofs).

## Sign asymmetry: added generators cost the full dimension (cycle 101)
- `RHTower.IntegerBeurling.summable_pertSeq_of_nonpos` (module `RHTower/IntegerBeurlingAddedGeneratorsFullDimension.lean`, axiom-clean). If `e ≤ 0` (generators only added) and the integer count is `A x + O(x^θ)`, then `Σ_n |e(n)| n^{−s}` converges for every `Re s > θ`. The added mass has dimension ≤ θ, not merely ≤ 2θ.
- Proof:
  1. With `c(n) = −e(n)/log n ≥ 0`, `L(a)/ζ = K·exp L(c)` on `Re s > 1`.
  2. The continued quotient `numerator/((s−1)ζ)/K` is analytic on `{Re s > θ, |Im s| < 4}`, where `(s−1)ζ` has no zeros; it equals `exp L(c)` right of the abscissa `k` of `c` and has real part ≥ 1 on real points.
  3. So `Re F(k) ≥ 1`, `log F` is analytic near `k` and agrees with `L(c)`.
  4. The corpus's local Landau transfer (`landau_local_summability_transfer`) then pushes summability below `k`, a contradiction unless `k ≤ θ`.
- Contrast: deletions (`e ≥ 0`) only give the ℓ² floor `κ/2`, since `exp(−P)` may vanish analytically at the abscissa while `exp(P)` cannot.

## Atomic-mass form (2026-09-29, MC loop cycle 104)
- `RHTower.IntegerBeurling.not_isBigO_count_of_frequently_abs_mass` (module `RHTower/IntegerBeurlingAtomicMassFloor.lean`, axioms propext, Classical.choice, Quot.sound).
  - Hypotheses: a finite expansion `Σ_{n≤x} e n = Σ_J c_ρ x^ρ + O(x^η)` with `Re ρ < 2`, and absolute mass `Σ_{n≤N}|e n| ≥ c₁N^κ` for infinitely many `N`.
  - Conclusion: `Σ_{n≤x} a n − Ax ≠ O(x^θ)` for `θ, η < κ/2`.
  - Not needed: no leading term, no condition on `c_κ`, no sign condition.
- Corollary `not_isBigO_count_of_frequently_abs_mass_of_isBigO` (`J = ∅`): if the signed Chebyshev function of the perturbation is `O(x^η)` and the count error is `O(x^θ)`, the ℓ¹ mass has dimension ≤ `2max(θ,η)`. Sign cancellation cannot hide integer atoms.
- The floor is `κ₁/2`, where `κ₁` is the ℓ¹ dimension; the signed leading exponent only bounds `κ₁` from below.
- Escape route: infinitely many zeros. The Gaussian integers `G = {2} ∪ {p,p : p≡1(4)} ∪ {p² : p≡3(4)}` give `N_G = πx/4 + O(x^{131/416})`, ℓ¹ dimension 1 and signed Chebyshev `ψ(x,χ₄) + O(√x)`. There the zeros of `L(s,χ₄)` cancel the atomic noise. Consistency check: with `J = ∅` and `η = Θ_{χ₄} ≥ ½` the floor holds, and Hardy's `Ω(x^{1/4})` for the circle problem is exactly `κ₁'/2` with `κ₁' = ½`.

## Literature audit (2026-09-29, MC loop cycle 109)
- Absolute prototype: Hilberdink–Neamah (Int. J. Number Theory 16 (2020) 1005–1011).
  - Setting: a discrete Beurling system with `Π = Li + O(x^{α+ε})`, `N = ρx + O(x^{β+ε})`, `M = O(x^{γ+ε})`.
  - Result: `Θ = max(α,β,γ) ≥ ½`, and at least two of the three exponents equal `Θ`.
  - Their conjecture: no `[½,½,0]` system exists.
  - Broucke–Vindas (arXiv 2102.08478) built `[0,½,½]` systems with real-number generalized primes and `π_P − Li = O(1)`. Their method needs support sequences much denser than ℤ, so it gives no integer-supported systems.
- What is new here: the relative, fractional-dimension form.
  - The perturbation of ℕ is integer-supported and may be signed.
  - The floor is `κ₁/2`, with `κ₁` the ℓ¹ dimension of `e`, measured against ζ as base. HN's absolute theorem only gives `½` for the whole system, which ℕ-perturbations satisfy trivially through ζ's own zeros.
- The absolute analogue "no integer system with θ_N, θ_M < ½" is contained in HN.

# Constituent Theory of the Zeros (CTZ)

Namespace `GaloisForLFunctions.ConstituentTheoryOfTheZeros`; umbrella
`ConstituentTheoryOfTheZeros.lean`. Specification: §2.11 of
[the review-1011 report](../../../docs/reports/review-1011/obstacles-summary.md).

*What the zero set of `ξ` does not contain.*

## 1. Motivation

Over a finite field the zeta function of a curve is `P(q^{−s})` divided by two trivial factors:
a Dirichlet polynomial in one base whose zeros are exactly the zeros of the completed zeta
function. The numerator is an arithmetic object with a finite expansion that shares all its zeros
with the function. It is a **constituent**, and every proof of the Riemann hypothesis for curves
works on it.

Over `ℤ` no object of this kind is known, and the theorems of the corpus that survive when
positivity, forms and operators are excluded are all statements about objects of this kind: a
bounded Dirichlet series whose zeros are zeros of `ξ` has them on the critical line, and no
Dirichlet polynomial has all its zeros among those of `ξ`. They locate no zero of `ξ`. They say
what the zero set of `ξ` does not contain.

CTZ makes this a field. It asks which functions with an arithmetic expansion can share zeros with
`ξ` — all of them, those in a half-plane, those in a strip, those in a box, those of a limit — and
it proves the answers pointwise, with no sign of a form and no operator. Two facts about `ℤ` do the
work: the deep zeros have density zero, and the fractional part jumps at every integer.

## 2. Objects

| Object | Meaning |
|---|---|
| Arithmetic expansion | `F(s) = Σ_i c_i a_i^s` with positive real scales `a_i` and `Σ ‖c_i‖ a_i^σ < ∞` on a set of real parts `σ`; a Dirichlet series is the case `a = 1/n` |
| Wiener class of a strip | the functions with an arithmetic expansion over positive rational scales, absolutely convergent on the closed strip `σ₁ ≤ Re s ≤ σ₂`; norm `Σ ‖c_q‖ max(q^{σ₁}, q^{σ₂})` |
| Constituent on a set `U` | a function `F ≢ 0`, holomorphic on `U`, every zero of which in `U` is a zero of `ξ`. `U` is the plane (exact), a half-plane `Re s > x` with `x < ½`, a strip about the critical line, or a box |
| Constituent up to finitely many zeros | all zeros in `U` but finitely many are zeros of `ξ` |
| Series of fractional parts | `g(u) = Σ_i b_i {a_i u}` (`InfiniteRankPurityTheory.fractSeries`); its Mellin transform at `−s` is `−(ζ(s)/s) Σ b_i a_i^s` |
| Merged weight at a scale | `w(t) = Σ_{a_i = t} b_i`: the total weight an expansion carries at the scale `t` |
| Logarithmic derivative | `G = F'/F`; `−(ζ/s)·G` is holomorphic where `F` is a constituent |
| Zero shifts | `RHTower.zetaZeroShiftSet ρ₀ r`: the shifts `τ` that carry a zero of `ζ` into the disc of radius `r` about `ρ₀ + iτ` |
| Box | `{x < Re s, |Im s| < H}` |
| Splitting, defect | `ξ = E + E^♯` with `E^♯(s) = conj E(1 − s̄)`; the defect is the zero divisor of `E` right of the line |

## 3. Language

- **Constituent**, **exact / on a half-plane / in a strip / in a box**: as in §2.
- **Pure** constituent: all its zeros in `U` lie on the critical line.
- **Trivial** constituent: one without zeros in `U`.
- **Factor**: an exact constituent.
- **Wiener class**: absolutely convergent expansion. **Bounded class**: bounded holomorphic with a
  Dirichlet series far to the right; the Wiener class of a half-plane is contained in its bounded
  class, and the bounded class of `Re s > x` is contained in the Wiener class of `Re s > x + ½`.
- **Recurrence**: an almost period carries a zero to a zero nearby. **Density**: the proportion of
  heights at which `ζ` has a zero near a given point off the line is zero.
- **Jump**: the discontinuity of a series of fractional parts at `u₀`, minus the weight of the
  indices with `a_i u₀ ∈ ℤ`.
- **Scale**: the positive real `a_i` of a term; scales `≤ 1` decay to the right, scales `≥ 1` to
  the left.
- **Sign-free**: no nonnegativity of a form, a kernel, a measure or a coefficient, and no operator,
  enters the proof.

## 4. Mechanisms

1. **Recurrence against density.** A zero of an almost periodic function recurs along a relatively
   dense thick set of heights. Off the line the heights at which `ζ` has a zero nearby have
   density zero. So a constituent in the bounded class is pure.
2. **The fractional part carries `ζ`.** `∫_0^∞ {u} u^{−s−1} du = −ζ(s)/s` on `0 < Re s < 1`; so
   `−(ζ(s)/s) Σ b_i a_i^s` is the Mellin transform of `Σ b_i {a_i u}` on every line of absolute
   convergence inside the strip.
3. **Gluing across a strip.** If the transforms of `g₊` on a right line and of `g₋` on a left line
   are one function, holomorphic and bounded between the lines, then `g₊ = g₋`.
4. **The jump law.** Equal functions have equal jumps: for every `u₀ > 0` the weight of the right
   indices with `a_i u₀ ∈ ℤ` equals the weight of the left indices with `q_j u₀ ∈ ℤ`.
5. **Möbius inversion at every scale.** The jump law at the points `1/(kt)`, `k ≥ 1`, and Möbius
   inversion over `k` give the equality of the merged weights at the scale `t`. No restriction on
   the scales of either side is needed.
6. **Wiener inversion on a strip.** A function of the Wiener class of a closed strip that is
   bounded below there has its inverse in the class: the characters of the Wiener algebra of the
   positive rationals with the weight `max(q^{σ₁}, q^{σ₂})` are the limits of the points of the
   strip (one real part for all primes; Kronecker for the phases).
7. **The analytic quotient.** `ζ·F'/F` is holomorphic where `ζ` vanishes at the zeros of `F`;
   between heights at which `F` is bounded below across the strip the maximum principle bounds it.
8. **Compactness in bounded length.** The Dirichlet polynomials of length `N` with bounded
   coefficients and two coefficients bounded below form a compact family closed under vertical
   translation; a statement about each member becomes uniform.
9. **The index law.** A defect of degree `κ` leaves at most `κ` zeros right of the line; the
   bound passes to locally uniform limits.

## 5. Questions

| # | Question | Source |
|---|---|---|
| Q1 | Do the zeros of `ζ` carry an almost periodic constituent: can a bounded Dirichlet series on `Re s > x`, `x < ½`, whose zeros there are zeros of `ξ`, have a zero? | B153 |
| Q2 | Partial common zeros: can a Dirichlet polynomial or series be a constituent in a strip about the line while it has other zeros outside the strip? | §1.5, not covered |
| Q3 | Up to which height can a Dirichlet polynomial of length `N` share zeros with `ξ`? | §2.11 |
| Q4 | Can a sequence of approximants be constituents in growing boxes? | §2.11 |
| Q5 | Which splittings have a defect certified by sizes in a height window? | §2.11 |
| Q6 | What replaces the carry-free digit calculus when the carry is a nonzero class? | §2.11 |
| Q7 | Is there a sign-free mechanism that acts on `ξ` itself? | §2.11, M4 |

## 6. Tools

| Tool | State |
|---|---|
| Recurrence of zeros of strip almost periodic functions; good heights | `InfiniteRankPurityTheory.exists_thick_zero_shifts_of_almostPeriodic`, `exists_good_heights_of_almostPeriodic` |
| Density zero of the zero shifts on both sides of the line | `InfiniteRankPurityTheory.exists_zetaZeroShiftSet_density_zero` |
| Series of fractional parts, their transforms and jumps; two functions with one transform | `InfiniteRankPurityTheory.fractSeries_eq`, `tsum_jump_eq`, `tsum_eq_of_tsum_dvd` |
| The jump law on a strip of any width about the line, with any scales on both sides | to build |
| Merged weights of the two sides agree at every scale; the expansion continues across the line | to build |
| The Wiener algebra of a strip over the positive rationals; its characters; Wiener's lemma | to build |
| A zero-free almost periodic function is bounded below on closed substrips | to build |
| Bohr's inequality: bounded on `Re s > x` gives absolute convergence on `Re s > x + ½` | to build |
| Uniform heights by compactness in bounded length | to build |
| One-sided inverse expansions of zero-free exponential polynomials | `InfiniteRankPurityTheory.hasSum_logWeight_of_zeroFree` |
| The index law and its semicontinuity | `InfiniteRankPurityTheory.hermiteBiehler_index_general`, `encard_zeros_le_of_tendstoLocallyUniformly` |

## 7. Pillar theorems

**Foundations (in `InfiniteRankPurityTheory`).**

| Theorem | Lean |
|---|---|
| A bounded Dirichlet series whose zeros in `Re s > x` are zeros of `ξ` has them on the critical line | `re_eq_half_of_zeros_subset_xi` |
| An exponential polynomial with real frequencies and at least two terms has infinitely many zeros that are not zeros of `ξ` | `infinite_zeros_not_xi_zeros` |
| Two-sided rigidity: scales `≤ 1` right of the line and `≥ 1` left of it force a constant | `eq_const_mul_riemannZeta_div` |

**Theorems of this programme.** Listed here as they are proved in Lean; the paper proofs are on
the card `docs/drafts/pipeline/1-in-progress/ctz-constituent-theory-of-the-zeros.md`.

## 8. Calibration

| Model | Reading |
|---|---|
| Curve over `𝔽_q` | `P(q^{−s})` is an exact pure constituent of its own completed zeta function; the fractional part of the base-`q` comb jumps only at the powers of `q` |
| `1 − 2^{½−s}` | its logarithmic derivative has the weight `−log 2` at the scale `1` on the left and `0` on the right: not a constituent in any strip about the line |
| Non-tempered pair `ξ(s + a) ξ(s − a)` | has every structure of `ξ` and its zeros off the line: a theorem that holds for it is not a theorem of the field |
| Exponential polynomials with frequencies in `ℓℤ`, `ℓ → 0` | `Π_ρ (1 − e^{−ℓ(s − ρ)})` over the zeros in a box is an exact constituent in the box: boxes alone constrain nothing without a bound on the length and the frequencies |

## 9. Traps

| Trap | Truth |
|---|---|
| The factor theorem needs the expansion left of the line to have scales `≥ 1` | Möbius inversion works at every scale; any absolutely convergent expansion on a left line will do |
| A series has no highest frequency, so no left expansion | left of the line its logarithmic derivative has a two-sided expansion over the positive rationals, by Wiener's lemma on a strip |
| Positions of zeros can exclude a constituent on the line | the gaps of the zeros of `ξ` tend to zero; every almost periodic pattern on the line is approximated by zeros |
| Purity of a constituent says where zeros of `ξ` are | it says where the zeros of the constituent are |
| Sharing zeros in a box is restrictive | not without bounds on length and frequencies (§8) |

## 10. Open research topics

- Q1 for the bounded class of a half-plane `Re s > x` with `0 ≤ x < ½` and no absolute convergence
  left of the line.
- Q3 with explicit heights; Q4 for Dirichlet polynomials of growing length.
- Q5, Q6, Q7.

## 11. Context

| Neighbour | Interface |
|---|---|
| InfiniteRankPurityTheory | the two pointwise theorems, the jump law, recurrence, the index law; CTZ continues its Q2 past polynomials |
| SignFreePurityMechanisms | the price of Frobenius lifts, separation by the height, the digit calculus of the Carlitz–Goss zeta function |
| ArithmeticOrientationTheory | the Wiener algebra `𝒲_σ` of a half-plane and its Wiener lemma; CTZ needs the algebra of a strip, over the group of positive rationals |
| HTGeometry, SquareRootThreshold | strip almost periodicity; Kronecker's theorem for the prime logarithms |
| RHTower | `ξ`, the Mellin transform of the fractional part, zero density, Bohr recurrence |

## 12. Success criteria and contributions

CTZ succeeds when each question of §5 has a theorem-level answer: a theorem, or a sharp boundary
with the exact statement that remains.

A **contribution** is unconditional and pointwise; uses no sign of a form and no operator; holds
for curve zeta functions, whose constituents are themselves; fails for the non-tempered pair; and
is not a restatement of a theorem of §7.

## 13. Big picture

The constraint "no positivity, no operator" leaves two pointwise mechanisms, and both act on
constituents. The field determines how far they reach: from polynomials to series, from the plane
to strips and boxes, from exact sharing to sharing in the limit. Its main conjecture is that no
bounded almost periodic function has a zero and all its zeros among those of `ξ`.

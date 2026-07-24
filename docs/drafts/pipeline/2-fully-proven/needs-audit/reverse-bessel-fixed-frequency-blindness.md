# Reverse-Bessel radial jets are blind to every fixed Euler frequency

- **ID:** reverse-bessel-fixed-frequency-blindness
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / growing-order route discriminator
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [ANALYTIC CONTENT FORMALIZED]`
- **Parent:** `squared-xi-radial-jet-reverse-bessel-source-alignment.md`
- **Statement:** After normalization by its constant coefficient, the order-`n` reverse-Bessel radial polynomial converges at every fixed nonnegative frequency to the exponential that exactly cancels the Euler damping; hence no finite set of primes can dominate the growing-order squared-Xi source.

## Theorem

Let

```text
b_(n,j) = (2*n-j)!/(2^(n-j)*(n-j)!*j!),
B_n(x)  = sum_(j=0)^n b_(n,j)*x^j.
```

For every `n>=0` and `x>=0`,

```text
B_n(x) = (1/n!) integral_0^infinity
           exp(-u) u^n (x+u/2)^n du.                    (1)
```

Moreover,

```text
0 <= exp(-x) B_n(x)/b_(n,0) <= 1,                       (2)
lim_(n->infinity) exp(-x) B_n(x)/b_(n,0) = 1            (3)
```

for every fixed `x>=0`.

Consequently, at any fixed `w>0` and any fixed integer `m>=2`,

```text
m^(-1/2-w) B_n(w log m)/b_(n,0) -> m^(-1/2).            (4)
```

## Proof `[PROVED HERE]`

Expand the last factor in `(1)` and integrate termwise.  The coefficient of
`x^j` is

```text
(1/n!) * choose(n,j) * 2^(-(n-j))
  * integral_0^infinity exp(-u) u^(2*n-j) du
= (2*n-j)!/(2^(n-j)*(n-j)!*j!)
= b_(n,j).
```

For the normalized coefficients, direct cancellation gives

```text
b_(n,j)/b_(n,0)
  = (1/j!) product_(r=0)^(j-1) 2*(n-r)/(2*n-r).         (5)
```

Every factor in the product lies in `[0,1]`, and for fixed `j` it tends to
one as `n->infinity`.  Therefore

```text
0 <= b_(n,j)/b_(n,0) <= 1/j!,
b_(n,j)/b_(n,0) -> 1/j!.
```

Extend the coefficient sequence by zero for `j>n`.  Dominated convergence
against `x^j/j!` yields

```text
B_n(x)/b_(n,0) -> sum_(j>=0) x^j/j! = exp(x),
```

and the same coefficient bound gives `B_n(x)/b_(n,0)<=exp(x)`.  This proves
`(2)`--`(3)`.  Substituting `x=w log m` in `(3)` and using
`m^(-w)=exp(-x)` gives `(4)`.

## RH-false route consequence

The normalized prime part of the squared-Xi jet is

```text
sum_(m>=2) Lambda(m) m^(-1/2-w)
  B_n(w log m)/b_(n,0).                                 (6)
```

Equation `(4)` shows that each fixed prime-power atom loses its Euler damping
as `n` grows.  The limiting fixed-frequency weights are
`Lambda(m)/sqrt(m)`, whose total mass is not summable.  Thus the limit cannot
be exchanged with the Euler sum: the mass necessarily escapes through a
prime window whose location grows with `n`.

This kills a least-prime or finite-prime growing-order argument.  It does not
kill the growing-order route itself.  A viable proof must obtain a uniform
moving-window comparison with the completed Gamma/polar source before taking
the order limit.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/ReverseBesselFixedFrequencyBlindness.lean` (namespace
`RHTower`), building on the parent card's formalized reverse-Bessel weights
`squaredRadialJetWeight` and its closed form. Formalized unconditionally:

- `reverseBesselPoly n x = ∑_{j=0}^n b(n,j) x^j` (`b = squaredRadialJetWeight`).
- The ratio recurrence `b(n,j+1)·(2n−j)·(j+1) = b(n,j)·2(n−j)` (`weight_ratio_rec_nat`), derived from
  the closed form, and the normalized-coefficient domination
  `weight_le_div (hj : j ≤ n) : (b(n,j):ℝ) ≤ (b(n,0):ℝ)/j!` — the exact content of `(5)`'s
  `b(n,j)/b(n,0) ≤ 1/j!` (integer form `weight_mul_factorial_le : b(n,j)·j! ≤ b(n,0)`).
- `reverseBesselPoly_div_le_exp (hx : 0 ≤ x) : reverseBesselPoly n x / b(n,0) ≤ exp x` — the upper
  bound half of `(2)`.
- `reverseBesselRatio_tendsto (j) : (b(n,j)/b(n,0)) → 1/j!` as `n → ∞` — the termwise limit, by
  induction on `j` from the ℝ ratio recurrence (per-step factor `2(n−j)/((2n−j)(j+1)) → 1/(j+1)`).
- `reverseBesselPoly_div_tendsto_exp (hx : 0 ≤ x) : B_n(x)/b(n,0) → exp x` — the fixed-frequency
  limit `(3)`, via mathlib's Tannery theorem `tendsto_tsum_of_dominated_convergence` dominated by
  `x^j/j!` against the exp series.
- `reverseBessel_fixed_frequency_blind (hw : 0 < w) (hm : 2 ≤ m) :`
  `m^{-1/2-w} · B_n(w log m)/b(n,0) → m^{-1/2}` — the Euler-frequency blindness `(4)`.

`#print axioms` on all of these: `propext`, `Classical.choice`, `Quot.sound` only.  The full
analytic content `(2)`–`(4)` is thus formalized; the integral representation `(1)` is an independent
alternative derivation of the coefficients (already available via the parent's closed form) and is
not needed.

## Gates

- [x] exact positive integral representation
- [x] normalized coefficient domination (Lean: `RHTower.weight_le_div`, `reverseBesselPoly_div_le_exp`)
- [x] fixed-frequency limit (Lean: `RHTower.reverseBesselPoly_div_tendsto_exp`,
  `reverseBessel_fixed_frequency_blind`)
- [x] finite-prime localization ruled out
- [ ] determine the moving prime-window scale uniformly in `n` and `w`
- [ ] compare that window with the cancellation-preserving completed source
- [ ] formalize only if the moving-window comparison becomes source-bearing


## Log

- 2026-07-24 -- Formalized the normalized-coefficient domination (`(5)`'s `b(n,j)/b(n,0) ≤ 1/j!`) and
  the exponential upper bound `B_n(x)/b(n,0) ≤ exp x` (upper half of `(2)`) in
  `RHTower.ReverseBesselFixedFrequencyBlindness`, reusing the parent card's reverse-Bessel closed
  form via the ratio recurrence. Axioms clean; module builds and is wired into the RHTower umbrella.
  Remaining: the `→ exp x` convergence `(3)` via Tannery (route recorded above).
- 2026-07-24 -- Completed Stage 2: formalized the fixed-frequency limit `(3)`
  `B_n(x)/b(n,0) → exp x` (`reverseBesselPoly_div_tendsto_exp`, via the termwise limit
  `reverseBesselRatio_tendsto` and mathlib's Tannery theorem) and the Euler-frequency blindness
  `(4)` (`reverseBessel_fixed_frequency_blind`). Full analytic content `(2)`–`(4)` now unconditional;
  axioms clean; module builds. Only the open moving-window comparison gates remain.

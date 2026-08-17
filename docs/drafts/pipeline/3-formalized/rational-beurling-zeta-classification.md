# Which rational functions are Beurling zeta functions

- **ID:** `RATIONAL-BEURLING-CLASSIFICATION-001`
- **Stage:** 3-formalized · **RH used:** no · **Computation used:** no
- **Lean:** unconditional, no hypotheses, no added axioms

## The classification

Let `R` be rational with `R(∞) = 1`, poles `p_1,…,p_n` and zeros `z_1,…,z_n` (multisets, closed
under conjugation).  Then `R` is the zeta function of a Beurling generalized prime system with
locally finite positive prime measure **iff**

```
   F(t) := ∑_{i} e^{p_i t} − ∑_{j} e^{z_j t}  ≥  0    for all t > 0.
```

*Proof.*  For a positive prime measure with logarithmic density `w`, `log ζ(s) = ∫_0^∞ e^{-st} w(t) dt`.
Frullani evaluates the Laplace transform of `(e^{at} − e^{bt})/t` as `Log(s−b) − Log(s−a)`, so a
rational target forces `w(t) = F(t)/t`, uniquely by injectivity of the Laplace transform.  Local
finiteness of the prime measure requires `∫_0^1 w < ∞`, which forces `#poles = #zeros` (otherwise
`|w| ≥ c/t`); positivity of the measure is exactly `F ≥ 0`. ∎

The equal-cardinality condition and the first-order condition `∑p_i ≥ ∑z_j` are
`abs_density_ge_of_count_ne` and `sum_pole_ge_sum_zero_of_nonneg`.  What remained was the inequality
`F ≥ 0` itself, a question about a difference of two exponential sums with equally many terms.  This
card settles the two natural guesses about it.

## 1. Power-sum dominance is sufficient

Expanding both exponential sums, the Taylor coefficients of `F` are the power-sum differences
`σ_k = ∑_i p_i^k − ∑_j z_j^k`.  Hence

**Theorem.**  If `σ_k ≥ 0` for every `k ≥ 0`, then `F ≥ 0` on `[0, ∞)`, so `R` is realizable.

Lean: `factorNumerator_nonneg_of_powerSum_le`, proved by exhibiting `F(t)` as the sum of the
termwise-nonnegative series `∑_k σ_k t^k / k!`.  This is the exact converse of the necessary
conditions: the first nonvanishing `σ_k` must be positive, and if *all* of them are nonnegative the
inequality holds.

## 2. Majorization is not necessary — and the gap is arithmetically real

The classical route to `∑ e^{p_i t} ≥ ∑ e^{z_j t}` is Karamata's inequality applied to the convex
function `x ↦ e^{xt}`, which requires the pole multiset to **majorize** the zero multiset.  That
condition is strictly stronger than realizability.

**Theorem.**  For poles `{3, 0, 0}` and zeros `{2, 2, −1}`, majorization fails at the second partial
sum (`3 + 0 < 2 + 2`), yet the exponential difference factors exactly:

```
   e^{3t} + 2 − 2e^{2t} − e^{−t}  =  (e^t − 1)^3 (e^t + 1) / e^t   ≥ 0     (t ≥ 0).
```

Lean: `exp_difference_factorization`, `exp_difference_nonneg`.  Substituting `x = e^t` turns the
inequality into `x^4 − 2x^3 + 2x − 1 = (x−1)^3(x+1) ≥ 0` for `x ≥ 1`; the identity is exact, so the
counterexample is unconditional rather than numerical.

Note also that `σ_1 = σ_2 = 0` here and `σ_3 = 12 > 0`: the configuration sits exactly on the
boundary of the first two necessary conditions and is saved by the third.  So no finite truncation
of the power-sum conditions is equivalent to realizability either.

**Arithmetic content.**  Rescaling `t ↦ t/3` moves the top pole to `s = 1`, giving a genuine Beurling
system: simple pole at `1` (a density), double pole at `0`, and **zeros at `2/3` (double) and
`−1/3`**.  Its zeta violates RH with `Re s = 2/3 > 1/2`, its integer-counting function is
`N(x) = ρ x + O(x^ε)` for every `ε > 0` since the only singularity off `s = 1` sits at the origin —
and its pole/zero configuration is **not** majorizing.  So the RH-violating systems built earlier in
this programme are not the majorizing ones; majorization is a proper sub-class.

## 3. Where this leaves the question

Realizability of a rational Euler factor is now bracketed exactly:

```
   majorization  ⟹  power-sum dominance  ⟹  F ≥ 0  ⟹  first nonvanishing σ_k > 0,
```

with the first implication strict by §2 and the last not reversible by any finite truncation.  The
remaining gap — a usable characterisation of `F ≥ 0` strictly between power-sum dominance and the
power-sum sign conditions — is a self-contained question about differences of exponential sums, and
by the classification it is *equivalent* to classifying the rational Beurling zeta functions, hence
to classifying which explicit zero configurations a generalized prime system can exhibit.

## 4. Lean

| result | theorem | module |
|---|---|---|
| exponential series with a real base | `hasSum_exp` | `RHTower/BeurlingRationalRealizability` |
| **power-sum dominance ⟹ realizable** | `factorNumerator_nonneg_of_powerSum_le` | same |
| **exact factorisation of the non-majorizing example** | `exp_difference_factorization` | same |
| the example is realizable | `exp_difference_nonneg` | same |
| balance (`#poles = #zeros`) | `abs_density_ge_of_count_ne` | `RHTower/BeurlingRationalFactorBalance` |
| trace (`∑p ≥ ∑z`) | `sum_pole_ge_sum_zero_of_nonneg` | same |

Wired into `GaloisForLFunctions.RHTower`; `lake build` green; axioms
`[propext, Classical.choice, Quot.sound]`.

## 5. Novelty (bounded audit)

Checked: Beurling (1937); Diamond–Montgomery–Vorhauer (2006); Zhang; Broucke–Debruyne–Vindas
(`arXiv:2004.11501`); Broucke–Debruyne–Révész (`arXiv:2309.01567`); Révész (Mathematika 2022);
Hilberdink–Lapidus; Kaczorowski–Perelli.  Explicit Beurling systems with rational zeta appear as
ad hoc examples throughout that literature, but the checked sources do not state the realizability
criterion as an inequality on exponential sums, do not identify the power-sum conditions as its
Taylor data, and do not record that majorization is strictly stronger than realizability.  Karamata's
inequality is classical and is used here only as the comparison point that the example defeats.

---

# Continuation: the decision criterion, and where it stops

Notation: merge the poles and zeros into distinct exponents `a_1 > … > a_m` with integer coefficients
`c_k` = (multiplicity as a pole) − (multiplicity as a zero), so `F(t) = ∑_k c_k e^{a_k t}` and
`∑_k c_k = 0`.  Let `V` = number of sign changes of `(c_1,…,c_m)`, and let `μ ≥ 1` be the order of
vanishing of `F` at `0`, i.e. `μ = min{k ≥ 1 : σ_k ≠ 0}`.

## 6. The criterion

**Theorem.**  If `V ≤ μ + 1` then

```
   F > 0 on (0,∞)   ⟺   c_1 > 0  and  σ_μ > 0.
```

*Proof.*  Substitute `x = e^t`, so `G(x) = ∑ c_k x^{a_k}` and the claim is `G > 0` on `(1,∞)`.
Laguerre's rule for exponential sums bounds the number of real zeros of `F`, with multiplicity, by
`V`.  The origin already carries multiplicity `μ`, so at most `V − μ ≤ 1` further real zeros exist,
i.e. at most one further root of `G` in `(0,1) ∪ (1,∞)`, and it is simple.

If `c_1 > 0` and `σ_μ > 0`, then `G > 0` just to the right of `1` (sign `σ_μ`) and `G > 0` near `+∞`
(sign `c_1`).  A single simple root in `(1,∞)` would force a sign change between those two regimes,
contradicting the agreement of the two signs; hence no root lies in `(1,∞)` and `G > 0` there.
Conversely `σ_μ ≤ 0` fails positivity near `1⁺` and `c_1 ≤ 0` fails it near `+∞`. ∎

So in the regime `V ≤ μ + 1` realizability is decided by **two sign checks** — the leading
coefficient and the first nonvanishing power sum — with no root-finding.  The two examples of §1–2
are the extremes: `{3,0,0}` against `{2,2,−1}` has `V = μ = 3`, and `{3,3,1,1,1,1}` against
`{2,2,2,2,2,0}` has `V = 3 = μ + 1` with

```
   2e^{3t} − 5e^{2t} + 4e^{t} − 1 = (e^t − 1)^2 (2e^t − 1) ≥ 0     (t ≥ 0),
```

whose extra simple root sits at `x = 1/2`, i.e. at `t = −log 2 < 0`, exactly where it does no harm.

## 7. Where the criterion stops, and why

For `V ≥ μ + 2` two or more further roots are permitted and they may sit in `(1,∞)` in a pair, so
the sign data at the two ends no longer determines the answer: `G` can dip and return.  Beyond that
regime realizability is genuinely a root-location question.  Two structural remarks bound what is
possible.

* **Commensurable exponents.**  If all `a_k` lie in `λℚ` then, after `x = e^{λt/q}`, `G` is an
  honest polynomial and `G ≥ 0` on `[1,∞)` is equivalent to a sums-of-squares certificate
  `G(1+v) = σ_0(v) + v σ_1(v)`.  Realizability is then a semidefinite condition, hence decidable.

* **Complex exponents.**  The arithmetically interesting case — an off-line zero pair `β ± iγ` —
  contributes `−2 e^{βt} cos(γ t)`, and Laguerre's rule does not apply: the coefficient sequence is
  no longer finite-sign-change data.  The condition becomes `R(t) ≥ 2 e^{βt} cos(γt)` for the real
  part `R`, which is *sufficient* in the `γ`-free form `R(t) ≥ 2e^{βt}` and *necessary* only on the
  peak set `(2π/γ)ℤ`.  This is why every RH-violating system built in this programme used the
  `γ`-free sufficient form: the sharp complex criterion is not a sign-change count.

## 8. Lean

`exists_iteratedDeriv_eq_zero_of_order` (`HTGeometry/IteratedRolleChain`): if `f` is smooth,
vanishes to order `μ` at the origin and again at some `s > 0`, then `f^{(μ)}` has a zero in `(0,s)`.
This is the multiplicity-carrying half of Rolle and the step by which an order-`μ` zero plus one
further zero becomes a genuine zero of a high derivative — the input Laguerre's bound is applied to.
Built, wired, axioms `[propext, Classical.choice, Quot.sound]`.

**Not formalized, and cited as classical:** Laguerre's rule for exponential sums (the number of real
zeros with multiplicity is at most the number of sign changes of the coefficient sequence; Laguerre
1883, Pólya–Szegő Part V, Ch. 1).  mathlib has no zero-counting-with-multiplicity for real analytic
functions, so formalizing it means building that notion first; the iterated-Rolle chain above is the
first component.  This is the identified next construction, not a gap in the mathematics.

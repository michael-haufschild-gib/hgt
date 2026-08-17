# The functional equation is blind to RH; positivity is what excludes the deformation

- **ID:** `FE-BLINDNESS-BALANCE-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / COMPLETION OF THE FIREWALL
- **Parent:** `beurling-zero-certification-barriers.md` §4
- **RH used:** no · **Computation used:** no
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN CERTIFIED] [NOT RH]`

## The pivot

The Beurling firewall isolated one input it could not test: the **functional equation**.  Every
counterexample it produced lacked one.  So the natural reading was "the functional equation is the
arithmetic content of RH".  This card tests that reading and finds it **half wrong**: the functional
equation on its own is as blind as the prime distribution.  What excludes the deformation is
positivity of the prime measure — and that exclusion is an exact, elementary criterion.

Kaczorowski–Perelli's degree-1 classification does not apply here: its axioms fix the frequencies to
be `n^{-s}` with the Ramanujan bound, whereas a Beurling system has arbitrary real frequencies.

## 1. The functional equation alone is blind

Fix `β ∈ (1/2, 1)` and set

```
h(s) = (s − β)(s − 1 + β),        h(1 − s) = h(s).
```

Then `ξ_β := h · ξ` is entire of order 1, real on the real axis, and satisfies **the same functional
equation** `ξ_β(s) = ξ_β(1 − s)` as the completed Riemann zeta, with the same Gamma factor and the
same growth.  Its zeros are those of `ξ` together with the **real pair `β`, `1 − β`, both off the
critical line**.

Hence no argument that uses only the functional equation, the order, and reality can prove RH: those
hypotheses are satisfied by `ξ_β`, for which RH is false.  This is the exact mirror of the firewall
statement on the prime side.

## 2. What excludes it: two realizability constraints

If a Euler factor `R(s) = ∏_i (s − p_i)^{-1} ∏_j (s − z_j)` is to come from a *positive* generalized
prime measure, then in the logarithmic coordinate the density is forced to be

```
w(t) = ( ∑_i e^{p_i t} − ∑_j e^{z_j t} ) / t
```

(each pole contributing `+e^{p t}/t`, each zero `−e^{z t}/t`, by the Frullani evaluation).  Two
constraints follow, and they are the entire obstruction.

**Balance.**  `w` must be integrable at the origin, since the prime measure is locally finite.  The
numerator is continuous with value `#poles − #zeros` at `t = 0`; if that is nonzero then
`|w(t)| ≥ c/t` on a right neighbourhood of `0`, which is not integrable.  So

```
#poles = #zeros  (with multiplicity).
```

Lean: `abs_density_ge_of_count_ne`.

**Trace.**  Given balance the numerator vanishes at `0`, so positivity `w ≥ 0` on `(0,∞)` forces its
derivative at `0` to be nonnegative:

```
∑_i p_i  ≥  ∑_j z_j.
```

Lean: `sum_pole_ge_sum_zero_of_nonneg`.

**Application.**  `h(s) = (s−β)(s−1+β)` has two zeros and no poles: `#poles − #zeros = −2 ≠ 0`.
Balance fails, so `h` is not the Euler factor of any positive generalized-prime measure, and `ξ_β` is
not the completed zeta of any Beurling system obtained from `ℤ` by adjoining primes.  Lean:
`symmetric_quadratic_factor_not_balanced`.

Note how the two constraints interact with the functional equation.  Symmetry about `Re s = 1/2`
forces zeros and poles into pairs `{s, 1−s}`, so **Trace** reads `∑ p_i = #poles/2 = #zeros/2 = ∑ z_j`
— equality, the boundary case.  A Beurling zeta has exactly one pole, at `s = 1`.  So a symmetric
rational deformation would have to supply its compensating poles somewhere other than `{1}`, which no
Beurling system provides.  **The functional equation and positivity are jointly rigid and separately
blind.**

## 3. The completed picture

| input | status |
|---|---|
| prime-counting data at any scale (reciprocal, Mertens, log-jet Grams) | blind — `rh-sensitivity-threshold-of-the-prime-measure` |
| integer-counting regularity at any power scale | blind — `regular-beurling-integers-do-not-constrain-the-zeros` |
| discreteness of the system | barred in all three construction regimes — `beurling-zero-certification-barriers` |
| functional equation + order + reality | **blind — this card §1** |
| functional equation **and** positive prime measure | jointly rigid — this card §2 |

So the arithmetic content of RH is not any one of these hypotheses but exactly their *conjunction*.
Every criterion that drops either half is provably incapable of deciding RH; every criterion that
keeps both is, by the degree-1 rigidity philosophy, a restatement of RH for `ζ` itself.  That is the
precise sense in which the four-card programme closes.

## 4. Lean

| result | theorem | module |
|---|---|---|
| imbalance forces a `1/t` singularity | `abs_density_ge_of_count_ne` | `RHTower/BeurlingRationalFactorBalance` |
| positivity forces the trace inequality | `sum_pole_ge_sum_zero_of_nonneg` | same |
| the symmetric quadratic factor is unrealizable | `symmetric_quadratic_factor_not_balanced` | same |

Built, wired into `GaloisForLFunctions.RHTower`, axioms `[propext, Classical.choice, Quot.sound]`.

## 5. Novelty (bounded audit)

Checked: Kaczorowski–Perelli, *On the structure of the Selberg class* I–VII (degree-1 classification,
integer frequencies + Ramanujan — inapplicable here); Hilberdink on `[α,β]`-systems; Broucke–Debruyne–
Révész `arXiv:2309.01567`; Révész, *Density estimates for the zeros of the Beurling ζ function*
(Mathematika 2022); Lapidus–van Frankenhuijsen fractal membranes (conjectural functional equations for
Beurling zetas).  §1's deformation is elementary and would be accepted on sight; what does not appear
in the checked sources is the pairing of it with §2's **Balance/Trace** criterion as an exact
realizability test, nor the resulting statement that the functional equation and positivity are
separately blind and jointly rigid.

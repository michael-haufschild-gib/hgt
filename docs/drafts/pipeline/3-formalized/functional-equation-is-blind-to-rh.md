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

The imbalance argument excludes this particular pure quadratic factor as a locally finite
positive adjunction. It does not establish rigidity for all rational deformations with compensating
poles. Continuous Beurling systems can have additional poles, as the explicit family in
`regular-beurling-integers-do-not-constrain-the-zeros` demonstrates. No general theorem combining
functional-equation symmetry and positive prime measure follows from this factor-balance test.

## 3. The completed picture

| input | status |
|---|---|
| specified reciprocal-weight observables in the positive-adjunction comparison | apply the exact hypotheses in `rh-sensitivity-threshold-of-the-prime-measure`; not an exclusion of all prime-counting data |
| selected integer-counting power bound in the continuous class | insufficient alone; model depends on exponent, counting estimate paper-only — `regular-beurling-integers-do-not-constrain-the-zeros` |
| discreteness of the system | barred in all three construction regimes — `beurling-zero-certification-barriers` |
| functional equation + order + reality | **blind — this card §1** |
| the specific unbalanced rational adjunction in §2 | excluded by coefficient balance; no general joint-rigidity theorem |

These examples test different sets of assumptions. They do not establish that the arithmetic
content of RH is exactly one conjunction, or exclude every criterion omitting one named feature.
For each proposed criterion, a countermodel must satisfy its full assumptions simultaneously;
continuous counterexamples cannot exclude criteria requiring additional discrete arithmetic data.

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

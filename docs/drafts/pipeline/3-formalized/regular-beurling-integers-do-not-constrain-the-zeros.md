# Regular generalized integers do not constrain the zeros

- **ID:** `BEURLING-REGULAR-INTEGERS-NO-CONSTRAINT-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / FIREWALL, and a retraction
- **Parent:** `rh-sensitivity-threshold-of-the-prime-measure.md` §6 (whose universal design rule is withdrawn)
- **RH used:** no · **Computation used:** no
- **Scientific status:** density positivity, rational transform and zero are Lean certified;
  the counting estimate in §2(b) is paper-only. Classical continuous Beurling construction;
  no novelty or RH proof claimed.

## One sentence

For each `β ∈ (1/2,1)`, `γ != 0` and selected `θ > 0`, there is a continuous positive-density
model with a genuine zeta zero at `β+iγ`; its paper counting estimate is `N(x)=ρx+O(x^θ)`.
The model depends on `θ`. This refutes sufficiency of that counting estimate in this continuous
class, not its necessity or usefulness in a proof with additional arithmetic hypotheses.
Ordinary integer counting is unconditionally `floor x=x+O(1)`; RH does not assert a bound for it.

## 1. The construction

Work in the logarithmic coordinate `t = log u`.  A positive density `w` on `(0,∞)` with
`∫_0^1 w < ∞` and `w(t) = O(e^{t}/t)` defines a Beurling prime measure `dΠ(u) = w(log u) du/u`
whose zeta is `ζ(s) = exp F(s)`, `F(s) = ∫_0^∞ e^{-st} w(t) dt`, convergent for `Re s > 1`.

Fix `β ∈ (1/2,1)`, `γ ≠ 0`, `δ ∈ (0, 1)`, and a positive integer `A`.  Put

```
w(t) = ( e^{t} + A e^{δ t} − (A − 1) − 2 e^{β t} cos(γ t) ) / t.
```

**Coefficient balance.**  The numerator at `t = 0` is `1 + A − (A−1) − 2 = 0`, so `w` is bounded
near the origin: the system is locally finite.  (This balance is exactly the statement that the
zeta function below has as many zeros as poles counted with multiplicity, hence tends to `1` at
`s = ∞`, as the Laplace transform of a locally finite counting measure with unit mass at the origin must.)

**Positivity.**  Since `cos ≤ 1`,

```
t · w(t) ≥ K(t) := e^{t} + A e^{δ t} − (A − 1) − 2 e^{β t},     K(0) = 0,
K'(t) = e^{t} + A δ e^{δ t} − 2 β e^{β t}.
```

Set `t₀ = log(2β)/(1−β) ≥ 0` (nonnegative because `β > 1/2`).  For `t ≥ t₀` one has
`e^{(1−β)t} ≥ 2β`, hence `e^{t} ≥ 2β e^{β t}` and `K'(t) ≥ 0`.  For `0 ≤ t ≤ t₀` one has
`2β e^{β t} ≤ 2β e^{β t₀} =: C` while `A δ e^{δ t} ≥ A δ`, so `K'(t) ≥ 0` as soon as `A δ ≥ C`,
i.e. as soon as

```
A ≥ ( 2 β e^{β log(2β)/(1−β)} ) / δ.
```

With such an `A`, `K' ≥ 0` on `[0,∞)`, hence `K ≥ K(0) = 0`, hence **`w ≥ 0` on `(0,∞)`**.

**The zeta function.**  Group the numerator as

```
( e^{t} − e^{(β+iγ)t} ) + ( e^{δ t} − e^{(β−iγ)t} ) + (A−1)( e^{δ t} − e^{0·t} ),
```

three Frullani integrands after division by `t`.  Using
`∫_0^∞ (e^{-at} − e^{-bt}) dt/t = Log b − Log a` for `Re a, Re b > 0`, with `Re s > 1`,

```
F(s) = [Log(s−β−iγ) − Log(s−1)] + [Log(s−β+iγ) − Log(s−δ)]
        + (A−1)[Log(s) − Log(s−δ)],
```

so that

```
ζ(s) = exp F(s) = ( (s−β)² + γ² ) · s^{A−1} / ( (s−1) · (s−δ)^A ).
```

## 2. What the system does

**(a) Zeros off the critical line.**  `ζ(β + iγ) = 0`, and the denominator
`(β+iγ−1)(β+iγ−δ)^A` is nonzero because its factors have imaginary part `γ ≠ 0`.  So `β ± iγ` are
genuine zeros, with `β > 1/2` arbitrary in `(1/2, 1)`.  **RH fails for this system, arbitrarily
badly.**

**(b) A counting bound at the selected exponent — paper only.** The rational function has
residue `ρ=((1−β)^2+γ^2)/(1−δ)^A > 0` at `1`. Partial fractions of `ζ(s)/s` give a counting
function of the form

```
N(x) = ρx + x^δ P(log x) + C,       deg P <= A-1,       x>=1.
```

Here a constant term can occur from the origin. For each `θ>δ`, the polynomial factor is
`O(x^(θ−δ))`, giving `N(x)=ρx+O(x^θ)`. Choosing `δ<θ` constructs a suitable model for each
requested exponent. The pole at the positive number `δ` prevents this argument from yielding all
positive error exponents for that one model. The Lean capstone has no counting-function clause.

A separate fixed-model repair with zeros `2/3±ig` and a quadratic logarithmic remainder is
tracked in `not_new_scientific_knowledge/continuous-beurling-logarithmic-error-audit.md`. It uses a different
rational function with compensating poles at zero; it does not change this theorem's quantifiers.

**(c) Prime and integer measures are distinct.** The continuous logarithmic-prime counting
measure here has `Π(x)=∫_0^(log x) w(t) dt`. No estimate for a discrete prime sequence `π(x)` is
proved by the Lean theorem. In particular, a discretization theorem cannot be inferred from the
rational transform alone.

## 3. Consequence and scope correction

The parent card's proposed universal requirement that an RH proof must control integer-counting
error at a specified scale was unsupported and remains withdrawn. These examples instead show
that the selected counting estimate is **insufficient by itself in the continuous class**.
A counterexample to sufficiency does not refute necessity. It also does not prove that every RH
proof must use exact integer occurrence, distributivity, or any particular combination of operations.

Before applying this obstruction, check every hypothesis of the proposed criterion against the
same model. These examples are continuous and assert no functional equation. They cannot exclude
a criterion using additional discrete or arithmetic hypotheses they fail to satisfy. The positive
adjunction problem in the parent card has its own assumptions; changing to an absolute continuous
system changes that comparison class.

## 4. Sharpness of the coefficient balance

Within the class of systems whose zeta is a ratio of finitely many linear factors, the balance
`#zeros = #poles` at `t = 0` is forced by local finiteness (`∫_0^1 w < ∞`), and the `O(t)` vanishing
of the numerator then forces the first-order condition

```
1 + (sum of pole abscissas) − (sum of zero abscissas) − 2β ≥ 0.
```

With a single compensating pole and no auxiliary zeros this reads `δ ≥ 2β − 1`, which caps `β` at
`3/4` when `δ < 1/2`.  The construction above escapes that cap by using `A` poles at `δ` together
with `A−1` zeros at the origin: the first-order condition becomes `1 + Aδ − 2β ≥ 0`, satisfiable for
every `δ > 0` by taking `A` large.  This is why `θ` can be pushed to `0`.

## 5. Lean

| result | theorem | module |
|---|---|---|
| existence of the compensating coefficient `A` | `exists_regularCoefficient` | `RHTower/BeurlingRegularIntegersOffLineZeros` |
| numerator monotone from `K' ≥ 0`, hence `w ≥ 0` | `regularNumerator_nonneg`, `regularDensity_nonneg` | same |
| three-way Frullani split of the weighted density | `cexp_mul_regularDensity` | same |
| Laplace transform of the density | `integral_cexp_mul_regularDensity` | same |
| `exp F(s) = ((s−β)²+γ²)s^{A−1}/((s−1)(s−δ)^A)` | `cexp_integral_regularDensity` | same |
| the zeta vanishes at `β+iγ`, genuinely | `regularZeta_eq_zero`, `regularZeta_denom_ne_zero_at_zero` | same |
| no other singularity with `Re s > δ` | `regularZeta_denom_ne_zero` | same |
| **the packaged theorem** | `regular_integers_do_not_constrain_zeros` | same |

Built, wired into `GaloisForLFunctions.RHTower`, axiom audit
`[propext, Classical.choice, Quot.sound]`.  It reuses `HTGeometry/FrullaniIntegral` (built for the
parent card; mathlib has neither the Frullani integral nor the complex-rate exponential integral).

Not formalized, and stated as classical Mellin inversion only: the passage from "`ζ` rational with
its only `Re s > δ` pole simple at `s = 1`" to "`N(x) = ρx + O(x^{δ+ε})`".  The Lean statement
carries the analytic form, which is the checkable content.

## 6. Separate discrete question — not established here

The earlier card conjectured a discrete Beurling system with a nonreal zero right of `1/2` and
`N(x)=ρx+O(x^θ)` for every `θ>0` in the **same** system. That is a separate assertion, not a
consequence of this continuous construction. No discretization preserving those exact properties
has been supplied here. This audit makes no claim about its current literature status and does
not adopt it as an RH proof route.

## Audit outcome

The positive survivor is the explicit continuous density and rational transform with a prescribed
zero, with the original theorem's quantifiers retained. The fixed-model logarithmic counting
construction is a separate auxiliary result. Neither supplies a new zero-forced relation for
ordinary zeta. **NO POSITIVE SALVAGE FOUND as a novel RH architecture.**

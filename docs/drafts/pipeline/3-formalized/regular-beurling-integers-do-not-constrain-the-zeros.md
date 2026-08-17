# Regular generalized integers do not constrain the zeros

- **ID:** `BEURLING-REGULAR-INTEGERS-NO-CONSTRAINT-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / FIREWALL, and a retraction
- **Parent:** `rh-sensitivity-threshold-of-the-prime-measure.md` §6 (whose design rule this refutes)
- **RH used:** no · **Computation used:** no
- **Scientific status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN CERTIFIED] [NOT RH]
  [NOVELTY: BOUNDED AUDIT — the qualitative phenomenon is consistent with the [α,β]-system
  literature; the explicit rational-zeta form and the `θ → 0` sharpness are the contribution]`

## One sentence

For every `β ∈ (1/2, 1)`, every `γ ≠ 0` and every `θ > 0` there is an explicit Beurling
generalized number system whose integer-counting function is *more* regular than the Riemann
hypothesis claims for `ℤ` — `N(x) = ρx + O(x^{θ})` for every `θ > 0` — and whose zeta function
nevertheless vanishes at `β ± iγ`; so no asymptotic regularity of the integer-counting function
implies RH, and the design rule of the parent card is false.

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
`s = ∞`, as the Laplace transform of a finite measure must.)

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

**(b) Integers as regular as one likes.**  `ζ` is a rational function whose only pole with
`Re s > δ` is the simple pole at `s = 1`, with residue `((1−β)²+γ²)/((1−δ)^A)` > 0.  Since
`ζ(s) = s∫_1^∞ N(x) x^{-s-1} dx` on `Re s > 1` and `ζ` is rational (so `O(1)` on vertical lines,
`ζ(∞) = 1`), Mellin inversion with a contour at `Re s = δ + ε` gives

```
N(x) = ρ x + O( x^{δ+ε} ),        ρ = residue at s = 1.
```

`δ ∈ (0,1)` is free, so for every `θ > 0` we may take `δ < θ` and obtain
`N(x) = ρ x + O(x^{θ})`.  For `ℤ` itself, `N(x) = ⌊x⌋ = x + O(1)`, which satisfies the same bound
for every `θ > 0`.  **The two systems are indistinguishable at every power scale of `N`, and they
disagree about RH.**

**(c) The primes pay for it.**  `Π(x) = ∫_0^{log x} w(t) dt/t · …`, and the oscillatory term
contributes `π(x) = Li(x) + Θ(x^{β}/log x)`.  So the prime counting error exponent is `β > 1/2`
while the integer counting error exponent is `δ ≈ 0`; `max{β, δ} = β ≥ 1/2`, consistent with the
Broucke–Vindas constraint `max{α,β} ≥ 1/2` for `[α,β]`-systems.  Regularity is *transferred* from
the primes to the integers, not created.

## 3. Consequence: the retraction

The parent card's §6 concluded that an RH criterion must control `N(x) − ρx` at the scale
`x^{1/2}`.  Part (b) refutes this: control of `N` at *every* power scale is compatible with the
worst possible zero placement.  The corrected statement is

> An RH proof must use **which** integers occur, not how many.  Neither reciprocal-weight prime
> data (`1/p`, `Λ(n)/n`, Mertens constants, prime log-jet Grams — parent card) nor any asymptotic
> regularity of `N(x)` (this card) can decide RH.  The load-bearing input is the exact identity
> `N(x) = ⌊x⌋`, i.e. the multiplicative structure of `ℤ`, not any asymptotic shadow of it.

Where the Landau obstruction of the parent card does bite is only the *relative* problem: if one
insists on **adjoining** primes to `ℤ` (positive perturbation, so that the comparison object is
`ζ` itself), then a new off-line zero forces a real singularity of `ζ_ℬ/ζ` at abscissa `≥ β`.  In
the absolute Beurling category that compensating singularity is placed at `s = δ ≈ 0`, where it
costs nothing.

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

## 6. Open, and worth attacking

**[CONJECTURE — discrete realization]** The system above is *continuous*.  The Diamond–Montgomery–
Vorhauer/Broucke–Debruyne–Vindas technology discretizes continuous Beurling systems while
preserving counting asymptotics.  Conjecture: there is a **discrete** Beurling system (a genuine
sequence `1 < p₁ ≤ p₂ ≤ …`) with `N(x) = ρx + O(x^{θ})` for every `θ > 0` and a zeta zero with real
part `> 1/2`.  Falsity would be far more interesting than truth: it would mean discreteness itself
— the integrality of the generalized integers — is the missing arithmetic input, and would give the
first structural reason why `ℤ` is special beyond its counting function.

**Why this is the right next question.**  Both firewalls in this pair rule out classes of criteria
by exhibiting continuous Beurling counterexamples.  Discreteness is the one hypothesis neither
counterexample respects.  If discreteness cannot be added, the whole Beurling-counterexample method
is exhausted and the firewalls are final; if it can, the method extends and RH is provably immune to
an even larger class of arguments.

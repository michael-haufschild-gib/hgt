# The RH-sensitivity threshold of a prime measure is exactly σ = 1/2

- **ID:** `RH-SENSITIVITY-THRESHOLD-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / STRUCTURAL NO-GO WITH SHARP CONVERSE
- **Parent open core:** `../1-in-progress/xi-same-fibre-fixed-star-source-descent.md` §C31
- **RH used:** no
- **Computation used:** no
- **Scientific status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN CERTIFIED] [NOT RH]
  [NOVELTY: BOUNDED AUDIT]`

## One sentence

Adjoining to the rational primes a positive generalized-prime measure of *arbitrarily small
reciprocal mass* can place a zeta zero anywhere on any line `Re s = β` with `1/2 < β < 1`, whereas
no adjoined measure whose abscissa of convergence is at most `1/2` can move a single zero — so the
Riemann hypothesis lives exactly at the `σ = 1/2` scale of the prime measure, and every criterion
built from reciprocal-mass (Mertens, `1/p`, `Λ(n)/n`, prime-log-jet) data is provably incapable of
deciding it.

## 0. Why this card exists

The parent card's open core asked for a *two-port secondary source character*: a canonical source
2-cell `H_{p,r,N}` with `∂H = P_{p,N} − P_{r,N} + exact`, whose quadratic Stokes law would force
`A_q(1/p − 1/r) = 0`, hence `A_q = 0`, hence RH.

Two independent unconditional theorems close that request.

1. **Parametric vacuity** (§1, Lean `XiGammaSixWoldJordanParametricVacuity`).  The entire
   Wold–Jordan actual-source descent apparatus depends on the Xi copy `q` *only* through the single
   nonnegative real scalar `A_q`, and the descent predicate for a **free** real parameter `A` holds
   iff `A = 0`.  Since every ingredient the proposed construction would use (Big-Witt rows, one-leg
   trace, ambient and graph admission, the common singular vector, the prime-labelled quadratic
   energy) is defined verbatim for every value of `A`, a naturality-only construction of `H` would
   prove the parametric statement at `A = 1`, which is false.  **Verdict on the open core: FALSE as
   posed.**

2. **The sensitivity threshold** (§2–§5, this card).  The reason no *repair* inside the same data
   class can work: the only arithmetic input the whole C27–C31 chain consumes is
   `∑_p 1/p = ∞` — a statement at the `σ = 1` scale of the prime measure.  §3 exhibits prime systems
   for which that input still holds verbatim, together with Mertens-normality and a power-saving
   PNT, and for which RH is **false**.

## 1. Parametric vacuity (statement)

Let `A(q)` be the Gamma-six harmonic weight, so that the literal Wold–Jordan carrier satisfies
`carrier(p, q)² = A(q)/p`.  Write `Desc(q)` for the actual-source descent predicate of the parent
module and, for a free real `A`, write `Desc*(A)` for the same predicate with the prime-labelled
energies `A/p`.

**Theorem 1.**  `Desc*(A) ↔ A = 0` for every real `A`; hence `¬ ∀A, Desc*(A)`.  Moreover
`Desc(q) ↔ Desc*(A(q))`, so `Desc` depends on `q` through `A(q)` alone.

*Proof.*  The energy reporter is `Finsupp.lsum` with coefficient `c(i.1.1)` for a coefficient
function `c` of the left prime; on a trace-normalized fixed-left row with left prime `p_a` it
returns `c(p_a)` at every cutoff.  A continuous reporter agreeing with it on all rows must give the
common limit `v_sing` the value `c(p_a)` for every `a`, so `A/2 = A/3`, so `A = 0`.  Conversely at
`A = 0` the zero reporter works.  Taking `c(p) = carrier(p,q)² = A(q)/p` identifies `Desc` with
`Desc*(A(q))`. ∎

The RH-equivalence proved in the parent module is therefore the pullback of the arithmetic-free
scalar condition `A = 0` along `q ↦ A(q)`, and `A(q) = 4 F(2 Re q − 1)²` is a function of
`Re q` alone: no ζ-arithmetic enters anywhere.

## 2. Setting for the threshold theorem

A **continuous Beurling prime measure** is a positive Borel measure `Π` on `(1, ∞)`, finite on
bounded sets.  Its zeta function is

```
ζ_Π(s) = exp ( ∫_(1,∞) u^{-s} dΠ(u) ),
```

wherever the integral converges.  The rational primes are
`Π_ℤ = ∑_{p, k ≥ 1} (1/k) δ_{p^k}`, for which `∫ u^{-s} dΠ_ℤ = log ζ(s)` on `Re s > 1`.

For a positive Borel measure `ν` on `(1, ∞)` put `ℬ(ν) = Π_ℤ + ν`; then, where everything
converges,

```
ζ_{ℬ(ν)}(s) = ζ(s) · exp F_ν(s),      F_ν(s) = ∫_(1,∞) u^{-s} dν(u).
```

Write `m_σ(ν) = ∫ u^{-σ} dν(u) ∈ [0, ∞]` for the **σ-mass** and
`σ_c(ν) = inf { σ : m_σ(ν) < ∞ }` for the abscissa (for a positive measure, absolute and ordinary
convergence abscissas coincide).  Two special values matter:

- **reciprocal mass** `m_1(ν) = ∫ u^{-1} dν(u)` — the total mass of the adjoined generalized primes
  in the `1/p` weighting;
- **Mertens mass** `∫ u^{-1} log u dν(u)` — the amount by which `∑_{n ≤ N} Λ_ℬ(n)/n` exceeds
  `∑_{n ≤ N} Λ(n)/n` in the limit; finiteness of this number is exactly Mertens-normality of
  `ℬ(ν)` relative to `ℤ`.

**RH for `ℬ(ν)`** means: `ζ_{ℬ(ν)}` continues to `Re s > 1/2` with no zeros there (apart from the
pole at `s = 1`).

In the logarithmic coordinate `t = log u` a measure with density `w(u) du` becomes the density
`g(t) = e^t w(e^t)` on `(0, ∞)`, and `F(s) = ∫_0^∞ e^{-st} g(t) dt`, `m_σ = ∫_0^∞ e^{-σt} g(t) dt`,
Mertens mass `= ∫_0^∞ t e^{-t} g(t) dt`.  All Lean statements are in this coordinate.

## 3. Theorem A — stability below the threshold

**Theorem A.**  Let `ν ≥ 0` with `m_σ(ν) < ∞` for every `σ > 1/2` (i.e. `σ_c(ν) ≤ 1/2`).  Then `F_ν`
converges absolutely on `Re s > 1/2`, `exp F_ν` is holomorphic and **zero-free** there, and the
zeros of `ζ_{ℬ(ν)}` in `Re s > 1/2` are exactly the zeros of `ζ`.  In particular RH holds for
`ℬ(ν)` iff RH holds.

*Proof.*  Fix `σ₀ > 1/2`.  For `Re s ≥ σ₀` and `u > 1`, `|u^{-s}| = u^{-Re s} ≤ u^{-σ₀}`, so `F_ν`
converges absolutely and uniformly on `{Re s ≥ σ₀}`; by Weierstrass it is holomorphic on
`Re s > σ₀`, and `σ₀ > 1/2` was arbitrary.  Since `exp` omits `0`, `exp F_ν` has no zeros where
`F_ν` is finite.  Finally `ζ_{ℬ(ν)} = ζ · exp F_ν` on `Re s > 1`, and both sides continue to
`Re s > 1/2`, so the zero sets agree there. ∎

Lean: `zeros_unchanged_of_mass_abscissa_le_half` (absolute convergence at every `Re s > 1/2` by
domination, plus `z · exp F = 0 ↔ z = 0`).

**Remark (Landau rigidity — sharpness of the hypothesis).**  If `exp F_ν` has a zero or pole at a
point with real part `β`, then `F_ν` is singular there, so `σ_c(ν) ≥ β`; and since `dν ≥ 0`,
Landau's theorem says the *real* point `σ_c(ν)` is itself a singularity of `F_ν`.  Hence any
adjoined measure that moves a zero to the line `Re s = β` necessarily has abscissa `≥ β` and leaves
a real singularity there, i.e. changes the generalized-integer counting function at order
`x^{β−δ}` for every `δ > 0`.  So Theorem A's hypothesis is not an artefact: it is the exact
dividing line.

## 4. Theorem B — instability above the threshold, explicitly

Fix `β ∈ (1/2, 1)` and `γ ≠ 0`.  Define the adjoined measure by its density on `(1, ∞)`

```
w_{β,γ}(u) = 2 u^{β−1} ( 1 − cos(γ log u) ) / log u ≥ 0,      dν_{β,γ} = w_{β,γ}(u) du,
```

equivalently, in the logarithmic coordinate,

```
g_{β,γ}(t) = 2 e^{βt} ( 1 − cos(γ t) ) / t ≥ 0        (t > 0).
```

`g` is continuous on `(0, ∞)`, nonnegative, and `g(t) = O(t)` as `t → 0⁺` because
`1 − cos γt = γ²t²/2 + O(t⁴)`.

**Theorem B.**

1. *(Laplace transform.)*  For `Re s > β`,
   ```
   F_{β,γ}(s) = ∫_0^∞ e^{-st} g_{β,γ}(t) dt
              = Log(s − β − iγ) + Log(s − β + iγ) − 2 Log(s − β),
   ```
   all three logarithms principal (their arguments have positive real part).  Hence
   ```
   exp F_{β,γ}(s) = ( (s − β)² + γ² ) / (s − β)².
   ```
2. *(Enlarged zeta and its zero.)*  `ζ_{ℬ(ν)}(s) = ζ(s) · ((s−β)² + γ²)/(s−β)²`, a function
   meromorphic on `ℂ` with a simple pole at `1`, a double pole at `β`, and **zeros at `β ± iγ`** in
   addition to the zeros of `ζ`.  Since `β > 1/2`, **RH fails for `ℬ(ν_{β,γ})`**.
3. *(σ-masses and abscissa.)*  For `σ > β`,
   `m_σ(ν_{β,γ}) = log ( 1 + γ²/(σ−β)² )`, and `m_β(ν_{β,γ}) = ∞`.  Hence `σ_c(ν_{β,γ}) = β`
   exactly.
4. *(Reciprocal and Mertens mass.)*
   ```
   m_1(ν_{β,γ}) = log ( 1 + γ²/(1−β)² ),
   ∫ u^{-1} log u dν_{β,γ}(u) = 2γ² / ( (1−β) ( (1−β)² + γ² ) ).
   ```
   Both are finite and both tend to `0` as `γ → 0⁺`.  So for every `ε > 0` and every
   `β ∈ (1/2, 1)` there is `γ > 0` with reciprocal mass `< ε` and Mertens mass `< ε`, while the
   enlarged zeta has a zero at `β + iγ`.

*Proof of (1).*  Substituting `u = e^t` gives
`F(s) = ∫_0^∞ 2 e^{-(s−β)t} (1 − cos γt)/t dt`.  Write `a = s − β`, so `Re a > 0`, and use

```
2 e^{-at}(1 − cos γt) = ( e^{-at} − e^{-(a−iγ)t} ) + ( e^{-at} − e^{-(a+iγ)t} ),
```

which is the identity `e^{-(a−iγ)t} + e^{-(a+iγ)t} = 2 e^{-at} cos γt`.  Both `a ± iγ` have real
part `Re a > 0`, so each of the two terms, divided by `t`, is a Frullani integrand.  The complex
Frullani evaluation

```
∫_0^∞ ( e^{-at} − e^{-bt} ) / t dt = Log b − Log a          (Re a, Re b > 0)
```

is proved by writing `(e^{-at} − e^{-bt})/t = ∫_0^1 (b−a) e^{-(a + u(b−a))t} du` (fundamental
theorem of calculus in `u`), swapping the order of integration — legitimate because
`Re(a + u(b−a)) ≥ min(Re a, Re b) > 0` for `u ∈ [0,1]`, giving the dominating function
`|b−a| e^{-ct}` on `(0,∞) × (0,1]` — evaluating the inner `t`-integral as `(b−a)/(a + u(b−a))`, and
integrating in `u` against the primitive `Log(a + u(b−a))`, which is legitimate because the segment
from `a` to `b` lies in the right half plane, hence in the slit plane where `Log` is a primitive of
`1/z`.  Applying it twice gives
`F(s) = (Log(a−iγ) − Log a) + (Log(a+iγ) − Log a)`, and exponentiating,
`exp F = (a−iγ)(a+iγ)/a² = (a² + γ²)/a²`. ∎

*Proof of (2).*  Both sides of `ζ_{ℬ(ν)} = ζ · exp F` are meromorphic on `Re s > β` and agree on
`Re s > max(1, β)`, so they agree there; the right-hand side continues to all of `ℂ`.  At
`s = β + iγ` the factor `(s−β)² + γ² = (iγ)² + γ² = 0` while `(s−β)² = −γ² ≠ 0`, so the factor
vanishes and `ζ` is finite there (`β + iγ ≠ 1` since `γ ≠ 0`). ∎

*Proof of (3).*  The formula for `σ > β` is (1) evaluated at the real point `s = σ`:
`Log(σ−β−iγ) + Log(σ−β+iγ) = log((σ−β)² + γ²)` (the two logarithms are conjugate, so the
imaginary parts cancel and the real parts are each `log √((σ−β)²+γ²)`), and subtracting
`2 log(σ−β)` gives `log(1 + γ²/(σ−β)²)`.

For `m_β = ∞`: suppose `m_β = M < ∞`.  Since `g ≥ 0` and `e^{-σt} ≤ e^{-βt}` for `σ ≥ β`, `t > 0`,
every `m_σ` with `σ > β` is finite and `m_σ ≤ M`.  But `m_{β+δ} = log(1 + γ²/δ²) → ∞` as `δ → 0⁺`.
Explicitly, taking `δ = |γ| / √(e^M + 1)` gives `γ²/δ² = e^M + 1` and
`m_{β+δ} = log(e^M + 2) > log(e^M) = M`, a contradiction. ∎

*Proof of (4).*  The reciprocal mass is (3) at `σ = 1`.  For the Mertens mass, `t g(t) =
2 e^{βt}(1 − cos γt)`, and with `a = 1 − β > 0`,
```
∫_0^∞ e^{-t} · t g(t) dt = 2∫_0^∞ e^{-at} dt − ∫_0^∞ e^{-(a−iγ)t} dt − ∫_0^∞ e^{-(a+iγ)t} dt
  = 2/a − 1/(a−iγ) − 1/(a+iγ) = 2/a − 2a/(a²+γ²) = 2γ² / ( a (a² + γ²) ).
```
Both expressions are continuous in `γ` and vanish at `γ = 0`. ∎

## 5. The threshold theorem and its corollaries

**Theorem C (threshold).**  For positive adjoined prime measures `ν` on the rational primes:

- if `σ_c(ν) ≤ 1/2` then RH for `ℬ(ν)` is equivalent to RH;
- for every `β ∈ (1/2, 1)` and every `ε > 0` there is `ν` with `σ_c(ν) = β`, reciprocal mass `< ε`,
  Mertens mass `< ε`, and RH false for `ℬ(ν)` with a zeta zero on `Re s = β`.

Hence `σ = 1/2` is exactly the sensitivity threshold, and the reciprocal (`σ = 1`) scale of the
prime measure carries **no** information about RH.

**Corollary D (criterion firewall).**  Let `C` be any property of prime systems which is implied by
data invariant under, or continuous in, adjoining a positive measure of small reciprocal and Mertens
mass — in particular any property determined by

- the divergence `∑ 1/p = ∞`,
- Mertens-normality `∑_{n ≤ N} Λ(n)/n = log N + C + o(1)`,
- normalized prime log-jet Gram limits `H_k(N) = ∑_{n≤N} Λ(n) n^{-1} (log n)^k` after any
  multiplicative regularization,
- any functional continuous in the reciprocal-mass norm.

Then `C` cannot be equivalent to RH: `C` holds for `ℬ(ν_{β,γ})` while RH fails there.

**Corollary E (upgrade of the corpus's blindness axiom N1).**  The card
`beurling-cross-system-blindness-of-multiplicative-regularization-law` proves that multiplicatively
regularized prime log-jet Gram limits are constant across Mertens-normal Beurling systems, and
exhibits a witness pair (rational primes vs. the `2 → 3` generator swap) whose **zero sets** differ.
That witness does not decide RH: the swapped system's extra zeros sit on `Re s = 0`.  The system
`ℬ(ν_{β,γ})` of §4 is Mertens-normal (finite Mertens mass, Theorem B(4)) and **violates RH**.  So
N1 upgrades from *"cannot determine the zero set"* to *"cannot decide the Riemann hypothesis"*.

**Corollary F (the parent open core, second kill).**  The only arithmetic input in the C27–C31
chain is `¬ Summable (fun p => 1/p)`.  That holds verbatim for `ℬ(ν_{β,γ})`, which contains all
rational primes.  Every structural step of the chain — divergent row trace, bounded ambient `ℓ²`
norm, common singular vector, `A/p` carrier square — is a statement about a prime list with
divergent reciprocal sum and survives the enlargement.  A producer built from that data alone would
prove RH for `ℬ(ν_{β,γ})`, which is false.  Combined with Theorem 1, the L/R/CCM/P Frankenstein
descent cluster is closed: **retire, do not repackage.**

## 6. What the threshold says positively — **and the retraction of the design rule**

`ζ_{ℬ(ν)}` sees `ν` through `F_ν(s) = ∫ u^{-s} dν(u)`.  Within the class of *positive* adjunctions
to the rational primes, moving a zero into `Re s > 1/2` costs abscissa `> 1/2`, hence (Landau) a
real singularity at the same abscissa, hence a change of the generalized-integer counting function
`N(x)` of size `x^{β−δ}`.  An earlier revision of this card drew from that the design rule

> ~~The arithmetic input any RH proof must consume is control of `N(x) − ρx` at the power scale
> `x^{1/2}`.~~

**That rule is false and is retracted.**  It is refuted, unconditionally and explicitly, by the
companion card `regular-beurling-integers-do-not-constrain-the-zeros`: for every `β ∈ (1/2,1)`,
every `γ ≠ 0` and every `θ > 0` there is a Beurling system whose zeta is the rational function
`((s−β)² + γ²)s^{A−1}/((s−1)(s−δ)^A)` with `0 < δ < θ` — so its generalized integers satisfy
`N(x) = ρx + O(x^{θ})` for *every* `θ > 0`, better regularity than RH claims for `ℤ` — while its
zeta vanishes at `β ± iγ`.  The Landau obstruction of §3 applies only to *adjoining* primes to
`ℤ` (where the comparison is with `ζ` itself); in the absolute Beurling category the compensating
real singularity may be placed arbitrarily close to `s = 0`, at no cost to `N`.

What survives, and is the corrected statement:

> **Reciprocal-weight data — `1/p`, `Λ(n)/n`, Mertens constants, `ℓ²` prime energies, log-jet
> Grams — cannot decide RH (this card).  Neither can any asymptotic regularity of the
> generalized-integer counting function (companion card).  An RH proof must use *which* integers
> occur, not how many: the input is the exact multiplicative structure `N(x) = ⌊x⌋`, not any
> `N(x) = ρx + O(x^{θ})`.**

Every corpus lane whose prime weights are `1/p`-type (Wold–Jordan carriers, Big-Witt `1/(pq)` rows,
harmonic singular graphs, Mertens-window Grams) is dead by this card.  Lanes whose prime weights are
`Λ(n) n^{-1/2}`-type (explicit formula, Weil quadratic form, restricted-aperture CCM) are not
touched by either card — but note that they are also *not* protected by the retracted rule; their
survival has to be argued on other grounds.

## 7. Lean

| result | theorem | module |
|---|---|---|
| complex exponential integral `∫_0^∞ e^{-zt} dt = 1/z`, `Re z > 0` | `integral_cexp_neg_mul` | `HTGeometry/FrullaniIntegral` |
| Frullani integrand is integrable on `(0,∞)` | `integrableOn_frullani` | same |
| complex Frullani `∫_0^∞ (e^{-at} − e^{-bt})/t dt = Log b − Log a` | `integral_frullani` | same |
| adjoined density is nonnegative, continuous on `(0,∞)` | `adjoinedDensity_nonneg`, `continuousOn_adjoinedDensity` | `RHTower/BeurlingRHSensitivityThreshold` |
| Laplace transform `= Log(s−β−iγ) + Log(s−β+iγ) − 2 Log(s−β)` | `integral_cexp_mul_adjoinedDensity` | same |
| adjoined Euler factor `= ((s−β)²+γ²)/(s−β)²` | `cexp_integral_adjoinedDensity` | same |
| enlarged zeta vanishes at `β + iγ` | `perturbedZeta_eq_zero` | same |
| `σ`-mass `= log(1 + γ²/(σ−β)²)` | `integral_adjoinedDensity_mass` | same |
| abscissa is exactly `β` (the `β`-mass diverges) | `not_integrableOn_adjoinedDensity_abscissa` | same |
| Mertens mass `= 2γ²/((1−β)((1−β)²+γ²))` | `integral_mertensIntegrand` | same |
| stability half of the threshold | `zeros_unchanged_of_mass_abscissa_le_half` | same |
| **the threshold theorem** | `rh_sensitivity_threshold` | same |
| descent predicate is a scalar condition on a free parameter | `abstractPrimeReciprocalSourceDescends_iff` | `RHTower/XiGammaSixWoldJordanParametricVacuity` |
| the parametric family is false at `A = 1` | `not_forall_abstractPrimeReciprocalSourceDescends` | same |
| Xi descent is the pullback of the parametric family | `deningerBigWittWoldJordanActualSourceEnergyDescends_iff_abstract` | same |
| **parametric vacuity of the open core** | `woldJordanSourceDescent_parametric_vacuity` | same |

Both modules build with `lake env lean` and `lake build`, are wired into
`GaloisForLFunctions.HTGeometry` and `GaloisForLFunctions.RHTower`, and every theorem above audits
to `[propext, Classical.choice, Quot.sound]`.

Mathlib gap closed on the way: mathlib has no Frullani integral and no complex-rate exponential
integral `∫_0^∞ e^{-zt} dt` (only real rates and the Gamma-weighted form).  Both are now in
`HTGeometry/FrullaniIntegral` and are reusable.

## 8. Novelty audit (bounded)

Checked: Beurling (1937); Diamond–Montgomery–Vorhauer, *Beurling primes with large oscillation*
(Invent. Math. 2006); Broucke–Debruyne–Vindas, *Beurling integers with RH and large oscillation*
(Adv. Math. 2020, `arXiv:2004.11501`); Broucke–Vindas, *Some examples of well-behaved Beurling
number systems* (`arXiv:2309.01567`); Révész, *Oscillation of the remainder term in the PNT of
Beurling, caused by a given zeta-zero* (`arXiv:2202.01837`); Debruyne–Vindas zero-density work
(`arXiv:2211.08716`, `arXiv:2409.10051`); Hilberdink–Lapidus fractal-membrane survey
(`arXiv:math/0410270`); Connes–Consani, *Weil positivity and trace formula, the archimedean place*
(Selecta Math. 2021, `arXiv:2006.13771`); Connes–Consani–Moscovici semilocal prolate work (2024–25).

The ingredients are classical: Beurling's own examples are continuous measures of exactly this
`1 − cos` type, and the Landau obstruction is standard.  What is not found in the checked sources,
and is the content of this card, is

1. the **two-sided threshold statement** — abscissa `≤ 1/2` moves no zero (Theorem A) *and* every
   abscissa `β ∈ (1/2,1)` is realizable with arbitrarily small reciprocal and Mertens mass
   (Theorem B(4)), so that the σ-scale `1/2` is exactly where RH-sensitivity begins;
2. the use of that pair as a **classifier for RH criteria** (Corollary D), with the resulting design
   rule of §6;
3. the exact masses `log(1 + γ²/(σ−β)²)` and `2γ²/((1−β)((1−β)²+γ²))` for this deformation.

This is a bounded audit of the checked sources, not a claim of exhaustive priority.
`[NOVELTY UNVERIFIED]` on item 1's classical half.

## 9. Log

- Created directly in 3-formalized.  Paper proof complete and dependency-closed before Lean; Lean
  modules built, wired, indexed, axiom-audited.
- Two claims were *not* made and should not be added later without proof: (i) that the enlarged
  system can be discretized while preserving the masses (true in the literature's technology, not
  proved here); (ii) that the enlarged system's counting function `N(x)` is `ρx + O(x^{β+δ})`
  (elementary but not formalized — only the mass statements are).

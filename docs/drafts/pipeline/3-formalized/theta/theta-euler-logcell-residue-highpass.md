# Literal Euler multiplication has a noncompact residue channel beyond the logarithmic continuum clock

- **ID:** `theta-euler-logcell-residue-highpass`
- **Stage:** 3-formalized
- **Type:** THEOREM and exact source-transport boundary (paper and Lean); certificate
  [`theta-euler-logcell-residue-highpass-formalized.md`](theta-euler-logcell-residue-highpass-formalized.md)
- **Routes:** STC, RHist, U, CSB, MPLF
- **Status:** `[PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]`
- **Source:** The literal normalized theta integer translation and its multiplicative law in `FrankensteinThetaPrimeTranslationCommonForcing.lean`; the theta Euler sum in `ThetaCuspFinitePrimeSource.lean`; the prime Poisson/Mertens clock in [the STC paper theorem](../route%20stc/stc-poisson-mertens-clock-commutator.md).

## Reinterpretation

The prime Poisson history has continuum clock `log log p` because
prime harmonic mass `Σ_(p≤x) 1/p` grows like `log log x`.
Theta's literal Euler translations act by `x↦x+log n` and their
cofactor labels are **all positive integers**. Integer harmonic
mass grows like `log x`, so the aligned continuum clock is
`log n`. Passing from prime labels to their Euler-invariant
cofactor hull changes the clock. It also exposes a residue channel
that the continuum clock does not see.

## Exact logarithmic-cell theorem

Let `H=ℓ²(ℕ_{≥1})` with standard vectors `e_n`. For each integer
`p≥2`, let the literal multiplication isometry be

```text
S_p e_n=e_(pn),                 S_p S_q=S_(pq).
```

Partition the positive half-line into **exact logarithmic cells**

```text
I_n=[log n,log(n+1)),          ℓ_n=|I_n|=log((n+1)/n).
```

Let `Ue_n=1_(I_n)/sqrt(ℓ_n)` and let `T_a` be right translation
on the **coefficient log clock** `L²(0,∞)`. This is dual to the
outward `x↦x+log p` shift of a theta source term, with the same
label multiplication `n↦pn`. The step-function subspace `U(H)` is invariant under
`T_(log p)`. Its exact pullback `W_p=U* T_(log p) U` is

```text
W_p e_n=Σ_(r=0)^(p−1) c_(n,r) e_(pn+r),
c_(n,r)=sqrt(ℓ_(pn+r)/ℓ_n),
Σ_r c_(n,r)²=1,              W_p W_q=W_(pq).             (1)
```

Each `W_p` is an isometry. Define the uniform residue or
low-pass channel

```text
V_p e_n=p^(−1/2)Σ_(r=0)^(p−1)e_(pn+r).
```

Then `V_p` is an isometry and

```text
W_p−V_p ∈ Schatten₂.                                     (2)
```

In contrast, the literal zero-residue Euler channel is not a
compact perturbation of physical translation. Precisely,

```text
‖S_p−W_p‖_ess = sqrt(2−2/sqrt(p)) > 0.                  (3)
```

The source-preserving part outside the low-pass channel is

```text
R_p=S_p−p^(−1/2)V_p,
V_p*R_p=0,                 R_p*R_p=(1−1/p)I.             (4)
```

Thus, modulo a Hilbert--Schmidt correction,

```text
S_p=p^(−1/2)W_p+R_p+Schatten₂.                           (5)
```

The two representations also have an exact **mixed curvature**:

```text
‖S_pW_p−W_pS_p‖_ess = sqrt(2−2/p) > 0.                 (6)
```

Each semigroup is internally multiplicative and commutative, but
the literal Euler and continuum transports do not commute even
modulo compacts on the natural coefficient clock.

More strongly, **all prime residue channels are complete modulo
the unit/vacuum coordinate**:

```text
closure(span{Ran R_p : p prime}) = {f∈H : f(1)=0},
⋂_(p prime) ker R_p* = ℂ e_1.                            (7)
```

This is a single-vacuum arithmetic quotient before any Xi divisor
or source graph is imposed. It is not a source index or an RH
argument: the actual coefficient vector `n^(−1/2)` is outside
`H`, and no theta-domain/port map has been built on (7).

The theta integer shift carries coefficient `p^(−1/2)`, so the
literal source shift is `p^(−1/2)S_p`. Its residue part has norm
`p^(−1/2)sqrt(1−1/p)` on every cofinal basis vector; it does not
decay as `n→∞` for any fixed `p`. The continuum translation sees
only the uniform residue combination. The exact arithmetic
occurrence is in the high-pass channel.

The smallest closed subspace containing all prime basis vectors
and invariant under every `S_p` is `ℓ²(ℕ_{≥2})`: every `n≥2`
is a prime times a positive integer. Adding the seed/unit vector
`e_1` gives all of `H`. A prime-only Poisson carrier therefore
cannot be invariant under theta's literal integer Euler action.

The single vacuum remains separated after applying the **literal
Gaussian theta seed** on the positive physical half-line. Define

```text
(C e_n)(x)=n^(−1/2) h(x+log n),
h=thetaCuspLogSeed,                    x≥0.                (9)
```

Then `C:H→L²(0,∞)` is Hilbert--Schmidt, and there exists
`g∈L²(0,∞)` with

```text
⟨g,C e_n⟩=0  (n≥2),       ⟨g,C e_1⟩≠0.             (10)
```

Consequently `C e_1` is outside the closed span of every higher
literal theta atom. Combining (7) and (10), the all-prime
high-pass images have a **source-visible one-dimensional vacuum
quotient** on this positive half-line. This is stronger than
pointwise first-atom tail dominance, which would not control
closure under arbitrarily large coefficients. It still has no
reflection-compatible index, Xi determinant, or two-ended domain law.
The actual Euler source converges absolutely in this half-line
`L²`, so the same functional extracts its literal unit term:

```text
⟨g,k⟩=Σ_(n≥1)⟨g,C e_n⟩=⟨g,h⟩≠0.             (10a)
```

## Proof

The cells partition `[0,∞)`. Translating `I_n` by `log p` gives

```text
[log(pn),log(p(n+1))) = ⋃_(r=0)^(p−1) I_(pn+r)
```

as a disjoint union up to endpoints. Expanding the translated
constant function in the normalized cell basis gives (1). The
coefficient-square identity follows from the exact telescope

```text
Σ_(r=0)^(p−1) ℓ_(pn+r)
  = log(p(n+1))−log(pn)=ℓ_n.
```

Translation adds logarithms, proving `W_pW_q=W_(pq)`; literal
integer multiplication proves the same law for `S_p`.

For fixed `p,r`, the elementary integral formula
`ℓ_n=∫_n^(n+1)dt/t` gives, uniformly in `0≤r<p`,

```text
ℓ_n=1/n+O(n^(−2)),
ℓ_(pn+r)=1/(pn)+O_p(n^(−2)),
c_(n,r)=p^(−1/2)+O_p(n^(−1)).
```

The `p`-cell target blocks for distinct `n` are orthogonal.
Therefore

```text
‖W_p−V_p‖_(S₂)²
 = Σ_n Σ_(r<p)|c_(n,r)−p^(−1/2)|² <∞,
```

proving (2). Within the `n`th target block,

```text
‖(S_p−W_p)e_n‖²=2−2c_(n,0)→2−2/sqrt(p).
```

Those output blocks are orthogonal and `e_n` tends weakly to
zero. Removing finitely many blocks gives matching upper bounds
for the essential norm, proving (3). Orthogonality of the
residue isometries `e_n↦e_(pn+r)` gives
`V_p* S_p=p^(−1/2)I`; expanding `R_p*R_p` proves (4), and (5)
follows from (2).

For (6), the output of `S_pW_p e_n` lies on indices
`p²n+pr`, while the output of `W_pS_p e_n` lies on
`p²n+r`, with `0≤r<p`. These sets meet only at `r=0`.
Both vectors have norm one, so their squared difference is
`2−2c_(n,0)c_(pn,0)→2−2/p`. Again the output blocks for
distinct `n` are disjoint; finite-rank truncation and weakly
null `e_n` give the matching essential-norm bounds.

For (7), a vector `f∈H` orthogonal to every `Ran R_p` obeys

```text
f(pn)=(1/p)Σ_(r=0)^(p−1) f(pn+r),
f(pn)=(1/(p−1))Σ_(r=1)^(p−1)f(pn+r).                (8)
```

The second line follows by moving the `r=0` term. Every integer
`m≥2` has a prime divisor `p`, so (8) says `f(m)` is an average
of finitely many strictly later values. An `ℓ²` sequence tends
to zero. If `f` were nonzero at some `m≥2`, the positive maximum
of `|f(m)|` on that tail would be attained at a **last** index
`m₀`: only finitely many entries can exceed half that maximum.
But each later value in (8) has strictly smaller modulus than
`|f(m₀)|`, contradicting the average identity. Thus `f(m)=0`
for `m≥2`, while `f(1)` is unrestricted because every `R_p`
has image supported on indices at least `2`. Taking orthogonal
complements proves (7).

Finally, multiplying a prime index by arbitrary positive integers
produces every integer `n≥2`, and no multiplication can produce
`1` from a prime. This proves the invariant-hull statement.

## The literal seed keeps the vacuum visible

The exact formula in `ThetaCuspFinitePrimeSource.lean` is

```text
h(x)=2π exp(5x/2)(2π exp(2x)−3)exp(−π exp(2x)).
```

Put `u=exp(2x)≥1` and `λ_n=πn²`. Then (9) becomes

```text
(C e_n)(x)
 =2π n² u^(5/4)(2λ_n u−3)exp(−λ_n u).          (11)
```

The Gaussian dominates every fixed polynomial, uniformly for
`u≥1`, so `Σ_n‖C e_n‖²<∞`; this proves `C` is
Hilbert--Schmidt. Also `C S_p=T_p C`, where
`(T_p f)(x)=p^(−1/2)f(x+log p)`: this is the exact source
shift already formalized in the corpus, now stated on the atom
coefficient carrier.

Here is an explicit separating functional. On the right
half-plane let

```text
B(s)=∏_(n≥2) ((λ_n−s)/(λ_n+s))²,
F(s)=exp(−s)(s−λ_1)B(s)/(s+1)².                    (12)
```

The product converges locally because `Σ_(n≥2)1/λ_n<∞`;
each factor has modulus below one on `Re s>0`. Thus `B` is
bounded analytic, has a double zero at every `λ_n`, `n≥2`,
and `B(λ_1)≠0`. The rational factor in (12) lies in the
right-half-plane Hardy space `H²`, so `F∈H²`. By the classical
Hardy--Laplace [Paley--Wiener theorem](https://arxiv.org/abs/2401.16091),
the factor `exp(−s)` makes `F` the Laplace transform of some
`q∈L²([1,∞),du)`:

```text
F(s)=∫_1^∞ q(u) exp(−su)du.
```

Set `g(x)=2u^(−1/4) conjugate(q(u))` with `u=exp(2x)`.
Since `dx=du/(2u)`,
`‖g‖²=2∫_1^∞u^(−3/2)|q(u)|²du≤2‖q‖²`.
Changing variables in the inner product and differentiating the
Laplace transform yields

```text
⟨g,C e_n⟩
 =2π n²[−2λ_n F'(λ_n)−3F(λ_n)].               (13)
```

For `n≥2`, both `F(λ_n)` and `F'(λ_n)` vanish. At `n=1`,
`F(λ_1)=0` but
`F'(λ_1)=exp(−λ_1)B(λ_1)/(λ_1+1)²≠0`.
This proves (10). The precise complex conjugation in the
definition of `g` uses the usual inner-product convention;
either convention gives the same separation statement.

The separator can be extended by zero to the negative physical
half-line, so it also separates the same literal translated atoms
inside `L²(ℝ)`. The full-line synthesis is bounded on `H`:
its Gram matrix is
`(nm)^(−1/2)⟨h(·+log n),h(·+log m)⟩`;
the correlation of `h` decays exponentially in the difference
`log n−log m`, and each unit `log n` shell has bounded harmonic
mass. The weighted Schur test therefore applies. This extension
does **not** make the separating functional compatible with the
modular reflection or the theta one-port boundary relation.

## Conjecture loop and the surviving hard gate

- **Prime Poisson bulk clock alone intertwines the theta Euler
  source:** false. Its `log log p` coordinate does not implement
  shifts by `log p`; prime labels are not closed under Euler
  multiplication.
- **The all-integer logarithmic continuum clock represents source
  multiplication modulo compact error:** false. Its exact
  translation is `W_p`, and (3) gives a positive essential-norm
  gap from literal `S_p`.
- **A source-faithful carrier can retain the missing information:**
  (4) and (7) supply an exact residue sector with a single
  vacuum quotient. The unbounded cofinal source still needs a
  graph/profile space. All-prime compatibility is a mixed
  multiplicative--residue problem; this Hilbert quotient alone
  gives no Xi divisor law or zero exclusion.

The next mathematical target is an all-prime coupling of the
`R_p` channels to the actual Gaussian theta seed and the
two-ended Xi domain selector. The literal-atom vacuum survives
in physical `L²` by (10); the difficult step is producing a
reflection-compatible source index through the singular Xi
domain without admitting
off-line boundary modes. Any positive continuum argument
that drops these noncompact channels is coefficient-incomplete.
External novelty and the global source-domain construction remain
unverified.

**Lean audit boundary:**
Every displayed result is formalized; see the certificate.
- `ThetaEulerPrimeResidueAverageVacuum` proves the prime-block maximum principle.
- `ThetaEulerLogCellResidueChannels` proves (1)–(8) and the invariant hull, with the operator
  identifications, the logarithmic-cell isometry and translation pullback, the Schatten₂
  comparison, the essential norms and the closed-span identity (7).
- `ThetaEulerLogCellSeedVacuum` (with `QuasiPolynomialBlaschkeIsometry`) proves the literal-seed
  separation (9)–(13) and (10a), and the bounded full-line synthesis.
- The separator is obtained from finite Blaschke products, which are isometries of
  `L²(0,∞)`, and Hilbert-space duality, in place of the infinite Blaschke function and the
  Hardy–Laplace theorem.

No assertion about Xi zero location is formalized here.

# Positive theta-source flow that removes one real Xi zero pair

- **ID:** `theta-positive-real-zero-division`
- **Stage:** 3-formalized. Lean: `GaloisForLFunctions.RHTower.ThetaZeroDivisionSource`, see `theta-positive-real-zero-division-formalized.md`
- **Type:** THEOREM (paper and Lean)
- **Route:** source-side divisor geometry for STC, CSB, U, RG, K-RVM, MPLF, and RG-HF
- **Status:** `[PROVED HERE ON PAPER] [NOT AN RH PROOF]`

## Theorem

Let `k=thetaCuspFullSource` and
`F(z)=∫ℝ exp(−izx)k(x)dx=XiC(z)`. Fix any `γ>0` with `F(γ)=0`.
For `x∈ℝ` define

```text
g_γ(x) = γ ∫₀∞ sin(γt) k(|x|+t)dt.                 (1)
```

Then `g_γ` is real, even, smooth, strictly positive everywhere, has every
exponential moment, and satisfies `g_γ(x)/k(x)→0` as `|x|→∞`; in
particular `sup_x g_γ(x)/k(x)<∞`. Its entire Fourier transform is

```text
G_γ(z)=F(z)/(1−z²/γ²),                             (2)
```

with the quotient interpreted by removable singularities at `±γ`.
Thus the Xi divisor loses one multiplicity at each of `±γ` and is
otherwise unchanged. Total source mass is unchanged: `∫g_γ=∫k`.

For `0≤ε≤1`, the source

```text
k_{ε,γ}=(1−ε)k+εg_γ
```

remains strictly positive, even, smooth, and exponentially decaying. Its
transform has the exact factorization

```text
F_{ε,γ}(z)=G_γ(z)[1−(1−ε)z²/γ²].                (3)
```

For `0≤ε<1`, one pair of zeros is at
`±γ/√(1−ε)`; it moves outward on the real axis and escapes to infinity
as `ε↑1`. Every other Xi zero retains its original location and at
least its original multiplicity; a moving root can add a multiplicity
when it crosses another real Xi zero. At `ε=1` the selected pair is deleted. When `±γ` are
simple, neither remains a zero at `ε=1`; for higher multiplicity, one
copy is removed. The total mass is constant along the flow.

The corpus proves unconditionally that simple real Xi zeros exist in
superlinear quantity, so this theorem supplies actual unconditional
instances. It neither creates an off-line zero nor proves that all Xi
zeros are real.

## Proof

The corpus proves `k>0`, evenness, global strict log-concavity, and
every-rate exponential derivative decay. Strict log-concavity and
evenness imply `k'(y)<0` for `y>0`. For `x≥0`, integration by parts
with the nonnegative primitive `1−cos(γt)` gives

```text
g_γ(x)=∫₀∞ [1−cos(γt)] [−k'(x+t)]dt > 0.        (4)
```

The boundary terms vanish: the primitive is zero at `t=0` and bounded
at infinity, while `k(x+t)→0`. The integrand is nonnegative and is
strictly positive on an open subset of `(0,∞)`. Equivalently, one may
pair consecutive sine half-periods. With `f_x(t)=k(x+t)`, this gives

```text
∫₀∞ sin(γt)f_x(t)dt
 = Σ_{n≥0} ∫_{2nπ/γ}^{(2n+1)π/γ}
     sin(γt)[f_x(t)−f_x(t+π/γ)]dt  > 0.         (4a)
```

The series and integrals converge absolutely because `k` decays faster
than every exponential; each bracket is strictly positive. Thus (1)
is positive for `x≥0`, and evenness makes it positive everywhere.

For `x≥0`, differentiating under the integral or the equivalent
one-sided form

```text
g_γ(x)=γ∫_x∞ sin(γ(t−x))k(t)dt
```

gives `g_γ''+γ²g_γ=γ²k` on `(0,∞)` and

```text
g_γ'(0+) = −γ²∫₀∞ cos(γt)k(t)dt = −γ²F(γ)/2 = 0.
```

The even reflection is therefore `C²`; the differential equation and
even smoothness of `k` recursively make it `C∞` across zero. It obeys
the same equation on all of `ℝ`.

The first-atom tail gives `−(log k)'(x)≥c exp(2x)` for all large `x` and
some `c>0`. Concavity of `log k` therefore yields, for `t≥0`,
`k(x+t)≤k(x)exp(−c exp(2x)t)`. Consequently

```text
0 < g_γ(x) ≤ γ∫₀∞ k(x+t)dt
             ≤ [γ/(c exp(2x))]k(x)             (x≫1).   (5)
```

The same holds on the negative tail by evenness. On the remaining
compact interval, `g_γ/k` is bounded by continuity and `k>0`.
The integral formula and the ODE give every-rate exponential decay for
`g_γ` and its derivatives, so its Fourier transform is entire.

Fourier transformation of the global ODE gives
`(γ²−z²)G_γ(z)=γ²F(z)`. Since `F(±γ)=0` (evenness), division extends
entirely across both points and proves (2). At `z=0` it gives
`G_γ(0)=F(0)`, the mass identity. Algebra gives (3), and its explicit
roots give the stated zero flow. Positivity of the convex combination
is immediate from positivity of both sources.

## Sharp boundary and limitation

The [relative-source rigidity theorem](../../2-fully-proven/theta/theta-tail-divisor-capacity-threshold.md)
proves that a source bounded in absolute value by `Ck` cannot preserve
the **complete** Xi divisor unless it is a scalar multiple of `k`.
Formula (1) shows that deleting just one real zero pair opens a positive
relative-source direction. The full-divisor hypothesis in that rigidity
theorem is therefore exact; it cannot be weakened to all but finitely
many Xi zeros.

This is a source-cone flow, not a producer of RH. Its input is an already
known real Xi zero and its source differs from the literal modular/Euler
source. It demonstrates why positivity, even together with the positions
of all *other* zeros, cannot locate the selected pair without an exact
arithmetic constraint.

## Formalization gate

- [x] Paper proof using corpus positivity, strict log-concavity,
      first-atom tail, entire Fourier identity, and a real Xi zero.
- [x] Formalize positivity through the `1−cos` integration-by-parts
      identity and the negative derivative of the strict even
      log-concave source.
- [x] Formalize the source integral, ODE, smooth even join, relative
      tail bound, and entire Fourier division.
- [x] Formalize the positive flow and exact zero-pair motion, then wire
      completed leaf modules into the RHTower umbrella.

The half-period sine argument and Fourier/ODE identities are classical.
The exact completed-theta positive zero-deletion flow was not located in
the current corpus search; no external publication novelty is claimed.

## Log
- 2026-09-27 — all theorem items formalized unconditionally in `ThetaZeroDivisionSource` (general complex zero-division layer, theta specialization, positive flow, multiplicity bookkeeping; instances from Hardy's theorem); moved to 3-formalized.

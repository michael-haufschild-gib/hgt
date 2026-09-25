# Prime Poisson commutator carries the flat theta primitive's bulk chirality

- **ID:** `stc-poisson-thermal-chirality-flat-primitive`
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM and sharp transport boundary
- **Routes:** STC, RHist, U, CSB, K-RVM, MPLF
- **Status:** `[PROVED HERE ON PAPER] [BULK SYMBOL EVENNESS AND STRICT DECREASE IN LEAN] [FULL OPERATOR FORMALIZATION OPEN] [NOT AN RH PROOF]`
- **Dependencies:** [Poisson/Mertens clock commutator](stc-poisson-mertens-clock-commutator.md), [trace-class prime defect](stc-mertens-trace-class-xi-divisor-barrier.md), [flat theta one-port](theta-quantile-critical-one-port-rigging.md), `HTGeometry/CoshFourierTransform.lean`, and the exact Mertens error in `Sieve/MertensSecondSharp.lean`.

## Reinterpretation and exact statement

The flat theta one-port has a universal bulk primitive: on
mean-zero compact tests in `L²(ℝ)`,

```text
(Hf)(x)=∫_(-∞)^x f(y)dy,       S=iH.
```

Use Fourier convention `f̂(ξ)=∫_ℝf(x)e^(iξx)dx` and take the
self-adjoint Fourier-multiplier realization of `S` as
multiplication by `−1/ξ` on its maximal domain. The prime
Poisson/Mertens bulk is full-line convolution `W_full` by
`h(x)=sech²(x/2)` before half-line compression. Put `Xf(x)=xf(x)`
and `J_full=i[X,W_full]`, taking the bounded commutator extension.
Then:

1. The exact Fourier multipliers are

   ```text
   W_full ↔ m(ξ)=4πξ/sinh(πξ),       m(0)=4,
   J_full ↔ m'(ξ),
   S      ↔ −1/ξ.                                       (1)
   ```

   Equivalently `W_full=F(S)` and `J_full=G(S)` in bounded
   Borel functional calculus, where for `t≠0`

   ```text
   F(t)=4π/[t sinh(π/t)],       G(t)=m'(−1/t),
   F(0)=G(0)=0.
   ```

   Both are bounded; `F` is even and `G` is odd with
   `sgn G(t)=sgn t`. This is an exact hyperbolic regularization
   of the singular flat primitive, rather than a similarity
   between the full prime and theta operators.

   `m` is positive and even, strictly decreasing in `|ξ|>0`.
   Its derivative is odd and has sign `−sgn ξ`. Consequently

   ```text
   sgn(J_full)=sgn(S)       almost everywhere in Fourier space. (2)
   ```

   The positive Poisson Gram alone identifies `|ξ|` but loses
   frequency orientation. Its clock commutator recovers that
   orientation exactly in the translation-invariant bulk. The
   joint symbol `(m(ξ),m'(ξ))` is injective on `ℝ`.
2. Let `U` be the harmonic-prime-cell isometry, `K` the literal
   prime Poisson Gram, `A=UKU*` on `L²(0,∞)`, and `W` the
   half-line compression of `W_full`. Let `X_P` multiply a prime
   coordinate by `log log p`, and let `C_P=i[X_P,K]` denote the
   bounded self-adjoint commutator extension. Then

   ```text
       U C_P U* − P_+ J_full P_+ ∈ Schatten₁.             (3)
   ```

   Thus the **signed** prime commutator, as well as the positive
   Gram, has the universal flat bulk modulo a trace-class
   arithmetic defect. This does not identify it with the
   determinant-bearing theta inverse.
3. The sign operation needed to extract chirality is singular at
   zero. Trace-class closeness in (3) alone cannot transfer a
   Hardy polarization: compact self-adjoint `L,L'` can satisfy
   `L−L'∈Schatten₁` while `sgn L−sgn L'` is noncompact. Hence
   (2) identifies a candidate **orientation carrier**, not an
   arithmetic proof of the theta boundary-port balance.
4. The other singularity lies at the **top edge `4`** of the prime
   continuum band. As `ξ→0`,

   ```text
   4−m(ξ)=(2π²/3)ξ²+O(ξ⁴),
   m'(ξ)=−(4π²/3)ξ+O(ξ³),
   (−1/ξ)m'(ξ)→4π²/3.                              (5)
   ```

   Thus recovering the flat theta primitive from the positive
   prime bulk requires a square-root edge inverse:
   `|S|∼π√(2/3)/√(4−W_full)` in Fourier space. The signed
   commutator fixes its orientation, while the edge inverse
   supplies its unbounded magnitude. This locates a possible
   **singular** source transport; it does not establish that the
   arithmetic defect survives it with the Xi divisor or correct
   port sign.
5. Half-line compression creates a **nonzero trace commutator**.
   Write `W=P_+W_full P_+`, `J=P_+J_full P_+`, and retain the prime
   pair `A=UKU*`, `C=UC_PU*`. Both `[W,J]` and `[A,C]` are trace
   class, and

   ```text
   tr[A,C] = tr[W,J]
           = 2i ∫₀^∞ u² sech⁴(u/2)du
           = i/(2π) ∫_ℝ |m'(ξ)|²dξ ≠ 0.               (6)
   ```

   This scalar is a boundary orientation anomaly. It survives the
   literal prime correction exactly, yet contains no arithmetic
   information able by itself to select the Xi divisor.

This locates the missing cross-route operation. Prime Poisson
history has the absolute spectral scale `m`; its Mertens-clock
commutator supplies the missing odd orientation. A source-faithful
RH bridge must additionally control the singular sign extraction,
the half-line boundary and the theta weighted-domain/port
selection. The previous trace-class Xi-divisor mismatch rules out
identifying the arithmetic correction alone with the Xi inverse.

## Full-line proof

The `s=2` hyperbolic-secant Fourier formula already identified
in the trace-class card gives

```text
∫_ℝ sech²(x/2)e^(iξx)dx=4πξ/sinh(πξ),
```

with limit `4` at `ξ=0`. Since `xh(x)` is integrable,
differentiation under the integral gives
`m'(ξ)=i∫xh(x)e^(iξx)dx`. The commutator has kernel
`(x−y)h(x−y)`, so its Fourier multiplier is
`i∫xh(x)e^(iξx)dx=m'(ξ)` after the prefactor `i` in `J_full`.
For a mean-zero compact test, integration by parts gives
`Ĥf(ξ)=i f̂(ξ)/ξ`; therefore `S=iH` has multiplier `−1/ξ`.

For `ξ>0`, set `t=πξ`. The numerator of `m'(ξ)` has the sign
of `sinh t−t cosh t`. This expression vanishes at zero and has
derivative `−t sinh t<0`, so `m'(ξ)<0`; oddness gives the
opposite sign for `ξ<0`. This proves (2). Since `m` is strictly
decreasing in `|ξ|`, equality of two `m` values forces equal
absolute frequencies; the sign of `m'` distinguishes them
unless both are zero. The joint symbol is injective.

The Taylor series `sinh t=t+t³/6+O(t⁵)` at `t=0`, applied to
`m(ξ)=4t/sinh t` with `t=πξ`, gives (5). Solving the first
asymptotic for `1/|ξ|` proves the square-root edge law. Since
`m(ξ)↑4` as `ξ→0`, this is the actual top edge of the bulk
band, not an arbitrary regularization parameter.

## Prime-cell trace-class lift

The preceding trace-class theorem gives `A=W+E`, `E∈S₁`, and
a step clock `φ(y)=log log p+B=y+δ(y)` on prime cell `I_p`,
with `|δ(y)|≤D e^(−y)`. Constants commute, so

```text
U C_P U* = i[M_φ,A],
U C_P U* − i[Y,W]
          = i[Y,E]+i[M_δ,W]+i[M_δ,E],                 (4)
```

where `Y` is multiplication by `y` on the half-line. The first
term is trace class despite unbounded `Y`: on unit blocks
`Q_j×Q_k`, write `y−z=(j−k)+(y−j)−(z−k)`.
The prior local nuclear estimate

```text
‖1_(Q_j)E1_(Q_k)‖₁
 ≤ C(e^(−j)+e^(−k))e^(−c|j−k|)
```

therefore bounds the corresponding `[Y,E]` block by the same
right side times `|j−k|+2`, still summable over `j,k`.
The finitely many initial-cell rows are finite rank for `A`;
their `Y`-weighted columns remain in `L²` by exponential
off-diagonal decay. Initial rows of `W` remain nuclear after
multiplication by `y−z` by the same local smooth-kernel argument.

For `[M_δ,W]`, each local convolution block of `W` is nuclear
with norm `O(e^(−c|j−k|))`; left and right multiplication by
`δ` costs `O(e^(−j)+e^(−k))`, again summable. For
`[M_δ,E]`, use the preceding nuclear bound for `E` and the
same bounded multipliers. Thus all three terms of (4) are
trace class. Finally `i[Y,W]=P_+J_full P_+`, proving (3).

The singularity in item 3 is sharp. On `ℓ²(ℕ)`, set
`L e_n=2^(−n)e_n` and `L' e_n=(−1)^n2^(−n)e_n`.
Then `L−L'` is trace class, since the sum of its diagonal
moduli is finite. But `sgn L=I` while
`sgn L' e_n=(−1)^n e_n`, so their sign difference has value
`2e_n` on infinitely many odd coordinates and is not compact.
This explicitly blocks the inference from (3) to an oriented
theta port without further arithmetic control near zero.

## Exact half-line boundary trace

The full-line multipliers `m` and `m'` commute. For `x,y>0`, their
half-line compressions instead have commutator kernel

```text
[W,J](x,y)
  = i ∫_(-∞)^0 (x+y−2z)h(x−z)h(y−z)dz.                (7)
```

Indeed, insert `I=P_++P_-` between the full-line operators in
their zero commutator. The crossing terms over `z<0` give (7).
Let `a_z(x)=(x−z)h(x−z)` and `b_z(x)=h(x−z)` for `x>0`.
The integrand in (7) is the sum of two rank-one kernels
`a_z⊗b_z+b_z⊗a_z`. Their trace norms have integrable bound
`2‖a_z‖₂‖b_z‖₂`: `h(u)≤4e^(−u)` for `u>0` makes this decay
exponentially as `z→−∞`, while it is bounded near zero. Thus
`[W,J]∈S₁`, and rank-one trace followed by Fubini gives

```text
tr[W,J]
 = 2i ∫_(-∞)^0∫₀^∞ (x−z)h(x−z)² dx dz
 = 2i ∫₀^∞ u²h(u)²du.
```

Plancherel for `m=Fourier(h)` gives the last expression of (6).
Finally `A=W+E` and `C=J+F` with `E,F∈S₁` by (3) and the
prior prime-cell theorem. Expanding `[A,C]−[W,J]` yields
`[E,J]+[W,F]+[E,F]`. Each is trace class with trace zero by
cyclicity of a trace-class factor against a bounded operator.
This proves the exact prime trace in (6). Its strict nonzero
value follows from `h(u)>0` for `u>0`.

## Conjecture loop and remaining gate

- **K alone determines the theta chirality:** false. Its bulk
  multiplier `m` is even and cannot distinguish `ξ` from `−ξ`.
- **K together with the Mertens-clock commutator carries bulk
  chirality:** proved by (1)--(3). This is an exact oriented
  cross-route bridge at the level of universal bulk symbols.
- **Trace-class closeness transfers the sign projection and hence
  RH:** false as a general principle by the diagonal example.
- **The prime arithmetic defect changes the oriented boundary
  trace:** false; (6) proves this trace is exactly universal.

The surviving conjecture is a **source-specific, singular
transport** from the oriented prime bulk through its `4`-edge
inverse and the theta weighted-domain port. It must retain the
Xi determinant and control the commutator's near-zero spectrum;
neither property follows from this theorem.

**Audit:** `STCPoissonThermalChirality.lean` proves the real thermal
symbol is even and strictly decreasing on positive frequencies.
The Fourier-multiplier identity, full-line operator chirality,
prime-cell trace-class lift, and boundary trace anomaly remain
paper proofs using the cited corpus facts. The sign-instability
example is elementary and paper-proved. External novelty is
unverified.

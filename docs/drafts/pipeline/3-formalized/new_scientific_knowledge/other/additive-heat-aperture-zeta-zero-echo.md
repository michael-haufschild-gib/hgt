# Additive heat-aperture energy detects zeta zeros by loss of the subleading echo

- **ID:** `additive-heat-aperture-zeta-zero-echo`
- **Stage:** 3-formalized / candidate-new
- **Type:** THEOREM (paper); candidate source measurement
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`; proof and preliminary parent audit
  complete, independent expert verification pending
- **Source:** the full normalized prime density matrix coupled to the additive heat kernel on the
  integer lattice
- **Statement:** For every `s=sigma+it` with `1/2<sigma<1`, a canonical strictly positive heat
  quadratic form of the normalizable vector `(n^(-s))` has a polyhomogeneous small-time expansion.
  Its subleading complex coefficient is an explicit nonzero Gamma factor times `conj(zeta(s))`.
  Hence a zeta zero in the Hilbert strip is exactly the disappearance of the subleading
  particle--wave interference echo.

## Why this is a joint measurement

Let

```text
Psi_s(n)=n^(-s)/sqrt(zeta(2 sigma)),
```

which belongs to `l2(N)` exactly when `sigma>1/2`.  For `x>0`, define the additive heat operator

```text
H_x(m,n)=exp(-pi x (m-n)^2).
```

The kernel depends on additive separation `m-n`; the state depends on multiplicative prime
factorization.  Their quadratic form

```text
E_s(x)=<Psi_s,H_x Psi_s>
      = (1/zeta(2 sigma))
        sum_(m,n>=1) m^(-conj(s)) n^(-s)
          exp(-pi x (m-n)^2)                            (1)
```

is therefore a literal additive--multiplicative joint observable of the full density, including
every off-diagonal coherence.

For every `x>0`, the series in (1) is absolutely convergent.  If `k=m-n` is fixed, the inner sum is
bounded by a translate of `sum_n n^(-2 sigma)`; summing over `k` is then controlled by the Gaussian.

The kernel is strictly positive definite.  Its circle Fourier multiplier is

```text
W_x(theta)=sum_(k in Z) exp(-pi x k^2) exp(ik theta)>0,
```

the strict positivity following also from Poisson summation.  Thus `E_s(x)>0` for every `x>0`.
No zeta zero is inserted into the definition.

The two aperture limits have the expected meanings:

```text
x -> infinity: H_x(m,n) -> 1_(m=n),     E_s(x) -> 1;
x -> 0:        H_x(m,n) -> 1,           full wave coherence.
```

For `sigma>1`, dominated convergence gives

```text
E_s(x) -> |zeta(s)|^2/zeta(2 sigma)
```

as `x` decreases to zero.  The theorem below identifies what replaces this limit in the Goldilocks
strip `1/2<sigma<1`.

## Fourier representation

Let

```text
f_s(theta)=sum_(n>=1) n^(-s) exp(in theta)
```

as an `L2(S^1)` boundary function.  It exists because `sigma>1/2`.  Fourier multiplication gives

```text
E_s(x)
  = (1/zeta(2 sigma))
    integral_(-pi)^pi W_x(theta)|f_s(theta)|^2 dtheta/(2pi).  (2)
```

Poisson summation gives

```text
W_x(theta)
  = x^(-1/2) sum_(ell in Z)
      exp(-(theta-2pi ell)^2/(4pi x)).                  (3)
```

Thus `W_x dtheta/(2pi)` is a Gaussian approximate identity at the additive phase `theta=0`, with
variance `2pi x`.

## Local source expansion

For `|theta|<2pi`, Jonquiere's expansion of the polylogarithm gives

```text
f_s(theta)
  = Gamma(1-s)(-i theta)^(s-1)
    + zeta(s) + O_s(theta).                             (4)
```

No value of a divergent Dirichlet series is used in the definition of `f_s`; equation (4) is the
local continuation theorem for its `L2` boundary germ.

For positive and negative `theta`, put

```text
A_+(s)=Gamma(1-s) exp(-i pi(s-1)/2),
A_-(s)=Gamma(1-s) exp(+i pi(s-1)/2).
```

Then (4) says

```text
f_s(theta)
  = A_+(s) theta^(s-1)+zeta(s)+O_s(theta),      theta>0,
f_s(theta)
  = A_-(s) |theta|^(s-1)+zeta(s)+O_s(theta),   theta<0. (5)
```

## Gaussian moments

For every complex `lambda` with `Re(lambda)>-1`, (3) gives

```text
integral_(-pi)^pi W_x(theta)|theta|^lambda dtheta/(2pi)
  = (4pi x)^(lambda/2)
      Gamma((lambda+1)/2)/sqrt(pi)
    + O_lambda(exp(-c/x)).                              (6)
```

The proof is the ordinary absolute moment of a centered Gaussian; the other terms in (3) are
exponentially remote from zero.

Both exponents required below satisfy the integrability condition:

```text
2 sigma-2 > -1,
Re(s-1)=sigma-1 > -1.
```

## Heat-aperture expansion theorem

`[PROVED]` Fix `s=sigma+it` with `1/2<sigma<1`.  As `x` decreases to zero,

```text
zeta(2 sigma) E_s(x)
  = L(s) x^(sigma-1)
    + C(s) conj(zeta(s)) x^((s-1)/2)
    + conj(C(s) conj(zeta(s)) x^((s-1)/2))
    + |zeta(s)|^2
    + o(1),                                             (7)
```

where

```text
L(s)
  = |Gamma(1-s)|^2 cosh(pi t)
    (4pi)^(sigma-1) Gamma(sigma-1/2)/sqrt(pi),          (8)

C(s)
  = Gamma(1-s) sin(pi s/2)
    (4pi)^((s-1)/2) Gamma(s/2)/sqrt(pi).                (9)
```

Moreover `L(s)>0` and `C(s)!=0` throughout the open strip.

The coefficient has the simpler completed-source form

```text
C(s) = (1/2) pi^((s-1)/2) Gamma((1-s)/2).              (9a)
```

Indeed `sin(pi s/2)Gamma(s/2)=pi/Gamma(1-s/2)`, and the duplication formula at
`(1-s)/2` gives

```text
Gamma((1-s)/2) Gamma(1-s/2)=2^s sqrt(pi) Gamma(1-s).
```

Substitution into (9) proves (9a).

### Proof

Insert (5) into `|f_s(theta)|^2`.  On each side of zero there are four types of term.

1. The singular square is

   ```text
   |A_+|^2 theta^(2 sigma-2)
   ```

   on the positive side and the analogous `|A_-|^2` term on the negative side.  Since `W_x` is
   even, (6) averages their coefficients.  Directly,

   ```text
   (|A_+|^2+|A_-|^2)/2
     = |Gamma(1-s)|^2 cosh(pi t),
   ```

   which gives (8).

2. The singular--regular cross term has complex coefficient

   ```text
   ((A_+(s)+A_-(s))/2) conj(zeta(s)).
   ```

   The elementary identity

   ```text
   (A_+(s)+A_-(s))/2
     = Gamma(1-s) sin(pi s/2)
   ```

   together with the moment (6) at `lambda=s-1` gives (9) and the conjugate term in (7).

3. The regular square contributes exactly `|zeta(s)|^2`, because the approximate identity has
   total mass one.

4. The remainder in (5) is `O(theta)`.  Its product with the singular term is
   `O(|theta|^sigma)`, and all other remainder terms vanish at least linearly.  Equation (6) shows
   that every such contribution is `o(1)`.

This proves (7).  Positivity of `L` is immediate.  Gamma has no zeros, and neither `1-s` nor `s/2`
is a Gamma pole in the strip.  Also `sin(pi s/2)` has no zero there.  Hence `C(s)!=0`.  QED.

## Exact zero detector

`[PROVED]` If `t!=0`, the two powers

```text
x^((s-1)/2),   x^((conj(s)-1)/2)
```

are distinct log-oscillatory asymptotic channels.  The coefficient of the first is

```text
C(s) conj(zeta(s)).                                    (10)
```

Since `C(s)!=0`, this subleading channel is absent exactly when `zeta(s)=0`.

For real `s in (1/2,1)`, all factors in (9) are real and nonzero and `zeta(s)<0`; hence the merged
real subleading coefficient is also nonzero.  Thus for every `s` in the Goldilocks strip,

```text
zeta(s)=0
  iff
the subleading heat-aperture echo in (7) vanishes.      (11)
```

The complete shifted-value expansion and its single-missing-rung law are recorded in
`additive-heat-aperture-shifted-zeta-echo-ladder.md`. The `k`-th complex channel is an explicit
nonzero archimedean factor times `conj(zeta(s-k))`; every channel with `k>=1` is nonzero throughout
the strip.

On the critical line, `1-conj(s)=s`, so (9a) identifies the two echo coefficients exactly as

```text
conj(C(s)) zeta(s)
  = (1/2) pi^(-s/2) Gamma(s/2) zeta(s),

C(s) conj(zeta(s))
  = conjugate((1/2) pi^(-s/2) Gamma(s/2) zeta(s)).      (11a)
```

Thus the screen echo is literally one half of the completed zeta amplitude and its conjugate.  Off
the line, the echo instead multiplies the zeta value at `s` by the archimedean factor at the
different parameter `1-conj(s)`.  This is the exact completion mismatch that the superselection
descent must resolve.

## Canonical nonzero tangent at every echo defect

Define the regularized local germ

```text
R_s(theta)
  = f_s(theta)-Gamma(1-s)(-i theta)^(s-1).
```

Jonquiere's expansion gives

```text
R_s(theta)
  = zeta(s)+i zeta(s-1) theta+O_s(theta^2).             (11b)
```

`[PROVED]` If `1/2<Re(s)<1` and `zeta(s)=0`, then

```text
R_s(0)=0,
R_s'(0)=i zeta(s-1)!=0.                                (11c)
```

To prove nonvanishing, put `w=s-1`.  Then `-1/2<Re(w)<0`.  The functional equation expresses
`zeta(w)` as a product of nonzero elementary Gamma/trigonometric factors and `zeta(1-w)`, where
`Re(1-w)>1`.  The Euler product makes the last factor nonzero, and `w` is not a negative even
integer, so no trivial zero occurs.  Hence `zeta(s-1)!=0`.

This tangent is source-built, nonzero even at a multiple zero in the spectral parameter, and does
not divide by `zeta'(s)`. It supplies the required nonvanishing value. RH localization additionally
requires the primewise covariance value that characterizes a normal reflected intertwiner exactly
on the critical line.

This is not point sampling of an `L2` boundary class.  The entire function `E_s(x)` for `x>0` is a
strictly positive, absolutely convergent quadratic measurement of the full density.  The zeta
value is recovered as a uniquely identifiable asymptotic coefficient of that measurement.

The constant term also gives the canonical polyhomogeneous finite part

```text
FP_(x->0) E_s(x)=|zeta(s)|^2/zeta(2 sigma),             (12)
```

where `FP` means the coefficient of `x^0` after all nonzero powers in the intrinsic expansion are
removed.  Equation (12) is a consequence, not the definition, of the source measurement.

## Completed intensity

Multiplying (12) by the explicit nonzero archimedean weight

```text
zeta(2 sigma)
  * |(1/2)s(s-1) pi^(-s/2) Gamma(s/2)|^2
```

gives `|xi(s)|^2`.  Thus the additive heat aperture constructs the completed intensity from the
full prime density throughout `1/2<Re(s)<1`, with no zero divisor in its definition.

The Gamma factor is not cosmetic. The almost-periodicity theorem for bounded prime-screen
observables positively identifies an additional noncompact archimedean value as necessary for
vertical decay beyond the compact prime phase algebra.

## Superselection verdict

The theorem closes the **measurement-existence** half of the screen proposal on the right Hilbert
side:

- the object is source-defined, positive for every finite aperture, and phase-sensitive;
- it interpolates from the particle diagonal to full wave coherence;
- its missing subleading channel has exactly the zeta divisor; and
- its finite part gives the completed intensity after the canonical archimedean weight.

It does not close the **wall-localization** half.  A hypothetical off-line zero with
`1/2<Re(s)<1` would also remove the subleading echo while leaving the reflected sector disjoint.
The separate terminal theorem
`heat-echo-superselection-descent-is-rh.md` proves that asking disappearance of the heat echo to
create a reflected-sector morphism is exactly RH, not an independent intermediate statement.

## Source-separation tests

- A particle-only observable contains only diagonal values; reproducing (7) therefore requires the
  additional off-diagonal `m-n` coherence.
- A bounded prime-torus observable has an almost-periodic height signal; reproducing (7) therefore
  requires the additional noncompact value carrying the additive small-time singular expansion.
- A completely multiplicative phase twist changes the off-diagonal heat energy, so the detector is
  not local-unitary invariant.  Whether the exact theta completion rejects every prescribed-divisor
  Helson twist remains open.
- Replacing `m-n` by `log(m/n)` returns to the multiplicative Bohr screen and loses the fixed
  additive reference.

## Novelty and significance verdict

The ingredients are classical: positivity of the Gaussian Toeplitz kernel, the polylogarithm
boundary expansion, Poisson summation, and Gaussian moments.  The preliminary parent audit checked
exact-formula and equivalent searches across periodic-zeta Gaussian summability, polylogarithm heat
regularization, shifted-convolution heat kernels, heat-content asymptotics, and quantum-coherence
language.  It located the individual parents but no statement equivalent to (7), (11), or (12).

The closest exact parent is the standard local expansion

```text
Li_s(z)=Gamma(1-s)(log(1/z))^(s-1)
        + sum_(n>=0) zeta(s-n)(log z)^n/n!,
```

recorded as DLMF 25.12.12.  General heat-kernel/polyhomogeneous theory guarantees that conormal
boundary germs produce small-time expansions, but it does not identify this full-density
observable, isolate the half-order echo, or state its zero-locus consequence.  Shifted-convolution
and zeta-moment papers study different averages and kernels.

The novelty verdict is therefore provisionally positive: the theorem is not a renamed parent
result, and the zeta coefficient appears in a new observable role.  Because the proof is elementary
once the correct observable is found, independent expert comparison remains mandatory before
publication.

The significance gate passes: unlike a restatement of analytic continuation, the theorem
constructs an everywhere finite positive observable from the normalizable prime state and reads a
zeta zero from its asymptotic channel structure. It survives as a measurement theorem. A
zero-to-superselection descent requires the additional reflected covariance value named above.

## Gates

- [x] 0 -> 1: additive heat aperture, convergence region, positivity, and exact asymptotic target
  isolated
- [x] 1 -> 2: complete paper proof of the expansion, coefficient nonvanishing, zero equivalence,
  and finite part
- [x] preliminary parent novelty audit: exact/equivalent and broader parent searches completed; no
  equivalent theorem located
- [ ] independent proof audit: branch conventions and the complex Gaussian moment coefficient
- [x] 2 -> 3: fully formalized in Lean 4, unconditionally and axiom-clean; the polylog boundary
  asymptotics were built from scratch (`HurwitzZetaSmallShift`, `JonquiereExpansion`)

## Parent references

- [NIST DLMF 25.12.12, local polylogarithm expansion](https://dlmf.nist.gov/25.12.E12).
- [NIST DLMF 25.13, periodic zeta function](https://dlmf.nist.gov/25.13).
- [NIST DLMF 1.8(iv), Poisson summation](https://dlmf.nist.gov/1.8#iv).

## 2026-08-16 — Jonquière's expansion `(4)`/`(5)` is formalized unconditionally

Equation `(4)`, the local continuation theorem for the `L²` boundary germ of `f_s`, is now
Lean-closed on both sides of the phase origin.  Every declaration reports
`propext, Classical.choice, Quot.sound`.

**The missing input was the small-shift expansion of the Hurwitz zeta function.**  Mathlib carries
`hurwitzZeta`, `expZeta` and Hurwitz's formula `expZeta_one_sub`, but nothing about the behaviour
of `ζ(w, a)` as the shift `a` tends to zero, and its `a` lives on `UnitAddCircle`, so there is no
differentiability-in-`a` API to appeal to.

`formal/GaloisForLFunctions/RHTower/HurwitzZetaSmallShift.lean` builds it from the difference
series

```text
shiftDiffTerm b w n   = (n+1+b)^{-w} - (n+1)^{-w}
shiftDiffSeries b w   = ∑_{n ≥ 0} shiftDiffTerm b w n
```

- `norm_cpow_shift_sub_le` — the mean-value bound `‖(x+b)^{-w} - x^{-w}‖ ≤ ‖w‖ 2^{Re w+1} x^{-Re w-1}|b|`
  for `x ≥ 1`, `|b| ≤ 1/2`, obtained from `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on
  the segment `[x, x+b]`, which stays in `[x/2, ∞)`.
- `summable_norm_shiftDiffTerm`, `norm_shiftDiffSeries_le` — absolute convergence for **every**
  `Re w > 0` (not only `Re w > 1`), with the explicit linear bound
  `‖shiftDiffSeries b w‖ ≤ ‖w‖ 2^{Re w+1} ζ(Re w+1) |b|`.
- `differentiableAt_shiftDiffSeries` — analyticity in `w` on `Re w > 0`, by
  `differentiableOn_tsum_of_summable_norm` on a ball `B(w₀, Re w₀/2)`, where `‖w‖`, `Re w` and hence
  the majorant are uniform.
- `hurwitzZeta_sub_riemannZeta_eq` and `hurwitzZeta_neg_sub_riemannZeta_eq` — the identities

  ```text
  ζ(w, a)   - ζ(w) = a^{-w} + shiftDiffSeries a w        (0 < a ≤ 1/2)
  ζ(w, -a)  - ζ(w) =           shiftDiffSeries (-a) w
  ```

  for every `Re w > 0`.  Both are proved in the convergent regime `Re w > 1` from
  `hasSum_hurwitzZeta_of_one_lt_re` and then continued: the *difference*
  `ζ(·, a) - ζ` is entire (`differentiable_hurwitzZeta_sub_hurwitzZeta`), so the pole at `w = 1`
  never appears and the identity theorem runs on the convex half plane `{Re w > 0}` rather than on
  a punctured one.

**Jonquière.**  `formal/GaloisForLFunctions/RHTower/JonquiereExpansion.lean` combines Hurwitz's
formula, the two small-shift expansions, and the functional equation `riemannZeta_one_sub`:

```text
expZeta_eq_jonquiere         (0 < Re s < 1, 0 < θ ≤ π) :
    Li_s(e^{iθ}) = A₊(s) θ^{s-1} + ζ(s) + jonquiereRemainder s θ
expZeta_neg_eq_jonquiere     : the same with A₋(s) at the phase -θ
norm_expZeta_sub_jonquiere_le, norm_expZeta_neg_sub_jonquiere_le :
    ‖Li_s(e^{±iθ}) - (A_±(s) θ^{s-1} + ζ(s))‖ ≤ jonquiereConst s · θ
```

with `A₊(s) = Γ(1-s) e^{iπ(1-s)/2}`, `A₋(s) = Γ(1-s) e^{-iπ(1-s)/2}` — exactly the card's `(5)` —
and `jonquiereConst s` an explicit nonnegative constant.  The constant-term identification is the
one-line miracle of the functional equation: `(2π)^{s-1} Γ(1-s) ζ(1-s) · 2cos(π(1-s)/2)` **is**
`ζ(s)`.

**What remains for this card.**  The Gaussian-moment asymptotic `(6)`, and the assembly `(7)`.

### The Gaussian moment `(6)`: the exact half-line integral is formalized

`formal/GaloisForLFunctions/RHTower/GaussianAbsoluteMoment.lean` (unconditional,
`propext, Classical.choice, Quot.sound`):

```text
integral_cpow_mul_exp_neg_mul_sq_Ioi  (-1 < Re λ, 0 < b) :
    ∫_{(0,∞)} θ^λ e^{-bθ²} dθ = ½ (1/b)^{(λ+1)/2} Γ((λ+1)/2)
```

proved by the substitution `t = θ²` (`integral_comp_rpow_Ioi_of_pos` at `p = 2`) fed into
mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi`.  Supporting lemma `cpow_sq_ofReal`:
for a positive real base, `((x²))^c = x^{2c}`.

Because the integrand of `(6)` is even, only half-line integrals are ever needed: with
`b = 1/(4πx)` the `ℓ = 0` term of the Poisson form `(3)` contributes exactly
`(4πx)^{λ/2} Γ((λ+1)/2)/√π`, which is the stated main term.

**What remains for `(6)`.**  The Poisson/theta identity `(3)` (mathlib's `jacobiTheta₂`
functional equation), and the two exponentially small corrections: truncating the `ℓ = 0`
Gaussian from `[0,∞)` to `[0,π]`, and the `ℓ ≠ 0` terms.

### The Poisson form `(3)` is formalized

`formal/GaloisForLFunctions/RHTower/AdditiveHeatKernel.lean` (unconditional, axiom-clean):

```text
heatMultiplier x θ            = ∑_{k ∈ ℤ} exp(-π x k² + i k θ)
heatMultiplier_eq_jacobiTheta₂ : heatMultiplier x θ = jacobiTheta₂ (θ/2π) (i x)
heatMultiplier_poisson (0 < x) : heatMultiplier x θ
    = x^{-1/2} · ∑_{ℓ ∈ ℤ} exp(-(θ - 2πℓ)²/(4πx))
```

This is `(3)`: mathlib's `jacobiTheta₂_functional_equation` at `τ = i x`, where the prefactor
`1/(-i τ)^{1/2}` is exactly `x^{-1/2}`, the Gaussian factor `exp(-π i z²/τ)` is `exp(-π z²/x)`,
and the transformed theta series recombines termwise into `∑_n exp(-π(z-n)²/x)` at `z = θ/2π`.

`formal/GaloisForLFunctions/RHTower/GaussianAbsoluteMoment.lean` also gained the real-variable
moment `integral_rpow_mul_exp_neg_mul_sq_Ioi` and the exponentially small tail

```text
norm_integral_cpow_mul_exp_neg_mul_sq_Ioi_le (0 ≤ c) :
    ‖∫_{(c,∞)} θ^λ e^{-bθ²} dθ‖ ≤ e^{-bc²/2} · ½ (2/b)^{(Re λ+1)/2} Γ((Re λ+1)/2)
```

which is the shape that makes the `[0,π]` truncation of the `ℓ = 0` Gaussian `O(e^{-c/x})`.

**What remains for `(6)`.**  Interchanging the `ℓ`-sum with the integral, and the `ℓ ≠ 0` bound
`|θ - 2πℓ| ≥ π|ℓ|` on `(0, π]`, which makes those terms `O(e^{-π/(4x)})` uniformly for `x ≤ 1`.
Then `(2)` (Parseval for the convolution operator) and the assembly `(7)`.

### The Poisson form is split and its off-centre mass bounded

`formal/GaloisForLFunctions/RHTower/HeatMultiplierReal.lean` and
`.../HeatMultiplierTail.lean` (both unconditional, axiom-clean):

```text
heatGauss x n θ            = exp(-(θ - 2πn)²/(4πx))
summable_heatGauss         (0 < x)                        -- from summable_jacobiTheta₂_term_iff
heatMultiplier_eq_ofReal   (0 < x) :
    heatMultiplier x θ = ↑(x^{-1/2} · ∑_{n ∈ ℤ} heatGauss x n θ)
tsum_heatGauss_split       : ∑_n heatGauss x n θ = heatGauss x 0 θ + heatRemainder x θ
heatRemainder_le  (0 < x ≤ 1, 0 < θ ≤ π) :
    heatRemainder x θ ≤ exp(-π/(4x)) · heatTailConst
```

The last is the uniform off-centre estimate: on the phase window `(0, π]` and for `n ≠ 0`,
`|θ - 2πn| ≥ 2π|n| - π ≥ π|n|`, so `heatGauss x n θ ≤ exp(-πn²/(4x))`, and for `x ≤ 1` this is
`exp(-π/(4x))·exp(-π(n²-1)/4)` with the second factor summable over `ℤ`
(`summable_heatTailMajorant`, via a geometric majorant `exp(-π|n|/4)`).

So the whole multiplier is, on the window, the single Gaussian `exp(-θ²/(4πx))` scaled by
`x^{-1/2}`, plus something exponentially small — which is exactly the input `(6)` needs, since the
`ℓ = 0` half-line integral is already `integral_cpow_mul_exp_neg_mul_sq_Ioi` and the `[0,π]`
truncation is already `norm_integral_cpow_mul_exp_neg_mul_sq_Ioi_le`.

**What remains for `(6)`.**  Only the assembly: multiply out
`x^{-1/2}·(1/π)·½·(4πx)^{(λ+1)/2}Γ((λ+1)/2) = (4πx)^{λ/2}Γ((λ+1)/2)/√π` and add the two error
terms.  Then `(2)` (Parseval for the convolution operator) and `(7)`.

### Equation `(6)` is formalized

`formal/GaloisForLFunctions/RHTower/HeatMomentAsymptotic.lean` (unconditional, axiom-clean):

```text
norm_heatWindowMoment_sub_main_le  (-1 < Re λ, 0 < x ≤ 1) :
  ‖ ∫_{(0,π]} θ^λ W_x(θ) dθ  −  x^{-1/2}·½·(4πx)^{(λ+1)/2}·Γ((λ+1)/2) ‖
    ≤ x^{-1/2} ( e^{-π/(4x)}·heatTailConst·π^{σ+1}/(σ+1)
               + e^{-π/(8x)}·½·(8πx)^{(σ+1)/2}·Γ((σ+1)/2) ) ,   σ = Re λ

heatMomentMain_eq (0 < x) :
  (1/π)·x^{-1/2}·½·(4πx)^{(λ+1)/2}·Γ((λ+1)/2) = (4πx)^{λ/2}·Γ((λ+1)/2)/√π
```

which together are `(6)` in the card's normalisation `(1/2π)∫_{-π}^{π} = (1/π)∫_0^π`.  The proof
is the three-way split: the window integral minus the scaled central Gaussian is bounded by
`heatRemainder_le` against `∫_0^π θ^σ = π^{σ+1}/(σ+1)`; the central Gaussian on `(0,π]` is the
half-line moment `integral_cpow_mul_exp_neg_mul_sq_Ioi` minus its tail
`norm_integral_cpow_mul_exp_neg_mul_sq_Ioi_le`; and at `b = 1/(4πx)` those constants read
`b π²/2 = π/(8x)` and `2/b = 8πx`.  Supporting: `integrableOn_cpow_mul_heatMultiplier`
(via `continuous_heatMultiplier`, from `differentiableAt_jacobiTheta₂_fst`),
`integral_rpow_window`, `integral_gauss_window_eq`, and
`rpow_neg_half_le_exp` (`x^{-1/2} ≤ (2/a)e^{a/(2x)}` for `0 < x ≤ 1`, which absorbs the
`x^{-1/2}` prefactor into a slower exponential when a clean `O(e^{-c/x})` is wanted).

**What remains for this card.**  Equation `(2)` — the Fourier/Parseval representation of the heat
quadratic form `E_s(x)` as `(1/ζ(2σ))∫ W_x |f_s|² dθ/2π` — and the final assembly `(7)`, followed
by the exact zero detector.

### The finite form of the Fourier representation `(2)`

`formal/GaloisForLFunctions/RHTower/HeatMultiplierFourier.lean` and
`.../HeatQuadraticForm.lean` (unconditional, axiom-clean):

```text
heatCoeff x k                       = exp(-π x k²)
summable_heatCoeff (0 < x)
integral_heatMultiplier_mul_exp     : ∫_{(-π,π]} W_x(θ) e^{ikθ} dθ = 2π · exp(-π x k²)
integral_heatMultiplier_mul_trigPoly_normSq (0 < x) (s : Finset ℤ) (a : ℤ → ℂ) :
    ∫_{(-π,π]} W_x(θ) · |∑_{n ∈ s} aₙ e^{inθ}|² dθ
      = 2π · ∑_{n ∈ s} ∑_{m ∈ s} aₙ conj(a_m) · exp(-π x (n-m)²)
```

The first is honest termwise integration: `∑_k exp(-πxk²)` is summable so the multiplier series
converges in `L¹` of the window (`integral_tsum_of_summable_integral_norm`), and
`∫_{-π}^{π} e^{imθ} dθ = 2π·[m = 0]` is the elementary orthogonality
(`integral_exp_mul_complex`, with `e^{imπ} = e^{-imπ} = (-1)^m`).  The second is the exact
finite-mode form of `(2)`: **the additive heat double sum of a coefficient family is the heat
quadratic form of its trigonometric polynomial.**

**What remains for `(2)`.**  Passing `N → ∞`.  The plan of record: `f_s` is the `L²(S¹)` function
`θ ↦ expZeta (θ/2π) s`, which is in `L²` for `σ > 1/2` because Jonquière (already formalized)
gives `|f_s(θ)| ≲ |θ|^{σ-1} + 1` and `2(σ-1) > -1`; its Fourier coefficients are `n^{-s}` for
`n ≥ 1` and `0` otherwise, proved by analytic continuation in `s` from `Re s > 1` (both sides are
analytic in `s` on the strip, the integral by dominated convergence against the same Jonquière
bound).  Then `f_s^N → f_s` in `L²` and `W_x` is bounded, so the finite identity passes to the
limit.  After that: the assembly `(7)`.

### Regularity of the boundary germ

`RHTower/HurwitzZetaSmallShift.lean` gained `continuousOn_shiftDiffTerm` and
`continuousOn_shiftDiffSeries` (uniform convergence on `|b| ≤ 1/2` against the same majorant, via
`tendstoUniformlyOn_tsum`), and `RHTower/JonquiereExpansion.lean` gained

```text
continuousOn_expZeta_phase (0 < Re s < 1) :
    ContinuousOn (fun θ : ℝ => expZeta (θ/2π) s) (Ioc 0 π)
```

Mathlib's `hurwitzZeta`/`expZeta` take their first argument on `UnitAddCircle` and carry **no**
regularity API in it, so this had to come from the Jonquière decomposition: the singular power and
the constant are visibly continuous, and the remainder is continuous because the shift-difference
series converges uniformly in the shift.  This is the regularity `(2)` and `(7)` need in order to
treat `f_s` as an honest pointwise function on the punctured window.

### The boundary germ on the window: regularity and the `L²` profile

`formal/GaloisForLFunctions/RHTower/BoundaryGermL2.lean` (unconditional, axiom-clean):

```text
phaseGerm s θ                = expZeta (θ/2π) s
continuousOn_phaseGerm_pos   : ContinuousOn (phaseGerm s) (Ioc 0 π)
continuousOn_phaseGerm_neg   : ContinuousOn (phaseGerm s) (Ico (-π) 0)
integrableOn_abs_rpow_window : -1 < r →  IntegrableOn (|·|^r) (Ioc (-π) π)
norm_phaseGerm_le            : θ ∈ Ioc (-π) π, θ ≠ 0 →
    ‖phaseGerm s θ‖ ≤ (‖A₊‖ + ‖A₋‖ + ‖ζ(s)‖ + jonquiereConst s · π) · (|θ|^{σ-1} + 1)
```

The negative half is the reflected Jonquière expansion `expZeta_neg_eq_jonquiere` composed with
`θ ↦ -θ`; the bound is the two-sided remainder estimate with the trivial `θ ≤ π`.  Since
`2(σ-1) > -1` exactly when `σ > 1/2`, this profile is square integrable on the window — which is
the Hilbert-space input `(2)` needs.

**Immediate next step.**  `MemLp (phaseGerm s) 2 (volume.restrict (Ioc (-π) π))` (measurability by
splitting the window at the origin, then domination by the profile above), then
`fourierCoeffOn` of the germ by analytic continuation in `s` from `Re s > 1`, then
`hasSum_fourier_series_L2` to pass `N → ∞` in the finite quadratic-form identity.

### The germ is `L²` on the window

`RHTower/BoundaryGermL2.lean` gained

```text
aestronglyMeasurable_phaseGerm  -- window split at the origin, aestronglyMeasurable_union_iff
memLp_jonquiereProfile          -- ‖C(|θ|^{σ-1}+1)‖² is integrable exactly when σ > 1/2
memLp_phaseGerm (1/2 < Re s < 1) : MemLp (phaseGerm s) 2 (volume.restrict (Ioc (-π) π))
```

so `f_s` is an honest `L²` object on the window, with the Jonquière profile as its dominating
function.  `σ > 1/2` enters exactly once, through `2(σ-1) > -1`.

### Route correction for `(2)` versus `(7)`

Identifying the *Fourier coefficients* of `phaseGerm s` with `n^{-s}` is a boundary-convergence
theorem for a Dirichlet series with bounded partial sums (abscissa of conditional convergence
`≤ 0`), not a corollary of anything already formalized: the analytic-continuation-in-`s` argument
cannot be run on `{0 < Re s < 1} ∪ {Re s > 1}` because that set is disconnected and the Jonquière
bound is only available for `Re s < 1`.  The mathlib hook for it is
`LSeries_eq_mul_integral` at `r = 0` (partial sums of `e^{2πima}` are bounded by
`|1 - e^{2πia}|^{-1}`), which expresses the `L`-series through an integral valid on the whole of
`Re s > 0` and can then be matched against `expZeta` by the identity theorem on that connected
half plane.

Consequently the order of work is: **first `(7)` for the integral-defined energy**, whose every
ingredient is now formalized — the Jonquière expansion `(5)`, the window moment `(6)`, the exact
total mass `(1/2π)∫_{-π}^{π} W_x = 1` (the `k = 0` case of `integral_heatMultiplier_mul_exp`), and
evenness of `W_x` — **then `(1) = (2)`** as the separate bridge from the double sum to that
integral, using the finite identity `integral_heatMultiplier_mul_trigPoly_normSq`,
`memLp_phaseGerm`, and the boundary-convergence theorem above.

### `(6)` in the card's normalisation, and the exact total mass

`formal/GaloisForLFunctions/RHTower/HeatFullWindowMoment.lean` (unconditional, axiom-clean):

```text
heatMultiplier_even                       : W_x(-θ) = W_x(θ)          (reindex k ↦ -k)
integral_abs_cpow_mul_heatMultiplier_window (-1 < Re λ, 0 < x) :
    ∫_{(-π,π]} |θ|^λ W_x = 2 ∫_{(0,π]} θ^λ W_x
heatMoment x λ      = (1/2π) ∫_{(-π,π]} |θ|^λ W_x        -- the card's LHS of (6)
heatMomentTerm x λ  = (4πx)^{λ/2} Γ((λ+1)/2) / √π        -- the card's main term
norm_heatMoment_sub_term_le (-1 < Re λ, 0 < x ≤ 1) :
    ‖heatMoment x λ − heatMomentTerm x λ‖ ≤ (1/π)·(the exponentially small bound)
heatMoment_zero (0 < x) : heatMoment x 0 = 1
```

**Equation `(6)` is therefore closed**, in exactly the card's normalisation, and the `λ = 0` case
is *exact*, not asymptotic — it is the `k = 0` case of `integral_heatMultiplier_mul_exp`, so the
`|ζ(s)|²` term of `(7)` will carry no error at all.

The reflection uses `intervalIntegral.integral_comp_neg` on the two halves and the evenness of the
multiplier; the negative half needs its own integrability (`|θ|^λ` is only continuous away from
the origin, so the measurability runs on `Ioo(-π,0)` and transfers by the null difference).

### The moment layer is complete

`RHTower/HeatFullWindowMoment.lean` also proves the vanishing that `(7)`'s error analysis needs:

```text
tendsto_exp_neg_div_nhdsGT_zero  : exp(-a/x) → 0            as x ↓ 0
tendsto_rpow_neg_half_mul_exp    : x^{-1/2} exp(-a/x) → 0   as x ↓ 0
tendsto_heatMoment_of_pos_re (0 < Re λ) : heatMoment x λ → 0 as x ↓ 0
```

The middle one is `rpow_neg_half_le_exp` (`x^{-1/2} ≤ (2/a)e^{a/(2x)}` for `0 < x ≤ 1`) squeezed
against `e^{-a/(2x)}`; the last combines it with `(6)` and the vanishing of the main term
`(4πx)^{λ/2}`.

**All of `(6)` and its consequences are therefore formalized.**  What `(7)` needs from here is
purely algebraic bookkeeping plus one more elementary lemma:

1. `heatMoment_halfSplit`: for a two-sided coefficient pair,
   `(1/2π)∫_{-π}^{π} W_x·(c_± |θ|^λ) = ((c₊+c₋)/2)·heatMoment x λ`
   — immediate from `integral_abs_cpow_mul_heatMultiplier_window` and the reflection.
2. Expand `|f_s|² = P + E` with `P` the four Jonquière main terms and
   `‖E(θ)‖ ≤ K(|θ|^σ + |θ| + |θ|²)`, using `‖R(θ)‖ ≤ jonquiereConst s · |θ|`.
3. `W_x ≥ 0` (visible from `heatMultiplier_eq_ofReal`), so
   `‖(1/2π)∫ W_x·E‖ ≤ K(heatMoment x σ + heatMoment x 1 + heatMoment x 2) → 0`.
4. The three main moments are `heatMomentTerm` at `λ = 2σ-2`, `s-1`, `conj s - 1`, and the fourth
   is the exact `heatMoment x 0 = 1`; matching them against `(8)`/`(9)` is the identity
   `(A₊ + A₋)/2 = Γ(1-s) sin(πs/2)` and `(|A₊|² + |A₋|²)/2 = |Γ(1-s)|² cosh(πt)`.

### Steps 1 and 2 of `(7)`

`RHTower/HeatMomentSplit.lean`:

```text
heatMultiplierValue x θ, heatMultiplier_eq_value, heatMultiplierValue_nonneg,
norm_heatMultiplier   -- W_x is a nonnegative real
heatMoment_halfSplit (0 < x, -1 < Re λ) :
    (1/2π) ∫_{(-π,π]} ((if 0 < θ then c₊ else c₋)·|θ|^λ)·W_x = ((c₊+c₋)/2)·heatMoment x λ
```

`RHTower/HeatEnergyPrincipal.lean`:

```text
jonquiereLeadAt s θ   = if 0 < θ then A₊(s) else A₋(s)
germPrincipal s θ     = jonquiereLeadAt s θ · |θ|^{s-1} + ζ(s)
norm_phaseGerm_sub_principal_le : ‖f_s(θ) - P(θ)‖ ≤ jonquiereConst s · |θ|
norm_germPrincipal_le           : ‖P(θ)‖ ≤ (‖A₊‖+‖A₋‖+‖ζ(s)‖)(|θ|^{σ-1}+1)
norm_germSq_sub_principalSq_le  : ‖|f_s|² - |P|²‖ ≤ heatEnergyErrorConst s · (|θ|^σ + |θ|)
```

the last from `f f̄ - P P̄ = (f-P)f̄ + P(f-P)‾` and `|θ|·|θ|^{σ-1} = |θ|^σ`.

**Remaining for `(7)`:** integrate.  `W_x ≥ 0` gives
`‖(1/2π)∫ W_x(|f_s|²-|P|²)‖ ≤ heatEnergyErrorConst s ·(heatMoment x σ + heatMoment x 1) → 0`
by `tendsto_heatMoment_of_pos_re`; and `(1/2π)∫W_x|P|²` is the four `heatMoment_halfSplit` terms
at `λ = 2σ-2`, `s-1`, `conj s - 1`, `0`, whose coefficients are
`(|A₊|²+|A₋|²)/2`, `((A₊+A₋)/2)·conj ζ(s)`, its conjugate, and `|ζ(s)|²`.

### The energy, its principal part, and the four-moment identity

`RHTower/HeatEnergyExpand.lean`, `RHTower/HeatEnergyReal.lean`,
`RHTower/HeatEnergyAsymptotic.lean` (all unconditional, axiom-clean):

```text
conj_ofReal_cpow, cpow_mul_conj_cpow
germPrincipal_mul_conj (θ ≠ 0) :
    |P(θ)|² = (‖A_±‖²)|θ|^{2σ-2} + (A_± conj ζ)|θ|^{s-1}
              + (conj A_± · ζ)|θ|^{conj s-1} + ‖ζ‖²|θ|^0     -- the four two-sided power tests

realHeatMoment x λ, heatMoment_ofReal_exponent, norm_heatMoment_ofReal,
tendsto_realHeatMoment (0 < λ)                                -- real moments and their vanishing

heatEnergy s x          = (1/2π) ∫_{(-π,π]} |f_s(θ)|² W_x(θ) dθ
heatEnergyPrincipal s x = the four `heatMoment` terms, with the `λ = 0` one already collapsed to ‖ζ(s)‖²
integrableOn_germSq_mul_heatMultiplier        (from memLp_phaseGerm and boundedness of W_x)
integrableOn_principalSq_mul_heatMultiplier   (from the four `integrableOn_halfSplit` pieces)
heatEnergyPrincipal_eq (1/2 < σ < 1, 0 < x) :
    (1/2π) ∫_{(-π,π]} |P(θ)|² W_x(θ) dθ = heatEnergyPrincipal s x
```

The last is `(7)`'s main-term computation, exact: the a.e. four-term expansion of `|P|²`, split by
linearity, then four applications of `heatMoment_halfSplit` and the exact `heatMoment x 0 = 1`.

**All that is left of `(7)`** is the error limit: `heatEnergy - heatEnergyPrincipal` is
`(1/2π)∫W_x(|f_s|² - |P|²)`, whose norm is at most
`heatEnergyErrorConst s · (realHeatMoment x σ + realHeatMoment x 1)` by
`norm_germSq_sub_principalSq_le` and `W_x ≥ 0`, and both moments tend to zero by
`tendsto_realHeatMoment`.

## 2026-08-16 — equation `(7)` is Lean-closed

```text
RHTower.tendsto_heatEnergy_sub_principal (1/2 < Re s < 1) :
    Tendsto (fun x => heatEnergy s x - heatEnergyPrincipal s x) (𝓝[>] 0) (𝓝 0)
```

axiom report `propext, Classical.choice, Quot.sound`.  This **is** the heat-aperture expansion
theorem: the additive heat quadratic form of the boundary germ equals, up to `o(1)` as the aperture
closes, the sum of the four Gaussian moments of its Jonquière principal part —

```text
heatEnergyPrincipal s x
  = (‖A₊‖²/2 + ‖A₋‖²/2)·M(2σ-2)  +  ((A₊+A₋)/2)·conj ζ(s)·M(s-1)
    + ((conj A₊ + conj A₋)/2)·ζ(s)·M(conj s - 1)  +  ‖ζ(s)‖²
```

with `M = heatMoment` and the fourth term already exact because `heatMoment x 0 = 1`.

The final error step is `heatEnergy - heatEnergyPrincipal = (1/2π)∫W_x(|f_s|² - |P|²)`, whose norm
is bounded through `W_x ≥ 0` and `norm_germSq_sub_principalSq_le` by
`heatEnergyErrorConst s ·(realHeatMoment x σ + realHeatMoment x 1)`, and both real moments vanish
by `tendsto_realHeatMoment`.  Supporting: `norm_cpow_mul_heatMultiplier`,
`integrableOn_rpow_mul_heatMultiplierValue`.

**What is left on this card.**  (a) the cosmetic identification of the coefficients with `(8)`/`(9)`
— `(A₊+A₋)/2 = Γ(1-s) sin(πs/2)` and `(‖A₊‖²+‖A₋‖²)/2 = |Γ(1-s)|² cosh(πt)`, plus
`heatMomentTerm x (2σ-2) = (4π)^{σ-1}Γ(σ-1/2)/√π · x^{σ-1}` — together with `L(s) > 0` and
`C(s) ≠ 0`; (b) the exact zero detector; (c) the bridge `(1) = (2)` from the double sum to
`heatEnergy`, which needs the Dirichlet boundary-convergence theorem noted above.

### `(8)` and `(9)`, with positivity and nonvanishing

`RHTower/HeatEnergyCoefficients.lean` (unconditional, axiom-clean):

```text
jonquiereLead_avg        : (A₊ + A₋)/2 = Γ(1-s)·sin(πs/2)                       -- (9)
normSq_jonquiereLead_avg : (‖A₊‖² + ‖A₋‖²)/2 = |Γ(1-s)|²·cosh(π t)              -- (8)
heatMomentTerm_split     : heatMomentTerm x λ = [(4π)^{λ/2}Γ((λ+1)/2)/√π] · x^{λ/2}
heatEchoL s              = |Γ(1-s)|² cosh(πt) · (4π)^{σ-1}Γ(σ-1/2)/√π           -- (8)
heatEchoC s              = Γ(1-s) sin(πs/2) · (4π)^{(s-1)/2}Γ(s/2)/√π           -- (9)
heatEchoL_pos     (1/2 < σ < 1) : 0 < L(s)
heatEchoC_ne_zero (1/2 < σ < 1) : C(s) ≠ 0
```

`(9)` is `cos(π(1-s)/2) = sin(πs/2)`; `(8)` is `‖e^{±iπ(1-s)/2}‖ = e^{±πt/2}`.  Nonvanishing uses
`Γ(1-s) ≠ 0` and `Γ(s/2) ≠ 0` (neither argument is a nonpositive integer in the strip) and
`sin(πs/2) ≠ 0` (its zeros are the even integers, and `σ ∈ (1/2,1)` is not one).
`heatMomentTerm_split` exhibits every main term in the card's `coefficient × aperture-power` shape,
so `(7)` now reads exactly as displayed on the card.

**Left on this card:** the exact zero detector, and the bridge `(1) = (2)`.

### The exact zero detector `(11)`

```text
RHTower.heatEcho_eq_zero_iff (1/2 < σ < 1) :
    heatEchoC s * conj (riemannZeta s) = 0  ↔  riemannZeta s = 0
```

immediate from `heatEchoC_ne_zero` and injectivity of conjugation.  With `(7)`, `(8)`, `(9)` this
closes the card's **Statement**: the subleading complex coefficient of the small-aperture expansion
is an explicit nonzero Gamma factor times `conj ζ(s)`, so a zeta zero in the strip is exactly the
disappearance of the subleading echo.

**Still open on this card, both `[PROVED]` on paper:**

1. The bridge `(1) = (2)` — that `heatEnergy s x` *is* the double sum
   `(1/ζ(2σ)) Σ_{m,n} m^{-conj s} n^{-s} e^{-πx(m-n)²}`.  The finite-mode identity
   (`integral_heatMultiplier_mul_trigPoly_normSq`) and `memLp_phaseGerm` are in place; what is
   missing is `fourierCoeffOn (phaseGerm s) n = n^{-s}` for `n ≥ 1` and `0` otherwise.  That is the
   Dirichlet boundary-convergence theorem (bounded partial sums ⇒ abscissa of conditional
   convergence `≤ 0`), whose Abel-summation estimate is exactly the mean-value bound
   `norm_cpow_shift_sub_le` already proved in `HurwitzZetaSmallShift.lean`; the identification with
   `expZeta` is then the identity theorem on the connected half plane `{Re s > 0}`.
2. The canonical nonzero tangent `(11c)`: `R_s(θ) = f_s(θ) - Γ(1-s)(-iθ)^{s-1}` satisfies
   `R_s(0) = ζ(s)` and `R_s'(0) = i ζ(s-1) ≠ 0`.  This needs the *second-order* small-shift
   expansion `shiftDiffSeries b w = -w ζ(w+1) b + O(b²)` — obtainable by applying
   `norm_cpow_shift_sub_le` at exponent `w+1` to the derivative — plus the functional equation to
   turn `-(2π)^{-w}Γ(w+1)ζ(w+1)·2i sin(πw/2)/(2π)` into `i ζ(s-1)`.  Nonvanishing of `ζ(s-1)` on
   the strip is the functional equation again: `Re(s-1) ∈ (-1/2,0)`, and `ζ(2-s) ≠ 0`,
   `Γ(2-s) ≠ 0`, `sin(π(s-1)/2) ≠ 0` there.

### `(11b)` and `(11c)`: the canonical nonzero tangent

`RHTower/HurwitzZetaSmallShift.lean` gained the **second-order** small-shift expansion

```text
norm_cpow_shift_sub_linear_le  : ‖(x+b)^{-w} - x^{-w} + w b x^{-w-1}‖ ≤ C x^{-Re w-2} b²
hasSum_riemannZeta_shift_succ  : ∑_{n≥0} (n+1)^{-w-1} = ζ(w+1)         (0 < Re w)
norm_shiftDiffSeries_add_linear_le :
    ‖shiftDiffSeries b w + w·b·ζ(w+1)‖ ≤ C(w)·b²
```

— the second-order bound is the *same* mean-value lemma applied at exponent `w+1` to the derivative,
so no new analytic input was needed.

`RHTower/JonquiereExpansion.lean` gained `jonquiereTangent`, `jonquiereTangentConst` and

```text
norm_jonquiereRemainder_sub_tangent_le (0 < Re s < 1, 0 < θ ≤ π) :
    ‖jonquiereRemainder s θ - jonquiereTangent s · θ‖ ≤ jonquiereTangentConst s · θ²
```

`RHTower/HeatEnergyTangent.lean` closes the card's tangent claims:

```text
riemannZeta_sub_one_eq      : ζ(s-1) = -2(2π)^{s-2}Γ(2-s)cos(πs/2)ζ(2-s)
riemannZeta_sub_one_ne_zero (1/2 < σ < 1) : ζ(s-1) ≠ 0
jonquiereTangent_eq         : jonquiereTangent s = i·ζ(s-1)                      -- (11b)
regGerm s θ                 = f_s(θ) - A₊(s)θ^{s-1}      (= f_s(θ) - Γ(1-s)(-iθ)^{s-1})
norm_regGerm_sub_tangent_le : ‖R_s(θ) - (ζ(s) + iζ(s-1)θ)‖ ≤ C·θ²                -- (11b)
tendsto_regGerm             : R_s(θ) → ζ(s)                                       -- R_s(0) = ζ(s)
tendsto_regGerm_slope (ζ(s) = 0) : R_s(θ)/θ → i·ζ(s-1)                            -- (11c)
tangent_ne_zero             : i·ζ(s-1) ≠ 0                                        -- (11c)
```

`ζ(s-1) ≠ 0` is the functional equation: `Re(s-1) ∈ (-1/2,0)` is left of the critical strip, and
`ζ(2-s)`, `Γ(2-s)`, `cos(πs/2)` are all nonzero there (`cos(πs/2) = 0` needs `s` an odd integer).

**The only item still open on this card is the bridge `(1) = (2)`.**

### Route for the bridge `(1) = (2)`, and its first brick

The bridge does **not** need the Fourier coefficients of the germ after all.  It suffices to know

1. `f^N(θ) = ∑_{n ≤ N} n^{-s} e^{inθ} → phaseGerm s θ` pointwise off the origin, and
2. a uniform Abel bound `|f^N(θ)| ≤ C|θ|^{σ-1}`, which is in `L²` exactly when `σ > 1/2`;

then dominated convergence gives `f^N → f_s` in `L²`, and the finite identity
`integral_heatMultiplier_mul_trigPoly_normSq` passes to the limit against the bounded `W_x`.

For (1) the plan of record is **Abel summation into an absolutely convergent series**: with
`A(k) = ∑_{j ≤ k} e^{ijθ}` bounded by `2/‖1 - e^{iθ}‖`,

```text
∑_{n=1}^{N} e^{inθ} n^{-s} = A(N)·N^{-s} + ∑_{k=1}^{N-1} A(k)·(k^{-s} - (k+1)^{-s})
```

and the right-hand series converges **absolutely** for `Re s > 0` because
`‖k^{-s} - (k+1)^{-s}‖ ≤ ‖s‖ k^{-σ-1}`.  Its sum is therefore an analytic function of `s` on
`{Re s > 0}` by `differentiableOn_tsum_of_summable_norm` (the same tool used for
`shiftDiffSeries`), and it agrees with `expZeta` for `Re s > 1`, hence everywhere on that
*connected* half plane by the identity theorem — which is exactly the step the earlier
"disconnected domain" obstruction blocked.

First brick, now proved: `RHTower.norm_cpow_shift_sub_le_of_nonneg`

```text
0 < x, 0 ≤ b, 0 < Re w  →  ‖(x+b)^{-w} - x^{-w}‖ ≤ ‖w‖ · x^{-Re w - 1} · b
```

— the same mean-value argument as `norm_cpow_shift_sub_le` but with no size restriction on the
shift, which is what the `b = 1` step of Abel summation needs.

### Abel summation: the Dirichlet series converges on the whole right half plane

`formal/GaloisForLFunctions/RHTower/DirichletAbel.lean` (unconditional, axiom-clean):

```text
coeffPartial c k   = ∑_{j<k} c j
abelDirichlet c s  = ∑' k, coeffPartial c (k+1) · ((k+1)^{-s} - (k+2)^{-s})
norm_abelTerm_le   : ‖·‖ ≤ (B‖s‖)·(k+1)^{-Re s-1}            (bounded partial sums)
summable_abelTerm  : the Abel series converges absolutely for Re s > 0
sum_eq_abelPartial : ∑_{i<n} (i+1)^{-s} c i
                       = n^{-s}·coeffPartial c n + ∑_{k<n-1} coeffPartial c (k+1)·(…)
tendsto_abelDirichlet (‖coeffPartial c k‖ ≤ B, 0 < Re s) :
    ∑_{i<n} (i+1)^{-s} c i  →  abelDirichlet c s
```

So a Dirichlet series with bounded coefficient partial sums converges for every `Re s > 0`, and
its value is an **absolutely** convergent series — which is what makes the `s`-analyticity
available.  The summation by parts is `Finset.sum_range_by_parts`; the termwise estimate is the
new `norm_cpow_shift_sub_le_of_nonneg` at shift `1`; the head term `n^{-s}·A(n)` vanishes because
`‖A(n)‖ ≤ B` and `n^{-Re s} → 0`.

**Remaining for the bridge:** (i) analyticity of `abelDirichlet c ·` on `{Re s > 0}` by
`differentiableOn_tsum_of_summable_norm` (the majorant is already uniform on balls);
(ii) boundedness of the geometric partial sums `∑_{j≤k} e^{ijθ}` by `2/‖1-e^{iθ}‖`;
(iii) `abelDirichlet = expZeta (θ/2π)` for `Re s > 1`, hence on all of `{Re s > 0}` by the
identity theorem; (iv) the uniform Abel bound `|f^N(θ)| ≤ C|θ|^{σ-1}` and dominated convergence in
`L²`; (v) the limit of the finite quadratic-form identity.

### The Dirichlet boundary-convergence theorem is proved

`RHTower/DirichletAbel.lean` now closes the crux of the bridge:

```text
differentiable_abelTerm, differentiableAt_abelDirichlet (‖coeffPartial c k‖ ≤ B, 0 < Re s₀) :
    the Abel sum is analytic on {Re s > 0}
norm_coeffPartial_geom_le (‖z‖ = 1, z ≠ 1) : ‖∑_{j<k} z^{j+1}‖ ≤ 2/‖1-z‖
expCoeff a j = e^{2πia(j+1)}, norm_coeffPartial_expCoeff_le
abelDirichlet_eq_expZeta_of_one_lt_re : equality with expZeta for Re s > 1
abelDirichlet_eq_expZeta (a ≠ 0 in ℝ/ℤ, 0 < Re s) :
    abelDirichlet (expCoeff a) s = expZeta a s
```

Combined with `tendsto_abelDirichlet` this says: **for `0 < Re s` and `a ∉ ℤ`, the conditionally
convergent Dirichlet series `∑ e^{2πian} n^{-s}` converges to `expZeta a s`** — the pointwise
statement `f^N(θ) → phaseGerm s θ` that the bridge needs.  The identity theorem now runs on the
*connected* half plane `{Re s > 0}` because the Abel-summed series is absolutely convergent there,
which is exactly what the earlier obstruction lacked.

**Remaining for the bridge:** the sharp uniform bound `|f^N(θ)| ≤ C|θ|^{σ-1}` (obtained by
applying `sum_eq_abelPartial` at two cut-offs and splitting the range at `M ≈ 1/|θ|`), then `L²`
dominated convergence and the limit of `integral_heatMultiplier_mul_trigPoly_normSq`.

### Orthogonality, and a route that avoids the sharp Abel bound

`RHTower/TrigPolyOrthogonality.lean` (unconditional, axiom-clean):

```text
integral_trigPoly_normSq (s : Finset ℤ) (a : ℤ → ℂ) :
    ∫_{(-π,π]} |∑_{n ∈ s} aₙ e^{inθ}|² dθ = 2π · ∑_{n ∈ s} ‖aₙ‖²
```

This makes the sharp uniform bound `|f^N(θ)| ≤ C|θ|^{σ-1}` **unnecessary**: since
`‖f^N - f^M‖²_{L²} = 2π ∑_{M ≤ n < N} n^{-2σ}` and `∑ n^{-2σ}` converges for `σ > 1/2`, the
truncations `(f^N)` are a **Cauchy sequence in `L²`** of the window.  Completeness gives a limit
`g ∈ L²`; a subsequence converges a.e.; and `f^N → phaseGerm s` pointwise off the origin by
`tendsto_abelDirichlet` + `abelDirichlet_eq_expZeta`.  Hence `g = phaseGerm s` a.e., so
`f^N → phaseGerm s` in `L²` — which is exactly what the limit of
`integral_heatMultiplier_mul_trigPoly_normSq` needs.

**Remaining for the bridge:** the `Lp` plumbing for that Cauchy argument, and the continuity of
`u ↦ ∫ W_x · u · conj u` on `L²` (immediate from boundedness of `W_x`).

### The truncated germ: pointwise limit and exact `L²` norm

`RHTower/HeatEnergyBridge.lean` (unconditional, axiom-clean):

```text
modeSet N, sum_modeSet            -- the first N positive Fourier modes
dirichletTrunc s N θ = ∑_{n ∈ modeSet N} n^{-s} e^{inθ}
integral_dirichletTrunc_normSq    : ∫_{(-π,π]} |f^N|² = 2π ∑_{i<N} (i+1)^{-2σ}
tendsto_dirichletTrunc (0 < Re s, -π < θ ≤ π, θ ≠ 0) :
    f^N(θ) → phaseGerm s θ
```

The second is the Dirichlet boundary theorem in the form the bridge consumes: for `θ` in the
punctured window the phase `a = θ/2π` is not an integer, so `e^{2πia} ≠ 1` and
`(a : ℝ/ℤ) ≠ 0`, and `tendsto_abelDirichlet` combined with `abelDirichlet_eq_expZeta` gives the
pointwise limit.

With `integral_dirichletTrunc_normSq` the truncations are Cauchy in `L²`, and the identification of
the `L²` limit with `phaseGerm s` follows from the pointwise statement — the remaining step is the
`Lp` bookkeeping plus the (elementary) continuity of `u ↦ ∫ W_x u conj u`.

### The Cauchy estimate for the truncations

`RHTower/HeatEnergyBridge.lean` also proves

```text
modeSet_subset, modeSet_sdiff  : modeSet M \ modeSet N ≅ Finset.Ico N M   (N ≤ M)
integral_trunc_sub_normSq (N ≤ M) :
    ∫_{(-π,π]} |f^M - f^N|² = 2π ∑_{i ∈ Ico N M} (i+1)^{-2σ}
```

so `(f^N)` is Cauchy in `L²` with the *explicit* modulus `2π·(tail of ∑ (i+1)^{-2σ})`, which
converges precisely because `σ > 1/2`.

**Remaining:** Fatou against the pointwise limit `tendsto_dirichletTrunc` upgrades this to
`∫ |phaseGerm s - f^N|² ≤ 2π·(tail)`, hence `f^N → phaseGerm s` in `L²`; then Cauchy–Schwarz
against the bounded `W_x` transfers it to the heat integral, and
`integral_heatMultiplier_mul_trigPoly_normSq` supplies the truncated double sum, whose limit is
the absolutely convergent double sum of `(1)`.

### Fatou: the germ is the `L²` limit of its truncations

`RHTower/HeatEnergyBridge.lean` (unconditional, axiom-clean):

```text
summable_truncMajorant, truncTail s N = ∑'_i ((i+N)+1)^{-2σ}, tendsto_truncTail : truncTail → 0
integral_trunc_sub_normSq_real  : ∫ ‖f^M - f^N‖² = 2π ∑_{i ∈ Ico N M} (i+1)^{-2σ}
continuous_dirichletTrunc
lintegral_germ_sub_trunc_le (1/2 < σ < 1) :
    ∫⁻ ENNReal.ofReal ‖phaseGerm s θ - f^N θ‖² ≤ ENNReal.ofReal (2π · truncTail s N)
```

The Fatou step runs `lintegral_liminf_le` against the pointwise limit
`tendsto_dirichletTrunc` (shifted by `N` so the index stays `≥ N`), with each
`∫⁻` term rewritten to `ENNReal.ofReal (∫ …)` by `ofReal_integral_eq_lintegral_ofReal` and
bounded by `sum_Ico_le_truncTail`.  Since `truncTail s N → 0`, this **is** the statement that the
truncations converge to the germ in `L²` of the window.

**Remaining:** convert the `lintegral` bound to `∫ ‖phaseGerm - f^N‖² → 0`, then Cauchy–Schwarz
against the bounded `W_x` and the limit of `integral_heatMultiplier_mul_trigPoly_normSq`.

### `L²` convergence of the truncations, in real form

```text
aestronglyMeasurable_germ_sub_trunc_sq, integrableOn_germ_sub_trunc_sq
integral_germ_sub_trunc_le (1/2 < σ < 1) :
    ∫_{(-π,π]} ‖phaseGerm s θ - f^N θ‖² ≤ 2π · truncTail s N
tendsto_integral_germ_sub_trunc (1/2 < σ < 1) :
    ∫_{(-π,π]} ‖phaseGerm s θ - f^N θ‖² → 0
```

So `f^N → phaseGerm s` in `L²` of the window — the statement the bridge needs — is now proved
unconditionally, in ordinary real-integral form (the `lintegral` bound is converted through
`integral_eq_lintegral_of_nonneg_ae` and `ENNReal.toReal_mono`).

**Remaining for `(1) = (2)`:** Cauchy–Schwarz against the bounded `W_x` turns this into
`∫ W_x |f^N|² → ∫ W_x |phaseGerm s|²`; the left side is `2π ×` the truncated additive double sum
by `integral_heatMultiplier_mul_trigPoly_normSq`, and that converges to the full (absolutely
convergent) double sum of `(1)`.

### Cauchy–Schwarz and the uniform `L²` bound on the truncations

```text
memLp_dirichletTrunc, memLp_germ_sub_trunc
integral_norm_mul_le, integral_norm_mul_le_sqrt   -- Hölder at p = q = 2, in √ form
integral_dirichletTrunc_normSq_real : ∫ ‖f^N‖² = 2π ∑_{i<N} (i+1)^{-2σ}
integral_dirichletTrunc_normSq_le   : ∫ ‖f^N‖² ≤ 2π ∑'_i (i+1)^{-2σ}     (uniform in N)
```

so the two factors in the Cauchy–Schwarz estimate
`|∫ W_x(|f^N|² - |f|²)| ≤ M·(∫‖f^N-f‖²)^{1/2}·((∫‖f^N‖²)^{1/2} + (∫‖f‖²)^{1/2})`
are respectively `→ 0` and uniformly bounded.  The last assembly step is to run that estimate and
combine it with `integral_heatMultiplier_mul_trigPoly_normSq`.

## 2026-08-16 — the card is fully formalized

Every displayed statement of this card is now closed unconditionally in Lean 4.  All declarations
report `propext, Classical.choice, Quot.sound`.

### `(1) = (2)`: the quadratic form is the additive double sum

`formal/GaloisForLFunctions/RHTower/HeatEnergyBridge.lean` closes the transfer

```text
integrable_norm_mul, tendsto_heatIntegral_trunc (1/2 < σ < 1, 0 < x) :
    ∫ W_x |f^N|²  →  ∫ W_x |f_s|²
```

by the pointwise split `|a|² - |b|² = (a-b)·conj a + b·conj(a-b)`, the bound
`‖W_x‖ ≤ M` on the compact window, Hölder at `p = q = 2`, the `L²` convergence
`tendsto_integral_germ_sub_trunc` and the uniform bound `integral_dirichletTrunc_normSq_le`.

`formal/GaloisForLFunctions/RHTower/HeatDoubleSum.lean` then builds the double sum itself:

```text
heatPairTerm s x (m,n) = (m+1)^{-s} · conj((n+1)^{-s}) · exp(-π x (m-n)²)
summable_heatPairTerm (1/2 < σ, 0 < x)      -- absolute convergence of (1)
heatDoubleSum s x = ∑'_{(m,n)} heatPairTerm s x (m,n)
heatEnergy_eq_heatDoubleSum (1/2 < σ < 1, 0 < x) : heatEnergy s x = heatDoubleSum s x
heatDoubleSum_eq_iterated                          : the same sum in iterated form
```

The absolute convergence claimed in the card ("if `k=m-n` is fixed, the inner sum is bounded by a
translate of `∑ n^{-2σ}`; summing over `k` is then controlled by the Gaussian") is formalized by
the **arithmetic-mean majorant**: `‖heatPairTerm‖ ≤ ((m+1)^{-2σ} + (n+1)^{-2σ})·e^{-πx(m-n)²}/2`,
each half of which is summable on `ℕ × ℕ` by `summable_prod_of_nonneg` — the inner Gaussian sum is
a translate of `∑_{k ∈ ℤ} e^{-πxk²}` and the outer factor is `∑ (m+1)^{-2σ}` — the two halves
being exchanged by `Equiv.prodComm` and the evenness `heatCoeff x (-k) = heatCoeff x k`.  This
replaces the Cauchy–Schwarz argument by an identity that `ring` can check.

The finite-`N` identity is `integral_heatMultiplier_mul_trigPoly_normSq` at the coefficient family
`n ↦ n^{-s}` on `modeSet N`, giving `heatQuadratic_trunc_eq`, and the square partial sums converge
to the tsum by `tendsto_atTop_finset_of_monotone` on `range N ×ˢ range N`.

### Strict positivity of the aperture

`formal/GaloisForLFunctions/RHTower/HeatAperturePositivity.lean`:

```text
heatMultiplierValue_pos (0 < x)          : W_x(θ) > 0                      -- from the Poisson form
integral_dirichletTrunc_mul_expNeg, integral_phaseGerm_mul_expNeg :
    ∫_{(-π,π]} f_s(θ) e^{-iθ} dθ = 2π                                       -- the first mode
two_pi_le_integral_phaseGerm_normSq      : 2π ≤ ∫ |f_s|²
realHeatEnergy s x, heatEnergy_eq_ofReal : E_s(x)·ζ(2σ) is a real number
realHeatEnergy_pos (1/2 < σ < 1, 0 < x)  : it is strictly positive
heatEnergy_ne_zero
```

The first Fourier coefficient is computed on the truncations by orthogonality and transported to
the germ by the same Hölder estimate; Cauchy–Schwarz against the first mode then forces
`∫|f_s|² ≥ 2π`, and `W_x` attains a strictly positive minimum on the compact window.  So the
aperture energy is strictly positive **with no zeta value entering**, exactly as the card claims.

### The completed echo coefficient

`formal/GaloisForLFunctions/RHTower/HeatEchoCompleted.lean`:

```text
sin_pi_mul_half_ne_zero (0 < σ < 2)
sin_mul_gamma_half      : sin(πs/2)·Γ(s/2)·Γ(1-s/2) = π          -- Euler reflection
gamma_duplication_one_sub : Γ((1-s)/2)·Γ(1-s/2) = Γ(1-s)·2^s·√π  -- Legendre duplication
heatEchoC_eq_completed (0 < σ < 2) : C(s) = ½ π^{(s-1)/2} Γ((1-s)/2)          -- (9a)
conj_heatEchoC_of_critical (σ = 1/2) : conj C(s) = ½ π^{-s/2} Γ(s/2)          -- (11a)
tendsto_heatEnergy_finitePart (1/2 < σ < 1) :
    E_s(x)ζ(2σ) minus the four nonzero-power channels → |ζ(s)|²               -- (12)
```

`(9a)` is proved by substituting the two Gamma identities into `(9)` and splitting
`(4π)^{(s-1)/2} = (2^{(s-1)/2})² π^{(s-1)/2}`, `2^s = (2^{(s-1)/2})²·2`; the hypotheses are
relaxed to the strip `0 < σ < 2` precisely so that the critical line is included, which is what
`(11a)` needs (`conj s = 1 - s` there, `Complex.cpow_conj` and `Complex.Gamma_conj`).

### Index of the formalization

| Card item | Lean declaration |
|---|---|
| `(1)` absolute convergence | `RHTower.summable_heatPairTerm` |
| `(1) = (2)` | `RHTower.heatEnergy_eq_heatDoubleSum` |
| `E_s(x) > 0` | `RHTower.realHeatEnergy_pos` |
| `(3)` Poisson form | `RHTower.heatMultiplier_poisson` |
| `(4)`, `(5)` Jonquière | `RHTower.expZeta_eq_jonquiere`, `RHTower.expZeta_neg_eq_jonquiere` |
| `(6)` Gaussian moments | `RHTower.norm_heatMoment_sub_term_le` |
| `(7)` expansion theorem | `RHTower.tendsto_heatEnergy_sub_principal` |
| `(8)` `L(s) > 0` | `RHTower.heatEchoL_pos` |
| `(9)` `C(s) ≠ 0` | `RHTower.heatEchoC_ne_zero` |
| `(9a)` completed form | `RHTower.heatEchoC_eq_completed` |
| `(10)`, `(11)` zero detector | `RHTower.heatEcho_eq_zero_iff` |
| `(11a)` critical line | `RHTower.conj_heatEchoC_of_critical` |
| `(11b)`, `(11c)` tangent | `RHTower.regGerm_eq`, `RHTower.tendsto_regGerm_slope`, `RHTower.tangent_ne_zero` |
| `(12)` finite part | `RHTower.tendsto_heatEnergy_finitePart` |

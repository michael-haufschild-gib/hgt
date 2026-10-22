# The CCM parity selector is a finite-prime boundary Hankel carrier

- **ID:** `ccm-finite-prime-parity-hankel-carrier`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** parity reduction of even convolution operators and Suzuki's screw-kernel
  realization of the restricted Weil form
- **Statement:** The even and odd restricted Weil forms have the exact decomposition
  `Q_even=T_a+H_a`, `Q_odd=T_a-H_a`. The parity carrier `H_a` is a boundary Hankel form whose
  negative part is an explicit finite sum of prime-power autocorrelations and whose regular part is
  archimedean.

## Setup

Use Suzuki's additive logarithmic coordinate on `(-a,a)`. On smooth compactly supported vectors,

```text
QW^a(f,g)
 =integral_(-a)^a integral_(-a)^a
    K(x-y)f(y)conjugate(g(x))dy dx,                    (1)
```

in the distributional sense, where `K=-g''` is real and even. Define unitary parity lifts from
`L2(0,a)` by

```text
(U_+ phi)(x)=2^(-1/2)phi(|x|),
(U_- phi)(x)=2^(-1/2)sgn(x)phi(|x|).                   (2)
```

On `C_c^infinity(0,a)`, put

```text
T_a(phi,psi)
 =integral_0^a integral_0^a
    K(x-y)phi(y)conjugate(psi(x))dy dx,

H_a(phi,psi)
 =integral_0^a integral_0^a
    K(x+y)phi(y)conjugate(psi(x))dy dx.                (3)
```

## Parity decomposition theorem

`[PROVED]` One has

```text
QW^a(U_+phi,U_+psi)=T_a(phi,psi)+H_a(phi,psi),
QW^a(U_-phi,U_-psi)=T_a(phi,psi)-H_a(phi,psi),          (4)
```

and hence

```text
QW^a(U_+phi,U_+psi)-QW^a(U_-phi,U_-psi)
 =2H_a(phi,psi).                                       (5)
```

### Proof

Split both variables in `(1)` into their positive and negative halves. For the even lift, the four
sign choices contribute

```text
K(x-y), K(x+y), K(-x-y), K(-x+y).
```

Since `K` is even, their normalized sum is `K(x-y)+K(x+y)`. For the odd lift, the two opposite-sign
terms acquire a minus sign, giving `K(x-y)-K(x+y)`. This proves `(4)`--`(5)`.

The identity extends to the corresponding closed parity forms wherever Suzuki's form closure is
used, by form-core density.

## Exact finite-prime carrier

Away from the prime-power atoms, `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-screw-kernel-positivity-improving-breakdown.md` proves

```text
K_reg(t)=e^(t/2)-e^(-5t/2)/(1-e^(-2t)),   t>0.         (6)
```

The prime part of Suzuki's screw function is

```text
sum_(n>=2) Lambda(n)n^(-1/2)(t-log n)_+.
```

Its second distributional derivative is the positive atomic measure

```text
sum_(n>=2) Lambda(n)n^(-1/2)delta_(log n).
```

Because `K=-g''`, the Hankel form therefore has the exact decomposition

```text
H_a(phi,psi)=H_(a,infinity)(phi,psi)-P_a(phi,psi),      (7)
```

where

```text
H_(a,infinity)(phi,psi)
 =integral_0^a integral_0^a
    K_reg(x+y)phi(y)conjugate(psi(x))dy dx,             (8)

P_a(phi,psi)
 =sum_(2<=n<e^(2a)) Lambda(n)n^(-1/2)
    integral_(max(0,log(n)-a))^(min(a,log(n)))
      phi(y)conjugate(psi(log(n)-y))dy.                 (9)
```

Endpoint atoms may be included with the standard half-weight convention; they do not affect the
closed form. Only prime powers with `log n<2a` occur. In the multiplicative CCM parameter
`lambda=e^a`, the parity carrier therefore uses exactly the finite prime-power cutoff

```text
n<lambda^2.                                            (10)
```

### Autocorrelation form

For real `phi`, extend it by zero outside `(0,a)` and put

```text
c_phi(t)=integral_R phi(y)phi(t-y)dy.                  (11)
```

Then

```text
H_a(phi,phi)
 =integral_0^(2a) K_reg(t)c_phi(t)dt
  -sum_(2<=n<e^(2a)) Lambda(n)n^(-1/2)c_phi(log n).    (12)
```

Thus parity is selected by one source-defined boundary comparison:

```text
finite prime-power Hankel correlations
versus
archimedean Hankel correlation.                        (13)
```

## Positive CCM consequence

`constrained-prolate-fourier-parity-floor-separation.md` proves that the source concentration model
selects the positive-Fourier floor over the negative-Fourier floor by `C lambda^(-4)`. Equations
`(4)` and `(12)` identify the exact arithmetic invariant that must preserve that ordering in the
true restricted Weil form.

A cofinal simple-even proof may therefore be organized around the positive inequality

```text
P_a(phi_lambda,phi_lambda)
 -H_(a,infinity)(phi_lambda,phi_lambda)
 >= parity_margin_lambda>0,                            (14)
```

on the source-selected radial-prolate half-vector, together with a lower bound for `T_a-H_a` on
the competing odd sector. To transfer the source parity gap quantitatively, the resulting margin
must dominate the bilinear comparison error at the `lambda^(-4)` relative scale.

This is a boundary constraint, not an evolution mechanism: the finite prime powers and the
archimedean kernel fix the parity through one Hankel correlation law.

## Pointed global incidence lift

The formalized critical-disc Euler-orbit theorems determine the topology in which `(14)` must be
proved. `CriticalDiscSchwarzCompleteness.lean` and `CriticalDiscEulerOrbitDensity.lean` show that,
after deleting any finite prime set, the genuine FE--Schwarz Euler increments have dense orbit on
every fixed-divisor regular-germ fibre. Every compact-open continuous invariant of that orbit is
therefore constant. Restoring the principal part leaves only divisor/multiplicity data as the
maximal continuous quotient. `CriticalTraceMomentGerm.lean` identifies the normalized odd trace
with its even moment germ, while `TraceHankelAnalyticInstability.lean` proves that the positive
trace-Hankel cone is nowhere thick in the compact-open germ topology.

Accordingly, the parity carrier is not a scalar function of the continued local germ. It is the
following pointed incidence state:

```text
I_a(phi,F)
 =(
    b_a(n)=Lambda(n)n^(-1/2) 1_(n<e^(2a)),
    K_reg(t)dt,
    c_phi(t),
    M(F)=normalized even trace-moment germ of F,
    Div(F)
   ).                                                   (15)
```

The first three entries form the source-side Hankel pairing `(12)`; the last two retain the
distinguished divisor/trace data of the same characteristic function. The carrier is **pointed** by
the actual von Mangoldt coefficient vector and the actual archimedean completion.

For a finite coefficient increment `delta b`, the Hankel margin obeys the exact cocycle law

```text
H_(b+delta b)(phi,phi)-H_b(phi,phi)
 =-sum_n delta b(n)c_phi(log n).                        (16)
```

Thus the carrier deliberately varies along the dense Euler-unit orbit; it does not descend to the
one-point regular-germ quotient. Equation `(16)` is the incidence that keeps the weighted prime
tail visible.

The natural global topology is the locally convex incidence topology generated by

```text
(b,c) |-> sum_n b(n)c(log n),
c |-> integral_0^infinity K_reg(t)c(t)dt,
F |-> M(F),
F |-> Div(F),                                           (17)
```

with absolute weighted-tail control on the first two pairings on every admitted radial-prolate
family. This topology is strictly finer than compact-open convergence of the regular germ because
the latter identifies the closure of every fixed-divisor Euler orbit, while `(16)` separates its
source points.

The positive CCM transfer problem is therefore:

```text
weighted all-prime coefficient tail
  + archimedean completion
  + radial-prolate autocorrelation samples
  + distinguished divisor/trace moments
  -> cofinal parity margin and Xi divisor.              (18)
```

Compact-open determinant convergence remains the final divisor-transfer conclusion, but a source
proof of that convergence must be built in the stronger incidence topology `(17)`.

## Cofinal inertia sharpening

The carrier's sign-indefiniteness is now exact. Prime-free corners already give infinite negative
index. For `a>log(2)/2`, the first-prime term in `(9)` is an interior negative reflection across
`x+y=log 2`; arbitrarily many narrow reflected-even and reflected-odd bump pairs retain opposite
signs against the regular kernel. Thus the full parity difference has infinite positive and
negative index cofinally. See `suzuki-prime-seam-parity-hankel-strong-indefiniteness.md`.

## Exact limitation

The sign of `H_a` is not fixed on the whole positive cone. The regular kernel is positive on an
open region at large aperture, while the prime atoms contribute negatively. Accordingly, `(14)` is
a source-specific arithmetic inequality, not a global order property. The theorem identifies the
carrier and the required margin but does not prove that inequality for the CCM prolate sequence.

## Novelty and significance verdict

The decomposition `T+H`/`T-H` is standard parity reduction for an even convolution kernel, and the
prime-power formula follows directly by differentiating Suzuki's explicit screw function. The
result is a useful route reduction but fails the parent-theory and anti-theatre gates for new
scientific knowledge. Its contribution is precision: cofinal parity transfer is reduced to the
finite-prime boundary Hankel inequality `(14)`.

## References

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean status

**Superseded, 2026-08-03.**  The "no screw distribution" premise of the previous decision is now
false.  `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-screw-kernel-positivity-improving-breakdown.md` built, unconditionally:

- `RHTower/Suzuki/SuzukiExplicitScrewRegularKernel.lean` — Suzuki's explicit screw function `screwFn`,
  the hinge sum `screwPrimeSum` with its off-atom local affineness, the archimedean Lerch tail, and
  `iteratedDeriv 2 (screwFn c₁ c₀) t = -screwRegularKernel t` off the prime-power atoms, plus the
  plastic-number sign threshold.
- `RHTower/Suzuki/SuzukiScrewDisjointCrossCoupling.lean` — `screwAtoms` and its discreteness,
  `screwRegularForm`, and the disjoint-support positive cross coupling.
- `RHTower/Suzuki/SuzukiScrewDistributionalKernel.lean` — global affineness of the hinge sum on an
  atom-free interval and the two-fold integration by parts `-∫ g φ'' = ∫ K φ`.
- `RHTower/Suzuki/SuzukiScrewCorrelationPairing.lean` — `screwCrossCorr`, `screwCorrelationForm`, and the
  shear identity `∫∫ K(x−y) f y h x = ∫ K u * c_(f,h)(u) du`.

`K_reg` of `(6)` is therefore `screwRegularKernel`, and `(12)`'s right-hand pairing is
`screwCorrelationForm` specialised to `φ = ψ`.

Every proved theorem of this card is now formalized unconditionally.

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiParityHankelDecomposition.lean`

- `diffBilinForm K f g = ∫∫ K(x−y) f y g x` and `sumBilinForm K f g = ∫∫ K(x+y) f y g x` — the
  Toeplitz and Hankel forms.  For `φ, ψ` supported in `(0,a)` these are exactly `T_a` and `H_a`,
  the zero extension being harmless.
- `evenParityLift`, `oddParityLift` — the lifts `(2)`, defined with `|x|` and `Real.sign` as
  published; `evenParityLift_eq_of_vanishing` / `oddParityLift_eq_of_vanishing` prove that on
  functions vanishing on `(-∞,0]` they are exactly symmetrisation and antisymmetrisation
  `(φ ± φ∘(-·))/√2`.  This is the step that replaces the four-quadrant split.
- `measurePreserving_negSnd` / `negFst` / `negBoth` and the corresponding `integral_comp_*`,
  `integrable_comp_*` — the three reflections of `ℝ × ℝ` are measure preserving, so
  `diffBilinForm_negReflect_left` (no evenness needed), `diffBilinForm_negReflect_right` and
  `diffBilinForm_negReflect_both` hold with no integrability hypothesis at all.
- **`diffBilinForm_evenParityLift`** and **`diffBilinForm_oddParityLift`** — equations `(4)`:
  `Q_even = T + H` and `Q_odd = T - H`; **`diffBilinForm_parity_difference`** — equation `(5)`:
  the gap is `2 H`.  The only hypotheses are evenness of `K`, vanishing of `φ, ψ` on `(-∞,0]`, and
  integrability of the two basic integrands.

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPrimeHankelCarrier.lean`

- `screwConvolve φ ψ t = ∫ φ y * ψ (t − y) dy` — the carrier `c_(φ,ψ)` of `(11)`;
  `screwCrossCorr_negReflect` identifies it with the reflected correlation.
- **`screwConvolve_eq_zero_of_two_mul_le`** — equation `(10)`: the convolution vanishes at every
  `t ≥ 2a`, hence only prime powers with `log n < 2a`, i.e. `n < lambda^2`, contribute.
- **`screwConvolve_eq_intervalIntegral`** — equation `(9)`: at `0 < t < 2a` the carrier is the
  integral over the explicit window `(max 0 (t−a), min a t)`.
- **`diffBilinForm_eq_correlation_pairing`**, **`sumBilinForm_eq_convolution_pairing`** — the shear
  identities `(8)`/`(12)`: each two-variable form is the kernel paired against the one-variable
  carrier, by two Fubini applications and one translation.
- `atomicHankelPart`, `primeHankelPart`, **`atomicHankelPart_eq_primeHankelPart`** — the atomic part
  `(9)` and the fact that enlarging the index range past `e^(2a)` adds nothing.
- **`atomicHankelPart_add`**, **`atomicHankelPart_sub`** — equation `(16)`, the exact coefficient
  cocycle `H_(b+δb) − H_b = −∑ δb n * c(log n)`.
- **`sumBilinForm_sub_atomic`** — equation `(7)`: the Hankel carrier is the regular convolution
  pairing minus the finite prime-power samples.
- **`parityGap_eq_regular_sub_atomic`**, **`parityGap_autocorrelation`** — `(5)` combined with
  `(7)`/`(12)`: the even sector exceeds the odd sector by exactly twice the difference between the
  archimedean convolution pairing and the finite prime-power convolution samples.  This is the
  arithmetic invariant of `(13)`.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem above.

Not formalizable at this card's level: the passage from a kernel that is a genuine distribution
(Suzuki's `-g''`, whose Toeplitz part is singular on the diagonal) to the closed parity forms.  The
card itself only claims this "by form-core density"; the Lean statements above are the exact
integrable-kernel content, and `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-screw-kernel-positivity-improving-breakdown.md` supplies the
distributional identification `-∫ g φ'' = ∫ K φ` on atom-free intervals.

## Gates

- [x] exact parity `T+H`/`T-H` decomposition proved
- [x] prime-power atomic Hankel term extracted
- [x] cutoff `n<lambda^2` proved
- [x] source-specific positive parity inequality isolated
- [x] finite Euler-unit incidence cocycle identified
- [x] pointed global carrier and stronger topology specified
- [x] Lean: parity lifts, `T+H`/`T-H` decomposition `(4)`--`(5)` unconditional
- [x] Lean: convolution carrier, shear identities `(8)`/`(12)`, cutoff `(10)`, window `(9)`
- [x] Lean: regular-minus-atomic split `(7)` and the coefficient cocycle `(16)`
- [ ] prove the radial-prolate Hankel margin `(14)`
- [ ] prove the competing odd-sector lower bound
- [ ] transfer the `lambda^(-4)` source parity gap to the true Weil form

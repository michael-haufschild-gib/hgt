# Large-aperture CCM simplicity requires sign-indefinite spectral geometry

- **ID:** `ccm-screw-kernel-positivity-improving-breakdown`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NECESSITY THEOREM / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096, equations (1.3), (2.9)--(2.11), and the proof of Theorem 1.4.
- **Statement:** Above an explicit aperture threshold, the exact restricted Weil operator has
  positive cross-couplings between disjoint nonnegative vectors. Therefore a cofinal CCM
  simple-even theorem must use sign-indefinite spectral geometry: parity-separated min--max,
  oscillation/no-crossing, source transversality, or projective comparison.

## Setup

Use Suzuki's additive logarithmic coordinate. For `a>0`, the restricted Weil form on
`C_c^infinity(-a,a)` is

```text
QW^a(f,g)
 = integral_(-a)^a integral_(-a)^a
     K(x-y) f(y) conjugate(g(x)) dx dy,                 (1)

K=-g''                                                     (2)
```

in the distributional sense, where for `t>0`

```text
g(t)
 =-4(e^(t/2)+e^(-t/2)-2)
  +sum_(n<=e^t) Lambda(n)n^(-1/2)(t-log n)
  -(t/2)(psi(1/4)-log pi)
  -(1/4)(Phi(1,2,1/4)-e^(-t/2)Phi(e^(-2t),2,1/4)).     (3)
```

Let `rho>1` be the unique real root of

```text
rho^3-rho-1=0,                                           (4)
```

and put

```text
t_*=log rho.                                               (5)
```

## Exact regular kernel away from prime-power atoms

`[PROVED]` If `t>0` and `t!=log n` for every integer `n>=2`, then

```text
K(t)=e^(t/2)-e^(-5t/2)/(1-e^(-2t)).                       (6)
```

In particular,

```text
K(t)>0  iff  e^(3t)-e^t-1>0  iff  t>t_*.                 (7)
```

### Proof

The prime-power hinge terms in `(3)` have zero classical second derivative away from their atoms
`t=log n`. The linear term also disappears. The exponential term contributes

```text
-(e^(t/2)+e^(-t/2))
```

to `g''`. Expanding the Lerch term gives

```text
(1/4)e^(-t/2)Phi(e^(-2t),2,1/4)
 =(1/4)sum_(k>=0)e^(-(2k+1/2)t)/(k+1/4)^2.              (8)
```

Since `2k+1/2=2(k+1/4)`, its second derivative is

```text
sum_(k>=0)e^(-(2k+1/2)t)=e^(-t/2)/(1-e^(-2t)).          (9)
```

Negating the sum of these contributions and simplifying proves `(6)`. Multiplication of `(6)` by
the positive quantity `e^(5t/2)(1-e^(-2t))` gives `(7)`.

## Sign-indefinite cross-coupling theorem

`[PROVED]` If

```text
a>t_*/2,                                                   (10)
```

there exist nonzero real nonnegative functions `f,h in C_c^infinity(-a,a)` with disjoint supports
such that

```text
QW^a(f,h)>0.                                               (11)
```

### Proof

Choose

```text
t in (t_*,2a) \ {log n:n>=2}.                              (12)
```

This is possible because the excluded set is discrete. By continuity of the regular kernel away
from its atoms and `(7)`, there is an open interval `J` containing `t` on which `K>0` and which
contains no `log n`. Choose sufficiently small disjoint intervals `I_-` and `I_+` centered at
`-t/2` and `t/2`, contained in `(-a,a)`, such that

```text
I_+-I_- subset J.                                         (13)
```

Take nonzero nonnegative smooth bumps `f,h` supported in `I_-`, `I_+`. The diagonal principal-value
singularity never meets the product support, and the prime-power delta atoms are excluded by `(13)`.
Thus `(1)` is an ordinary integral there, and

```text
QW^a(f,h)
 =integral_(I_+) integral_(I_-) K(x-y)f(y)h(x)dy dx>0.  (14)
```

This proves `(11)`.

For a lower-semibounded real symmetric form, positivity preservation of the associated semigroup
implies the first Beurling--Deny inequality

```text
q(f,h)<=0                                                  (15)
```

for all nonnegative form-domain vectors with disjoint support. Adding a scalar multiple of the
`L2` norm does not change the cross pairing of disjoint vectors. Equations `(11)`--`(15)` therefore
show that no scalar shift of the exact restricted Weil operator has a positivity-preserving, hence
no positivity-improving, semigroup for any aperture satisfying `(10)`.

## Positive requirement for large-aperture simple-evenness

Suzuki proves small-aperture simple-evenness by first obtaining an irreducible Dirichlet limiting
form with positivity-improving semigroup and then using perturbation theory. The theorem above shows
that the exact cofinal Weil form enters a genuinely sign-indefinite class. The positive cofinal
target is therefore

```text
parity-reduced restricted Weil operators
  + quantitative separation/no-crossing across growing aperture
  + source-selected overlap with the even prolate seed
  -> simple even ground state.                                    (16)
```

The explicit positive cross-couplings identify what such a theorem must control: sign changes and
parity sectors, rather than an order cone. The divided-difference commutator, an oscillation theorem,
a source-specific transversality law, or the projective comparison with `k_lambda` are all
structurally compatible mechanisms.

`constrained-prolate-fourier-parity-floor-separation.md` now supplies the positive source model for
that mechanism: after the zero-integral constraint, the positive-Fourier floor lies below the
negative-Fourier floor by `C lambda^(-4)`. A bilinear Weil-tail comparison preserving this ordering
would prove large-aperture even dominance without any order-preserving semigroup.

## Pipeline position

The theorem is complementary to
`positive-density-transverse-divisor-relocation-law.md`: the full characteristic function supplies
the required transverse localization, while the present theorem specifies the sign-indefinite
spectral mechanism needed to produce its simple-even ground vector. The CCM target remains exactly
the one in
`ccm-growing-aperture-mellin-determinant-transfer.md`.

## Novelty verdict

The calculation is a direct differentiation of Suzuki's explicit kernel followed by the standard
Beurling--Deny criterion. It gives a useful exact classification of the cofinal spectral geometry,
but it is routine parent theory after the kernel is written and is therefore classified as a bridge.

## Lean status

**Superseded, 2026-08-03.**  The previous "no Lean file is added" decision is retired: Suzuki's
explicit screw function `(3)` and its classical second derivative off the prime-power atoms are now
built, and both proved theorems of this card are formalized unconditionally.

`formal/GaloisForLFunctions/RHTower/SuzukiExplicitScrewRegularKernel.lean`

- `screwFn c₁ c₀` — Suzuki's explicit screw function `(3)`, with the two archimedean constants
  `ψ(1/4) − log π` and `(1/4)Φ(1,2,1/4)` carried as parameters and instantiated at
  `screwLinearCoeff = (Complex.digamma (1/4)).re − log π`, `screwLerchConst = screwLerchTail 0`.
- `screwPrimeSum` — the von Mangoldt hinge sum; `exists_locallyAffine_screwPrimeSum` proves it is
  locally affine off the atoms (the index set `{n : log n ≤ t}` is locally constant), which is the
  reason the arithmetic part contributes nothing to the regular kernel.
- `screwLerchTail`, `screwLerchTail₁`, `screwLerchTail₂` and `screwLerchTail₂_eq` — the archimedean
  Lerch tail `∑_k e^(−λ_k t)/λ_k²`, `λ_k = 2k + 1/2`, differentiated twice termwise on every ray
  `(δ,∞)` and summed to `e^(−t/2)/(1 − e^(−2t))`.  This is exactly `(8)`--`(9)`.
- `iteratedDeriv_two_screwFn` / `iteratedDeriv_two_screwFn_suzuki` — **equation `(6)`**:
  `iteratedDeriv 2 (screwFn c₁ c₀) t = −screwRegularKernel t` for every `t > 0` which is not a
  prime-power atom.
- `plasticRoot`, `plasticRoot_cubic`, `cubic_pos_iff_plasticRoot_lt`, `screwSignThreshold` —
  the unique real root of `ρ³ − ρ − 1` by the intermediate value theorem plus strict monotonicity
  on `[1,∞)`, and `t_* = log ρ`.
- `screwRegularKernel_mul_eq_cubic`, `screwRegularKernel_pos_iff_cubic`,
  `screwRegularKernel_pos_iff`, `screwRegularKernel_neg_of_lt_threshold` — **equation `(7)`**:
  `0 < K t ↔ 0 < e^(3t) − e^t − 1 ↔ t_* < t`, and strict negativity below the threshold.

`formal/GaloisForLFunctions/RHTower/SuzukiScrewDisjointCrossCoupling.lean`

- `screwAtoms`, `exists_atomFree_mem_Ioo`, `exists_atomFree_radius` — the atoms in a bounded
  interval form a finite set, so every nonempty open interval contains a non-atom and every
  non-atom has an atom-free neighbourhood.  This is the discreteness step of `(12)`.
- `screwRegularForm` — the ordinary double integral `∫∫ K(x − y) f y h x`, which is the restricted
  Weil form on pairs whose support difference avoids `0` and every atom.
- `exists_disjoint_positive_screwRegularForm` — **equations `(10)`--`(11)`, `(14)`**: for every
  aperture `a > t_*/2` two `C^∞` nonnegative bumps with disjoint supports inside `(−a,a)` are
  constructed (`ContDiffBump` at `±t/2` with radius controlled by the threshold gap, the atom gap,
  the aperture and the separation) and the resulting pairing is proved strictly positive.
- `SatisfiesBeurlingDeny`, `screwL2Pairing`, `screwL2Pairing_eq_zero_of_disjoint`,
  `not_satisfiesBeurlingDeny_screwRegularForm_add_smul` — **equation `(15)`**: the `L²` pairing of
  disjointly supported vectors vanishes, so *no* scalar shift of the form satisfies the first
  Beurling--Deny inequality, hence none has a positivity preserving semigroup.

`formal/GaloisForLFunctions/RHTower/SuzukiScrewDistributionalKernel.lean`

- `exists_affine_screwPrimeSum_Ioo` — on an atom-free open interval the hinge sum is not merely
  locally but **globally** one affine function, because every atom then lies outside the interval.
- `screwFnDeriv c₁ A`, `hasDerivAt_screwFn_Ioo`, `hasDerivAt_screwFnDeriv`,
  `continuousOn_screwFnDeriv` — the first derivative of `g` as an explicit smooth-plus-slope
  function, and its own derivative `−K` on all of `(0,∞)`.
- `neg_integral_screwFn_mul_secondDeriv` — **the distributional form of `(6)`**: two integrations
  by parts give `−∫_a^b g φ'' = ∫_a^b K φ` for every twice differentiable `φ` whose value and
  derivative vanish at the endpoints of a compact subinterval of an atom-free `(α,β) ⊆ (0,∞)`.
  This is what licenses reading `(1)` as an ordinary integral against `K` on such supports.

`formal/GaloisForLFunctions/RHTower/SuzukiScrewCorrelationPairing.lean`

- `screwCrossCorr`, `screwCorrelationForm` — the cross-correlation `c_(f,h)(u) = ∫ f y h(u+y) dy`
  and the one-variable pairing `∫ K u * c_(f,h)(u) du`.
- `integrable_uncurry_screwFormIntegrand`, `integrable_uncurry_screwShearIntegrand` — both
  two-variable integrands are continuous on an explicit compact rectangle and vanish outside it;
  this is where the hypothesis that the support difference stays in `(0,∞)` is consumed, the kernel
  being unbounded at the origin.
- `screwRegularForm_eq_screwCorrelationForm` — **the shear identity**
  `∫∫ K(x−y) f y h x = ∫ K u * c_(f,h)(u) du`, by two Fubini applications separated by one
  translation of the inner variable.
- `exists_disjoint_positive_screwCorrelationForm` — the positive cross coupling read in the
  difference variable, i.e. `(14)` in the coordinate in which `K = −g''` lives.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem above.

The chain `−g'' → K → ∫∫ K(x−y) f y h x → ∫ K c_(f,h)` is therefore complete in Lean, and the two
proved theorems of this card — the exact regular kernel `(6)`--`(7)` and the sign-indefinite
cross coupling `(10)`--`(15)` — carry no remaining formal gap.

## Gates

- [x] exact regular off-diagonal screw kernel computed
- [x] explicit positivity threshold identified
- [x] disjoint positive bump violation proved
- [x] stability under scalar shifts addressed
- [x] cofinal sign-indefinite spectral class identified
- [x] Lean: screw function, its second derivative `(6)` and the threshold `(7)` unconditional
- [x] Lean: disjoint positive cross coupling and the Beurling--Deny failure unconditional
- [x] Lean: integration-by-parts bridge from `−g''` to the regular kernel on atom-free intervals
- [x] Lean: Fubini identification of the two-variable and correlation pairings
- [ ] parity-separated/oscillatory cofinal simple-even theorem
- [ ] projective CCM ground-vector transfer
- [ ] RH

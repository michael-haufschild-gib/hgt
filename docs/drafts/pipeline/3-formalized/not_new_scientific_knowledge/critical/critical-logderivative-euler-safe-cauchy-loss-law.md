# The critical logarithmic-derivative RH kernel is an Euler-safe Cauchy-loss contraction

- **ID:** `critical-logderivative-euler-safe-cauchy-loss-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `ccm-safe-kernel-diagonal-fock-lift-rh-law.md` and
  `critical-logderivative-two-channel-weil-resolvent-law.md`
- **Statement:** On every half-plane lying strictly inside absolute Euler convergence, the
  RH-deciding critical logarithmic-derivative kernel is exactly an unconditional positive
  Carathéodory kernel minus its positive Hardy--Cauchy Schur loss.  RH is equivalent to the one
  remaining source-specific kernel domination, equivalently to an explicit finite
  Cauchy--Laplace observability inequality whose density is given by the absolutely convergent
  prime--Gamma logarithmic derivative.

## Goal

Replace the opaque request to prove positivity of the critical logarithmic-derivative kernel by a
static comparison of two kernels that are separately defined in the absolute Euler half-plane.
The unconditional term must have an explicit positive boundary density; the lost term must be a
canonical positive tensor factor; and the comparison must remain strictly stronger than ordinary
positive-realness.

The fixed half-unit, real-ray diagonal-Fock version of this carrier is already proved in
`ccm-safe-kernel-diagonal-fock-lift-rh-law.md`.  The incremental content here is the arbitrary
safe offset `a>1/2`, complex sampling nodes, and the explicit Herglotz boundary-density form of the
same contractivity problem.  This card is therefore a refinement of that bridge, not an independent
RH route.

## Setup

Put

```text
X(w)=xi(1/2+w),
L(w)=X'(w)/X(w).                                          (1)
```

Fix a real number `a>1/2` and write

```text
H_a={w in C : Re(w)>a},
d(w,v)=w+conjugate(v),
N(w,v)=L(w)+conjugate(L(v)).                              (2)
```

Every `w in H_a` corresponds to `s=1/2+w` with `Re(s)>1`.  Thus `X` is zero-free there and the
Euler series for the logarithmic derivative converges absolutely.

Define three kernels on `H_a`:

```text
K_a(w,v)=N(w,v)/(d(w,v)-2a),
C_a(w,v)=2a/d(w,v),
K_0(w,v)=N(w,v)/d(w,v).                                  (3)
```

Here `K_0` is the RH-complete kernel of the parent card.  The subscript zero records that its
denominator is the Cauchy kernel of the critical half-plane `Re(w)>0`, even though it is sampled
only in `H_a`.

## Unconditional Euler-safe positivity

`[PROVED]` Both `K_a` and `C_a` are positive semidefinite kernels on `H_a`, and

```text
C_a(w,w)=a/Re(w)<1.                                      (4)
```

Indeed, the Sondow--Dumitrescu horizontal-monotonicity theorem applied to the zero-free half-plane
`Re(s)>1` gives

```text
Re L(w)=d/dsigma log|xi(1/2+sigma+i Im(w))| at sigma=Re(w)>0.  (5)
```

Thus `L` maps `H_a` to the open right half-plane.  The half-plane Carathéodory theorem says
precisely that the first kernel in `(3)` is positive.  The second has the explicit Gram
representation

```text
C_a(w,v)=integral_(0,infinity)
           2a exp(-w x) exp(-conjugate(v) x) dx,           (6)
```

which proves its positivity and `(4)`.

## Exact Cauchy-loss identity

`[PROVED]` Pointwise on `H_a x H_a`,

```text
K_0=K_a-K_a circle C_a,                                  (7)
```

where `circle` denotes the Schur, or entrywise, product.  Consequently,

```text
RH
  <-> K_0 is positive on H_a
  <-> K_a circle C_a <= K_a.                              (8)
```

### Proof

The algebraic identity is immediate:

```text
K_a(w,v)*(1-C_a(w,v))
 =N(w,v)/(d(w,v)-2a) * (1-2a/d(w,v))
 =N(w,v)/d(w,v)
 =K_0(w,v).                                               (9)
```

The Schur product theorem and the preceding section also give

```text
K_a circle C_a >=0                                       (10)
```

unconditionally.  Hence `(7)` turns positivity of `K_0` into the domination in `(8)`.

The parent complete-detector theorem proves that positivity of `K_0` on an Euler uniqueness
half-plane is equivalent to RH.  For completeness, the same argument works on every `H_a`.
Positivity of the kernel

```text
(L(w)+conjugate(L(v)))/(w+conjugate(v))                   (11)
```

on the nonempty open set `H_a` is the Nevanlinna--Pick condition for the values of `L` to be the
restriction of a positive-real function on `Re(w)>0`.  The extension agrees with the actual
meromorphic `L` on `H_a`; uniqueness of analytic continuation therefore rules out every pole of
`L` in `Re(w)>0`.  Such a pole is a right-half nontrivial Xi zero.  Functional-equation symmetry
then gives RH.  Conversely, RH makes `Re(w)>0` zero-free, so the same Carathéodory theorem gives
positivity of `(11)` and hence its restriction to `H_a`.

This proves `(8)`.

## RKHS contraction form

Let `H(K_a)` and `H(C_a)` be the reproducing-kernel Hilbert spaces of the two unconditional
kernels, with kernel vectors `e_w` and `c_w`.  On the algebraic kernel span consider

```text
Delta_a(e_w)=e_w tensor c_w.                              (12)
```

For every finite node/coefficient system,

```text
||sum_j c_j e_(w_j)||^2
  =sum_(j,k)c_j conjugate(c_k) K_a(w_j,w_k),

||sum_j c_j e_(w_j) tensor c_(w_j)||^2
  =sum_(j,k)c_j conjugate(c_k)
     K_a(w_j,w_k) C_a(w_j,w_k).                           (13)
```

Therefore `(12)` descends to a contraction

```text
Delta_a : H(K_a) -> H(K_a) tensor H(C_a)                 (14)
```

if and only if `K_a circle C_a<=K_a`.  Combining with `(8)` gives the static operator criterion

```text
RH <-> Delta_a is contractive.                            (15)
```

This is a constraint on a canonical diagonal embedding, not a spectral flow or an auxiliary
determinant carrying a prescribed Xi divisor.

## Absolute-Euler boundary realization

On the boundary of `H_a` put

```text
h_a(t)=Re L(a+it).                                        (16)
```

The preceding monotonicity theorem gives `h_a(t)>0` unconditionally.  The logarithmic growth of
`L` kills the possible linear mass at infinity in the half-plane Herglotz representation, while
analyticity across `Re(w)=a` makes the finite boundary measure absolutely continuous.  Hence

```text
K_a(w,v)
 =1/pi * integral_R h_a(t)
    /((w-a-it)(conjugate(v)-a+it)) dt.                    (17)
```

Writing `s=1/2+a+it`, the density is source-defined by

```text
L(a+it)
 =1/s+1/(s-1)-1/2 log(pi)+1/2 psi(s/2)
  -sum_(n>=2) Lambda(n)n^(-s),                            (18)
```

and the series in `(18)` is absolutely convergent because `Re(s)=1/2+a>1`.

Insert `(6)` and `(17)` into the kernel domination.  The common factor `1/pi` cancels, giving the
following exact finite source inequality:

```text
2a * integral_R h_a(t) integral_(0,infinity)
       |sum_j c_j exp(-w_j x)/(w_j-a-it)|^2 dx dt

 <= integral_R h_a(t)
       |sum_j c_j/(w_j-a-it)|^2 dt.                       (19)
```

Thus, for every fixed `a>1/2`,

```text
(19) for every finite node/coefficient system
  -> K_a circle C_a<=K_a
  -> K_0>=0
  -> RH.                                                  (20)
```

Every quantity in `(19)` is formed before choosing a Xi zero and inside absolute Euler
convergence.  No divisor enumeration, real-rootedness, anti-Herglotz continuation sign,
RH-equivalent limiting measure, or theta-current bound occurs in the premise.

## Countable source criterion

Fix any rational `a>1/2`; `a=1` is the simplest choice, with boundary line `Re(s)=3/2`.
Continuity of the kernels and density of `Q(i)` imply that it is enough to test `(19)` for

```text
N in N,
w_1,...,w_N in Q(i) intersect H_a,
c_1,...,c_N in Q(i).                                     (21)
```

Consequently `(19)` is a countable family of finite, absolute-Euler value inequalities.

## The domination is not generic positivity

The pointwise estimate `(4)` does not imply the matrix domination.  This is already false for the
positive-real function

```text
F_a(w)=1/(w-a).                                           (22)
```

Its Carathéodory kernel is

```text
K_a^F(w,v)=1/((w-a)(conjugate(v)-a)).                     (23)
```

For two distinct real nodes `x,y>a`, the matrix of
`K_a^F-K_a^F circle C_a` is a positive diagonal congruence of

```text
S_a(x_i,x_j)=1-2a/(x_i+x_j).                              (24)
```

But

```text
det [[S_a(x,x),S_a(x,y)],
     [S_a(y,x),S_a(y,y)]]
 =-a*(x+y-a)*(x-y)^2/(x*y*(x+y)^2)<0.                    (25)
```

So even an unconditional positive Carathéodory kernel and a strictly subunit Cauchy factor do not
give `(19)`.  The open inequality is genuinely multi-node and must use exact structure of the
prime--Gamma density `h_a`.

## Interfaces with the formal corpus

The current Lean tree already supplies the target-side Cauchy algebra:

- `RHTower/XiWeilResolventSource.lean` proves absolute summability, exact divided differences of
  the Xi relative resolvent, and prime--Gamma formulas for finite Cauchy packets;
- `RHTower/XiWeilOneCauchyGate.lean` proves the existing one-Cauchy diagonal criterion, whose open
  sign is the RH-equivalent continued anti-Herglotz condition;
- `RHTower/XiHurwitzOrientationCauchyClosure.lean` proves that the full orientation vector lies in
  the continued regular-Cauchy source closure.

The new criterion is complementary.  It never enters the continued zero strip: it asks for a
matrix contraction on the line `Re(s)=1/2+a>1`, where the density is unconditionally positive and
the Euler series is absolute.  It therefore does not discharge the existing continued-Cauchy sign
by relabelling it.  The reusable missing formal infrastructure is the half-plane
Carathéodory/Herglotz kernel, its boundary `L^2(h_a dt)` realization, and the diagonal RKHS tensor
map `(12)`.

## Research consequence

The earlier vague source task

```text
construct a positive Gram factorization of K_0
```

can be replaced by the sharper positive task

```text
prove that the absolute-Euler boundary Cauchy family loses no more norm
under the canonical Laplace tensoring Delta_a.             (26)
```

The whole unconditional part of the decomposition is explicit.  The only open theorem is the
source-specific finite inequality `(19)`.  A successful proof would give the short chain

```text
absolute-Euler Cauchy--Laplace observability
  -> critical logarithmic-derivative kernel positivity
  -> RH.                                                   (27)
```

## Scientific status

The exact half-unit subtraction and diagonal-Fock contraction were already isolated in
`ccm-safe-kernel-diagonal-fock-lift-rh-law.md`.  The arbitrary-offset complex-node extension and its
boundary observability formula are a composition of classical Carathéodory, Herglotz,
Schur-product, RKHS, and Nevanlinna--Pick facts.  The card is therefore conservatively classified as
not new scientific knowledge and not a new carrier.  Its value is narrower: it converts the
existing Fock defect into an explicit absolute-Euler boundary inequality while removing divisor
data and nonpositive continued-source terms from the premise.

## References

- Jonathan Sondow and Cristian Dumitrescu, *A monotonicity property of Riemann's xi function and a
  reformulation of the Riemann Hypothesis*, arXiv:1005.1104.
- The classical Herglotz representation and Carathéodory/Nevanlinna--Pick kernel criteria on a
  half-plane.
- `ccm-safe-kernel-diagonal-fock-lift-rh-law.md`.
- `critical-logderivative-two-channel-weil-resolvent-law.md`.
- `xi-shift-loewner-prime-generator-law.md`.

## Lean decision (SUPERSEDED)

The original decision deferred formalization until reusable half-plane positive-kernel
infrastructure existed.  That infrastructure has now been built, and every proved statement of this
card is certified in Lean; see the section below.

## Gates

- [x] absolute-Euler positivity of `L` established
- [x] unconditional positive kernels `K_a` and `C_a` identified
- [x] exact critical-kernel loss identity proved
- [x] RKHS contraction criterion proved equivalent to RH
- [x] explicit prime--Gamma boundary density attached
- [x] finite Cauchy--Laplace observability inequality derived
- [x] countable rational test family extracted
- [x] generic positive-real shortcut ruled out by a two-node theorem
- [ ] prove `(19)` from exact relations of the canonical density `h_a`
- [ ] deduce RH

## Lean formalization — the proved content is COMPLETE (unconditional)

Every `[PROVED]` statement and every checked gate of this card is now a Lean theorem with a clean
axiom audit (`propext, Classical.choice, Quot.sound` only).  The missing reusable infrastructure
named in "Interfaces with the formal corpus" — the half-plane Carathéodory kernel and the RKHS Gram
dictionary — was built for this card and is stated for arbitrary functions, not for `L` alone.

### Reusable infrastructure (HTGeometry)

| Statement | Lean name | Module |
|---|---|---|
| Kernel form is natural in the index type | `kernelForm_mapDomain` | `HTGeometry/PSDKernelOperations` |
| Pullback of a positive kernel | `IsPSDKernel.comp` | `HTGeometry/PSDKernelOperations` |
| Every finite Gram matrix of a positive kernel is PSD | `IsPSDKernel.posSemidef` | `HTGeometry/PSDKernelOperations` |
| Schur (entrywise) product of positive kernels `(10)` | `IsPSDKernel.mul` | `HTGeometry/PSDKernelOperations` |
| Sums, the constant kernel, rank-one kernels | `IsPSDKernel.add`, `isPSDKernel_one`, `isPSDKernel_rankOne` | `HTGeometry/PSDKernelOperations` |
| Finite kernel energy and its Gram matrix form | `kernelEnergy`, `dotProduct_mulVec_kernelMatrix` | `HTGeometry/PSDKernelOperations` |
| `(13)` energy = squared Gram norm | `inner_self_kernelCombination`, `norm_sq_kernelCombination` | `HTGeometry/PSDKernelOperations` |
| Hermitian + nonnegative real form ⟹ PSD matrix | `posSemidef_of_isHermitian_of_re_nonneg` | `HTGeometry/PSDKernelOperations` |
| `(14)` domination ⟺ energy domination on every finite system | `isPSDKernel_sub_iff_forall_energy_le` | `HTGeometry/PSDKernelOperations` |
| Circle representation of the Carathéodory kernel | `circle_caratheodory_representation` | `HTGeometry/CaratheodoryKernelPositive` |
| Circle Gram positivity from a nonnegative boundary real part | `posSemidef_circleCaratheodoryGram` | `HTGeometry/CaratheodoryKernelPositive` |
| Unit-disc Carathéodory Gram positivity | `posSemidef_discCaratheodoryGram` | `HTGeometry/CaratheodoryKernelPositive` |
| **Half-plane Carathéodory kernel of a positive-real function is PSD** | `posSemidef_halfPlaneCaratheodoryGram`, `isPSDKernel_halfPlaneCaratheodory` | `HTGeometry/CaratheodoryKernelPositive` |
| Shifted half-plane version (offset `a`) | `isPSDKernel_shiftedCaratheodory` | `HTGeometry/CaratheodoryKernelPositive` |
| Energy is continuous in nodes and coefficients | `continuous_kernelEnergy` | `HTGeometry/PSDKernelDensity` |
| `(21)` dense test families decide positivity | `isPSDKernel_of_dense_energy` | `HTGeometry/PSDKernelDensity` |

The half-plane theorem is proved from scratch: the Cauchy integral formula applied to
`f / (r² − conj(y)·ζ)` gives

```text
(f x + conj (f y)) / (r² - x conj y)
  = (2 pi)^(-1) integral_0^(2 pi) 2 Re f(r e^(i theta)) (r e^(i theta) - x)^(-1)
      conj((r e^(i theta) - y)^(-1)) d theta,
```

a circle average of rank-one kernels with nonnegative weight; rescaling `f` and letting the radius
tend to `1` gives the disc, and the Cayley identity
`1 - z_u conj z_v = 2 (u + conj v) / ((u+1)(conj v + 1))` transports it to the half plane.

### Card statements (RHTower/XiEulerSafeCauchyLoss)

| Card item | Lean name |
|---|---|
| `(1)`–`(3)` the three kernels `K_a`, `C_a`, `K_0` | `safeCaratheodoryKernel`, `cauchyLossKernel`, `criticalLogDerivKernel` |
| `(5)` unconditional Euler-safe positivity `Re L > 0` on `Re W > 1/2` | `re_logDeriv_xiCent_pos` |
| `(4)` `C_a(W,W) = a / Re W` and `< 1` on `H_a` | `cauchyLossKernel_diag`, `cauchyLossKernel_diag_lt_one` |
| `(6)` Laplace Gram representation of `C_a` | `cauchyLossKernel_eq_laplace` |
| `K_a` is an unconditional positive Carathéodory kernel | `isPSDKernel_safeCaratheodoryKernel` |
| `C_a` is positive on `H_a` | `isPSDKernel_cauchyLossKernel` |
| `(10)` the Schur loss `K_a ∘ C_a` is positive | `isPSDKernel_schurLoss` |
| `(9)` `K_a (1 - C_a) = K_0` | `safeCaratheodoryKernel_mul_one_sub_cauchyLossKernel` |
| `(7)` `K_0 = K_a - K_a ∘ C_a` | `criticalLogDerivKernel_eq_sub` |
| `(8)`, first equivalence: RH ⟺ `K_0 ≥ 0` on every `H_a`, `a ≥ 1/2` | `riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel` |
| `(8)`, `(15)`: RH ⟺ `K_a ∘ C_a ≤ K_a` | `riemannHypothesis_iff_kernelDominates` |
| `(13)`–`(14)`: RH ⟺ the diagonal map does not increase any finite energy | `riemannHypothesis_iff_energy_le` |
| `(21)` countable Gaussian-rational test family | `riemannHypothesis_iff_rational_energy_le`, `countable_gaussianRationalSet`, `dense_safeGaussianRational` |
| `(22)`–`(23)` model positive-real function and its Carathéodory kernel | `modelCaratheodoryKernel`, `modelCaratheodoryKernel_eq` |
| `(24)`–`(25)` two-node determinant `-a(x+y-a)(x-y)²/(xy(x+y)²) < 0` | `modelLossSymbol`, `det_modelLossSymbol`, `det_modelLossSymbol_neg` |
| the generic positive-real shortcut fails | `not_isPSDKernel_modelLoss` |

Supporting continuity facts: `differentiableAt_logDeriv_xiCent`,
`continuous_logDeriv_xiCent_subtype`, `continuous_safeCaratheodoryKernel`,
`continuous_cauchyLossKernel`.

### How `(5)` is discharged unconditionally

`xiCent W = XiC (-i W)` (`xiCent_eq_XiC`), so `logDeriv xiCent W = -i · logDeriv XiC (-i W)`
(`logDeriv_xiCent_eq`) and `Re (logDeriv xiCent W) = Im (logDeriv XiC (-i W))`.  The corpus's
unconditional critical-strip width `xiZeroHalfPlaneBound_half` feeds
`xiRelativeResolventTrace_im_pos_of_halfPlaneBound`, whose conclusion is exactly the strict
positivity of that imaginary part for `Im z < -1/2`, i.e. for `Re W > 1/2`.  This is the
Sondow--Dumitrescu mechanism of the card, in the pairing form the corpus already owns.

### `(17)` and `(19)` are now proved

| Card | Lean |
|---|---|
| `(2)` boundary density `h_a(t) = Re L(a+it)` | `RHTower.eulerSafeDensity` |
| `(17)` `K_a(w,v) = pi^{-1} integral h_a(t) ((w-a-it)(conj v-a+it))^{-1} dt` | `RHTower.safeCaratheodoryKernel_eq_boundary_integral`, `RHTower.integral_density_mul_boundaryCauchy` |
| `(19)` the exact finite source inequality, as an identity for its deficit | `RHTower.eulerSafeDeficit_eq`, `RHTower.eulerSafeDeficitReal_eq` |
| `(19)` ⟺ RH | `RHTower.riemannHypothesis_iff_eulerSafeDeficitReal_nonneg` |

The realization `(17)` is proved in `RHTower/XiBoundaryCauchyRepresentation`, not through abstract
Herglotz theory but through the Poisson divisor expansion of `h_a` (each `Re (w -+ i alpha)^{-1}`
*is* a Poisson kernel) together with the Poisson average of a Cauchy kernel
`integral P_c(u) (A - iu)^{-1} du = (A + c)^{-1}` (`HTGeometry/PoissonCauchyIntegral`).  The
deficit of `(19)` is then exactly `pi` times the energy of `K_0`, which is the child card
`critical-logderivative-euler-safe-depoissonized-weil-stationarity`.

### What is *not* formalized

The one unproved gate of the card is unchanged and is not claimed:

- a proof of `(19)` from the prime--Gamma density, and hence RH.

The Lean development certifies the complete unconditional decomposition, the boundary realization,
and every equivalence between the domination, the diagonal contraction, the observability deficit
and RH, but proves no instance of the open inequality.

## Log

- 2026-08-20 — Formalized in Lean 4.  New reusable modules
  `HTGeometry/PSDKernelOperations`, `HTGeometry/CaratheodoryKernelPositive`,
  `HTGeometry/PSDKernelDensity`, and the card module `RHTower/XiEulerSafeCauchyLoss`.  All 29
  capstones audit to `propext, Classical.choice, Quot.sound`.  Promoted to stage 3.
- 2026-08-20 — Gap closed.  The boundary Herglotz realization `(17)` and the observability
  inequality `(19)` are now Lean-proved; see `RHTower/XiBoundaryCauchyRepresentation` and
  `RHTower/XiEulerSafeObservability`.  The only remaining open gate is the sign of `(19)` itself.

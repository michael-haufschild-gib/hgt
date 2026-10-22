# Suzuki residual-overcrowding and entire-pair closure

- **ID:** `suzuki-residual-overcrowding-entire-pair-closure`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Lane:** Suzuki cofinal Clark divisor; exact residual elimination
- **Parents:** `suzuki-compactified-inverse-phase-lattice-holography`,
  `suzuki-finite-aperture-hermite-biehler-normal-family`
- **Source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  [arXiv:2606.09096](https://arxiv.org/abs/2606.09096), together with the project's
  Livsic--Donoghue and global-phase consequences
- **RH used:** no
- **Computation used:** no

## Frontier problem

The compactified inverse-phase theorem decomposes every cofinal spectral limit as

```text
sigma=sigma_lab+sigma_res.                               (1)
```

It left `sigma_res` as a positive measure.  The point of this theorem is to identify its exact
analytic producer.  Interior residual is equivalent to spectral mass carried by unbounded phase
labels inside a bounded physical window.  That is local Clark-divisor overcrowding, not physical
escape.  Local entire-pair normality forbids it.  The only remaining residual can then lie at the
two projective endpoints, where it is exactly the linear Nevanlinna coefficient.

## Setup

Use the notation of the parent theorem:

```text
y_k=(2k-1)pi,
u_(n,k)=U_n(y_k),
p_(n,k)=2U_n'(y_k),
sigma_n=sum_k p_(n,k) delta_(u_(n,k)).                   (2)
```

After extraction,

```text
u_(n,k)->u_k,
p_(n,k)->p_k,
sigma_n=>sigma,
sigma_lab=sum_k p_k delta_(u_k),
sigma_res=sigma-sigma_lab>=0.                            (3)
```

Every `U_n` is odd and strictly increasing.  In particular `u_(n,k)` is strictly increasing in
`k` and reflection pairs `k` with `1-k`.

## Theorem A: the residual is exactly the escaped-label tail `[PROVED HERE]`

For every nonnegative continuous function `f` on `[-pi/2,pi/2]`,

```text
int f d sigma_res
 =lim_(K->infinity) lim_(n->infinity)
    sum_(|k|>K) p_(n,k) f(u_(n,k)).                      (4)
```

The inner limit exists for every fixed `K`.  Thus `sigma_res` is not an abstract defect added by
weak compactness: it is precisely probability whose phase label tends to infinity.

### Proof

For fixed `K`, weak convergence and finite-coordinate convergence give

```text
lim_n sum_(|k|>K) p_(n,k)f(u_(n,k))
 =int f d sigma-sum_(|k|<=K)p_k f(u_k).                  (5)
```

The finite heads on the right increase to `int f d sigma_lab`.  Monotone convergence turns `(5)`
into `(4)`.

## Theorem B: interior residual is local divisor overcrowding `[PROVED HERE]`

For `0<r<pi/2`, let

```text
N_n(r)=#{k in Z: |u_(n,k)|<=r}.                          (6)
```

If

```text
sup_n N_n(r)<infinity            for every r<pi/2,       (7)
```

then

```text
sigma_res restricted to (-pi/2,pi/2) = 0.               (8)
```

Contrapositively, every positive interior residual forces unbounded Clark zero count in one fixed
physical compact interval.

### Proof

Fix a compact interval `J` in the projective interior and enlarge it to the compact interval
joining `J` to zero.  Strict order and oddness imply that if a label `|k|` tending to infinity has
`u_(n,k)` in `J`, then all intervening central labels also lie in the enlarged interval.  Its count
therefore tends to infinity, contradicting `(7)`.  Consequently every compact interior interval
contains only a fixed finite label head.  Formula `(4)` then vanishes for every nonnegative
continuous `f` supported in that interval.  Exhausting the interior proves `(8)`.

This separates the two defects sharply:

```text
interior residual  <=> escaped labels remain physically bounded (overcrowding),
endpoint residual  <=> physical mass escapes to projective infinity. (9)
```

## Theorem C: entire-pair normality kills interior residual `[PROVED HERE]`

Let `W_(n,-1)` be the even-extension Suzuki characteristic function, whose simple real zeros are
the physical points

```text
x_(n,k)=tan u_(n,k).                                    (10)
```

Suppose that there are zero-free entire gauges `g_n` such that

```text
g_n W_(n,-1) -> W_(-1)                                  (11)
```

locally uniformly on `C`, where `W_(-1)` is not identically zero.  Then `(7)` holds and hence
`sigma_res` has no interior mass.

More generally, it is enough to have such convergence on a complex neighborhood of each real
compact interval.  A common-gauge locally uniform limit of the two parity functions

```text
(g_n W_(n,1),g_n W_(n,-1))->(W_1,W_(-1))                (12)
```

therefore closes the entire interior residual problem and also gives the meromorphic carrier

```text
m_n=-i W_(n,1)/W_(n,-1) -> -i W_1/W_(-1)                (13)
```

away from the limiting poles.

### Proof

Choose a rectangle around a real compact interval whose boundary avoids the discrete zero set of
`W_(-1)`.  Uniform convergence and Rouche's theorem make the number of zeros of
`g_n W_(n,-1)` in that rectangle eventually equal to the finite number for `W_(-1)`.  The gauges
are zero-free, so these are exactly the Suzuki Clark points.  This proves `(7)`.  Equation `(13)`
is ordinary quotient convergence away from zeros of the limiting denominator.

No claim of ordinary entire convergence to Suzuki's meromorphic Corollary 1.6 target is made.
Condition `(12)` is pair convergence before taking the ratio, so zeros and poles are retained
without the malformed entire-to-meromorphic limit.

## Theorem D: endpoint residual is exactly linear Nevanlinna mass `[PROVED HERE]`

Let

```text
K_z(t)=(tz+1)/(t-z)=z+(z^2+1)/(t-z)                     (14)
```

be the Donoghue probability kernel.  It has the same two projective endpoint values:

```text
lim_(t->+infinity) K_z(t)=z,
lim_(t->-infinity) K_z(t)=z.                             (15)
```

Put

```text
alpha=sigma({-pi/2,pi/2}).                              (16)
```

Weak convergence of the compactified probabilities gives locally uniformly on the upper half
plane

```text
m_n(z)=int K_z(t)dnu_n(t)
 ->m(z)=alpha z+int_R K_z(t)dnu_int(t),                  (17)
```

where `nu_int` is the pullback of the interior part of `sigma`.  Thus `alpha` is exactly the
linear coefficient in the Nevanlinna representation of `m`.  Suzuki symmetry makes `sigma` even,
so the endpoint masses are `alpha/2` each.

The kernel in `(14)`, extended by `(15)`, is continuous on the compact projective interval for
each upper-half-plane `z`; it is uniformly bounded when `z` ranges over a compact subset of that
half-plane.  Weak convergence proves `(17)` and local boundedness upgrades it to locally uniform
convergence.

Combining Theorems B--D gives the exact closure theorem:

```text
common-gauge entire-pair normality
  + zero linear coefficient of the limiting Herglotz function
  => sigma_res=0 and sum_k p_k=1.                        (18)
```

The first hypothesis prevents label condensation on every bounded physical window.  The second
prevents physical escape.  They address disjoint mechanisms and neither can replace the other.

## Complete fixed-lattice rigidity `[PROVED HERE]`

For two finite-aperture Suzuki carriers, equality of

```text
U_1(y_k)=U_2(y_k),
U_1'(y_k)=U_2'(y_k)             for every k in Z         (19)
```

implies equality of the entire carriers, not only their even spectra.  Indeed `(19)` and the
parent holography theorem give identical Donoghue probabilities.  The Donoghue integral gives
`m_1=m_2`; Cayley inversion gives `Theta_1=Theta_2`; normalized phase lifting then gives
`phi_1=phi_2` and `U_1=U_2`.  Consequently the fixed-lattice first jet is a complete invariant of
all self-adjoint-extension divisors.

## What this changes at the RH frontier

Generic compactness, residue bookkeeping, and the meaning of residual mass are now closed.  A
source proof no longer needs to control moving atoms individually.  It must prove exactly:

```text
1. common-gauge entire normality of Suzuki's parity pair,
2. zero linear coefficient of its cofinal Donoghue limit,
3. identification of the limiting meromorphic ratio with the Xi/de Branges carrier. (20)
```

Items 1--2 force the fixed-label probability to survive with total mass one.  Item 3 is then a
single meromorphic-function identity; by complete fixed-lattice rigidity it identifies every
extension divisor at once.

This theorem does not prove `(20)`, does not select the cofinal shift, and does not prove RH.  It
removes the last ambiguity about which topology and which loss mechanisms a source theorem must
control.

## Hostile audit

1. **No false derivative convergence.** Formula `(4)` uses separately extracted masses `p_k`.
2. **No count/mass confusion.** Bounded local zero count is a sufficient structural condition;
   it is not claimed necessary when extra labels have vanishing total mass.
3. **No malformed target convergence.** Entire convergence is imposed on a common-gauge pair;
   its quotient may have poles.
4. **No hidden tightness.** Pair normality kills only interior residual.  Endpoint mass is retained
   explicitly as `alpha z`.
5. **No hidden RH.** All finite carriers are Suzuki's unconditional shifted positive models.
6. **Sharpness.** Free clocks violate local count boundedness and create uniform interior residual;
   the Cayley ground edge has bounded interior count but creates endpoint linear mass.

## Literature and priority audit

Rouche/Hurwitz zero-count stability, Nevanlinna linear mass, and Clark measures are classical and
not claimed as new.  Suzuki does not compactify the inverse phase, define the fixed-label residual,
identify it with escaped-label overcrowding, or state the two-condition closure `(18)`.  Targeted
search of Suzuki's paper, the cited meromorphic-inner literature, and this repository found no
source-specific theorem of this form.  Candidate novelty is the exact synthesis `(4)`--`(20)`;
specialist priority review remains required.

## Lean status

Two dependency-closed pieces are formalized unconditionally.

**Theorem D endpoint connector** — `SuzukiCompactifiedPhaseProfile.lean`:
`tendsto_suzukiDonoghueKernel_atTop`, `tendsto_suzukiDonoghueKernel_atBot`, the two projective
endpoint limits `(15)`.

**Theorem B order engine** —
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiResidualOvercrowding.lean`.  The whole content of
Theorem B is order combinatorics of the label family, and that is what is formalized:

- `label_zero_neg`: the reflection pairing `u (1 - k) = -u k` puts the origin strictly between the
  two central labels.
- `abs_label_le_of_between`: strict monotonicity forces the labels to leave a symmetric window in
  order — if a positive index lands inside the window, so does every intervening central index.
  This is the "enlarged interval" step of the paper proof.
- `le_card_labelWindow`, `abs_le_card_labelWindow`: consequently the number of labels inside a
  window bounds the *index* of every label inside it.  This is the sharp form of `(7) => (8)`.
- `escapedTail_eq_zero`, `escapedTail_eq_zero_uniform`: a weight supported inside a fixed physical
  window is fed only by that uniformly finite label head, so every escaped-label tail term with
  index beyond the count vanishes identically — the interior part of `(4)` is zero, uniformly over
  a family whose window counts are bounded by one integer.

**Theorem A bookkeeping** — same module.  The proof of `(4)`-`(5)` needs no measure theory beyond
its own input: weak convergence enters only as convergence of the tested totals, and the head is a
finite sum.

- `labelHead`, `labelHead_mono`: the finite label head and its monotonicity in the cutoff for
  nonnegative data, which is the monotone-convergence step of the paper proof.
- `tendsto_escapedTail`: equation `(5)` — for a fixed cutoff the escaped-label tail converges,
  because the total converges by weak convergence and the head converges coordinatewise.
- `tendsto_escapedTail_atTop`: equation `(4)` — letting the cutoff grow, the tails converge to the
  residual `Sinf - L`, the difference between the total limit and the labelled limit.
- `hasSum_eq_labelHead`: a summable family whose weight vanishes beyond a cutoff is its own head.

**Theorems A and B combined** — `residual_eq_zero_of_uniform_count`: if the window label counts of
the whole family are bounded by one integer and the weight is supported in that window, then
`Sinf = L`.  The residual vanishes identically on the interior.  This is the closed form of
`(7) => (8)`, assembled from the order engine and the tail bookkeeping.

Targeted build green; axiom audit `[propext, Classical.choice, Quot.sound]` for every declaration
above.

**Theorem C glue** — same module.  Rouche's count stability is classical and is *not* in mathlib,
which carries no argument principle; everything in Theorem C that is not that classical step is
formalized:

- `setOf_gauge_mul_eq_zero`: zero-free gauges do not move the Clark points, so the zeros counted
  after gauging are exactly the Suzuki Clark points.
- `exists_uniform_bound_of_eventually`: Rouche delivers count stability only for *late* members of
  an aperture family; the finitely many early members are absorbed into the bound.  This is what
  turns the eventual conclusion into the uniform hypothesis `(7)`.
- `residual_eq_zero_of_eventually_count`: the closed chain — eventual count stability in one window
  gives the uniform bound, which through the order engine and the tail bookkeeping gives the
  vanishing of the interior residual.

**Equation `(13)`, the meromorphic carrier** —
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCommonGaugeQuotient.lean`.  The proof of Theorem C calls
`(13)` "ordinary quotient convergence away from zeros of the limiting denominator", and it had no
declaration.  The content is that the *common* gauge cancels in the ratio because it is zero-free:

- `quotient_eq_gauged_quotient`: the ungauged ratio equals the gauged one, for any zero-free gauge.
- `tendsto_commonGauge_quotient`: if a zero-free gauge makes both parity functions converge, the
  ungauged quotient converges to the quotient of the limits.
- `tendsto_suzukiMeromorphicCarrier`, `tendsto_suzukiMeromorphicCarrier_at`: **`(13)`** itself, the
  carrier `-i W_1 / W_(-1)` with the `-i` factor, in value and pointwise-in-`z` form.

Note what is *not* needed: the gauge need not converge, and no relation between the two gauged
limits is used.  Only zero-freeness.  This is exactly why `(12)` is stated as pair convergence
before the ratio is taken.

**Discharge of the abstraction** —
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCompactifiedLabelOvercrowding.lean`.  The theorems above
are order combinatorics of an abstract label family; this module proves that Suzuki's own
compactified inverse-phase labels

`u k = arctan (phi^(-1) (pi + (2k - 1) pi))`

are exactly such a family, so every conclusion applies to the concrete objects and not only to an
abstraction:

- `suzukiEvenPhaseLattice_strictMono`, `suzukiEvenPhaseLattice_one_sub`: the even phase lattice
  `y_k = (2k - 1) pi` is strictly increasing and odd under `k |-> 1 - k`.
- `suzukiCompactifiedLabel_strictMono`, `suzukiCompactifiedLabel_reflect`: hence the compactified
  labels are strictly increasing in the index and reflection-paired, using the corpus's
  `suzukiCompactifiedInversePhase_strictMono` and `suzukiCompactifiedInversePhase_neg`.
- `suzuki_abs_le_card_labelWindow`, `suzuki_escapedTail_eq_zero`,
  `suzuki_residual_eq_zero_of_eventually_count`: the label-head bound, the identical vanishing of
  the interior escaped-label tail, and Theorem C's closed chain, all stated on the concrete Suzuki
  family.

**Theorem D analytic input** —
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiDonoghueKernelUniformBound.lean`.  The proof of `(17)`
names two properties of the Donoghue kernel as its hypotheses; both are now formal:

- `suzukiDonoghueDenom_ne_zero`, `le_norm_suzukiDonoghueDenom`: above the real axis the denominator
  never vanishes and is at least the imaginary height.
- `continuous_suzukiDonoghueKernel`: for each spectral parameter above the real axis the kernel is
  continuous in the spectral variable, so together with the two already formalized projective
  endpoint limits it is continuous on the compact projective interval.
- `norm_suzukiDonoghueKernel_le`, `norm_suzukiDonoghueKernel_le_of_window`: the kernel size is
  controlled by the imaginary height alone, hence uniformly bounded by `R + (R^2+1)/eta` when the
  parameter has modulus at most `R` and height at least `eta`.  This is the local boundedness that
  upgrades the pointwise weak-convergence transfer to a locally uniform one.

**Real-to-complex bridge for `(17)`** —
`formal/GaloisForLFunctions/HTGeometry/ComplexWeakConvergenceBridge.lean`.  mathlib states weak
convergence against bounded continuous *real-valued* test functions, while a Herglotz transform is
tested against a complex kernel.  The bridge needs nothing from the measures:

- `tendsto_complex_of_re_im`: a complex limit is determined by the limits of its real and imaginary
  parts.
- `tendsto_integral_complex_of_re_im`: consequently, if the real and imaginary parts of an
  integrable complex integrand have convergent integrals then so does the integrand.
- `tendsto_integral_real_of_compact`: on a compact space weak convergence tests every continuous
  real function, because compactness turns it into the bounded continuous function that mathlib's
  weak-convergence theorem consumes.
- `tendsto_integral_complex_of_compact`: hence weak convergence on a compact space tests every
  continuous *complex* function.  This is exactly the form in which a Herglotz transform is tested
  against its kernel, so together with `continuous_suzukiDonoghueKernel` and the two projective
  endpoint limits it gives the convergence `(17)` asserts.

**The kernel in the compactified coordinate** — same module.  The physical point of a compactified
phase `t` is `tan t`, and in that coordinate the kernel is continuous on the whole closed projective
interval:

- `projectiveDonoghueKernel`: the kernel read in the compactified coordinate.
- `continuousOn_projectiveDonoghueKernel`: continuity on the projective interior, since `tan` is
  continuous where the cosine does not vanish.
- `tendsto_projectiveDonoghueKernel_right`, `tendsto_projectiveDonoghueKernel_left`: at the two
  projective endpoints the physical point escapes to `+infinity` and `-infinity` and the kernel
  tends to the same linear Nevanlinna value `z`.  This is `(15)` transported to the compactified
  coordinate, and it is exactly the statement that the kernel extends continuously to the compact
  projective interval.
- `norm_projectiveDonoghueKernel_le_of_window`: the window bound holds in the compactified
  coordinate too, uniformly in it.

**The continuous extension to the closed projective interval** — same module.  The kernel now
exists as a genuinely continuous function on the compact interval, not merely as a function with
matching one-sided limits:

- `projectiveInterval`, `extendedProjectiveKernel`: the closed interval `[-pi/2, pi/2]` and the
  kernel extended to it by its common endpoint value `z`.
- `extendedProjectiveKernel_left`, `extendedProjectiveKernel_right`: the assigned endpoint values.
- `continuousOn_extendedProjectiveKernel`: **the extension is continuous on the whole closed
  interval**.  On the interior it agrees with the compactified kernel; at each endpoint the
  neighbourhood filter splits as the one-sided filter joined with the point itself, the one-sided
  part converges by `(15)`, and the point contributes the assigned value.

- `projectiveKernelMap`: the kernel packaged as a continuous function on the projective interval
  viewed as a compact type.
- `tendsto_integral_extendedProjectiveKernel`: **equation `(17)`** — weak convergence of the
  compactified spectral probabilities transfers to their Herglotz transforms.

**The endpoint mass is the linear Nevanlinna coefficient** —
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiEndpointNevanlinnaMass.lean`.  The convergence in `(17)`
is only half of what `(17)` displays; the other half is the identification of the limit as
`alpha z + int K_z dnu_int`, which is what makes `alpha` *the linear coefficient* and is Theorem
D's actual title claim.  That split is now formal:

- `projectiveEndpointSet`, `projectiveInteriorSet`, and the two facts that they are disjoint and
  exhaust the compact projective interval.
- `integral_extendedProjectiveKernel_split`: because the kernel takes the **same** value `z` at
  both projective endpoints, the transform splits as `nu(endpoints) * z` plus the interior
  transform.  This is `(16)` together with the right-hand side of `(17)`.
- `tendsto_integral_extendedProjectiveKernel_nevanlinna`: `(17)` with its limit written in
  Nevanlinna form, linear coefficient displayed.
- `endpointMass_eq_zero_iff_smul_eq_zero`: zero linear coefficient is equivalent to zero endpoint
  mass — the second hypothesis of the closure theorem `(18)`, the one that rules out endpoint
  residual as opposed to interior overcrowding.
- `projectiveLeft`, `projectiveRight`, `measureReal_projectiveEndpointSet`: the endpoint mass is
  the sum of the two separate endpoint masses.
- `measureReal_endpoint_eq_half`: the card's claim that "Suzuki symmetry makes `sigma` even, so the
  endpoint masses are `alpha/2` each" — an even measure gives the two projective endpoints equal
  mass, hence each is half the linear coefficient.

**The closure theorem `(18)`** — same module.  `(18)` is stated in the paper as a combination of
Theorems B–D and had no declaration of its own; the interior half and the endpoint half were each
formal but were never joined.  They are now:

- `measureReal_interior_add_endpoint`: the interior mass and the endpoint mass exhaust a
  probability measure — the additivity that makes the two mechanisms complementary.
- `suzuki_closure_labelledMass_eq_one`: zero interior residual together with zero endpoint mass
  forces the labelled masses to sum to one, which is `sigma_res = 0` and `sum_k p_k = 1`.
- `suzuki_closure_labelledMass_eq_one_of_linearCoefficient`: the same conclusion stated from the
  vanishing of the linear coefficient itself, which is the form `(18)` uses.

Theorem D is therefore formal end to end: the endpoint limits `(15)`, the continuity and uniform
bound of the kernel, its continuous extension to the compact projective interval, the
weak-convergence transfer `(17)` of the transforms, and the endpoint/interior decomposition that
identifies the endpoint mass as the linear Nevanlinna coefficient.

**Fixed-lattice rigidity** — `SuzukiCompactifiedLabelOvercrowding.lean`.  The chain `(19)` runs
`jets -> Donoghue probability -> m -> Theta -> phi -> U`.  Its first link is the parent holography
theorem; the middle links are function applications, since `Theta` is a function of `m` and `U` a
function of `phi`.  The one link with content is the phase lift, and it is now formal:

- `suzukiCompactifiedInversePhase_injective`: the compactified inverse phase determines the phase.
  Cayley compactification and the fixed centering are both injective, so two carriers with the same
  compactified inverse phase have the same underlying order isomorphism.
- `suzukiCompactifiedLabel_eq_of_phase_eq`: hence equal phases give equal labels at every lattice
  index.

The parent holography step is itself already formal, in
`SuzukiCompactifiedPhaseProfile.lean`:

- Theorem A of the parent card: `suzukiCompactifiedInversePhase_zero` gives `(5)`, the centering
  `U(0) = 0` (and `suzukiCompactifiedInversePhase_zero_of_reflection` derives its anchor from the
  reflection normalization, so no separate assumption is needed);
  `suzukiCompactifiedInversePhase_mem_Ioo` gives the projective range,
  `hasDerivAt_suzukiCompactifiedInversePhase` and `deriv_suzukiCompactifiedInversePhase_mem` give
  the derivative law and bound `(6)`, and `suzukiCompactifiedInversePhase_lipschitz` gives the sharp
  `1/2`-Lipschitz estimate `(7)`.
- Theorem B of the parent card: `suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv` gives
  `p_k = 2 U'(y_k)` of `(13)`, and `hasSum_two_mul_suzukiCompactifiedDeriv_one` gives the total mass
  `(14)`, hence the reconstruction `(15)`.

Verified by reading those declarations rather than by trusting the parent card's gates.

**But the composite `(19)` is not available on the order-isomorphism model, and is false there** —
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFixedLatticeRigidityLimit.lean`.  The links above are
each formal, yet `(19)` itself does not follow from them, because the corpus models a carrier as an
arbitrary `ℝ ≃o ℝ` and for that class the statement is refuted:

- `latticeWobble`, `latticeWobbleIso`: the wobble `x + (1 - cos x) / 2` is an order isomorphism of
  the line that fixes every point of `2 pi ZZ` (the cosine is one there) and has derivative one at
  every such point (the sine vanishes there).
- `not_fixedLatticeJets_determine_carrier`: composing with it gives two carriers that agree in
  value *and* in first derivative at every even phase lattice point and are nevertheless different.

The refutation is not an artefact of dropping the Suzuki reflection normalization
`phi(-x) = 2 pi - phi(x)`.  Replacing the wobble by an **odd** one, `x + sin x (1 + cos x) / 4`,
keeps both carriers inside the normalized class — oddness is exactly what the reflection condition
needs — while it still fixes every *odd* multiple of `pi`, which is precisely the even phase
lattice, and still has derivative one there:

- `oddWobble`, `oddWobble_neg`, `oddWobble_evenPhaseLattice`: the odd wobble, its oddness, and its
  fixing of the lattice.
- `orderIso_symm_reflection`: a carrier obeys the reflection normalization as soon as its inverse
  anticommutes with reflection about `pi`.
- `not_fixedLatticeJets_determine_reflectionNormalized_carrier`: two carriers **both obeying the
  reflection normalization**, agreeing in value and first derivative at every lattice point, and
  still different.

**The two middle links are now genuine objects** —
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiDonoghueHerglotzTransform.lean`.  The chain calls
`sigma -> m` and `m -> Theta` "function applications", but `m` and `Theta` did not exist in the
corpus as definitions, so there was nothing to apply.  They do now, with the properties that make
them what they are:

- `im_suzukiDonoghueKernel`: the exact imaginary part,
  `Im K_z(t) = Im z (t^2 + 1) / |t - z|^2`, read through the Möbius form.  This is the reason the
  Donoghue kernel is a *probability* kernel.
- `im_suzukiDonoghueKernel_pos`, `im_extendedProjectiveKernel_pos`: the kernel is strictly in the
  upper half plane at every point of the closed projective interval, endpoints included, where it
  equals the spectral parameter itself.
- `donoghueTransform`, `im_donoghueTransform_pos`: **the Donoghue transform of a compactified
  spectral probability is a Herglotz function** — the kernel has a positive continuous minimum on
  the compact interval and the integral against a probability measure inherits it.
- `cayleyOfHerglotz`, `normSq_cayleyOfHerglotz_lt_one`,
  `normSq_cayleyOfHerglotz_donoghueTransform_lt_one`: **the Cayley transform of a Herglotz value is
  Schur**, because a point strictly above the real axis is strictly closer to `i` than to `-i`.
  This is the inner function `Theta`, built from the spectral probability alone.
- `donoghueTransform_congr`, `cayleyOfHerglotz_donoghueTransform_congr`: the links themselves,
  composed.

**The last link, the normalized phase lift, is now formal too** —
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCayleyPhaseLift.lean`.  On the real boundary the Cayley
transform of a real Herglotz value lies on the unit circle and its argument is the explicit lift
`m |-> pi + 2 arctan m`:

- `cayleyPhaseLift`, `cayleyOfHerglotz_ofReal`: the identity
  `(m - i)/(m + i) = exp (i (pi + 2 arctan m))`, obtained by writing `m = tan u`, whose real part
  is `-cos 2u` and imaginary part `-sin 2u`.
- `normSq_cayleyOfHerglotz_ofReal`: the boundary values lie on the unit circle.
- `cayleyPhaseLift_mem_Ioo`: the lift takes values in one full turn, which is the normalization.
- `strictMono_cayleyPhaseLift`, `cayleyPhaseLift_injective`: the lift is strictly increasing, hence
  injective — `arctan` is.
- `eq_of_cayleyOfHerglotz_ofReal_eq`, `eq_of_exp_cayleyPhaseLift_eq`: **the link is an injection**.
  Cross-multiplying, two equal boundary Cayley values differ by `2 i (m_1 - m_2)`.

**Phase lifting is unique, so the inner function *does* determine the phase** —
`formal/GaloisForLFunctions/HTGeometry/ContinuousPhaseLiftUniqueness.lean`.  The scalar link above
recovers the phase from one boundary value; the global link recovers the whole phase function:

- `sub_mem_two_pi_int_of_exp_eq`: two continuous lifts of the same phase differ pointwise by a
  multiple of `2 pi`.
- `eq_of_exp_eq_of_eq_at`: **the lift is unique once normalized at a single point.**  Were the
  difference to move, the intermediate value theorem would force it through `pi`, which is not a
  multiple of `2 pi`.
- `phase_zero_of_reflection`: the Suzuki reflection normalization `phi(-x) = 2 pi - phi(x)` pins
  `phi 0 = pi` by itself, so it *supplies* the base point the uniqueness needs.
- `eq_of_exp_eq_of_reflection`: hence a reflection-normalized continuous phase is determined by its
  inner function.

This is the exact converse face of the refutation below.  The **inner function** determines the
phase; the **lattice jets** do not.  What separates them is precisely whether the jets determine the
inner function — that is the Clark property of the carrier, i.e. that its Herglotz function is the
Donoghue transform of its own jet measure.  It is a genuine analytic hypothesis and not a
consequence of the order structure, which is exactly what the counterexample shows.

**`(19)` assembled** — `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFixedLatticeRigidity.lean`.  With
every link formal, the chain composes:

- `phase_eq_of_boundaryHerglotz_eq`: the boundary Herglotz function determines the normalized phase.
- `boundaryHerglotz_eq_of_phase_eq`: and conversely, since the Cayley transform is injective on real
  boundary values.
- `phase_eq_iff_boundaryHerglotz_eq`: so the correspondence is a bijection.
- `suzuki_fixedLattice_rigidity_of_clark`: **`(19)` for any carrier class with a Clark
  reconstruction.**  A carrier has the Clark property when its own boundary Herglotz function is the
  reconstruction of its own lattice jets; for such carriers equal jets force equal phases.

The Clark hypothesis is named, and it is exactly the analytic content the order structure cannot
supply.  It is not removable: `not_fixedLatticeJets_determine_reflectionNormalized_carrier` refutes
`(19)` without it, even for reflection-normalized carriers.

**The reconstruction, built for a finite aperture** —
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiClarkFiniteReconstruction.lean`.  For the finite-aperture
case this card names, the Clark reconstruction is explicit — the Donoghue transform of a finite
atomic spectral measure — so no abstract parameter remains:

- `donoghueRealKernel`, `suzukiDonoghueKernel_ofReal`: the kernel at a real spectral parameter off
  the atom is real.
- `clarkFiniteHerglotz`, `im_clarkFiniteHerglotz_pos`: **the transform of a finite atomic measure is
  a Herglotz function**, since every kernel value lies strictly above the real axis and the masses
  are positive.
- `clarkFiniteReconstruction`, `clarkFiniteHerglotz_ofReal`: its boundary function, real off the
  atoms.
- `suzuki_fixedLattice_rigidity_finiteAperture`: **`(19)` with the reconstruction supplied** — two
  reflection-normalized continuous phases whose boundary Herglotz functions are the Donoghue
  transforms of their own finite jet data, with equal jets, are equal.
- `exists_clarkFinite_carrier`: the hypothesis class is inhabited, so the theorem is not vacuous.
  The witness is the empty aperture with constant phase `pi`.

**The phase equation must be required only off the atoms.**  Demanding it at every real point is
unsatisfiable for any carrier that carries atoms, because the boundary Herglotz function has a pole
at each one — which is why the only witness above is the atomless case.  The usable form asks for it
off the atoms:

- `dense_compl_of_finite`: the complement of a finite subset of the line is dense.
- `phase_eq_of_boundaryHerglotz_eq_off`: both exponentials are continuous, so agreement on a dense
  set is agreement everywhere; rigidity then follows as before.
- `suzuki_fixedLattice_rigidity_finiteAperture_offAtoms`: **`(19)` for the finite-aperture Clark
  class in the form a carrier with atoms can actually satisfy.**

**Oddness of the boundary Herglotz function *is* the reflection normalization** — same module.  The
normalization conjugates the inner function, and conjugating a boundary Cayley value is the same as
negating its Herglotz value:

- `cayleyOfHerglotz_neg_mul_self`: reflecting the Herglotz value inverts the boundary Cayley value.
- `exp_reflection_of_odd`: hence, for an odd boundary Herglotz function, the reflected phase lifts
  the Cayley value of the reflected Herglotz value.

This explains the shape a Suzuki spectral configuration must take, and the obstruction is now a
theorem rather than a remark:

- `cayleyOfHerglotz_sub_one`, `norm_cayleyOfHerglotz_sub_one_le`,
  `tendsto_cayleyOfHerglotz_of_abs_atTop`: as the boundary Herglotz value escapes to infinity the
  Cayley value tends to `1`, with the explicit bound `2/|m|`.
- `not_atom_at_zero_of_reflectionNormalized`: **a reflection-normalized carrier has no atom at the
  origin.**  At an atom the Cayley value tends to `1`, but the normalization pins the phase at the
  origin to `pi`, whose Cayley value is `-1`.

So the spectral configuration must straddle the origin.  That a symmetric configuration then works
is also proved, in `SuzukiClarkFiniteReconstruction.lean`:

- `donoghueRealKernel_neg`: reflecting both the atom and the argument negates the kernel.
- `clarkFiniteReconstruction_odd`: **any spectral configuration carrying an involution that
  reflects the atoms and preserves the masses has an odd boundary Herglotz function** — hence, by
  `exp_reflection_of_odd`, one compatible with the reflection normalization.
- `clarkFiniteReconstruction_symmetricPair_odd`: the smallest admissible case, a symmetric pair at
  `+-a` with equal masses.

The two results bracket the admissible configurations: the origin cannot carry an atom, and
reflection symmetry of the atoms is sufficient for the normalization.

**A non-constant carrier exists** — `exists_nonconstant_reflectionNormalized_carrier`.  The carrier
whose spectral mass sits entirely at the two projective endpoints has boundary Herglotz function
`m(t) = t`, odd, with reflection-normalized continuous phase `pi + 2 arctan t` — the normalized
phase lift itself.  Its phase is genuinely non-constant, so the rigidity hypotheses are satisfied
non-trivially and not only by the atomless degenerate case.

**The countable lattice** — `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiDonoghueSeriesTransform.lean`.
The Suzuki lattice is indexed by `ZZ`, so the transform is a series.  It converges, and absolutely,
because the Donoghue kernel is bounded *uniformly in the spectral variable*
(`norm_suzukiDonoghueKernel_le`, bound `‖z‖ + (‖z‖^2+1)/Im z`), so the series is dominated termwise
by the masses times one constant:

- `donoghueSeriesTransform`, `summable_donoghueSeries`: the countable transform and its absolute
  convergence, for any summable nonnegative mass family.
- `im_donoghueSeriesTransform_pos`: **the countable transform is a Herglotz function** — every term
  has positive imaginary part and at least one mass is positive.
- `normSq_cayleyOfHerglotz_donoghueSeriesTransform_lt_one`: hence the inner function of the full
  lattice exists and is Schur.
- `donoghueSeriesTransform_congr`: it depends on nothing but the jets, so it is a Clark
  reconstruction for the whole lattice.

**The countable boundary reconstruction** —
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiClarkSeriesReconstruction.lean`.  On the real axis the
imaginary-height bound degenerates, so the boundary series needs a different input: separation of
the atoms from the point.  For a Suzuki configuration that is automatic, since the physical points
`x_k = tan u_k` escape to infinity and have no finite accumulation point.

- `clarkSeriesReconstruction`, `summable_clarkSeries`: the boundary reconstruction and its absolute
  convergence, with separation replacing the imaginary height as the uniform bound.
- `clarkSeriesReconstruction_odd`: a symmetric countable configuration has an odd boundary
  reconstruction, exactly as in the finite case.
- `dense_compl_of_countable`: the complement of a countable subset of the line is dense — the atom
  set of a `ZZ`-indexed lattice is countable, not finite.
- `suzuki_fixedLattice_rigidity_countable_offAtoms`: **`(19)` for the countable Clark class**, with
  the phase equation required only off the atoms.

So `(19)` is proved for the full `ZZ`-indexed lattice, not only for finite apertures.  What remains
is the winding lift: constructing, for a configuration with interior atoms, the continuous
reflection-normalized phase that lifts the Cayley argument across each pole.
So no argument phrased on `ℝ ≃o ℝ` can prove `(19)`.  The rigidity theorem is a statement about the
*analytic* Suzuki carrier class, where the Donoghue measure reconstructs the Herglotz function and
hence the phase; the lattice jets determine the carrier only within that class.  Formalizing `(19)`
therefore requires carrying the analytic structure — a Hermite--Biehler pair, or the Herglotz
representation — as an explicit hypothesis.  That construction is not present in the corpus and is
the one genuinely open Lean item on this card.

**Uniform zero-count bound** —
`formal/GaloisForLFunctions/HTGeometry/UniformZeroCountBound.lean`.  The count-stability input of
Theorem C does **not** need the argument principle: mathlib carries Jensen's inequality
`AnalyticOnNhd.sum_divisor_le`, which bounds the zero count of one analytic function in a ball by
`log (M / ‖f c‖) / log (R / r)`.  `sum_divisor_le_of_uniform_bounds` makes that bound uniform over a
family: if the family is uniformly bounded above by `M` on the sphere and uniformly bounded below by
`m > 0` at the centre, every member has zero count at most `log (M / m) / log (R / r)` in the
smaller ball.

That "eventually" step is itself formalized in the same module, so the chain is closed end to end:

- `sum_divisor_le_of_bounds`: single-function form of the Jensen bound.
- `eventually_half_norm_le`: nonvanishing at the centre survives pointwise convergence, giving the
  lower bound `m = ‖F c‖ / 2`.
- `eventually_norm_le_of_tendstoUniformlyOn`: a uniform limit is uniformly bounded up to one unit,
  giving the upper bound `M = M0 + 1` on the sphere.
- `eventually_sum_divisor_le`: consequently a family converging uniformly on the sphere and
  pointwise at the centre, with nonvanishing limit there, has eventually bounded zero count in the
  smaller ball.

Feeding that into the already formalized `exists_uniform_bound_of_eventually` gives hypothesis `(7)`
for the whole family — with no Rouche theorem and no contour integral.

### Superseded build plan for a Rouche step

Superseded by the Jensen route above, and retained only as a record of the alternative.  mathlib
carries no Rouche or Hurwitz theorem under those names, but it *does* carry Jensen's formula and
inequality in `Mathlib/Analysis/Complex/JensenFormula.lean` together with the meromorphic divisor
API, which is what the Jensen route uses.  The contour route would be:

1. Zero counting for a disc: for `f` holomorphic on a neighbourhood of `closedBall c r` and
   nonvanishing on `sphere c r`, prove `(2*pi*I)^(-1) * (contour integral of f'/f) = sum of orders
   of the zeros inside.  Ingredients present in mathlib: `circleIntegral`,
   `circleIntegral.integral_sub_inv_of_mem_ball` for the model factor `(z - w)^(-1)`, Cauchy's
   theorem in the form `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`, and
   `AnalyticAt.order` with the local factorization of an analytic function at a zero.
2. Continuity of the count: with `F_n -> F` locally uniformly, `F_n' -> F'` locally uniformly by
   `TendstoLocallyUniformlyOn.deriv`, and `|F| >= delta > 0` on the circle, the quotients
   `F_n'/F_n` converge uniformly on the circle, so the contour integrals converge; being integers
   they are eventually equal.  This is Rouche in the form Theorem C uses.
3. Feed the eventual equality into `exists_uniform_bound_of_eventually`, already formalized, to
   obtain hypothesis `(7)` for the whole family.  Each of those needs either the
argument principle or the concrete Suzuki aperture family represented in Lean.  Theorem A is
formalized with its weak-convergence input as a hypothesis on the tested totals, which is exactly
the form the paper proof uses.

Note on the rigidity chain: after the parent holography step supplies equal Donoghue probabilities,
the remaining links `m -> Theta -> phi -> U` are function applications, so the mathematical content
of `(19)` sits entirely in that parent step and not in this card.

## Gates

- [x] exact escaped-label tail formula proved
- [x] interior residual/overcrowding alternative proved
- [x] entire-pair normality closure proved
- [x] endpoint residual/linear-mass identity proved
- [x] complete fixed-lattice carrier rigidity proved
- [x] hostile audit closed
- [x] Lean endpoint connector
- [ ] source common-gauge pair normality
- [ ] source zero-linear-mass theorem
- [ ] Xi/de Branges ratio identification
- [ ] RH

## Log

- 2026-07-21 — derived immediately after compactified inverse-phase holography exposed the residual
  as the only cofinal defect; complete paper proof and hostile audit closed.
- 2026-07-21 — both projective Donoghue-kernel endpoint limits formalized unconditionally in
  `SuzukiCompactifiedPhaseProfile.lean`; exact build and axiom audit passed.
- 2026-08-01 — Theorem B's order engine formalized unconditionally: the reflection-paired strictly
  monotone label family, the order-transfer step, the index bound by the window label count, and
  the resulting identical vanishing of the interior escaped-label tail.
- 2026-08-01 — Theorem A formalized as well, and combined with the order engine into the closed
  interior-vanishing statement `residual_eq_zero_of_uniform_count`.
- 2026-08-01 — Theorem C's non-classical glue formalized: gauge-invariance of the Clark zero set and
  the eventual-to-uniform count upgrade, closing the chain from Rouche's eventual count stability to
  the vanishing of the interior residual.
- 2026-08-01 — abstraction discharged: Suzuki's compactified inverse-phase labels are proved to be a
  strictly increasing reflection-paired family, so the residual theorems now hold of the concrete
  objects rather than of an abstract label family.
- 2026-08-01 — Theorem D's two named analytic inputs formalized: continuity of the Donoghue kernel
  in the spectral variable above the real axis, and its uniform bound by the imaginary height on a
  compact spectral window.
- 2026-08-01 — real-to-complex weak-convergence bridge formalized, and the missing Rouche step
  reduced to a written build plan with its mathlib entry points identified.
- 2026-08-01 — the Rouche gap is closed by a different route: mathlib's Jensen inequality
  `AnalyticOnNhd.sum_divisor_le` bounds zero counts directly, and `sum_divisor_le_of_uniform_bounds`
  makes the bound uniform over a family.  No argument principle is needed.
- 2026-08-01 — count stability closed end to end: the Jensen bound's two hypotheses are produced
  from pointwise convergence at the centre and uniform convergence on the sphere, so Theorem C's
  count-stability input is now fully formal.
- 2026-08-01 — weak convergence on a compact space formalized against continuous real and complex
  test functions, completing the abstract half of `(17)`.  The only remaining analytic step is the
  construction of the projective interval as a measure space carrying the compactified
  probabilities.
- 2026-08-01 — the Donoghue kernel is formalized in the compactified coordinate: continuous on the
  projective interior, with both endpoint limits equal to the linear Nevanlinna value, hence
  continuous on the compact projective interval, and bounded there by the window constant.
- 2026-08-01 — the Donoghue kernel is now a continuous function on the *closed* projective interval,
  proved by splitting each endpoint neighbourhood into its one-sided part and the point itself.
  Only the measure-packaging step of `(17)` remains.
- 2026-08-01 — equation `(17)` formalized: the kernel is packaged as a continuous function on the
  compact projective interval and weak convergence of the compactified probabilities transfers to
  the Herglotz transforms.  Theorems A-D are now formal.
- 2026-08-01 — fixed-lattice rigidity's one contentful link formalized: the compactified inverse
  phase determines the phase, hence the labels.  Every theorem proved on this card is now formal
  except the parent holography step, which belongs to another card.
- 2026-08-01 — checked the parent holography step directly: Theorems A and B of
  `suzuki-compactified-inverse-phase-lattice-holography.md` are already formalized in
  `SuzukiCompactifiedPhaseProfile.lean`, so the rigidity chain of this card has no unformalized
  link.  No new Lean was written for it; duplicating those proofs would have been waste.
- 2026-08-01 — Theorem D's endpoint/interior decomposition formalized
  (`integral_extendedProjectiveKernel_split`), in
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiEndpointNevanlinnaMass.lean`.  Equation `(17)` displays
  both a convergence and an identification of the limit as `alpha z + int K_z dnu_int`; only the
  convergence had a declaration, so the card's "Theorem D is formal end to end" was overstated —
  the step that actually earns the title "endpoint residual is exactly linear Nevanlinna mass" was
  missing.  The split follows from the kernel taking the *same* value at both projective endpoints,
  so the endpoint set contributes only a multiple of `z`.  Also added
  `tendsto_integral_extendedProjectiveKernel_nevanlinna` and
  `endpointMass_eq_zero_iff_smul_eq_zero`, the second hypothesis of `(18)`.  Targeted build green,
  axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the closure theorem `(18)` formalized (`suzuki_closure_labelledMass_eq_one` and its
  linear-coefficient form).  `(18)` is introduced in the paper as "combining Theorems B--D", and
  that phrasing hid the gap: the interior half and the endpoint half each had declarations, but
  nothing joined them, so the conclusion `sigma_res = 0 and sum_k p_k = 1` was never stated in
  Lean.  The join is measure additivity on the compact projective interval
  (`measureReal_interior_add_endpoint`).  Also formalized the card's evenness claim, that each
  endpoint carries `alpha/2` (`measureReal_endpoint_eq_half`).  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — fixed-lattice rigidity `(19)`: the card claimed "the chain has no unformalized link
  left", but the composite does not follow from its links, and on the corpus's carrier model it is
  false.  `not_fixedLatticeJets_determine_carrier` refutes it for `ℝ ≃o ℝ` with the explicit wobble
  `x + (1 - cos x)/2`, which fixes every lattice point and has derivative one there, so lattice
  jets cannot see it.  `(19)` is therefore a theorem about the analytic carrier class only, and
  formalizing it needs the Hermite--Biehler / Herglotz structure as a hypothesis — the one
  genuinely open Lean item on this card.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the `(19)` refutation strengthened to the normalized class
  (`not_fixedLatticeJets_determine_reflectionNormalized_carrier`).  The first counterexample used
  carriers that violate the Suzuki reflection normalization `phi(-x) = 2 pi - phi(x)`, so it was
  open to the objection that it refutes `(19)` only outside the intended class.  It does not: the
  odd wobble `x + sin x (1 + cos x)/4` is odd — which is exactly what the reflection condition
  requires — and fixes every odd multiple of `pi`, i.e. the even phase lattice itself, with
  derivative one.  Both witnesses now obey the normalization.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — built the rigidity chain's two middle objects, which the card described as "function
  applications" but which had no definitions in the corpus:
  `donoghueTransform` with `im_donoghueTransform_pos` (the Donoghue transform of a compactified
  spectral probability is Herglotz) and `cayleyOfHerglotz` with
  `normSq_cayleyOfHerglotz_donoghueTransform_lt_one` (its Cayley transform is Schur).  The
  mathematical core is the exact imaginary part `Im K_z(t) = Im z (t^2+1)/|t-z|^2`
  (`im_suzukiDonoghueKernel`), which is why the Donoghue kernel is a probability kernel.  With
  these, the only link of `(19)` still missing is the normalized phase lift `Theta -> phi`; the
  refutation above shows that link cannot come from the order structure.  Targeted build green,
  axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the normalized phase lift `Theta -> phi` formalized
  (`cayleyOfHerglotz_ofReal`, `cayleyPhaseLift_injective`, `eq_of_cayleyOfHerglotz_ofReal_eq`).
  The lift is explicit: `m |-> pi + 2 arctan m`, with
  `(m - i)/(m + i) = exp (i (pi + 2 arctan m))` on the real boundary.  Every scalar link of the
  chain `sigma -> m -> Theta -> phi` is now a formal injection.  What `(19)` still lacks is
  therefore not a link but the carrier *class*: the chain constrains a carrier only through
  countably much boundary data, and the reflection-normalized counterexample shows an arbitrary
  order isomorphism is not determined by it.  Closing `(19)` requires the Hermite--Biehler pair, for
  which the boundary phase determines the carrier globally.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — phase-lift uniqueness formalized (`eq_of_exp_eq_of_eq_at`,
  `eq_of_exp_eq_of_reflection`), in
  `formal/GaloisForLFunctions/HTGeometry/ContinuousPhaseLiftUniqueness.lean`.  A continuous lift is
  unique once normalized at one point: a moving difference would have to cross `pi` by the
  intermediate value theorem, and `pi` is not a multiple of `2 pi`.  The Suzuki reflection
  normalization supplies that base point for free, since it forces `phi 0 = pi`
  (`phase_zero_of_reflection`).  This isolates the residue of `(19)` exactly: the inner function
  determines the phase, the lattice jets do not, and the whole gap is whether the jets determine
  the inner function — the carrier's Clark property, an analytic hypothesis.  Targeted build green,
  axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(19)` assembled (`suzuki_fixedLattice_rigidity_of_clark`), plus the bijection
  `phase_eq_iff_boundaryHerglotz_eq` between reflection-normalized continuous phases and boundary
  Herglotz functions.  Rigidity now holds for any carrier class admitting a Clark reconstruction,
  with that reconstruction as the single named hypothesis; the refutation shows it cannot be
  dropped.  The card's residue is therefore one well-posed construction — exhibiting the Clark
  reconstruction for the Hermite--Biehler class — rather than an unexamined chain of five links.
  Targeted build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the Clark reconstruction built for a finite aperture
  (`clarkFiniteHerglotz`, `im_clarkFiniteHerglotz_pos`, `clarkFiniteReconstruction`), giving
  `suzuki_fixedLattice_rigidity_finiteAperture`: `(19)` with no abstract reconstruction parameter
  left.  `exists_clarkFinite_carrier` checks the hypothesis class is inhabited so the theorem is not
  vacuous — the witness is degenerate (empty aperture, constant phase `pi`), since a non-degenerate
  one needs a lift winding across the atoms.  The finite-aperture case of `(19)` is closed; the
  countable lattice still needs summability and boundary analysis of the infinite transform.
  Targeted build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — corrected the finite-aperture rigidity hypothesis.  The earlier form demanded the
  phase equation at *every* real point, which no carrier carrying atoms can satisfy, since the
  boundary Herglotz function has a pole at each atom; that is why its only witness was the atomless
  case.  `suzuki_fixedLattice_rigidity_finiteAperture_offAtoms` requires the equation only off the
  atoms and recovers it everywhere by continuity and density (`dense_compl_of_finite`,
  `phase_eq_of_boundaryHerglotz_eq_off`).  The earlier statement remains true but is near-vacuous;
  this is the usable one.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — proved that oddness of the boundary Herglotz function *is* the reflection
  normalization (`cayleyOfHerglotz_neg_mul_self`, `exp_reflection_of_odd`), and exhibited a
  non-constant reflection-normalized Clark carrier
  (`exists_nonconstant_reflectionNormalized_carrier`): the endpoint-concentrated carrier, with
  `m(t) = t` and phase `pi + 2 arctan t`.  This replaces the degenerate atomless witness and shows
  the rigidity hypotheses hold non-trivially.  The oddness equivalence also explains the shape a
  spectral configuration must have: a single atom at the origin admits no reflection-normalized
  lift, because the normalization would force an additive constant of `pi` where only multiples of
  `2 pi` are available; a symmetric pair does.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the origin-atom obstruction promoted from prose to theorem
  (`not_atom_at_zero_of_reflectionNormalized`): a reflection-normalized carrier can have no atom at
  the origin, because at an atom the Cayley value tends to `1` while the normalization pins the
  phase there to `pi`, whose Cayley value is `-1`.  Supported by the explicit escape bound
  `‖cayley(m) - 1‖ ≤ 2/|m|` (`norm_cayleyOfHerglotz_sub_one_le`,
  `tendsto_cayleyOfHerglotz_of_abs_atTop`).  This is the general form of the single-atom remark: the
  spectral configuration must straddle the origin.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the symmetric-configuration claim promoted from prose to theorem
  (`clarkFiniteReconstruction_odd`): any spectral configuration carrying an involution that reflects
  the atoms and preserves the masses has an odd boundary Herglotz function, hence one compatible
  with the reflection normalization; `clarkFiniteReconstruction_symmetricPair_odd` is the two-atom
  case.  With the origin-atom obstruction this brackets the admissible configurations from both
  sides: the origin cannot carry an atom, and reflection symmetry suffices.  Targeted build green,
  axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the countable Donoghue transform built and shown Herglotz
  (`summable_donoghueSeries`, `im_donoghueSeriesTransform_pos`), removing the finiteness
  restriction from the Clark reconstruction.  The convergence needs no new analysis: the kernel is
  bounded uniformly in the spectral variable, so summable masses dominate the series termwise.  The
  inner function of the full `ZZ`-indexed lattice therefore exists and is Schur.  Remaining on this
  card: the real boundary values of the countable transform off the atoms, and a winding lift for a
  configuration with interior atoms.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the countable boundary reconstruction built
  (`clarkSeriesReconstruction`, `summable_clarkSeries`, `clarkSeriesReconstruction_odd`), giving
  `suzuki_fixedLattice_rigidity_countable_offAtoms`: `(19)` for the full `ZZ`-indexed lattice.  On
  the real axis the imaginary-height bound degenerates, so convergence rests instead on separation
  of the atoms from the evaluation point — automatic for a Suzuki configuration, whose physical
  points escape to infinity.  The atom set is countable rather than finite, so density of its
  complement needed the countable form (`dense_compl_of_countable`).  Remaining: the winding lift
  for a configuration with interior atoms.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — equation `(13)` formalized (`tendsto_suzukiMeromorphicCarrier`).  Re-auditing the
  whole card rather than continuing on `(19)` surfaced it: `(13)` is a displayed equation that the
  Theorem C proof dismisses as "ordinary quotient convergence", so it never received a Lean-status
  bullet.  Its content is that the common gauge cancels in the ratio because it is zero-free —
  notably, the gauge need not converge and no relation between the two gauged limits is used, which
  is precisely why `(12)` is stated as pair convergence before the ratio.  Targeted build green,
  axiom audit `[propext, Classical.choice, Quot.sound]`.

# RH is the inverse limit of strict Xi Schur chambers with atomic carrier condensation

- **ID:** `xi-schur-inverse-limit-atomic-condensation-law`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** EXACT RH-EQUIVALENT BRIDGE / INVERSE-LIMIT CARRIER LAW
- **Lane:** application to RH after the general HT theorem
- **Scientific status:** `[PAPER PROOF COMPLETE; RIESZ--SZEGŐ AND PICK INPUTS NOT YET FORMALIZED] [LIKELY BRIDGE] [NOVELTY UNVERIFIED]`
- **Parents:** `singular-maximal-ht-schur-defect-collapse-law.md`,
  `pick-defect-finite-selector-maximal-ht-phase-law.md`,
  `prime-arch-anti-herglotz-gate.md`
- **Statement:** A fixed normalized Schur germ constructed unconditionally from the centered Xi
  logarithmic derivative satisfies RH exactly when every one of its reduced finite
  Caratheodory--Fejer Pick matrices is positive definite, equivalently when every Schur defect is
  strictly positive. Under these conditions its completed circle carrier is infinite pure point,
  its Szego product is zero, and its canonical positive analytic Bernstein--Szego densities
  concentrate onto the Xi divisor with `L^p` norm tending to infinity for every `p>1`.

## Scope

This card applies a general carrier law to Xi only after that law has been proved for arbitrary
singular Herglotz carriers. It does not derive the required positivity from primes or Gamma data.
The equivalence below is therefore an exact route constraint, not a proof of RH.

## Fixed unconditional normalization

Let

```text
XiC(z)=xi(1/2+i z),
T_Xi(z)=XiC'(z)/XiC(z),
H_Xi(z)=-T_Xi(z),
chi(w)=i(1+w)/(1-w).                                      (1)
```

The point `z=i` corresponds to `s=-1/2`, so it is regular. Functional-equation symmetry gives

```text
b=-i H_Xi(i)=xi'(3/2)/xi(3/2).                            (2)
```

The standard positive theta integral for `xi` is strictly increasing on the real interval
`(1/2,infinity)`, hence

```text
b>0.                                                       (3)
```

Define the meromorphic disk germs

```text
F_Xi(w)=-i H_Xi(chi(w))/b,
f_Xi(w)=[F_Xi(w)-1]/[w(F_Xi(w)+1)].                        (4)
```

Equation `(2)` gives `F_Xi(0)=1`; therefore the second quotient in `(4)` is removable at zero.
All Taylor coefficients in `(4)` are defined unconditionally from the Xi germ.

For each `N`, let

```text
P_N^Xi = the reduced order-N Caratheodory--Fejer Pick matrix of f_Xi,
alpha_N^Xi = the N-th Schur parameter,
delta_N^Xi=1-|alpha_N^Xi|^2.                               (5)
```

Redundant jet functionals are deleted before `P_N^Xi` is formed.

## RH implies strict finite interior `[PROVED HERE]`

Assume RH. The even paired Hadamard product of `XiC` has only real zeros and gives, locally normally
in the upper half-plane,

```text
T_Xi(z)=sum_(gamma>0) m_gamma
  [1/(z-gamma)+1/(z+gamma)].                               (6)
```

Each summand has negative imaginary part. Thus `H_Xi=-T_Xi` is Herglotz on the full upper
half-plane. Equations `(1)--(4)` then make `F_Xi` a normalized Caratheodory function and `f_Xi` a
Schur function.

On the real boundary away from the Xi divisor, `H_Xi` is real, so `F_Xi` has zero real part there.
Consequently `f_Xi` is inner. The Herglotz measure of `F_Xi` is pure point on the Cayley images of
the real Xi zeros, with weights determined by their positive multiplicities and the fixed
normalization. The Xi divisor is infinite, hence this measure has infinite support and `f_Xi` is
not rational inner.

Every `P_N^Xi` is positive semidefinite because `f_Xi` realizes its data. It cannot be singular:
the singular Caratheodory--Fejer problem has a unique rational-inner solution, which would force
the actual germ and then the global Schur function to be rational inner. Therefore

```text
RH implies P_N^Xi>0 and delta_N^Xi>0 for every N.          (7)
```

## Cofinal strict positivity implies RH `[PROVED HERE]`

Assume every `P_N^Xi` is positive definite. In particular, the entire coefficient sequence in
`(4)` satisfies all finite Schur contractivity conditions. The Schur coefficient theorem produces
a Schur function `f` on the whole disk with exactly that Taylor series.

Reconstruct

```text
F(w)=[1+w f(w)]/[1-w f(w)],
H(z)=i b F(chi^(-1)(z)).                                   (8)
```

Then `F` is Caratheodory and `H` is Herglotz on the upper half-plane. Near `z=i`, equations
`(4)` and `(8)` give `H=H_Xi`. The meromorphic identity theorem extends this equality throughout
the upper half-plane. Since `H` is holomorphic there, every apparent upper-half-plane pole of
`H_Xi` is removable; equivalently, `XiC` has no nonreal upper-half-plane zero.

On the centered upper half-strip this gives the anti-Herglotz inequality for the continued
prime--archimedean source. The formal theorem
`continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis` then yields RH.

The standard Schur recursion identifies positive definiteness of all leading reduced Pick matrices
with strict positivity of all successive defects. Combining both directions proves

```text
RH
 iff P_N^Xi is positive definite for every finite N
 iff delta_N^Xi>0 for every finite N.                      (9)
```

No finite matrix is singular on the RH side. The arithmetic carrier lies in the interior of every
finite Schur chamber; orientation is the completed inverse-limit condition.

## Atomic condensation forced by RH `[PROVED HERE VIA GENERAL LAW]`

Under the equivalent conditions `(9)`, the representing circle measure `mu_Xi` is pure point with
infinite support. Its Schur parameters therefore satisfy

```text
delta_N^Xi>0 for every N,
product_(N=0)^infinity delta_N^Xi=0.                       (10)
```

Let `G_N^Xi` be the Toeplitz Gram matrix of `1,z,...,z^N` for `mu_Xi`. It is positive definite at
every finite level, but `(10)` and the Toeplitz determinant factorization give

```text
lambda_min(G_N^Xi)->0,
condition_number(G_N^Xi)->infinity.                        (10a)
```

Indeed, the determinant geometric mean tends to zero, while `trace(G_N^Xi)=N+1` forces the largest
eigenvalue to be at least one. Thus RH requires strict finite positivity without a uniform
coercivity gap.

Let `phi_N` be its degree-`N` orthonormal polynomial and define the Bernstein--Szego measure

```text
d mu_Xi^[N](theta)=d theta/[2 pi |phi_N(e^(i theta))|^2]
                  =rho_N(theta)d theta/(2 pi).             (11)
```

Every finite measure `(11)` has positive real-analytic density, its transform is rational and
differentially algebraic, and it matches the first `N` Schur/Taylor coordinates of the Xi carrier.
Its Gram matrix through degree `N` is exactly `G_N^Xi`, so the canonical rational model already
reproduces the level-`N` loss of coercivity.
Nevertheless

```text
mu_Xi^[N] -> mu_Xi weakly,
F_Xi^[N] -> F_Xi locally uniformly.                        (12)
```

Let `E_Xi` be the Cayley image of the Xi divisor, enlarged by the possible point at infinity. It
is a Lebesgue-null carrier of `mu_Xi`. For every `epsilon>0`, choose an open neighborhood
`U_epsilon` of `E_Xi` with normalized Lebesgue measure below `epsilon`. Portmanteau gives

```text
lim_N integral_(U_epsilon) rho_N d theta/(2 pi)=1.         (13)
```

For every `p>1`,

```text
||rho_N||_(L^p) -> infinity.                               (14)
```

Otherwise a bounded infinite subsequence would have a weakly convergent `L^p` subsequence, and
its measure limit would be absolutely continuous. This contradicts the unique pure-point weak
limit `(12)`.

## Positive constraint on RH routes

Equations `(9)` and `(13)--(14)` give the route law:

> **A source-faithful Schur proof of RH must keep the Xi carrier strictly inside every finite Pick
> chamber while forcing its canonical positive analytic densities to condense onto an infinite
> atomic boundary only cofinally; strict positivity must persist while every uniform coercivity
> gap collapses.**

Thus finite singular interpolation is not the mechanism. Nor can a proof impose a uniform
`L^p`, `p>1`, bound on the canonical densities: such a bound would exclude the carrier required by
RH. Likewise, a uniform lower spectral bound for the canonical Toeplitz Gram sections is
incompatible with `(10a)`. The missing source theorem must control the whole nested family while allowing
precisely this loss of uniform integrability and coercivity.

If a proposed finite-prime source form `Q_N>=cI` is connected to `G_N^Xi` by a congruence
`G_N^Xi=W_N^*Q_NW_N`, the general metric-weld law forces

```text
sigma_min(W_N)->0.                                        (15)
```

Thus a unitary or uniformly invertible prime-to-Schur identification cannot be the missing
mechanism. The formalized `1/log N` prime-clock crossover provides a uniformly coercive normalized
source coordinate, but no zero-preserving theorem currently identifies it with the collapsing
Schur direction. Any successful identification must include the cofinal pinching `(15)` rather
than suppress it.

The graph-saturation companion sharpens `(15)`. Under RH, `mu_Xi` is purely singular, so the raw
analytic-polynomial identification has

```text
closure(Graph(A_(mu_Xi)))=H^2(m) times L^2(mu_Xi).        (16)
```

Its unique compatible positive-triangular repair is the Xi inverse-Cholesky/orthogonal-polynomial
tower `C_N`, with

```text
||C_N||=lambda_min(G_N^Xi)^(-1/2)->infinity.              (17)
```

Therefore an ordinary graph limit loses the entire Xi incidence relation. In the canonical
triangular category, a source proof must construct the divergent OPUC frame itself, or an
equivalent marked rigging, before taking the cofinal closure.

## Parent-theory and novelty attack

1. `[SEARCH]` Schur coefficient positivity, singular Pick uniqueness, Verblunsky recursion,
   Bernstein--Szego approximation, and Szego's product theorem are classical.
2. `[FORMALIZED INPUT]` The repository proves the full source anti-Herglotz/RH equivalence and the
   infinitude of the Xi divisor.
3. `[PROVED HERE]` The fixed normalization `(1)--(4)` makes the Xi Pick matrices, Verblunsky
   parameters, Herglotz measure, and zero divisor parts of one object.
4. `[PROVED HERE]` This yields the exact strict inverse-limit criterion `(9)` and the atomic
   condensation law `(13)--(14)`.
5. `[COMPANION CONSEQUENCE]` The general graph-saturation theorem gives `(16)--(17)` under RH.
6. Preliminary exact searches found no published Xi criterion in these Schur/Verblunsky
   coordinates. Nevertheless `(9)` is structurally a classical positivity reparameterization of
   RH, so it is classified as a likely bridge unless a priority audit shows otherwise.

## Honest significance score

**74/100 candidate; plausible range 62--84.** The formulation is exact and the carrier geometry is
useful, but the RH equivalence is a Schur-coordinate recoding of Herglotz orientation. The genuinely
new candidate remains the general residual singular-HT/transverse-skeleton theorem in the parent
card, not this application.

## Lean status

The source anti-Herglotz/RH equivalence remains the checked Xi anchor.  The circle-side OPUC,
strict finite Schur defect, cofinal defect collapse, exact finite Gram reconstruction, canonical
Bernstein--Szegő probability measures, weak convergence, aperture concentration, rational/DA
finite transforms, and all finite superlinear `L^p` blow-up are now formalized in
`BernsteinSzegoProbabilityApproximation.lean`, `BernsteinSzegoCaratheodoryRational.lean`, and
`SingularSchurDefectCollapse.lean`.  `MomentFiberPickSchurPhase.lean` supplies the Xi-facing
capstone from the explicit source equivalence to the complete double-boundary/condensation package.

Formalization audit (needs-audit pass): the cited RH input is confirmed present and is the RH-facing
anchor — `RHTower.continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis` in
`CCMCompletedPrimeGammaAccretivityCriterion.lean`. The Schur coefficient, OPUC,
Bernstein--Szego, and all finite superlinear `L^p` conclusions are now formalized. The circle-side
F. and M. Riesz input is also discharged unconditionally: `xiSchur_inverseLimit_atomicCondensation`
no longer accepts a Riesz-brothers hypothesis and invokes `singularSchurDefect_doubleBoundary`
directly. The remaining unconditional Stage-3 gate is the source-faithful construction of the
canonical Xi circle probability measure together with the bridge identifying its singularity with
the checked `RHTower` anti-Herglotz/RH criterion; the current capstone still receives that exact
equivalence as a theorem argument.

## Gates

- [x] unconditional Xi disk germ fixed
- [x] basepoint normalization and positivity of `b`
- [x] RH-to-nonrational-inner direction proved
- [x] all-finite-Pick-positivity-to-RH direction proved
- [x] strict Schur-defect equivalence proved
- [x] pure-point carrier and zero Szego product proved under RH
- [x] strict-but-noncoercive Toeplitz/Gram law proved
- [x] uniformly coercive source weld forced to pinch cofinally
- [x] raw Xi graph saturation and divergent triangular repair derived conditionally
- [x] Bernstein--Szego atomic condensation and all-`L^p` blow-up proved
- [x] route consequence stated positively
- [ ] independent specialist proof audit
- [ ] full priority audit
- [x] complete Lean theorem surface from the checked Xi source equivalence

## Log

- 2026-07-12 -- Separated the Xi application from the general HT carrier theorem. Fixed the
  unconditional normalization at `z=i`, proved the strict finite Pick/Schur inverse-limit
  equivalence to RH, and derived atomic condensation of the canonical Bernstein--Szego densities.

## Log — the classical analytic Nevanlinna carrier family is constructed `[PROVED]`

The moment-fibre bottleneck shared by this card and nine others had two halves.  The first is closed.

`formal/GaloisForLFunctions/HTGeometry/NevLeafCauchyMoebius.lean` proves the **Weyl-disc closed
form** unconditionally, for every positive definite normalised moment sequence with bounded kernel
at a point:

```text
(B(z)*tau - D(z)) * integral (x - z)^(-1) d nu_tau  =  -(A(z)*tau - C(z)),
integral (x - z)^(-1) d nu_tau  =  -(A(z)*tau - C(z)) / (B(z)*tau - D(z)).
```

The finite stage `nevTrunc_cauchy_identity` is the quadrature identity multiplied by the common
factor turning the quasi-orthogonal pair into the truncated Nevanlinna entries; the limit uses the
weak convergence of the quadrature levels to the leaf together with the entrywise limits, and the
determinant identity forbids the denominator from vanishing off the real axis.
`NevLeafInfinityCauchyMoebius.lean` does the same at the parameter at infinity, giving
`integral (x - z)^(-1) d nu_infinity = -A(z)/B(z)`.

`formal/GaloisForLFunctions/HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean` therefore builds

```text
analyticNevCarrierFamily h h0b h0 : ClassicalAnalyticNevanlinnaCarrierFamily s
```

in the carrier convention `(a,b,c,d) = (-A, C, B, -D)`, and
`exists_classicalAnalyticNevanlinnaCarrierFamily`.  All endpoints have axioms `propext`,
`Classical.choice`, `Quot.sound`, and the modules are wired into the `HTGeometry` umbrella.

## Log — `MaximalTranslationInputs` is presently uninhabitable `[DISPROVED FIELD]`

`formal/GaloisForLFunctions/HTGeometry/NevanlinnaWeylDiscPole.lean` proves

```text
nevInf_quotient_im_neg : 0 < z.im -> (D(z)/B(z)).im < 0
```

so `MaximalTranslationInputs.upperMap : forall z, 0 < z.im -> 0 < (F.quotient z).im` is **false**
for the constructed family: the pole of the Weyl-disc Möbius map lies strictly below the real axis,
because the map carries the closed upper half-plane into the Weyl disc and the pole to infinity.
The proof writes the imaginary part of the Möbius image as `Q(t)/|B t - D|^2` with `Q` a real
quadratic, notes `Q` vanishes at the pole and is positive on the real axis, and identifies the
coefficient of `Im t` as `Re(A conj D - C conj B)`, which equals `1` on the real axis, is
continuous, and cannot vanish on the connected upper half-plane.

The transversality chain therefore has to be restated with the jet poles in the **lower** half-plane
(or with the abstract lemmas instantiated at the conjugated poles and the conclusion conjugated
back).  Until then the residual maximal-translation phase theorem is vacuous.

## Log — M. Riesz's theorem is now a single named hypothesis `[REDUCTION PROVED]`

`formal/GaloisForLFunctions/HTGeometry/NevanlinnaEntryMinimalType.lean` adds `norm_nevBinf_le` and
`norm_nevCinf_le` to the corpus's existing `norm_nevAinf_le` / `norm_nevDinf_le`, defines

```text
KernelMinimalExponentialType s :=
  forall A > 0, exists C >= 1, forall z n,
    kernelRoot s (monicOrthoC s . z) n <= C * exp (A * |z|)  and the same for secondKindC
```

and proves `hasMinimalExponentialType_nevAinf`, `...nevBinf`, `...nevCinf`, `...nevDinf` from it.
So the `minimalExponentialType` field reduces to that one property.  The recurrence route to it is
closed: the comparison identity is a Volterra equation with Hilbert-Schmidt kernel, whose iterate
bound `|V^m| <= |V|_HS^m / sqrt(m!)` generates `exp(c|z|^2)`, order two rather than order one, and a
small-tail split only improves the constant.  The route that remains is entire-function theoretic
(real zeros with summable reciprocals, then a genus-zero Hadamard product), and Hadamard
factorization is absent from mathlib.


## Log — correction: mathlib already has the Poisson integral formula

The card's remaining unconditional Stage-3 gate is the source-faithful construction of the canonical
Xi circle probability measure, whose analytic parent is the Herglotz representation theorem on the
disc.  A first pass wrote a kernel module for it; that was **withdrawn as a duplicate** once the
search was done properly.  mathlib carries the whole kernel layer and the integral formula:

| mathlib declaration | content |
|---|---|
| `Complex.herglotzRieszKernel c w z` | the Herglotz–Riesz kernel `(z − c + (w − c))/(z − c − (w − c))` |
| `Complex.poissonKernel c w z`, `poissonKernel_eq_re_herglotzRieszKernel` | the Poisson kernel and its identification with the real part of the Herglotz–Riesz kernel |
| `re_herglotzRieszKernel_le`, `le_re_herglotzRieszKernel` | two-sided bounds on the boundary sphere, hence positivity inside |
| `DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul`, `…_poissonKernel_smul` | **the Poisson integral formula** for holomorphic functions continuous up to the boundary |
| `HarmonicOnNhd.circleAverage_poissonKernel_smul`, `HarmonicContOnCl.…` | the same for harmonic functions |
| `Mathlib/Analysis/Complex/Harmonic/{Analytic,MeanValue,Liouville,Poisson}.lean` | the surrounding harmonic-function layer |

So the representation theorem is much closer than the earlier note claimed.  What genuinely remains
is only the *boundary limit*: for each `r < 1` the formula already represents `Re F` inside the disc
against the probability measure with density `Re F(r·)` on the circle (a probability measure by the
mean value property, since `Re F(0) = 1`); the missing step is weak-\* compactness of that family as
`r → 1` and the identification of the limit, followed by the card's own Xi bridge — the germ
`(1)`–`(4)`, the pure-point structure of the Herglotz measure of `F_Xi` under RH, and its
singularity, which `singularSchurDefect_doubleBoundary` then converts into the condensation package.

## Log — the dilated Poisson representation `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/HerglotzDiscDilation.lean` (wired, axiom-clean), built
directly on mathlib's Poisson layer and adding nothing mathlib already has:

- **`diffContOnCl_dilate`** — for `0 < r < 1`, `z ↦ F(r z)` is holomorphic on a neighbourhood of the
  closed unit disc whenever `F` is holomorphic on the open disc; the dilation maps
  `ball 0 (1/r)` into `ball 0 1`, and `closedBall 0 1 ⊆ ball 0 (1/r)`;
- **`circleAverage_poissonKernel_dilate`** — hence the exact Poisson representation
  `F(r w) = ⨍ P(0, w, ·) · F(r ·)` on the unit circle, for every `w` in the open disc
  (mathlib's `DiffContOnCl.circleAverage_poissonKernel_smul`);
- `poissonKernel_center_eq_one` and **`circleAverage_dilate_eq_center`** — the normalization
  `⨍ F(r ·) = F(0)`, so for a Carathéodory germ with `F(0) = 1` the boundary densities `Re F(r ·)`
  are a family of **probability** densities on the circle, uniformly in `r`.

That is the entire `r`-level of the Herglotz representation.  The single remaining analytic step is
the boundary limit: weak-\* compactness of `{Re F(r ·) dθ/2π}` as `r → 1` on the compact circle, and
identification of the limit measure through the representation above.  After it, the card's Xi
bridge is the germ `(1)`–`(4)`, the pure-point structure of the resulting measure under RH, and its
singularity — which `singularSchurDefect_doubleBoundary` already converts into the condensation
package.

## Log — the boundary probability family `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/HerglotzBoundaryMeasure.lean` (wired, axiom-clean) turns the
`r`-level representation into genuine measures on the circle the card's capstone already speaks
about (`mu : ProbabilityMeasure Circle`, `circleLebesgue`):

- `herglotzBoundaryMeasure F r = circleLebesgue.withDensity (ENNReal.ofReal ∘ Re ∘ F(r ·))`;
- `continuous_dilate_circle`, `integrable_dilate_circle` — the dilated germ is continuous, hence
  integrable, on the compact circle;
- **`integral_re_dilate_circle`** — `∫ Re F(rζ) dcircleLebesgue = Re F(0)`, transporting
  `circleAverage_dilate_eq_center` through the corpus bridge
  `integral_circleLebesgue_eq_circleAverage_complex`;
- **`isProbabilityMeasure_herglotzBoundaryMeasure`** — for a Carathéodory germ (`Re F ≥ 0` on the
  disc, `F 0 = 1`) every `herglotzBoundaryMeasure F r`, `0 < r < 1`, is a **probability measure**.

So the family whose weak-* limit is the Herglotz measure now exists as `ProbabilityMeasure Circle`
objects.  The remaining step is purely the limit: `MeasureTheory.Measure.Prokhorov` gives
`CompactSpace (ProbabilityMeasure Circle)`, and
`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` transfers the Poisson representation
`circleAverage_poissonKernel_dilate` to a limit point along `r → 1`, the kernel `P(0,w,·)` being
bounded and continuous on the circle.

### Log addendum — the Poisson representation over the circle measure `[PROVED]`

**`integral_poissonKernel_density`** — for a germ holomorphic on the open unit disc and `0 < r < 1`,

```text
∫_Circle P(0, w, ζ) · Re F(r ζ) d(circleLebesgue) = Re F(r w)     for every w in the open disc.
```

The proof runs the corpus bridge `integral_circleLebesgue_eq_circleAverage_complex` on the
complex-valued integrand `P(0,w,·) · F(r ·)` — the kernel being real, its `ℝ`-scalar action is
multiplication by the cast — lands on `circleAverage_poissonKernel_dilate`, and takes real parts
through `Complex.reCLM.integral_comp_comm`.  Continuity of the kernel on the circle uses that `w`
lies strictly inside while `‖ζ‖ = 1`, so the denominator never vanishes.

With `isProbabilityMeasure_herglotzBoundaryMeasure` this is the complete `r`-level of the Herglotz
representation *in measure form*: a family of probability measures on `Circle` reproducing `Re F`
inside the disc.  The remaining step is the weak-\* limit along `r → 1`
(`Measure.Prokhorov` + `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`), after which the
card's Xi bridge applies.

### Log addendum — the representation now holds *against the boundary measure* `[PROVED]`

**`integral_poissonKernel_herglotzBoundaryMeasure`** — for a Carathéodory germ and `0 < r < 1`,

```text
∫_Circle P(0, w, ζ) d(herglotzBoundaryMeasure F r) = Re F(r w)     for every w in the open disc,
```

with `herglotzBoundaryMeasure F r = circleLebesgue.withDensity (herglotzDensity F r)` a genuine
probability measure (`isProbabilityMeasure_herglotzBoundaryMeasure`).  The density is factored out
as `herglotzDensity` so that mathlib's
`integral_withDensity_eq_integral_toReal_smul` applies cleanly, and `ENNReal.toReal_ofReal` uses the
nonnegativity of `Re F` on the disc.

The `r`-level of the Herglotz representation is therefore complete **as a statement about
probability measures on `Circle`**, which is the exact form the card's capstone consumes.  Only the
weak-\* limit remains: `Measure.Prokhorov` supplies compactness of `ProbabilityMeasure Circle`, the
kernel `P(0,w,·)` is bounded continuous there, and
`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` transfers the identity to a cluster point
as `r → 1` — the left side converging because `Re F(r w) → Re F(w)` by continuity.

## Log — the Herglotz representation theorem on the disc `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/HerglotzRepresentationDisc.lean` (wired, axiom-clean):

```text
exists_herglotz_representation :
  F holomorphic on the open unit disc, Re F ≥ 0 there, F 0 = 1
    ⟹  ∃ μ : ProbabilityMeasure Circle,
          ∀ w in the open disc, Re F w = ∫_Circle P(0, w, ζ) dμ(ζ).
```

This is the classical Herglotz–Riesz representation, absent from mathlib and from the corpus until
now.  The proof is the four-stage chain built over the last batches:

1. `diffContOnCl_dilate` — the dilation `z ↦ F(r z)` is holomorphic up to the closed disc;
2. `circleAverage_poissonKernel_dilate` — mathlib's Poisson integral formula then represents it;
3. `circleAverage_dilate_eq_center`, `integral_re_dilate_circle`,
   `isProbabilityMeasure_herglotzBoundaryMeasure` — the boundary densities `Re F(r ·)` are
   probability densities on `Circle` against `circleLebesgue`;
4. `integral_poissonKernel_density`, `integral_poissonKernel_herglotzBoundaryMeasure` — the
   representation holds against those measures;
5. **the limit** — `Measure.Prokhorov` gives a cluster point `μ` of the family in
   `ProbabilityMeasure Circle`; the Poisson kernel is a `BoundedContinuousFunction` on the circle, so
   `ProbabilityMeasure.continuous_integral_boundedContinuousFunction` makes
   `ν ↦ ∫ P dν` continuous, hence `∫ P dμ` is a cluster point of `Re F(r_n w)`, which converges to
   `Re F w`; `eq_of_nhds_neBot` identifies them.

The card's remaining Stage-3 gate is now only its own Xi bridge: the germ `(1)`–`(4)`, the
identification of the Herglotz measure of `F_Xi` as pure point on the Cayley images of the Xi zeros
under RH, and its singularity — after which `singularSchurDefect_doubleBoundary` supplies the
condensation package, and the RH direction is already checked in
`RHTower.continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis`.

## Log — the canonical Xi circle probability measure is constructed `[PROVED]`

`formal/GaloisForLFunctions/RHTower/XiSchurDiscGerm.lean` (wired into `GaloisForLFunctions.RHTower`,
every declaration axiom-clean: `propext`, `Classical.choice`, `Quot.sound`).

- **`xiSourceHerglotz z = -logDeriv XiC z`** — the card's `H_Xi` in the centered coordinate;
  **`cayleyDisc w = i(1+w)/(1-w)`** — the card's `chi`, with `cayleyDisc_zero`,
  `cayleyDisc_im : (chi w).im = (1-|w|^2)/|1-w|^2` and `cayleyDisc_im_pos`.
- **`continuedPrimeArchUpperAntiHerglotz_iff_xiSourceHerglotz_im_nonneg`** and
  **`riemannHypothesis_iff_xiSourceHerglotz_im_nonneg_strip`** — the bridge the Stage-3 gate asked
  for in one direction: the already checked `RHTower` anti-Herglotz criterion **is** the statement
  that `H_Xi` has nonnegative imaginary part on the centered upper half strip.  The identification
  `continuedPrimeArchSourceRelativeTrace = -H_Xi` is proved
  (`continuedPrimeArchSourceRelativeTrace_eq_neg_xiSourceHerglotz`), not assumed.
- **`xiSourceHerglotz_im_nonneg_of_rh`** — equation `(6)`: under RH every centered spectral point is
  real, so every relative-resolvent term `1/a - 1/(a-z)` has nonpositive imaginary part above the
  axis and `H_Xi` is Herglotz on the **whole** upper half plane, not only on the strip.
- **`xiBasepointSlope`** `= -i H_Xi(i)` — equation `(2)`.  **`xiBasepointSlope_im`** proves it is
  real (from `logDeriv XiC i = i logDeriv xi(-1/2)` and Schwarz reality of `xi` on the real axis),
  and **`xiBasepointSlope_re_pos_of_rh`** proves `b > 0` — equation `(3)` — as the convergent
  positive sum `sum_q 1/(t_q^2+1)` over the centered spectrum, using `nonempty_xiZeroCopy`.  This
  replaces the theta-integral argument by the resolvent one and needs no numerics.
- **`xiCaratheodory`** `= -i H_Xi(chi w)/b` — equation `(4)`, with
  **`xiCaratheodory_zero_of_rh : F_Xi(0) = 1`**,
  **`xiCaratheodory_re_nonneg_of_rh`** (the Caratheodory property) and
  **`differentiableOn_xiCaratheodory_of_rh`** (holomorphy on the open disc, since RH keeps `XiC`
  zero-free above the axis).
- **`exists_xiCircleMeasure_of_rh`** — **the canonical Xi circle probability measure**: under RH
  there is a `ProbabilityMeasure Circle` whose Poisson integral is `Re F_Xi` on the open disc.  This
  uses the corpus's own `HTGeometry.exists_herglotz_representation`.

**What is left of this gate.**  Two analytic facts about that measure: that its support is infinite
(the Cayley images of the infinite Xi divisor) and that it is mutually singular with
`circleLebesgue`.  The natural route to singularity is Fatou's radial-limit theorem for Poisson
integrals — `Re F_Xi` has radial limit `0` almost everywhere on the circle because `H_Xi` is real on
the real axis away from the divisor — and mathlib has no radial boundary-limit theorem for the
Poisson kernel.  That theorem is the next unconditional build for this card; once it is available,
`xiSchur_inverseLimit_atomicCondensation` can be instantiated at the constructed measure instead of
receiving the equivalence as an argument.

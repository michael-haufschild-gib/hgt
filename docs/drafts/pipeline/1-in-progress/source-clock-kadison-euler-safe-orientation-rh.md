# Source-clock Kadison realization of the Euler-safe Xi orientation kernel

- **ID:** `source-clock-kadison-euler-safe-orientation-rh`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / HTGEOMETRY-TO-RHTOWER TRANSFER / RH ROUTE
- **Scientific status:** `[CONJECTURE] [EXACT RH CONSUMER PROVED] [ABSTRACT CLOCK REDRESSING
  FALSIFIED] [SOURCE-NATURAL REALIZATION OPEN] [NOVELTY UNVERIFIED]`
- **HT parents:**
  - `source-mackey-clock-interval.md`
  - `clock-descent-anomaly.md`
  - `../3-formalized/finite-clock-orthogonal-observability.md`
  - `../3-formalized/finite-clock-resolution-variance.md`
  - `../2-fully-proven/new_scientific_knowledge/herglotz-full-translation-ht-krein-index-orthogonality.md`
- **RH parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/xi-orientation-euler-safe-paired-cauchy-completeness.md`
  - `../2-fully-proven/not_new_scientific_knowledge/critical-logderivative-euler-safe-cauchy-loss-law.md`
  - `../2-fully-proven/not_new_scientific_knowledge/critical-logderivative-euler-safe-depoissonized-weil-stationarity.md`
- **Statement:** Construct directly from the absolute-Euler prime--Gamma source a coherent
  finite-clock star-Kadison system whose quadratic kernels converge to the Schwarz-paired Xi
  orientation kernel.  Source-built positivity then passes to the limit and proves RH.

## Exact target

Fix a rational `a>1/2` and a Gaussian-rational enumeration

```text
w_1,w_2,... in {w : Re(w)>a, Im(w)>0}.                    (1)
```

Put `X(w)=xi(1/2+w)` and `L(w)=X'(w)/X(w)`.  The completed source kernel on this
absolute-Euler quadrant is

```text
K_pair(w,u)
 =2 Re(
    (L(w)+conj(L(u)))/(w+conj(u))
    -(L(w)+L(u))/(w+u)).                                  (2)
```

For each clock cutoff `M`, construct from finite prime--Gamma source data:

1. a finite-dimensional real or complex Hilbert space `E_M`;
2. a nonzero clock period `N_M`, a period-`N_M` isometry `U_M`, and a stationary state
   `psi_M`;
3. for every finite real coefficient vector `r=(r_1,...,r_m)`, an operator
   `A_(M,r)` depending linearly on `r`;
4. compatibility maps under clock refinement;
5. a source topology in the source Mackey interval in which the resulting quadratic values
   converge.

The required limit law is

```text
lim_M Re <psi_M,
  [Phi_M(A_(M,r)^* A_(M,r))
    -Phi_M(A_(M,r))^* Phi_M(A_(M,r))] psi_M>

 =sum_(j,k<=m) r_j r_k K_pair(w_j,w_k),                  (3)
```

where `Phi_M` is conjugation twirling by `U_M`.  The construction of the left side must be fixed
functorially from the truncated von Mangoldt coefficients, the completed Gamma term, the nodes
`(1)`, and the clock refinement maps.  It may not be obtained by factoring the matrix on the
right side or by inspecting Xi zeros.

## RH implication `[PROVED FROM EXISTING ENDPOINTS]`

Every finite star-Kadison value on the left of `(3)` is nonnegative.  Hence `(3)` makes every
finite matrix of `(2)` positive semidefinite.  The Euler-safe paired-Cauchy completeness theorem
then gives positivity of the Xi--Hurwitz orientation vector, and the formal one-vector Weil
criterion gives RH.

Equivalently, the parent Cauchy-loss theorem writes the unpaired critical kernel as

```text
K_0=K_a-K_a circle C_a,                                  (4)
```

where `K_a` is the positive prime--Gamma Caratheodory kernel and `C_a` is the positive Laplace
kernel.  The desired construction makes the conjugation-odd restriction of the defect in `(4)`
a source-built conditional-variance limit.

## Why bare hypertranscendence cannot supply `(3)` `[PROVED NO-GO]`

The corpus proves that maximal full-translation hypertranscendence, the embedded differential
field, the real structure, and the generator modulo `C(z)` coexist with every finite Krein index.
Symmetric rational divisor surgery also preserves the functional-equation involution while
changing the index by arbitrary even amounts.  Therefore none of the following can force the
sign in `(2)`:

- hypertranscendence of `xi` or its logarithmic derivative;
- differential independence of prime-power or Hurwitz translate palettes;
- the unpointed differential field or its jet-tail flag;
- functional-equation symmetry without a distinguished positive source realization.

The load-bearing HT datum must be the source marking: the enlarged continuous dual, its affine
calibration, and a reflection-compatible positive realization of the coherent clock anomaly.

## Abstract clock redressing is exactly RH `[PROVED]`

An existential finite-clock realization of a Hermitian matrix is not progress.  For a finite
Hermitian matrix `G`, the following are equivalent:

```text
G is positive semidefinite;

there exist a finite Hilbert space E, an involutive unitary U,
a U-fixed vector psi, and operators A_j such that

sum_(j,k) r_j r_k G_jk
 = Re <psi,D_U(sum_j r_j A_j) psi> for every real r,       (5)
```

where `D_U` is the star-Kadison defect of the two-cycle twirl.

The forward implication is explicit.  Write `G_jk=<b_j,b_k>` in a finite Gram space `H`, put
`E=K psi direct_sum H`, let `U` act by `+1` on `psi` and `-1` on `H`, and choose the rank-one
operator `A_j` with `A_j psi=b_j`.  The twirl erases `H`, so its star-Kadison value is
`||sum_j r_j b_j||^2`.  The reverse implication is Kadison positivity.

Applied to `(2)`, existence of arbitrary clocks in `(5)` for every finite node set is therefore
equivalent to positivity of `(2)`, hence equivalent to RH.  Such a statement only redresses the
target.  The source-natural restriction in `(3)` is essential.

## Interaction with the clock-descent anomaly

Finite HT clock freedom forbids a nonzero finite shadow from exactly representing the source
constraint.  Consequently the desired `U_M,A_(M,r)` cannot be claimed to be the completed source
at any one cutoff.  They must form a coherent anomalous family whose source-topological limit is
nontrivial.  The source Mackey interval is the candidate topology in which the infinite conormal
is continuous although every finite-coordinate conormal vanishes.

This supplies a falsification test.  If the clock maps converge only in the raw product topology,
the Hausdorff observation no-go forces the limit defect to vanish and it cannot equal `(2)`.  If
they are defined by a Gram factorization of `(2)`, the construction is circular.  If refinement
does not preserve the prime--Gamma source maps, the clocks are unrelated auxiliary carriers.

## Attacks on the current construction ideas

1. **Positive-density attack.**  Positivity of the Euler-safe density gives `K_a>=0`, not the
   domination `K_a circle C_a<=K_a`.  A two-node positive-real counterexample in the parent card
   proves that generic Herglotz positivity is insufficient.
2. **Large-offset attack.**  De-Poissonization cancels the safe damping prime power by prime power
   and recovers the stationary weights `-Lambda(n)/(2 sqrt(n))`.  Moving farther into absolute
   convergence cannot make `(3)` perturbative.
3. **Differential-matroid attack.**  Prime-power tail independence controls algebraic relations,
   not Hilbert orientation.  The arbitrary-Krein-index theorem proves this category gap is real.
4. **Finite-prime attack.**  Finite Euler connection kernels have simultaneous positive and
   negative phase chambers.  The completed Gamma/pole contribution and its exact phase locking
   must remain in every cutoff.
5. **Dilation-theorem attack.**  Abstract Stinespring, Naimark, Sz.-Nagy, or Gram dilation applied
   after proving positivity merely reproduces `(5)`.  A valid dilation must be written on source
   generators before the sign of `(2)` is known.
6. **Infinitesimal Gamma-root attack.**  The Cauchy kernel has positive convolution powers
   `C_a^theta`.  If the infinitesimal generator
   `-K_a circle log(C_a)` were positive, Schur multiplication by `C_a^theta` and integration in
   `theta` would prove `K_a-K_a circle C_a>=0`.  This attractive semigroup shortcut does not
   survive the actual source.  At `a=1` and the rational real nodes `w=6/5,17/10`, 70-digit
   evaluation of the exact completed logarithmic derivative gives a negative two-by-two
   determinant for `K_a circle (1-C_a^theta)` at
   `theta=0.01,0.05,0.1,0.2,0.5`, while the determinant at `theta=1` is positive.  This is a
   numerical falsification target, not a proved no-go; an analytic interval certificate remains
   to be written.  It nevertheless excludes using root-clock passivity as an assumption in the
   proof route.  The completed clock must be coupled non-infinitesimally.

## Polarized finite-clock algebra `[PROVED IN LEAN SCRATCH]`

For two arbitrary observables `X,Y`, define the polarized star-Kadison covariance

```text
D_U(X,Y)=Phi_U(X^*Y)-Phi_U(X)^*Phi_U(Y).                 (5a)
```

If `U` is a nonempty finite-period isometry, `psi` is `U`-fixed, and `P_U` is the cyclic gauge
average, then direct operator algebra gives the full complex cross-term identity

```text
<psi,D_U(X,Y)psi>
  =<(1-P_U)X psi,(1-P_U)Y psi>.                          (5b)
```

This was checked against the repository toolchain in
`/tmp/FiniteClockStarKadisonCovariance.lean`; its axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`.  Thus the existing diagonal norm-square theorem extends to
the exact two-node polarization required by `(3)`.  No self-adjointness assumption on `X` or `Y`
is needed.

Equation `(5b)` closes the generic finite-clock algebra but not the arithmetic source theorem.
For target nodes `w,u`, the remaining equality is precisely

```text
lim_M <b_(M,w),b_(M,u)>=K_pair(w,u),
b_(M,w)=(1-P_(U_M))A_(M,w)psi_M,                         (5c)
```

with every `b_(M,w)` constructed before target positivity.  Choosing the `b_(M,w)` by factoring
the matrix `K_pair` is the abstract redressing already excluded above.

## Open core

`[OPEN CORE]` Construct one explicit source functor

```text
finite completed prime--Gamma packet
  -> (E_M,U_M,psi_M,A_(M,-))                              (6)
```

and prove both refinement compatibility and the limit identity `(3)` without a target Gram
factorization.  The smallest acceptable first brick is a two-node formula which includes the
completed archimedean term and identifies its full cross term with a star-Kadison value by direct
operator algebra.  A diagonal-only or one-node identity is insufficient because the open RH
content is genuinely multi-node.

## Lean boundary

The current `HTGeometry` working tree contains the arbitrary-operator star-Kadison identities in
`FiniteClockStarKadison.lean`; `RHTower` already contains the paired-Cauchy source and Xi--Hurwitz
orientation consumers.  No new Lean consumer should be added until the two-node source formula in
the open core is proved.  A theorem taking `(3)` as a hypothesis and returning RH would be a
routine wrapper around existing endpoints.

## Gates

- [x] exact HT-to-RH transfer object isolated
- [x] abstract clock-existence redressing proved equivalent to positivity
- [x] unpointed HT and differential-matroid routes excluded by arbitrary-index theorem
- [x] source-purity and finite-clock anomaly firewalls stated
- [x] arbitrary two-observable finite-clock covariance proved in Lean scratch
- [ ] explicit two-node completed source clock constructed
- [ ] two-node star-Kadison/source-kernel identity proved
- [ ] coherent finite-clock refinement constructed
- [ ] Mackey/source-topological convergence to `(2)` proved
- [ ] paired passivity and RH deduced
- [ ] parent-theory and scientific-novelty audit completed

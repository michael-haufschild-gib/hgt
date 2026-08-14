# Weighted Euler tangent and global strip germ decouple jointly

- **ID:** `weighted-euler-tangent-global-graph-decoupling`
- **Stage:** 3-formalized / candidate-new
- **Type:** theorem (paper), `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Scientific status:** Provisional pending independent expert verification of the oversampling
  lemma, the analytic-functional support step, and the literature claim.
- **Statement:** In the natural `A_>1` weighted Dirichlet-coefficient topology, the critical
  summable norm `sum_p |b_p| log(p)/p`, and the full logarithmic Marcinkiewicz vanishing-tail space
  `M_0`, the joint graph of the actual-source FE--Schwarz Euler tangent over finite prime support is
  dense in the product of the complete coefficient space and the entire holomorphic regular-flux
  space on the off-line fundamental quadrant.  The generated finite Euler-unit gauge group has the
  same product closure.  At the exact critical boundary its affine actual-source closure is
  `(one+M_0) x O(Q_+)_R`; the sole continuous coefficient quotient left after fixing the divisor is
  the Mertens tail class in `Q_log=M_log/M_0`.

## Spaces and joint graph

Put

```text
Q_+={s : 1/2<Re s<1, Im s>0}.
```

Let `T_>1` be the real Frechet space of prime scalar fields `b=(b_p)` satisfying

```text
||b||_sigma=sum_p |b_p|(log p)p^(-sigma)<infinity
```

for every `sigma>1`.  Finite-support fields are dense.  This is topologically equivalent to the
actual-source coefficient tangent inside `A_>1`: the scalar `b_p` produces the whole ray

```text
d_b(p^m)=m(log p)b_p,       m>=1,                         (1)
```

and zero off prime powers.  Indeed,

```text
sum_(m>=1)|d_b(p^m)|p^(-m sigma)
  = |b_p|(log p) p^(-sigma)/(1-p^(-sigma))^2,
```

whose extra denominator is bounded above and below uniformly in `p` for fixed `sigma>1`.

Also let

```text
T_1={b : ||b||_1=sum_p |b_p|(log p)/p<infinity}.          (1a)
```

This Banach space is the strongest ordinary summable prime-ray topology at the Euler boundary.
Finite support is dense in both `T_1` and `T_>1`.  The actual constant field `b_p=1` is not in
`T_1`, by Mertens divergence; that exclusion will become the exact surviving boundary.

Finally let `M_log` be the logarithmic Marcinkiewicz prime-field space

```text
||b||_M = sup_(X>=2) 1/log X * sum_(p<=X) (log p)/p |b_p|,
```

and let `M_0` be the closure of finite-support fields in `M_log`.  This is the complete
vanishing-tail layer immediately below the nonzero Mertens corona.  It strictly contains `T_1`:
for example, `b_p=1/log p` lies in `M_0` because its normalized prime-harmonic tails tend to zero,
but it is not in `T_1` because `sum_p 1/p` diverges.  The actual unit field belongs to
`M_log\M_0` and has quotient norm one.

The FE-symmetric actual-source tangent is

```text
u_p(s)=w_p(s)-w_p(1-s),
w_p(s)=(log p)p^(-s)/(1-p^(-s))^2.
```

Define the finite-support joint graph

```text
Gamma_fin={ (b, sum_p b_p u_p) : b in c00(Primes,R) }
          subset T x O(Q_+)_R.                            (2)
```

For each

```text
T in {T_>1, T_1, M_0},
```

the theorem is

```text
closure(Gamma_fin)=T x O(Q_+)_R.                          (3)
```

This is not a consequence of density of the two projections: (3) says high-prime changes can alter
the global strip germ arbitrarily while their complete weighted coefficient tangent tends to zero.

## Dual reduction

Suppose a continuous real-linear functional on the product annihilates `Gamma_fin`.  Write it as

```text
lambda(b)+ell(f),
```

with `lambda in T'` and `ell in O(Q_+)_R'`.  Continuity of `lambda` gives `sigma_0>=1` and `C>0`
such that, for the unit field `e_p`,

```text
|lambda(e_p)| <= C(log p)p^(-sigma_0).                    (4)
```

Here `sigma_0=1` for `T_1`; for `T_>1`, finitely many defining seminorms reduce to one
`sigma_0>1`.  For `M_0`, the coordinate field `e_p` has exact norm

```text
||e_p||_M=1/p,                                           (4a)
```

because the defining supremum is attained at `X=p`.  Hence

```text
|lambda(e_p)|<=C/p<=C(log p)/p,
```

so (4) again holds with `sigma_0=1` (and (5) actually gives an extra factor `1/log p` in the
sample bound for `H_A`).

The graph relation gives

```text
lambda(e_p)+ell(u_p)=0.                                   (5)
```

Write `ell=Re L`, where `L` is a continuous complex-linear functional carried by a compact
`K subset Q_+`.  Let `L#` be its Schwarz-reflected analytic functional and put

```text
A=L+L#.
```

Then `A` is carried by `K union conj(K)`, and Schwarz reality of `u_p` gives

```text
A(u_p)=2 ell(u_p).
```

For the Fourier--Borel transform

```text
F_A(z)=A(s |-> exp(-zs)),
```

define the FE Lambert transform

```text
H_A(z)=sum_(m>=1)m[F_A(mz)-exp(-mz)F_A(-mz)].             (6)
```

On a sector around the positive real axis this is holomorphic, and

```text
A(u_p)=(log p)H_A(log p).
```

Equations (4)--(5) therefore give the super-source decay

```text
|H_A(log p)| <= 2C p^(-sigma_0).                          (7)
```

## Prime-log oversampling lemma

The decisive lemma is the following.

> Let `H` be a Lambert transform of an analytic functional carried by a compact subset of
> `0<Re s<1`.  If `H(log p)=O(p^(-sigma))` for all primes and some `sigma>0`, then
>
> ```text
> limsup_(x->infinity) log|H(x)|/x <= -sigma.              (8a)
> ```
>
> Equivalently, `H(x)=O(exp(-sigma' x))` for every `sigma'<sigma`.

The point is that `{log p}` is not merely a uniqueness set; its local sampling density grows
exponentially.

### Proof

Compactness of the carrier gives constants `delta>0`, `M`, and `C` with the uniform derivative
bound

```text
|H^(N)(x)| <= C M^N sum_(m>=1)m^(N+1)exp(-delta m x)       (8)
```

for large positive `x`.  Choose `c>0` so small that

```text
c log(Mm) <= (delta/2)m
                         for every integer m>=1.           (9)
```

Such a choice exists because `log(Mm)/m` is bounded on the positive integers.  The factor `M^N`
is therefore absorbed together with the `m^N` derivative growth rather than being left outside the
exponential estimate.  For `N=floor(cR)`, summing `m exp(-(delta/2)mR)` in (8)--(9) gives some
`delta_1>0` with

```text
sup_(R<=x<=R+1)|H^(N+1)(x)|
  <= C' exp(-delta_1 R).                                   (10)
```

Use the `N+1` Chebyshev--Lobatto nodes on `[R,R+1]`.  The prime number theorem with its classical
de la Vallee Poussin error implies that, for every fixed `B`, every interval

```text
[X, X+X/(log X)^B]
```

contains a prime once `X` is large.  Taking `B>5` places a distinct prime logarithm within
`O(R^(-B))` of every Chebyshev node.

To control interpolation stability, let `l_j` be the cardinal polynomials of the unperturbed
Chebyshev--Lobatto nodes.  Their Lebesgue constant is `O(log N)`.  Markov's inequality gives

```text
sum_j ||l_j'||_infinity = O(N^3 log N).                   (11)
```

Let `A_(ij)=l_j(y_i)`, where `y_i` is the perturbed prime-log node.  The mean-value theorem and
(11) imply

```text
||A-I||_(infinity->infinity)
  = O(R^(-B)N^3 log N)=o(1).                              (11a)
```

Thus `A` is invertible with uniformly bounded inverse.  A polynomial interpolating data `v_i` at
the perturbed nodes has unperturbed nodal values `A^(-1)v`, so the ordinary Chebyshev bound gives

```text
||P||_[R,R+1] = O(log N) max_i |v_i|.                     (11b)
```

This supplies the perturbed Lebesgue bound without a condition-number assumption on a general
Vandermonde matrix.

Interpolate `H` at the resulting prime-log nodes.  By the hypothesis, the interpolation polynomial
is uniformly

```text
O(poly(R)exp(-sigma R)).                                   (12)
```

on `[R,R+1]`.  The interpolation remainder, using (10), is bounded by

```text
C' exp(-delta_1 R)/(N+1)!
  = exp(-cR log R+O(R)).
```

which is superexponentially smaller than (12).  Hence, uniformly on `[R,R+1]`,

```text
H(x)=O(poly(R)exp(-sigma R)).
```

For completeness, the real-variable Lagrange remainder is applied separately to `Re H` and
`Im H`; no complex-valued Rolle theorem is being assumed.  Both derivatives are bounded by (10),
and recombining the two remainders changes only the absolute constant.

Taking logarithms, dividing by `R`, and letting `R` tend to infinity proves (8a).  QED.

## Separation of analytic-functional carriers

Apply the lemma to (7).  It gives positive-real indicator at most `-sigma_0`.

Mobius inversion of (6) gives

```text
G_A(z):=F_A(z)-exp(-z)F_A(-z)
       =sum_(n>=1)mu(n)n H_A(nz).                          (13)
```

For every `sigma'<sigma_0`, the exponential estimate for `H_A` makes (13) absolutely convergent on
the positive ray and gives `G_A(x)=O(exp(-sigma' x))`.  Letting `sigma'` increase to `sigma_0`
shows

```text
limsup_(x->infinity) log|G_A(x)|/x <= -sigma_0.            (14)
```

But `G_A` is the Fourier--Borel transform of

```text
B=A-R_*A,              R(s)=1-s.                          (15)
```

The functional `B` is carried by a compact subset of `0<Re s<1`: `A` is carried in the right
strip, and `R_*A` in the left strip.  The transform `G_A` is entire of exponential type.  For the
Fourier--Borel convention

```text
F_B(z)=B(s |-> exp(-zs)),
```

the conjugate-indicator theorem identifies the positive-real indicator with

```text
h_G(0)=-min {Re s : s in K_min},
```

where `K_min` is the minimal convex carrier (the conjugate indicator diagram).  Equation (14)
therefore puts `K_min` in `Re s>=sigma_0`.  But `K_min` is contained in the convex hull of every
carrier of `B`, while the displayed carrier is compactly contained in `Re s<1` and
`sigma_0>=1`.  A nonzero `B` is impossible.  Hence

```text
B=0,       hence A=R_*A.                                  (16)
```

Now `A` is carried both by the right compact `K union conj(K)` and, using `A=R_*A`, by its left
reflection.  Their convex hulls are separated by the critical line.  The minimal convex carrier of
a nonzero analytic functional would have to lie in both, which is impossible; hence `A=0`.  Thus
`L=-L#`.  The same minimal-carrier argument applies to the upper carrier `K` of `L` and the lower
carrier `conj(K)` supplied by the equality, giving `L=0`.  Hence `ell=0`.
Here zero is first obtained for the restriction to entire functions; Runge density of entire
functions in the convex domain `Q_+` and continuity of `L` give zero on all of `O(Q_+)`.

Equation (5) now gives `lambda(e_p)=0` for every prime.  Finite-support fields are dense in `T`, so
`lambda=0`.  The annihilator of `Gamma_fin` is zero, and real Hahn--Banach proves (3).

## Nonlinear finite-unit group

For a real parameter `b` near zero, let the one-prime FE--Schwarz Euler-unit increment be

```text
Delta_(p,b).
```

Its right-Euler coefficient change on the `p^m` ray is

```text
(log p)[(1+b)^m-1],
```

and its regular-flux derivative at zero is `u_p`.  For every real scalar `t`, repetition gives in
the joint topology

```text
N * (coefficient increment at t/N, Delta_(p,t/N))
    -> t * (d_(e_p),u_p).                                 (17)
```

For the `M_0` statement, the coefficient coordinate is the prime-parameter difference `a-one`;
then the repeated parameter increment is exactly `t e_p`.  The full prime-power coefficient ray
has the same critical corona coordinate by
`critical-all-grade-euler-corona-grade-one-reduction.md`, while its higher grades remain in the
vanishing-tail layer.

Therefore the closure of the additive group generated by finite Euler units contains
`Gamma_fin`, and (3) gives

```text
closure(G_joint)=T x O(Q_+)_R.                            (18)
```

Consequently every continuous invariant of the weighted source tangent and the complete global
regular flux, invariant under finite Euler units, is constant after the divisor is fixed.

For `T=M_0`, translate the coefficient coordinate by the actual unit field.  Finite Euler changes
have finite-support parameter difference and therefore preserve the quotient class `[one]` in
`Q_log`.  Equation (18) gives the exact affine closure

```text
closure(actual-source finite-unit joint orbit)
  = (one+M_0) x O(Q_+)_R.                                (19)
```

Across the ambient coefficient space, finite Euler changes preserve `Q_log`.  Inside the actual
class `[one]`, equation (19) proves that no further Hausdorff continuous invariant of coefficient
plus regular flux survives after the divisor is fixed.  Thus `Q_log` is the exact continuous
coefficient quotient left by this argument.

## Significance

Earlier results left open the possibility that joint weighted coefficient memory and the global
strip germ might retain a continuous compatibility even though each projection separately had a
dense finite-unit orbit.  Theorem (3) removes that possibility through the full vanishing-tail
layer.  The completion itself decouples:

```text
weighted A_>1, critical-summable, or full vanishing-tail Euler tangent
  x whole fundamental-quadrant regular flux.
```

Thus the missing RH invariant cannot be continuous even on the entire `M_0` coefficient layer when
that layer is retained jointly with every strip Taylor coefficient at every point.  At the critical
Marcinkiewicz boundary, the exact surviving continuous datum is the corona class `[one]`; an RH
invariant must couple that class to the global divisor nonseparably.

This result is stronger than product-topology graph decoupling, local tangent completeness, global
germ completeness, and density of finite modifications in the bounded Euler coefficient locus.
The new mechanism is **prime-log oversampling with an exact carrier separation at `Re=1`**, not mere
zero-set uniqueness.

## Attacks and scope

1. The theorem is tangent/additive.  It does not classify the nonlinear global incidence set of all
   Euler parameter fields.
2. The nonlinear conclusion concerns the additive group generated by finite local Euler units;
   repetition is used only to take closure of a static group.
3. The strongest coefficient topology in the theorem is `M_0`, the complete vanishing-tail layer,
   not the whole prime corona `M_log`.  The theorem identifies the boundary exactly: finite Euler
   changes fill the affine coset `one+M_0` but cannot alter `[one] in Q_log`.
4. The proof uses no zero divisor, RH predicate, positivity, operator, spectral carrier, or support
   cutoff.
5. The Fourier--Borel carrier/conjugate-indicator theorem is a classical parent input.  The
   candidate novelty is the quantitative prime-log oversampling lemma and its
   Euler-Lambert/FE--Schwarz joint-graph consequence.
6. The formal `PrimeBarycentricCoefficientDivergence` obstruction concerns interpolation on the
   canonical growing prefix of all prime-log nodes.  The oversampling proof does not use that
   exhaustion: in each unit interval it selects `O(R)` primes within `O(R^(-B))` of a fresh
   Chebyshev--Lobatto array.  The stability estimate (11)--(11b) applies to this selected local
   array, so the canonical-prefix barycentric divergence does not contradict the lemma.

## Preliminary parent and literature audit

The direct parents are:

- completeness and sampling of exponential systems;
- Fourier--Borel transforms and carrier/indicator theorems for analytic functionals;
- Chebyshev interpolation and stability under small node perturbations;
- the prime number theorem with de la Vallee Poussin error;
- Lambert-series Mobius inversion.

The closest quantitative-small-value parent located is Henrik L. Pedersen, *Entire functions and
logarithmic sums over nonsymmetric sets of the real line*, Ann. Acad. Sci. Fenn. Math. 25 (2000),
351--388.  Its Theorem 1.1 assumes a separated `h`-dense real sequence, a sufficiently small
exponential type `A<T*/h`, and a global weighted logarithmic-sum bound.  The prime logarithms are
not separated (their gaps tend to zero), while the lemma here assumes exponentially small
pointwise values and permits the Lambert transform's full carrier-determined type.  Thus
Pedersen's stated theorem does not subsume the prime-log oversampling lemma.  An independent
sampling specialist must still check whether another density theorem does.

The pure exponential-completeness literature does not by itself give (3): exact annihilation at the
frequencies is replaced here by coefficient-dual values of size `p^(-sigma_0)`, and those values must
be upgraded to a carrier shift past `Re=1`.  The checked Euler, Lambert, generalized-Muntz, and
analytic-functional sources did not state the oversampling lemma or the joint weighted graph
decoupling theorem.

Absence from the checked sources is not conclusive.  The theorem remains a provisional
`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` until independent specialists verify both the interpolation
argument and whether a general sampling theorem subsumes it.

## RH boundary

Together with the exact infinite-jet image classifier, the theorem leaves a sharply defined object:

```text
(critical nonsummable Euler tail class, global symmetric divisor).
```

Every topology based on absolute Dirichlet convergence, the critical summable norm, and the full
Marcinkiewicz vanishing-tail completion `M_0` is now excluded jointly with the regular completed-flux
field.  The actual unit source lies in the adjacent affine space `one+M_0`, and its only surviving
continuous coefficient datum is `[one] in Q_log`.  The all-grade corona reduction proves that
higher prime-power rays add no second quotient coordinate.  The next construction must therefore
derive a nonseparable pairing of `[one]` with the global divisor; merely placing exponent characters
in another corona still only records their real part and remains circular.

## Formalization progress (Lean)

- **Session start:** 2026-07-23, seed 775516966441434641.
- **Target module chain (RHTower/):**
  1. `WeightedEulerCoefficientSpaces.lean` — spaces `T_1` (critical summable), `M_log`
     (logarithmic Marcinkiewicz), vanishing-tail layer `M_0` via truncation tails; exact
     coordinate norm `(4a)`; unit field in `M_log` but not `T_1`; `T_1 ⊆ M_0`;
     witness `1/log p ∈ M_0 \ T_1`.  [IN PROGRESS this session]
  2. Ray-norm equivalence `(1)` (A_{>1} ↔ T_{>1} comparison, geometric-derivative series).
  3. Dual reduction `(4)–(5)` on compact carriers (reuse `CompactCarrier*`,
     `EulerUnitTangent`, `PrimeLambertMobiusInversion`).
  4. Oversampling lemma `(8a)` — Chebyshev–Lobatto + Markov + short-interval primes
     (biggest gap; needs new interpolation infrastructure; check
     `SectorPrimeZeroUniqueness` PNT-free route as possible substitute input).
  5. Carrier separation `(13)–(16)` and joint closure `(3)`, `(18)`, `(19)`.
- **Existing corpus connectors found:** `RHTower.Mertens.mertens_first_prime`
  (`MertensFirst.lean`, explicit constant), `CompactCarrierFourierBorel/Lambert/
  SectorUniqueness/FECompleteness`, `PrimeLambertMobiusInversion`, `EulerUnitTangent`,
  `PrimeLogExponentialTypeUniqueness`, `PrimeBarycentricCoefficientDivergence` (scope
  note 6), mathlib `not_summable_one_div_on_primes`.
- **[DONE 2026-07-23] Step 1 — coefficient-space layer.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerCoefficientSpaces.lean` (registered in the
  `RHTower` umbrella; `lake build` clean; `#print axioms` = standard three on all ten theorems).
  Proves unconditionally: `T_1 ⊆ M_0 ⊆ M_log` (`memVanishingTailLayer_of_memCriticalSummableLayer`,
  `memMarcinkiewiczLogLayer_of_memVanishingTailLayer`); exact coordinate norm `(4a)` as
  `isGreatest_marcinkiewiczLogQuotient_coordinate` (greatest quotient value `1/p`, attained at
  `X = p`); unit field in `M_log` with explicit bound `1 + C/log 2`
  (`unitField_memMarcinkiewiczLogLayer`, `C = mertensPrimeConstant`); unit field not in `T_1`
  (`unitField_not_memCriticalSummableLayer`, Mertens divergence) and not in `M_0`
  (`unitField_not_memVanishingTailLayer` — tail quotients exceed `1/4` cofinally, via two-sided
  Mertens); strictness witnesses `invLogField = 1/log · ∈ M_0 \ T_1`.
  `M_0` is formalized by uniform vanishing of truncation tails in the Marcinkiewicz quotient
  (equivalent to closure of finite support once the normed space is built — deferred).
- **[DONE 2026-07-23] Step 2 — ray-norm equivalence (card eq. (1)).**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerRayNormEquivalence.lean` (umbrella-registered,
  `lake build` clean, standard axioms).  Unconditional: closed form
  `primePowerRayMass_eq` (`Σ_m m log p |b_p| p^{-mσ} = log p |b_p|·p^{-σ}/(1-p^{-σ})²`); two-sided
  `p`-uniform comparison `le_primePowerRayMass` (constant 1) and `primePowerRayMass_le`
  (constant `(1-2^{-σ})⁻²`); level-`σ` summability equivalence
  `summable_indicator_primePowerRayMass_iff` for every `σ > 0`; boundary connector at `σ = 1` to
  `MemCriticalSummableLayer` (`T_1`).
- **NEXT (step 3):** dual reduction (4)–(5): joint-graph annihilator ⇒ coefficient-dual decay and
  Lambert relation on compact carriers; reuse `CompactCarrierFourierBorel/Lambert`,
  `EulerUnitTangent`, `PrimeLambertMobiusInversion`.
- **[DONE 2026-07-23] Step 3 — dual reduction (4)–(7).**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerDualReduction.lean` (umbrella-registered,
  `lake build` clean, standard axioms).  Unconditional against the existing compact-carrier
  Lambert infrastructure: `criticalNorm_coordinate` (`‖e_p‖_{T_1} = log p / p`, eq. (4) at
  `σ₀ = 1`); `map_compactPrimeEulerUnitTangent_eq_logMul_lambert`
  (`ℓ(u_p) = (log p)·H(log p)`); `norm_lambert_primeLog_le_of_graph_annihilation`
  (graph relation + weighted dual bound ⇒ `‖H(log p)‖ ≤ C p^{-σ₀}`, eq. (7)); critical instance
  `..._critical` (`≤ C/p`).
- **NEXT (step 4, the open engine):** prime-log oversampling lemma (8a): exponentially small
  prime-log samples of a compact-carrier Lambert transform force negative exponential indicator.
  Needed inputs to build: derivative bound (8) from the carrier (differentiate
  `compactCarrierLambertTransform` in the corpus normalisation), Chebyshev–Lobatto interpolation
  with `O(log N)` Lebesgue constant + Markov `O(N²)` bound (11)–(11b) (not in mathlib — build),
  primes in `[X, X + X/(log X)^B]` (needs dlVP-strength PNT — check `PrimeNumberTheoremAnd`-style
  in-tree resources or the corpus PNT-free `SectorPrimeZeroUniqueness` route as a substitute).
- **Step 4 design note (2026-07-23).**  The derivative bound (8)–(10) will be formalized via
  Cauchy estimates instead of term-by-term differentiation: the corpus already proves
  `compactCarrierLambertTransform` analytic wherever the exponential test is contracting; on the
  disc `|z − x| ≤ c₀x`, `c₀ = δ/(2(δ+M))` (`δ` = carrier real-part floor, `M` = carrier sup norm),
  one has `Re(zs) ≥ δ₂x`, hence `|H| ≤ ‖L‖ e^{−δ₂x}(1−e^{−δ₂R₀})^{−2}` there, and Cauchy gives
  `|H^{(N)}(x)| ≤ N! (c₀x)^{−N} · sup` — with `N = ⌊cx⌋`, `c` small, this is `≤ C e^{−δ₁x}`,
  which is exactly (10).  Same conclusion, no `M^N` bookkeeping.  The PNT-strength input
  (primes in `[X, X+X/(log X)^B]`) remains the deep block: neither mathlib nor the deps carry it;
  plan is elementary-PNT-with-power-log-error (Bombieri–Wirsing style) or await upstream, building
  the interpolation stability layer (11)–(11b) in the meantime — it is independent of the prime
  input.
- **[DONE 2026-07-23] Step 4a — derivative bound (10).**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerLambertDerivativeBound.lean`
  (umbrella-registered, `lake build` clean, standard axioms).  Unconditional Cauchy-estimate
  form of card display (10): `re_mul_carrier_ge_on_closedBall` (sector-disc real-part floor),
  `norm_compactCarrierLambertTransform_le_on_closedBall` (`‖H‖ ≤ 4‖L‖e^{−δx/2}` on the disc
  `|z−x| ≤ δx/(2M)`), and `norm_iteratedDeriv_compactCarrierLambertTransform_le`
  (`‖H^{(N)}(x)‖ ≤ 4‖L‖e^{−δx/2}` for every `N ≤ δx/(4M)` — factorial absorbed via
  `N! ≤ N^N ≤ (r/2)^N`, so the bound is uniform in the derivative order).
- **NEXT (step 4b):** interpolation stability layer (11)–(11b): Chebyshev–Lobatto nodes,
  `O(log N)` Lebesgue constant, Markov `‖l_j'‖ = O(N² log N)` row bound, perturbed-node
  invertibility `‖A − I‖ = o(1)`.  Independent of the prime-gap input.  Then step 4c: primes in
  `[X, X + X/(log X)^B]` (elementary PNT with power-log error — the deep block), and step 4d:
  assembly of (8a).
- **[DONE 2026-07-23] Step 5a — Möbius decay transfer (13)–(14), discrete form.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerMobiusDecayTransfer.lean`
  (umbrella-registered, `lake build` clean, standard axioms).  Reuses the corpus
  `weightedLambertMobius_inversion` + `weightedLambertMobiusPair_summable_of_geometric`.
  New: `tsum_pnat_coe_mul_geometric_le` (`Σ_{ℕ+} n ρⁿ ≤ ρ/(1-ρ)²`) and
  `norm_first_le_of_weightedLambert_decay`: geometric coefficients + `‖H(n)‖ ≤ D ρⁿ`, `ρ ≤ 1/2`
  ⇒ `‖a 1‖ ≤ 4 D ρ`.  Applied at `a_x(k) = F_A(kx) − e^{−kx}F_A(−kx)`, `ρ = e^{−σ'x}`, this is
  the card's (8a) ⇒ (14) step.
- **Remaining for the card:** 4b interpolation stability (11)–(11b); 4c short-interval primes
  (deep); 4d assembly of (8a); 5b carrier separation (15)–(16) (conjugate-indicator/minimal
  carrier — check `ExponentialTypeZeroDensity`, `CompactCarrierWedgeGeometry` for inputs);
  5c Hahn–Banach joint closure (3) and group/affine closures (18)–(19).
- **[DONE 2026-07-23] Step 5b(i) — two-ray Phragmén–Lindelöf bound.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerTwoRayPhragmenLindelof.lean`
  (umbrella-registered, `lake build` clean, standard axioms).
  `norm_le_exp_of_two_ray_exponential_decay`: entire `g` with `‖g z‖ ≤ A e^{τ‖z‖}` and two-sided
  real-ray decay `‖g(±x)‖ ≤ C e^{−εx}` obeys `‖g z‖ ≤ max C A · e^{−ε|Re z| + τ|Im z|}` globally
  (four mathlib PL quadrant applications with multipliers `e^{(±ε±τi)z}`).  This is the
  quantitative `h(0)+h(π) ≥ 0` input for carrier separation (15)–(16).
- **NEXT (step 5b(ii)):** Paley–Wiener vanishing: from the global bound, the Fourier transform
  `Φ(w) = ∫ g(x)e^{−iwx}dx` is analytic on the strip `|Im w| < ε`, vanishes for `|w| > τ` by
  rectangle contour shift (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` + side
  decay), hence `Φ ≡ 0` (identity theorem), hence `g|ℝ = 0` (mathlib Fourier inversion), hence
  `g ≡ 0`.  Then 5b(iii): instance `g = F_B·e^{cz}` for strip-carried `B` with ray decay from
  (14) ⇒ `F_B ≡ 0` ⇒ corpus `map_coordinate_pow_eq_zero_of_fourierBorel_zero` finishes (16).
- **[DONE 2026-07-23] Step 5b(ii-a) — strip Fourier transform analyticity.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerStripFourierAnalytic.lean`
  (umbrella-registered, `lake build` clean, standard axioms).  For `g` with the two-ray bound
  of 5b(i): `integrable_exp_neg_mul_abs` and `integrable_abs_mul_exp_neg_mul_abs` (line
  integrability of `e^{−c|x|}` and `|x|e^{−c|x|}`, missing from mathlib);
  `integrable_stripFourier_kernel`; `stripFourier g w = ∫ g(x)e^{−iwx}dx`;
  `hasDerivAt_stripFourier` (differentiation under the integral, dominated-convergence);
  `analyticOnNhd_stripFourier` on `{|Im w| < ε}`.
- **NEXT (step 5b(ii-b)):** contour shift: `stripFourier g w = 0` for real `|w| > τ` (rectangle
  Cauchy + vanishing sides using the two-ray bound), identity theorem on the connected strip
  (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`), Fourier inversion
  (`Continuous.fourierInv_fourier_eq`, note `𝓕 g ξ = stripFourier g (2πξ)`), then `g ≡ 0`,
  and the carrier-separation instance for `F_B e^{cz}`.
- **[DONE 2026-07-23] Step 5b(ii-b) — contour shift and high-frequency vanishing.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerStripFourierContourShift.lean`
  (umbrella-registered, `lake build` clean, `formal_tools.py lint` passes, indexes regenerated,
  standard axioms).  `stripFourierShifted_eq`: rectangle contour shift with exponentially
  vanishing sides (mathlib `integral_boundary_rect_eq_zero_of_differentiableOn` + interval-integral
  limits); `stripFourier_eq_zero_of_abs_gt`: for entire `g` with the two-ray bound,
  `stripFourier g w = 0` for every real `|w| > τ` (shift the line to `∓∞`).
- **NEXT (step 5b(ii-c), the Paley–Wiener finale):** identity theorem on the strip
  (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, strip is convex ⇒
  preconnected, zeros accumulate at `w = τ+1`), `𝓕 g ξ = stripFourier g (2πξ)` ⇒ `𝓕 g ≡ 0` ⇒
  `g|ℝ = 0` (mathlib `Continuous.fourierInv_fourier_eq`) ⇒ `g ≡ 0` (identity theorem on ℂ).
  Then the carrier instance for `F_B e^{cz}`.  ALSO: sanitize module docstrings per
  `formal/CLAUDE.md` (no card references — state the mathematics only) across the six
  WeightedEuler* modules.
- **[DONE 2026-07-23] Step 5b(ii-c) — Paley–Wiener finale: the two-ray vanishing theorem.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerPaleyWienerVanishing.lean`
  (umbrella-registered, `lake build` clean, standard axioms).  Chain complete:
  `stripFourier_eqOn_zero` (identity theorem on the convex strip, zeros accumulating from the
  contour-shift vanishing), `eq_zero_on_real_of_strip_bound` (Fourier inversion:
  `𝓕 g ξ = stripFourier g (2πξ)`), `eq_zero_of_strip_bound`, and the capstone
  **`eq_zero_of_two_ray_exponential_decay`**: an entire function of exponential type decaying
  exponentially on both real rays vanishes identically — the vanishing form of `h(0)+h(π) ≥ 0`
  used by the card's carrier separation (15)–(16).  Also DONE: docstring sanitization pass over
  all eight WeightedEuler* modules per `formal/CLAUDE.md` (mathematics only, no card references),
  indexes regenerated.
- **NEXT (step 5b(iii)):** carrier-separation instance: apply the vanishing theorem to
  `g(z) = F_B(z)·e^{cz}` where `F_B = compactFourierBorel` of the FE-odd difference functional on
  a compact carrier in `{Re s < 1}` — growth from `‖L‖`/carrier bounds (corpus
  `CompactCarrierFourierBorel`), plus-ray decay from the assembled (14), minus-ray growth from
  the carrier — concluding `F_B ≡ 0`, then the corpus
  `map_coordinate_pow_eq_zero_of_fourierBorel_zero` gives (16).  Remaining big blocks after
  that: 4b interpolation stability, 4c short-interval primes, 4d oversampling assembly,
  5c joint closures (3)/(18)/(19).
- **[DONE 2026-07-23] Step 5b(iii) — carrier separation (15)–(16), corpus instance.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerCarrierSeparation.lean`
  (umbrella-registered, `lake build` clean, standard axioms, index regenerated).
  `compactFourierBorel_eq_zero_of_ray_decay`: a compactly carried functional with carrier real
  parts `≤ β` whose Fourier–Borel transform decays at rate `σ₀ > β` on the positive ray has
  `F ≡ 0` — via `g = F·e^{cz}`, `c = (σ₀+β)/2`, and the Paley–Wiener two-ray vanishing theorem.
  `map_coordinate_pow_eq_zero_of_ray_decay`: hence `L(s^N) = 0` for every `N` (through the corpus
  `map_coordinate_pow_eq_zero_of_fourierBorel_zero`).  This is (16) with the ray decay (14) as
  its one explicit hypothesis.
- **Status roll-up.**  Formalized so far (12 modules, all unconditional, standard axioms):
  coefficient layers + strictness (steps 1), ray-norm equivalence (2), dual reduction (3),
  Cauchy derivative bound (4a), Möbius decay transfer (5a), two-ray PL bound (5b-i),
  strip-Fourier analyticity (5b-ii-a), contour shift + high-frequency vanishing (5b-ii-b),
  Paley–Wiener two-ray vanishing capstone (5b-ii-c), carrier separation instance (5b-iii).
  **The remaining open chain to discharge (14) unconditionally:** 4b Chebyshev–Lobatto
  interpolation stability (11)–(11b); 4c primes in `[X, X+X/(log X)^B]` (elementary PNT with
  power-log error — the deep block); 4d assembly of the oversampling lemma (8a); then 5c the
  Hahn–Banach joint closures (3)/(18)/(19).
- **Step 4b redesign (2026-07-23).**  The card's Chebyshev–Lobatto + Markov + `O(log N)`
  Lebesgue-constant machinery (11)–(11b) is NOT needed for (8a).  Since (8a) is a `limsup`
  statement and the node count `N = ⌈cR⌉` carries a free parameter `c`, an exponential
  Lebesgue bound `Λ ≤ e^{C''cR}` suffices: it contributes `+C''c` to the limsup, and letting
  `c → 0` AFTER `R → ∞` removes the loss.  The crude bound for `η`-separated nodes in a unit
  interval (`|l_i| ≤ 2^N/(η^N N!)`, from `i!(N−i)! ≥ N!/2^N`) is exponential with constant
  `∝ c` when `η ≈ 1/(2N)`, so near-EQUISPACED prime-log nodes at resolution `R^{−B}` work and
  the entire sharp-interpolation layer collapses to: (4b-1) the Lagrange remainder theorem via
  iterated Rolle (missing from mathlib; `Mathlib.LinearAlgebra.Lagrange` has only the algebra);
  (4b-2) the crude separated-node Lagrange bound (elementary products).  The prime input (4c)
  is unchanged: primes within `R^{−B}` of the equispaced grid = primes in
  `[X, X+X/(log X)^B]`-type windows.  4b-1/2 are generic real analysis → build in `HTGeometry`.
- **[DONE 2026-07-23] Step 4b-1 — iterated Rolle.**
  `formal/GaloisForLFunctions/HTGeometry/IteratedRolleVanishing.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).
  `exists_iteratedDeriv_eq_zero_of_zeros`: a real function with continuous iterated derivatives
  vanishing at `k+1` strictly increasing points has `f^{(k)}(ξ) = 0` in their closed span.
  Missing from mathlib; the mean-value engine for the Lagrange remainder.
- **NEXT (step 4b-2):** Lagrange interpolation remainder: for smooth `f`, interpolant `P` at
  `n+1` sorted nodes (mathlib `Lagrange.interpolate`), `|f(x) − P(x)| ≤
  sup|f^{(n+1)}|/(n+1)!·∏|x−x_i|` — apply iterated Rolle to `f − P − λW`.  Needs the polynomial
  facts `iteratedDeriv (n+1) (P.eval) = 0` (deg ≤ n) and `iteratedDeriv (n+1) (W.eval) = (n+1)!`
  (monic nodal `W`) — check `Polynomial.iterate_derivative_*` API.  Then 4b-3: crude
  `η`-separated Lagrange-basis bound `|l_i(x)| ≤ 2^N/(η^N·N!)`.
- **[DONE 2026-07-23] Step 4b-2 (foundations) — Lagrange remainder infrastructure.**
  `formal/GaloisForLFunctions/HTGeometry/LagrangeRemainder.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).  Proven:
  `iteratedDeriv_polynomial_eval` (analytic iterated derivatives of polynomial evaluation are
  algebraic iterated derivatives); `contDiff_polynomial_eval`; the Finset form
  `exists_iteratedDeriv_eq_zero_of_finset_zeros` of iterated Rolle (via `Finset.orderIsoOfFin`);
  `iterate_derivative_add'`; and `iterate_derivative_nodal`
  (`derivative^[n+1] (nodal s id) = C (n+1)!` via `eraseLead` decomposition).
- **NEXT (step 4b-2 finale):** assemble the remainder theorem
  `|f x − (Lagrange.interpolate s id f).eval x| ≤ M/(n+1)!·∏_{t∈s}|x−t|` for
  `ContDiff ℝ ⊤` f with `|f^{(n+1)}| ≤ M` on `[a,b] ⊇ s ∪ {x}`: φ := f − P.eval − λ·W.eval
  vanishes on `insert x s` (card n+2), Finset Rolle at order n+1, then
  `iteratedDeriv_sub`/`iteratedDeriv_const_smul` (ContDiffAt hypotheses) + the two polynomial
  derivative facts solve for λ.  Then 4b-3: crude η-separated Lagrange-basis bound.
- **[DONE 2026-07-23] Step 4b-2 (complete) — the Lagrange interpolation remainder.**
  Appended to `formal/GaloisForLFunctions/HTGeometry/LagrangeRemainder.lean` (`lake build`
  clean, standard axioms, index regenerated).  `iteratedDeriv_sub_polynomial_eval` (pointwise
  splitting of `f − Q.eval` under iterated derivatives) and the classical
  **`abs_sub_eval_interpolate_le`**: for `ContDiff ℝ ⊤` `f`, nodes `s ⊆ [a,b]` with
  `|s| = n+1`, and `x ∈ [a,b]`,
  `|f x − (Lagrange.interpolate s id f).eval x| ≤ M/(n+1)!·∏_{t∈s}|x−t|`
  where `M` bounds `|f^{(n+1)}|` on `[a,b]`.  Missing from mathlib.
- **NEXT (step 4b-3):** crude separated-node Lagrange-basis bound: for `η`-separated nodes in a
  unit interval, `|ℓ_i(x)| ≤ 2^N/(η^N·N!)` (via `∏_{j≠i}|x_i−x_j| ≥ η^N·i!(N−i)!` and
  `i!(N−i)! ≥ N!/2^N`), giving the interpolant sup bound
  `|P(x)| ≤ (N+1)·2^N/(η^N N!)·max_i|f(x_i)|`.  With 4b-2 this yields the abstract
  oversampling estimate; 4c (short-interval primes) then discharges the node hypothesis.
- **[DONE 2026-07-23] Step 4b-3 (part 1) — separated-node product estimates.**
  `formal/GaloisForLFunctions/HTGeometry/SeparatedNodeProducts.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).  `gap_telescope` + `sep_sub_le` +
  `sep_mul_index_dist_le` (consecutive gaps `≥ η` ⇒ `η·|i−j| ≤ |pts i − pts j|`);
  `prod_range_sub_eq_factorial` (`∏_{j<n}(n−j) = n!` over ℝ); `factorial_div_two_pow_le`
  (`n!/2^n ≤ i!·(n−i)!`).
- **NEXT (step 4b-3 part 2):** assemble the Lagrange denominator bound
  `∏_{j≠i}|pts i − pts j| ≥ η^N·N!/2^N` (reindex `univ.erase i` products through the ordered
  enumeration; split into below/above `i` and use the two product identities), then the basis and
  interpolant sup bounds.  After that only 4c (short-interval primes) and 4d (assembly) remain
  for the oversampling lemma (8a).
- **[DONE 2026-07-23] Step 4b-3 (part 2) — the crude Lagrange denominator bound.**
  Appended to `formal/GaloisForLFunctions/HTGeometry/SeparatedNodeProducts.lean` (`lake build`
  clean, standard axioms, index regenerated).  `prod_erase_enum` (erase-products reindex through
  the ordered enumeration), `prod_erase_index_dist`
  (`∏_{j≠i}|i−j| = i!·(N−i)!` by below/above splitting), and the capstone
  **`prod_erase_abs_sub_ge`**: for pairwise `η`-separated nodes,
  `∏_{u≠t}|t−u| ≥ η^N·N!/2^N`.  With `abs_sub_eval_interpolate_le` (4b-2) this pins both halves
  of the interpolation estimate.
- **NEXT (step 4b-3 part 3):** the Lagrange basis/interpolant sup bound: from the numerator
  `∏_{u ∈ s.erase t}|x−u| ≤ 1` (unit interval) and the denominator bound,
  `|ℓ_t(x)| ≤ 2^N/(η^N·N!)`, hence
  `|P(x)| ≤ (N+1)·2^N/(η^N·N!)·max_t|f(t)|` (mathlib `Lagrange.interpolate` as
  `∑ C (f t) * basis`, `Lagrange.eval_basis`).  Then 4c (short-interval primes), 4d (assembly).
- **[DONE 2026-07-23] Step 4b-3 (complete) — interpolant sup bound.**
  `formal/GaloisForLFunctions/HTGeometry/SeparatedNodeInterpolantBound.lean` (HTGeometry
  umbrella, `lake build` clean, standard axioms, index regenerated).
  `abs_eval_basis_le` (`|ℓ_t(x)| ≤ 2^N/(η^N·N!)` over `η`-separated nodes in a unit window) and
  **`abs_eval_interpolate_le_of_separated`**
  (`|P(x)| ≤ (N+1)·2^N/(η^N·N!)·B`).  **Step 4b is now fully formalized**: remainder
  (`abs_sub_eval_interpolate_le`) + sup bound, sufficient for the limsup oversampling argument
  with `η ≈ 1/(2N)` nodes.
- **NEXT (step 4d skeleton):** the abstract oversampling estimate: for `H` with the Cauchy
  derivative bound (`norm_iteratedDeriv_compactCarrierLambertTransform_le`, applied to Re/Im on
  `[R, R+1]`) and `N+1` `η`-separated sample points where `|H| ≤ ε_R`, combine 4b-2 + 4b-3:
  `|H(x)| ≤ (N+1)·2^N/(η^N N!)·ε_R + 4‖L‖e^{−δR/2}/(N+1)!` on `[R, R+1]`.  State it for real
  parts of a ℂ-valued `H` with hypothesis-supplied nodes; 4c will then produce the prime-log
  nodes (deep block: elementary PNT with power-log error).
- **[DONE 2026-07-23] Step 4d (part 1) — the abstract sampled-smallness estimate.**
  `formal/GaloisForLFunctions/HTGeometry/SampledSmallInterpolation.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).
  **`abs_le_of_sampled_small`**: smooth `f` small (`≤ ε₀`) on `N+1` `η`-separated samples of a
  unit interval with `|f^{(N+1)}| ≤ M` there satisfies
  `|f x| ≤ (N+1)·2^N/(η^N·N!)·ε₀ + M/(N+1)!` on the whole interval.  This is the analytic core
  of the oversampling lemma (8a) in the redesigned (limsup) form; steps 4a + 4b feed it exactly.
- **Remaining open chain for the card:** 4d-2 (ℂ-valued bridge: apply the estimate to Re/Im of
  the Lambert transform along `[R, R+1]`, connecting real `iteratedDeriv` of `H∘ofReal` to the
  complex `iteratedDeriv` bound from `norm_iteratedDeriv_compactCarrierLambertTransform_le` —
  plumbing via `HasDerivAt.comp_ofReal`); 4c (prime-log `η`-separated node supply near
  equispaced grids = primes in `[X, X+X/(log X)^B]`, elementary PNT with power-log error — the
  single deep block); 4d-3 (limsup assembly of (8a) with `c → 0`); 5c (joint closures
  (3)/(18)/(19): Hahn–Banach + the formalized dual reduction/carrier separation).
- **[DONE 2026-07-23] Step 4d-2 — the ℂ-valued sampled-smallness bridge.**
  `formal/GaloisForLFunctions/HTGeometry/SampledSmallComplex.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).
  `differentiable_deriv_of_entire`; `iteratedDeriv_comp_ofReal` (real iterated derivatives along
  ℝ = complex iterated derivatives, for entire functions); `iteratedDeriv_clm_comp` (projection
  commutation); `contDiff_comp_ofReal`; and
  **`norm_le_of_sampled_small_complex`**: an entire `H` small at `N+1` `η`-separated real
  samples of a unit window with `‖H^{(N+1)}‖ ≤ M` there obeys
  `‖H(x)‖ ≤ 2·((N+1)·2^N/(η^N·N!)·ε₀ + M/(N+1)!)` on the window — Re/Im interpolated
  separately, exactly the card's "no complex Rolle" remark.
- **Remaining for (8a):** 4c (the prime-log node supply: `η ≈ 1/(2N)`-separated prime logs in
  every `[R, R+1]` — needs elementary PNT with power-log error, THE deep block) and 4d-3 (the
  limsup assembly: feed `norm_iteratedDeriv_compactCarrierLambertTransform_le` (4a) and the
  sampled decay (7) into `norm_le_of_sampled_small_complex`, then `R → ∞`, `c → 0`).  Then 5c.
- **[DONE 2026-07-23] Step 4d-3 (part 1) — explicit factorial growth bounds.**
  `formal/GaloisForLFunctions/HTGeometry/FactorialGrowthBounds.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).
  `pow_mul_exp_neg_le_factorial` (`n^n e^{−n} ≤ n!`, from the exponential series);
  `succ_div_pow_le_exp_one` (`((n+1)/n)^n ≤ e`); `two_le_exp_one`; and
  **`interpolation_constant_le`**: at node separation `η = 1/(4(N+1))` the sampled-smallness
  sup constant obeys `(N+1)·2^N/(η^N·N!) ≤ e^{6(N+1)}` — the explicit exponential constant
  for the limsup assembly.
- **NEXT (step 4d-3 part 2):** the window decay bound: for entire `H` with the 4a derivative
  bound and `N_R+1 = ⌊cR⌋+1` nodes at separation `1/(4(N_R+1))` in `[R, R+1]` where
  `‖H‖ ≤ Ce^{−σR}`, `norm_le_of_sampled_small_complex` + `interpolation_constant_le` +
  `pow_mul_exp_neg_le_factorial` give
  `‖H(x)‖ ≤ 2C·e^{6(N_R+2)}e^{−σR} + 2K·e^{−δR}e^{−(N_R+1)(log(N_R+1)−1)}` on `[R, R+1]`;
  then the rate transfer: ∀ σ' < σ with `6c < σ − σ'` and `c log(cR) → ∞` beats `σ'`,
  conclude `∃ C', ‖H(x)‖ ≤ C'e^{−σ'x}` for large `x` — the (8a)-consumer form.  Then 4c.
- **[DONE 2026-07-23] Step 4d-3 (part 2) — the explicit window decay bound.**
  `formal/GaloisForLFunctions/HTGeometry/SampledWindowDecay.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).
  `one_div_factorial_le_superexp` (`1/n! ≤ e^{−n(log n −1)}`) and
  **`norm_le_window_of_sampled`**: at the canonical separation `1/(4(N+1))`,
  `‖H(x)‖ ≤ 2e^{6(N+1)}·ε₀ + 2M/(N+1)!` on the unit window.  All analytic constants of the
  oversampling lemma are now explicit.
- **NEXT (step 4d-3 part 3, the (8a) rate transfer):** for entire `H` with (i) the 4a
  derivative bound `M_R = K e^{−δR}` valid for orders `≤ δR/(4M)`, (ii) node families with
  `N_R := ⌊cR⌋` (`c ≤ δ/(8M)` so `N_R + 1 ≤` the 4a order ceiling for large `R`), and (iii)
  sample decay `ε₀ = Ce^{−σR}`: conclude for every `σ' < σ − 12c` an eventual bound
  `‖H(x)‖ ≤ C'e^{−σ'x}` on `x ≥ R₁` (windows tile the ray; `e^{6(N_R+2)} ≤ e^{12cR}` for
  `cR ≥ 1`; remainder term `2Ke^{−δR}e^{−(N_R+1)(log(N_R+1)−1)} ≤ e^{−σ'R}` eventually since
  `c log(cR) → ∞`).  Interface hypothesis for 4c: the node families.  Then 4c itself.
- **[DONE 2026-07-23] Step 4d-3 (part 3) — the ray rate-transfer theorem.**
  `formal/GaloisForLFunctions/HTGeometry/SampledRayRateTransfer.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).
  **`norm_le_ray_of_sampled_decay`**: for entire `H` with window derivative bounds
  `‖H^{(⌊cR⌋+1)}‖ ≤ Ke^{−δR}` and `⌊cR⌋+1` separated samples per window where
  `‖H‖ ≤ Ce^{−σR}`, one gets `‖H(x)‖ ≤ C′e^{−σ′x}` for all large `x`, for EVERY
  `σ′ ≤ σ − 6c` — all thresholds explicit, no asymptotic filters.  This IS the oversampling
  lemma (8a) modulo two instantiations: (α) the derivative hypothesis, discharged by 4a
  (`norm_iteratedDeriv_compactCarrierLambertTransform_le`) once `c ≤ δ/(8M)`-type consistency
  is checked; (β) the node hypothesis = prime logs at separation `1/(4(⌊cR⌋+1))` in `[R,R+1]`
  with the sampled decay from the dual reduction (7) — THE remaining deep block (4c: elementary
  PNT with power-log error).
- **The card's analytic program is now complete**; what remains is arithmetic (4c), two
  instantiation lemmas, and 5c (joint closures).
- **[DONE 2026-07-23] Instantiation (α) — Lambert window derivative bounds.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerLambertWindowDerivatives.lean`
  (umbrella-registered, `lake build` clean, standard axioms, index regenerated).
  **`lambert_derivative_window_bound`**: for carrier constants `δ ≤ M` and any node density
  `0 < c ≤ δ/(8M)`, the order-`⌊cR⌋+1` derivative of `compactCarrierLambertTransform` is
  `≤ 4‖L‖e^{−(δ/2)R}` on `[R, R+1]` for `R ≥ max(8M/δ, 2log2/δ)` — exactly the `hder`
  hypothesis of `norm_le_ray_of_sampled_decay` with `K = 4‖L‖`, rate `δ/2`.
  **The oversampling lemma (8a) is now reduced to a single hypothesis**: the prime-log node
  supply (4c).  Chain: nodes ⇒ `norm_le_ray_of_sampled_decay` (with the dual-reduction sample
  decay (7)) ⇒ ray decay (8a) ⇒ Möbius transfer (14) ⇒ carrier separation (16) — all other
  links formalized.
- **NEXT:** 4c (primes in short intervals — elementary PNT with power-log error) OR 5c (joint
  Hahn–Banach closures (3)/(18)/(19), independent of 4c).  rng-pick next iteration.
- **[DONE 2026-07-23] Step 5c(i) — quantitative Möbius ray recovery.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerMobiusRayRecovery.lean`
  (umbrella-registered, `lake build` clean, standard axioms, index regenerated).
  `norm_fourierBorel_le_of_lambert_ray_decay` (geometric ray decay + Lambert samples `≤ Dρⁿ`,
  `ρ ≤ 1/2` ⇒ `‖F x‖ ≤ 4Dρ`, via the 5a transfer and the corpus
  `weightedLambertTransform_ray_eq`), and its compact-carrier form
  `norm_compactFourierBorel_le_of_sampled_lambert_decay` (through the corpus
  `positiveLambertDerivative_compactFourierBorel`).  This converts oversampled Lambert decay
  (the rate-transfer output) into Fourier–Borel decay — the (14) link — feeding
  `compactFourierBorel_eq_zero_of_ray_decay` (5b-iii).
- **Full-chain status.**  Formalized links: (4)–(5) dual reduction ⇒ Lambert sample decay (7);
  4a+α window derivative bounds; 4b+4d interpolation/rate transfer (8a modulo nodes); 5c(i)
  Möbius recovery (14); 5b carrier separation (15)–(16) ⇒ coordinate-power vanishing.  Open:
  4c prime-log nodes (deep); FE-pairing bookkeeping (the card works with the FE-odd difference
  `B = A − R_*A`: assemble the reflected-carrier functional in the corpus FE framework,
  cf. `CompactCarrierFECompleteness`); 5c(ii) Hahn–Banach joint closure statements (3)/(18)/(19).
- **[DONE 2026-07-23] FE-pairing carrier separation (the `B = A − R_*A` form of (15)–(16)).**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerFECarrierSeparation.lean`
  (umbrella-registered, `lake build` clean, standard axioms, index regenerated).
  `norm_compactFourierBorel_le_exp`, `norm_compactFourierBorel_neg_ray_le`, and
  **`compactFourierBorel_sub_eq_zero_of_ray_decay`**: for two compactly carried functionals with
  all carrier real parts `≤ β`, positive-ray decay of the transform difference at any rate
  `σ₀ > β` forces the transforms to agree identically — the two-carrier Paley–Wiener separation
  matching the card's reflected pair (`A` on `K`, `R_*A` on the reflected carrier, both real
  parts `< 1` inside the strip).
- **4c status note:** verified this mathlib snapshot has neither PNT nor Wiener–Ikehara (only
  Chebyshev bounds/Bertrand, and ζ nonvanishing on `Re = 1` in `LSeries/Nonvanishing`).  The
  prime-node supply therefore requires building PNT-with-power-log-error — a multi-session
  sub-project (candidate: analytic route via the mathlib ζ framework + a formalized
  Perron/Tauberian step, or elementary Bombieri–Wirsing).  It is the ONLY remaining input to
  (8a); worth spinning off as its own reusable infrastructure effort.
- **Remaining:** 4c (above); 5c(ii) Hahn–Banach joint closure statements (3)/(18)/(19).
- **[DONE 2026-07-23] Step 5c(ii-a) — the Hahn–Banach density criterion.**
  `formal/GaloisForLFunctions/HTGeometry/DenseOfVanishingDual.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).
  `exists_dual_vanishing_of_notMem_closed_submodule` (geometric HB: a point outside a closed
  submodule is separated by a functional VANISHING on the submodule — the boundedness-on-a-
  subspace-implies-vanishing scaling argument) and
  **`topologicalClosure_eq_top_of_forall_dual_eq_zero`**: a submodule of a real normed space
  annihilated only by the zero functional is dense.  This is the closure engine for (3):
  the joint-graph annihilator computation (dual reduction ⇒ oversampling ⇒ Möbius ⇒ carrier
  separation, all formalized) plugs into this criterion.
- **NEXT (step 5c(ii-b)):** the joint-space model: coefficient side as `lp 1` over `Nat.Primes`
  (dictionary `b ↦ (log p/p)·b_p`), product with `C(K, ℂ)` (sup norm), the finite joint graph as
  a `Submodule.span` of `{(e_p, u_p)}`, and the capstone density statement assembling the
  annihilator chain — conditional only on the 4c node interface.  Then 4c (PNT sub-project) and
  the (18)/(19) group/affine corollaries.
- **[DONE 2026-07-23] Step 5c(ii-b, part 1) — coordinate span density in ℓ¹.**
  `formal/GaloisForLFunctions/HTGeometry/LpSingleSpanDense.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).
  **`span_lp_single_dense`**: the span of unit coordinate vectors is dense in
  `lp (fun _ : α => ℝ) 1` (via `lp.hasSum_single`).  In the rescaled dictionary
  `b ↦ ((log p/p)·b_p)_p`, this is the card's "finite-support fields are dense in `T_1`",
  the coefficient half of the joint closure (3).
- **NEXT:** 5c(ii-b, part 2): the product-space joint graph
  (`lp 1 × C(K,ℂ)` with `Submodule.span {((log p/p)·δ_p, u_p)}`) and the capstone density via
  `topologicalClosure_eq_top_of_forall_dual_eq_zero` + the formalized annihilator chain, with
  the 4c node interface as the one hypothesis.  Also open: (17) nonlinear repetition limit,
  (18)/(19) corollaries, and 4c (PNT sub-project).
- **[DONE 2026-07-23] Step (17) part A — the quadratic power-linearization bound.**
  `formal/GaloisForLFunctions/HTGeometry/PowerLinearizationBound.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).
  `choose_le_pow_div_factorial` (`C(n,j) ≤ n^j/j!`), `sum_Ico_pow_div_factorial_le`
  (`Σ_{2≤j≤n} x^j/j! ≤ x²e^x`), and **`abs_pow_sub_one_sub_le`**
  (`|(1+b)^m − 1 − mb| ≤ (m|b|)²e^{m|b|}`) — the tangency estimate behind the card's
  repetition display (17).
- **NEXT (step (17) part B):** the weighted repetition limit: with `b := t/N`, the scaled
  increment satisfies `Σ_m |N((1+t/N)^m −1) − tm|·p^{−mσ} ≤ (t²/N)·Σ m²(p^{−σ/2})^m → 0`
  for `N ≥ 2|t|/(σ log p)` — the coefficient-side convergence
  `N·Δ_{p,t/N} → t·d_{e_p}` in every level-σ ray norm.  Then remaining: 5c(ii-b) part 2 joint
  capstone; (18)/(19); 4c (PNT sub-project).
- **[DONE 2026-07-23] Step (17) part B — the weighted repetition limit.**
  `formal/GaloisForLFunctions/HTGeometry/ScaledPowerIncrementLimit.lean` (HTGeometry umbrella,
  `lake build` clean, standard axioms, index regenerated).
  **`tendsto_scaled_power_increment_ray`**: for every ratio `0 < r < 1` and parameter `t`,
  `Σ_m |n((1+t/n)^m −1) − tm|·r^m → 0` as `n → ∞` — termwise quadratic linearization dominated
  by `(t²/n)·Σ m²(√r)^m` once `e^{|t|/n} ≤ 1/√r`.  At `r = p^{−σ}` this is the card's (17)
  coefficient-side convergence `N·Δ_{p,t/N} → t·d_{e_p}` in every level-`σ` ray topology.
- **Remaining:** 5c(ii-b) part 2 (joint product-space capstone); (18)/(19) corollaries;
  4c (PNT-with-power-log-error sub-project — the single deep block gating unconditional (8a)).
- **[DONE 2026-07-23] Step 4c (combinatorial half) — prime-log node assembly.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerPrimeNodeAssembly.lean`
  (umbrella-registered, `lake build` clean, standard axioms, index regenerated).
  **`exists_separated_primeLog_nodes`**: one prime logarithm per `η`-window at the `4η`-spaced
  targets `y_i = R + 4η·i` (`η = 1/(4(N+1))`, `i ≤ N`) yields exactly the node-family interface
  of `norm_le_ray_of_sampled_decay`: `N+1` prime logs in `[R, R+1]`, pairwise `η`-separated,
  each a genuine `log p`.  **4c is now reduced to its pure arithmetic core**: a prime in every
  window `[y, y + 1/(4(⌊ce^y⌋-ish))]` — i.e. primes in multiplicative gaps
  `[X, X(1 + Θ(1/(c·log X)))]`, PNT-with-power-log-error strength.  That analytic core is the
  single remaining input for the whole card (everything else is formalized end-to-end) and
  should proceed as its own reusable sub-project (Selberg symmetry formula → elementary PNT
  with error, or mathlib-ζ analytic route).

- **[DONE 2026-07-24] Step 4c COMPLETE + (8a) UNCONDITIONAL — the prime-log
  oversampling lemma is discharged end-to-end.**
  The 4c sub-project (card `elementary-pnt-power-log-error-infrastructure`,
  now in 3-formalized) delivered the full elementary Erdős–Selberg chain:
  `RHTower.psiRemainder_eventually_le` (**ψ(N) = N + o(N), unconditional,
  standard axioms**), θ-form `chebyshevTheta_remainder_eventually_le`,
  window supply `exists_prime_log_window` (∀η>0, primes in every
  multiplicative window `[e^y, e^{y+η}]` past an explicit threshold), and
  `exists_separated_primeLog_nodes_unconditional` (∀N ∃R₀: N+1 separated
  prime logs in every unit window past R₀) — discharging the hwin
  hypothesis of `exists_separated_primeLog_nodes`.
  **Route resolution for (8a):** the growing-order transfer
  (`norm_le_ray_of_sampled_decay`, count ⌊cR⌋+1) needs shrinking windows
  `[X, X(1+Θ(1/log X))]` — power-log PNT strength, NOT delivered by ψ~x.
  Instead: NEW **fixed-order transfer**
  `HTGeometry.norm_le_ray_of_sampled_decay_fixed`
  (`SampledRayRateTransferFixed.lean`): N+1 nodes per window at canonical
  separation 1/(4(N+1)) + order-(N+1) derivative decay `Ke^{−δR}` ⟹ ray
  decay at rate **min σ δ** with explicit constant
  `2e^{6(N+1)}Ce^σ + 2Ke^δ/(N+1)!` — no 6c loss, reuses the banked
  count-generic `norm_le_window_of_sampled` verbatim. Fixed-N node
  demand matches the fixed-N prime supply exactly.
  **`RHTower.norm_le_ray_of_primeLog_sampled_decay`**
  (`WeightedEulerPrimeOversampling.lean`): H entire + window derivative
  bounds + sampled decay `‖H(log p)‖ ≤ C·p^{−σ}` at ALL primes ⟹
  `‖H(x)‖ ≤ C′e^{−(min σ δ)x}` for x large. UNCONDITIONAL (8a). Both
  first-compile clean, standard axioms, builds 2706/8539 jobs, index
  regenerated.
  **Downstream consequence:** the α-instantiation
  (`lambert_derivative_window_bound`, order ⌊cR⌋+1) needs its fixed-order
  companion: order-(N+1) Lambert window derivative bound
  `≤ K_N·e^{−δR}` (elementary: term-by-term differentiation gives
  `Σ|c_k|λ_k^{N+1}e^{−λ_k R} ≤ M^{N+1}‖L‖e^{−δR}` — check the existing
  proof's structure and restate at fixed order). Then the (8a)→(14)→(16)
  chain runs at rate min(σ, δ) > β as required by
  `compactFourierBorel_eq_zero_of_ray_decay` whenever the carrier depth
  δ exceeds the carrier bound β — verify this consistency when wiring.
- **NEXT:** (i) fixed-order α-instantiation (Lambert window derivative
  bound at order N+1); (ii) wire (8a)+(α)+(7) into the vanishing theorem
  (5b-iii instance); (iii) 5c(ii-b) part 2 joint product-space capstone;
  (iv) (18)/(19) corollaries.

- **[DONE 2026-07-24] Fixed-order α-instantiation.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerLambertWindowDerivativesFixed.lean`
  (umbrella-registered, build clean 8618 jobs, standard axioms, index
  regenerated, first-compile clean).
  **`lambert_derivative_window_bound_fixed`**: for carrier constants
  `δ ≤ M` and ANY fixed order `N+1`, the order-(N+1) derivative of
  `compactCarrierLambertTransform` is `≤ 4‖L‖e^{−(δ/2)R}` on `[R,R+1]`
  for all `R ≥ max(4M(N+1)/δ, 2log2/δ)` — the `hder` input of the
  fixed-order transfer with `K = 4‖L‖`, rate `δ/2`. No node-density
  parameter `c` at all.
- **[INTERFACE FINDING 2026-07-24] The (ii)-wiring blocker: global vs
  half-plane analyticity.** `norm_le_ray_of_sampled_decay_fixed` (and
  the whole SampledSmallComplex chain) hypothesizes `Differentiable ℂ H`
  GLOBALLY, but `compactCarrierLambertTransform` is analytic only where
  `‖compactExponentialTest‖ < 1` (a right half-plane). Inspection of
  `norm_le_of_sampled_small_complex` shows global analyticity is used
  ONLY through (a) `contDiff_comp_ofReal` (smoothness of the real
  restriction) and (b) `iteratedDeriv_comp_ofReal` (real=complex
  derivative identification on ℝ) — the interpolation core
  `abs_le_of_sampled_small` is a REAL lemma. REFACTOR PLAN (next):
  (R1) check `abs_le_of_sampled_small`'s smoothness hypothesis; localize
  to `ContDiffOn ℝ (N+1) (Icc a (a+1))` if global (Taylor remainder is
  interval-local).
  (R2) `norm_le_of_sampled_small_smooth`: version for g : ℝ → ℂ with
  real smoothness + real iteratedDeriv bounds (complex-free core;
  the hkey/re-im projection argument works verbatim).
  (R3) window + fixed-ray-transfer variants over the real interface.
  (R4) Lambert instance: half-plane `AnalyticAt` ⟹ restriction
  smoothness on (T₀,∞) + local derivative identification (induction
  as in `iteratedDeriv_comp_ofReal` but at analytic points), then
  wire (8a): sampled-at-primes Lambert decay ⟹ ray decay at
  `min σ (δ/2)`, nodes from the PNT supply.
- **NEXT:** (R1)–(R4) above; then 5b-iii vanishing instance; then
  5c(ii-b) part 2 capstone; (18)/(19).

- **[DONE 2026-07-24] (R1) — localized sampled-smallness via bump extension.**
  `formal/GaloisForLFunctions/HTGeometry/SampledSmallLocalization.lean`
  (HTGeometry umbrella, build clean, standard axioms, index regenerated).
  **`abs_le_of_sampled_small_of_contDiffOn`**: the interpolation estimate
  with smoothness only on an open interval `(c, d) ⊇ [a, a+1]`. Mechanism:
  NOT a refactor of the iterated-Rolle engine (which needs global
  continuity of all iterated derivatives) — instead a `ContDiffBump`
  multiplication: bump `≡ 1` on `[a−ε/4, a+1+ε/4]`, supported in
  `ball(a+1/2, 1/2+3ε/4) ⊂ (c,d)` (`ε := min(a−c, d−(a+1))`); the bumped
  function is globally smooth (product on `dist < 1/2+ε`, locally zero
  on `dist > 1/2+7ε/8`), agrees with `f` near the window, so
  `Filter.EventuallyEq.iteratedDeriv_eq` transports the derivative
  bounds and the estimate verbatim. Lean notes: `bump.rIn/rOut`
  projections need explicit `rfl` bridges for linarith; bump instance
  needs `Mathlib.Analysis.Calculus.BumpFunction.InnerProduct` import.
- **NEXT (R2–R4):** (R2) complex layer: `norm_le_of_sampled_small_complex`
  variant with `hH : ∀ t ∈ Ioo c d ×ℝ-segment, AnalyticAt ℂ H t`-style
  hypothesis — needs the LOCAL `iteratedDeriv_comp_ofReal` (restriction
  derivative identification at points where H is analytic on a ℂ-nbhd;
  mirror the global induction in SampledSmallComplex). (R3) window +
  fixed-order transfer over the local interface. (R4) Lambert instance
  (analytic on the contractivity half-plane) + prime nodes ⟹
  unconditional (8a) for the actual transform, rate min(σ, δ/2).

- **[DONE 2026-07-24] (R2) — smooth-curve window estimate + half-plane
  restriction bridge.**
  `formal/GaloisForLFunctions/HTGeometry/SampledSmallSmooth.lean`
  (HTGeometry umbrella, build clean 2704 jobs, standard axioms, index
  regenerated; only fix round was an unused-hypothesis lint rename).
  Three lemmas:
  1. **`norm_le_of_sampled_small_smooth`**: the complex window estimate
     for an arbitrary globally smooth curve `g : ℝ → ℂ` with REAL
     iterated-derivative bounds — the re/im projection argument never
     needed analyticity, only `iteratedDeriv_clm_comp` (global smooth).
  2. **`contDiffOn_comp_ofReal_of_analyticAt`**: `H` analytic on
     `{Re > T}` ⟹ restriction `t ↦ H(t)` is `ContDiffOn ℝ ⊤ (Ioi T)`
     (AnalyticAt.contDiffAt + restrict_scalars + ofReal comp).
  3. **`iteratedDeriv_comp_ofReal_of_analyticAt`**: on `Ioi T`, real
     iterated derivatives of the restriction = complex iterated
     derivatives — the LOCAL form of the entire-function identification,
     by the same induction with `Filter.EventuallyEq.iteratedDeriv_eq`
     over `Ioi_mem_nhds` and `AnalyticAt.deriv` for the inductive step.
- **NEXT (R3+R4 — the assembled Lambert (8a))**: per window `[R, R+1]`
  (`R > T+1`), define `g_R := bump_R · (H∘ofReal)` (R1-pattern bump,
  globally smooth via lemma 2, `=ᶠ H∘ofReal` near the window):
  `norm_le_of_sampled_small_smooth` + lemma 3 transports the complex
  derivative bounds (fixed-order α) and prime-node samples; assemble the
  fixed-order ray transfer over these window instances (mirror
  `norm_le_ray_of_sampled_decay_fixed`'s outer loop, replacing
  `norm_le_window_of_sampled` by the bumped-window instance); instantiate
  H := compactCarrierLambertTransform (analytic where the exponential
  test is contractive — check the corpus lemma giving `‖test‖ < 1` for
  `Re z` large: rg compactExponentialTest bounds) + prime nodes ⟹
  unconditional (8a) for the transform at rate min(σ, δ/2). Then 5b-iii
  vanishing instance; 5c(ii-b) capstone; (18)/(19).

- **[DONE 2026-07-24] (R3) — real-axis-analytic window estimate + ray
  transfer.**
  `formal/GaloisForLFunctions/HTGeometry/SampledRayRateTransferHalfplane.lean`
  (HTGeometry umbrella, first-compile clean, build 2718 jobs, standard
  axioms, index regenerated).
  **`norm_le_window_of_sampled_halfplane`** and
  **`norm_le_ray_of_sampled_decay_fixed_halfplane`**: the fixed-order
  window estimate and ray transfer with entirety weakened to
  `hH : ∀ t : ℝ, T < t → AnalyticAt ℂ H t` — analyticity AT REAL POINTS
  only (each AnalyticAt carries its own ℂ-neighborhood). Mechanism:
  per-window ℂ-valued bump curve `g = bump • (H∘ofReal)` (R1 pattern,
  `smul` smoothness), R2's smooth window estimate + local derivative
  identification, then the fixed-transfer outer loop verbatim.
  IMPORTANT ROUTE CORRECTION discovered en route: the Lambert transform
  is NOT analytic on a full half-plane — the contractivity region
  `‖compactExponentialTest‖ < 1` is conical (`(z·s k).re ≥ δ·Re z −
  M·|Im z|`). The R2/R3 hypotheses were therefore weakened from
  half-plane to real-axis analyticity (a mechanical sed patch — the
  proofs only ever evaluate hH at real points), which the transform DOES
  satisfy: at real t > 0, `(t·s k).re = t·(s k).re ≥ tδ > 0`, so
  `norm_compactExponentialTest_lt_one_of_re_pos` (banked in
  CompactCarrierLambert) supplies AnalyticAt via
  `compactCarrierLambertTransform_analyticAt`.
- **NEXT (R4 — the assembled unconditional Lambert (8a))**: instantiate
  `norm_le_ray_of_sampled_decay_fixed_halfplane` with
  H := compactCarrierLambertTransform L s, T := 0:
  hH from analyticAt + test-contractivity at real t > 0 (check the
  `d`-hypothesis shape of `norm_compactExponentialTest_lt_one_of_re_pos`:
  needs ∀k, d ≤ (z·s k).re with d > 0 — at z = t: d := t·δ ✓);
  hder from `lambert_derivative_window_bound_fixed` (K = 4‖L‖, rate δ/2,
  R₀ ≥ max(4M(N+1)/δ, 2log2/δ, 1));
  hnodes from `exists_separated_primeLog_nodes_unconditional` + Lambert
  sampled decay hypothesis at prime logs (the (7) interface) ⟹
  `‖transform(x)‖ ≤ C′e^{−min(σ, δ/2)x}` unconditionally. Then 5b-iii
  vanishing instance; 5c(ii-b) capstone; (18)/(19).

- **[DONE 2026-07-24] (R4) — ★ THE UNCONDITIONAL LAMBERT OVERSAMPLING
  (8a) IS COMPLETE ★.**
  `formal/GaloisForLFunctions/RHTower/WeightedEulerLambertOversampling.lean`
  (umbrella-registered, FIRST-COMPILE CLEAN, build clean, standard
  axioms, index regenerated).
  **`norm_le_ray_of_primeLog_sampled_lambert`**: for a compact carrier
  with real-part floor `δ`, norm ceiling `M`, any fixed order `N+1`, and
  sampled decay `‖Λ_L(log p)‖ ≤ C·p^{−σ}` at ALL primes:
  `‖Λ_L(x)‖ ≤ C′·e^{−min(σ, δ/2)·x}` for all `x` past the explicit
  threshold `max(4M(N+1)/δ, 2log2/δ, Rn, 1) + 1` — NO analytic
  hypotheses remain; the prime nodes come from the formalized elementary
  PNT. Assembly: real-axis analyticity via
  `norm_compactExponentialTest_lt_one_of_re_pos` at `d := tδ`
  (`(↑t·s k).re = t·(s k).re` by `Complex.mul_re` simp); hder from the
  fixed-order α; hnodes from
  `exists_separated_primeLog_nodes_unconditional` with `p^{−σ} ≤ e^{−σR}`
  at nodes ≥ R; outer transfer =
  `norm_le_ray_of_sampled_decay_fixed_halfplane` at `T = 0`.
  **Chain now closed end-to-end:** dual reduction (7) ⟹ [THIS] ⟹
  Möbius recovery (14) (`norm_fourierBorel_le_of_lambert_ray_decay`) ⟹
  carrier separation (15)–(16)
  (`compactFourierBorel_sub_eq_zero_of_ray_decay`) — every link
  unconditional, standard axioms.
- **NEXT:** wire the closed (8a)→(14)→(16) chain into the 5b-iii
  vanishing instance with the dual-reduction sample decay (7) as input
  (check rate consistency min(σ, δ/2) > carrier bound β — the (7)
  interface fixes σ; choose the carrier so δ/2 > β); then 5c(ii-b)
  part 2 joint product-space capstone
  (`topologicalClosure_eq_top_of_forall_dual_eq_zero` + annihilator
  chain); then (18)/(19) corollaries — after which THIS CARD is fully
  formalized.

- **[ROUTE RE-EVALUATION 2026-07-24 — the fixed-order (8a) is NOT
  sufficient for (16); power-log PNT is genuinely required.]**
  Rate audit of the closed chain: the FE-vanishing
  (`compactFourierBorel_sub_eq_zero_of_ray_decay`) needs ray decay at
  σ₀ > β (carrier Re-ceiling). The fixed-order (8a)
  (`norm_le_ray_of_primeLog_sampled_lambert`) caps at min(σ, δ/2) with
  δ the carrier Re-FLOOR — and δ ≤ β always, so min(σ, δ/2) < β
  unconditionally: the cap is intrinsic (Lambert derivative bounds decay
  at rate δ — Cauchy over sector discs — and a FIXED-order interpolation
  remainder inherits that rate). Only the growing-order transfer
  (`norm_le_ray_of_sampled_decay`, order ⌊cR⌋+1, superexponential
  remainder) delivers σ′ = σ − 6c > β. Its node demand: ⌊cR⌋+1 separated
  prime logs per unit window — VERIFIED not obtainable from o(x)-PNT
  even via free (non-grid) separated-node selection: o(x) forces primes
  only in fixed-relative-width windows, giving O(1) separated nodes.
  ⟹ THE remaining deep input: **ψ(x) = x + O(x/log^B x) (B ≥ 2)** —
  spun off as new card
  `1-in-progress/pnt-power-log-error-quantitative-selberg.md`
  (elementary route: quantitative Selberg/Wirsing—Bombieri iteration on
  top of the formalized symmetry+recursion corpus).
  The fixed-order chain artifacts remain valid and reusable theorems
  (and the α/R1–R4 localization machinery is exactly what the
  growing-order Lambert instantiation will need too — the growing-order
  transfer has the SAME global-entirety defect, to be fixed by the same
  bump route: `norm_le_window_of_sampled` count-generic + halfplane
  wrapper generalizes verbatim to order ⌊cR⌋+1).
  Meanwhile INDEPENDENT of (8a): 5c(ii-b) part 2 joint capstone and
  (18)/(19) corollaries — proceed in parallel.

- **[FRONTIER CORRECTION 2026-08-09 — the power-log PNT is already in the tree, twice.]**
  The route re-evaluation above names `ψ(x) = x + O(x/log^B x)` (`B ≥ 2`) as "THE remaining deep
  input" and spins it off to `1-in-progress/pnt-power-log-error-quantitative-selberg.md`. That card
  does not exist, and the input does — in two independent unconditional forms:

  - `RHTower.exists_chebyshevPsi_power_log`
    (`formal/GaloisForLFunctions/RHTower/ChebyshevPsiPowerLogPNT.lean`):
    `|ψ(⌊x⌋) − x| ≤ C·x·exp(−c·(log x)^{1/10})` for `x ≥ x₀`, by Perron unsmoothing of the
    tent-sum estimate with step `h = e^{−c₀u/4}`, `u = (log x)^{1/10}`;
  - the vendored `GaloisForLFunctions.PNTPlus.MediumPNT`:
    `(ψ − id) =O[atTop] fun x ↦ x·exp(−c·(log x)^{1/10})`, sorry-free and axiom-clean per
    `PNTPlus/PROVENANCE.md`.

  Either is strictly stronger than the demanded `O(x/log^B x)` for *every* `B`, because
  `L^B·exp(−c·L^{1/10}) → 0` as `L → ∞`.

  The growing-order consumers the re-evaluation asks for were built alongside it:
  `RHTower.exists_separated_primeLog_nodes_growing`
  (`RHTower/GrowingOrderPrimeLogNodes.lean`) supplies `⌊c₁R⌋+1` separated prime logs per unit
  window, and `RHTower.norm_le_ray_of_primeLog_sampled_decay_growing`
  (`RHTower/WeightedEulerGrowingPrimeOversampling.lean`) is the growing-order transfer;
  `RHTower/WeightedEulerAnnihilatorOversamplingCarrierEliminationUniversalityLaw.lean` then carries
  `compactFourierBorel_eq_zero_of_primeLog_graph_annihilation`.

  The card's "NEXT" list is therefore stale and must be re-audited declaration by declaration
  against the tree before any further mathematics is attempted here. The open work is the wiring
  and the `(18)`/`(19)` corollaries, not a quantitative prime number theorem.

- **[2026-08-09 — the growing-order carrier elimination is now Lean, and it is not vacuous.]**
  The fixed-order law
  `compactFourierBorel_eq_zero_of_primeLog_graph_annihilation` needs `β < min σ (α/2)`, and the
  companion `not_beta_lt_min_sigma_half_alpha_of_nonempty_positiveStrip` proves that hypothesis has
  no nonempty-strip instance: the walls force `α ≤ β`. Three new modules replace it by the
  growing-order route, whose rate hypothesis is the satisfiable `β < σ`.

  `HTGeometry/SampledRayRateTransferGrowingHalfplane.lean` —
  **`norm_le_ray_of_sampled_decay_halfplane`**: the growing-order transfer of
  `SampledRayRateTransfer` with global entirety weakened to analyticity on `{Re > T}`. The
  smooth-bump window estimate `norm_le_window_of_sampled_halfplane` is already order-generic, so
  the `⌊cR⌋ + 1` bookkeeping goes through unchanged — this is the "same bump route" the route
  re-evaluation predicted, and it removes the global-entirety defect that blocked the growing-order
  transfer for Lambert-type transforms.

  `RHTower/WeightedEulerGrowingCarrierElimination.lean` —

  - **`compactFourierBorel_eq_zero_of_lambert_ray_decay`**: the carrier-elimination core with the
    ray rate `κ` abstract; from `β < κ` and a Lambert ray bound at rate `κ`, the Möbius recovery,
    the two-sided decay extension and `compactFourierBorel_eq_zero_of_ray_decay` give
    `F_B ≡ 0` and `L(sᵐ) = 0` for every `m`;
  - **`norm_le_ray_of_primeLog_sampled_decay_growing_halfplane`**: growing-order prime-log
    oversampling for a half-plane analytic function, feeding
    `exists_separated_primeLog_nodes_growing` into the transfer above;
  - **`compactCarrierLambertTransform_analyticAt_pos`**: on a carrier with positive real-part
    floor the exponential test is contractive at every positive real point, so `T = 0` works;
  - **`compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_growing`** — the law:

    ```text
    0 < α, ∀ k, α ≤ Re(s k) ≤ β, β < σ,
    ∀ p prime, lam p + L (compactPrimeEulerUnitTangent s p) = 0,
    ∀ p prime, ‖lam p‖ ≤ C · log p · p^(-σ)
      ⟹ (∀ z, compactFourierBorel L s z = 0) ∧ ∀ m, L (s ^ m) = 0
    ```

  The node density is chosen inside the proof as `c = min (α/(8M)) ((σ−β)/12)` with
  `M = max α ‖s‖`, so the interpolation loss `6c` leaves ray rate `σ − 6c ≥ (σ+β)/2 > β`. The
  `α/2` cap is gone: it was an artifact of the fixed derivative order, exactly as diagnosed.

  All four declarations are unconditional; `#print axioms` reports only `propext`,
  `Classical.choice`, `Quot.sound`; both modules are umbrella-wired.

  The critical-boundary instance is the case the card is actually about, and it is now closed:

  > **`compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_critical`** — for a nonempty
  > compact carrier with `0 < α ≤ Re(s k) ≤ β < 1` and the `T₁`/`M₀` dual bound
  > `‖lam p‖ ≤ C·criticalNorm (primeCoordinateField p)`, prime-indexed graph annihilation forces
  > `compactFourierBorel L s ≡ 0` and `L (sᵐ) = 0` for every `m`.

  The critical dual reduction fixes `σ = 1` (`norm_lambert_primeLog_le_of_graph_annihilation_critical`
  gives Lambert samples `≤ C/p`), and the card's carrier is compactly contained in `Re s < 1`, so
  `β < σ` holds automatically. This is `(7) → (14) → (16)` at the critical boundary, unconditional
  and axiom-clean. What remains on the card is the joint product-space capstone `(3)` and the
  `(18)`/`(19)` corollaries — no further analytic input.

## 2026-08-09 — the joint-closure criterion is formalized

`formal/GaloisForLFunctions/HTGeometry/JointDenseOfVanishingDual.lean`, unconditional and
axiom-clean:

- `apply_eq_inl_add_inr` — a continuous functional on a product splits as the sum of its
  restrictions to the two factors;
- **`topologicalClosure_eq_top_of_forall_pair_dual_eq_zero`** — if the only *pair* `(f₁, f₂)` of
  continuous functionals with `f₁ x + f₂ y = 0` throughout a subspace of `E × F` is the zero pair,
  then that subspace is dense in the product.

This is exactly the shape of `(3)`, `(18)` and `(19)`: the card stresses that joint closure "is not
a consequence of density of the two projections", and the reason is visible in the criterion — the
annihilator of a subspace of a product is a set of *pairs*, and projection density only kills pairs
of the forms `(f₁, 0)` and `(0, f₂)`.  What excludes the intermediate closed subspaces is the
absence of a genuinely mixed annihilating pair, which is what the carrier-elimination theorems
supply.

Remaining for `(3)`/`(18)`/`(19)`: instantiating the two factors — the weighted coefficient space
and the holomorphic regular-flux space on the quadrant — and feeding the carrier-elimination
vanishing into this criterion.

### The `(18) → (19)` step is formalized

Same module, unconditional and axiom-clean:

- `closure_add_left_image` — translation commutes with closure, being a homeomorphism;
- **`dense_affine_of_topologicalClosure_eq_top`** — if a subspace is dense then every affine
  translate of it fills the space.

That is exactly the passage from the group closure `(18)` to the affine closure `(19)`
`= (1 + M₀) × O(Q₊)_R`: once the linear joint closure is known, the affine statement is a
translation and needs no new analysis.  So of the three remaining items, `(19)` follows from `(18)`
outright, and `(18)`/`(3)` both reduce to the pair criterion above.

What is genuinely left is the instantiation: the coefficient factor is a Banach space, but the
regular-flux factor `O(Q₊)_R` is a Fréchet space of holomorphic functions, so feeding it into the
criterion needs the locally convex form of the separation argument, with the analytic functionals of
the `compactFourierBorel` layer as the second component of the annihilating pair.

### The Fréchet obstacle is removed

`formal/GaloisForLFunctions/HTGeometry/LocallyConvexDenseOfVanishingDual.lean`, unconditional and
axiom-clean:

- `exists_dual_vanishing_of_notMem_closed_submodule_lcs`;
- `topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs`;
- **`topologicalClosure_eq_top_of_forall_pair_dual_eq_zero_lcs`** — the joint criterion with **no
  normed hypothesis on either factor**: any locally convex real topological vector spaces will do.

The norm was never needed.  `geometric_hahn_banach_closed_point` separates a point from a closed
convex set in any locally convex space, and the argument that a functional bounded above on a
subspace vanishes on it is scaling, not estimation.  So the criterion applies with the second factor
`O(Q₊)_R` a Fréchet space of holomorphic functions, which was the stated obstacle to instantiating
`(3)` and `(18)`.

What remains is now purely the concrete instantiation: exhibit the two factors with their locally
convex structures, define `Γ_fin` as a submodule of the product, and feed
`compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_critical` in as the vanishing of the
mixed annihilating pair.

### `(3)` in generated form

**`topologicalClosure_span_eq_top_of_pair_dual_lcs`** (same module), unconditional and axiom-clean:
for a family of pairs `(e_i, v_i)` in a product of locally convex spaces, the span is dense as soon
as the only pair of functionals annihilating **every generator** is the zero pair.

This is `(3)` in the form the card actually uses.  `Γ_fin` is the set of finite prime-support
combinations, i.e. the span of the generators `p ↦ ((log p/p)·δ_p, u_p)`, and the annihilation
hypothesis is checked one prime at a time — which is precisely the prime-indexed graph annihilation
`lam p + L(compactPrimeEulerUnitTangent s p) = 0` that the carrier-elimination theorems consume.

The chain for `(3)`/`(18)`/`(19)` is therefore complete at the level of criteria:

```text
prime-indexed annihilation  ──(carrier elimination)──▶  the pair is zero
        └──(topologicalClosure_span_eq_top_of_pair_dual_lcs)──▶  (3), (18)
                └──(dense_affine_of_topologicalClosure_eq_top)──▶  (19)
```

Only the concrete construction of the two factor spaces remains.

### The coefficient factor's annihilator computation

`formal/GaloisForLFunctions/HTGeometry/LpSingleAnnihilator.lean`, unconditional and axiom-clean:

**`eq_zero_of_forall_apply_lp_single`** — on `lp E p` with `p ≠ ∞`, a continuous functional
vanishing on every single-support element vanishes identically.

This is the first factor of the pair criterion, done: the weighted coefficient space is a weighted
`ℓ¹` over the primes, its single-support elements are the scaled Dirac masses `(log p/p)·δ_p` that
generate `Γ_fin`'s first component, and mathlib's `lp.hasSum_single` writes every element as the
unbounded sum of those pieces, which a continuous functional preserves.

So in the pair `(f₁, f₂)`, once the carrier elimination forces `f₂ = 0`, the surviving condition
`f₁((log p/p)·δ_p) = 0` for every prime gives `f₁ = 0` by this lemma.  The remaining construction is
the second factor alone.

### From the elimination's conclusion to the vanishing of the functional

`formal/GaloisForLFunctions/HTGeometry/VanishingOnClosedSpan.lean`, unconditional and axiom-clean:

- **`eq_zero_on_topologicalClosure_span`** — a continuous linear map vanishing on a set vanishes on
  the closed span of that set (its kernel is a closed submodule);
- **`eq_zero_of_topologicalClosure_span_eq_top`** — hence it is zero when that closed span is
  everything.

This is the step the carrier-elimination conclusion needs.  Those theorems deliver
`L (sᵐ) = 0` for every `m` and `compactFourierBorel L s ≡ 0`; what turns a family of scalar
identities into `L = 0` is exactly the passage to the closed span, and then a density statement for
the generating family.  Note also that the flux side of the elimination lives on `C(K, ℂ)` for a
compact carrier `K` — a Banach space — so the Fréchet structure of `O(Q₊)_R` enters only in the
card's statement, not in the route through compactly carried functionals.

## 2026-08-13 — the joint closures `(3)`, `(18)`, `(19)` are formalized; card complete

`formal/GaloisForLFunctions/RHTower/WeightedEulerJointClosure.lean`, unconditional and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only):

- **`RHTower.weightedEuler_helim`** — the dual reduction, unconditionally: if a continuous pair
  `(λ, ℓ)` annihilates every generator of the finite-support joint graph, then `ℓ = 0` on the whole
  quadrant space.
- **`RHTower.topologicalClosure_primeQuadrantGraph_eq_top'`** — equation `(3)`:
  `closure(Γ_fin) = T × O(Q₊)_R`.
- **`RHTower.closure_primeQuadrantGraph_eq_univ`** — equation `(18)`, the same closure for the
  generated group.
- **`RHTower.closure_affine_primeQuadrantGraph_eq_univ`** — equation `(19)`, the affine form:
  every translate of the joint graph is dense.

The route differs from the card's narrative in one place, and the difference is a genuine
correction.  The corpus's carrier elimination consumes the *unsymmetrised* Euler tangent
`w_p(s) = (log p) p^{-s}/(1 − p^{-s})²`, whereas the graph generator is the symmetrised
`u_p = w_p(s) − w_p(1 − s)`.  The functional actually fed to the elimination is therefore
`B = A − R∗A` with `R s = 1 − s`, carried by the four blocks
`([a,b] ∪ [1−b,1−a]) × ([c,d] ∪ [−d,−c])`, all inside `0 < Re < 1`; its Cauchy transform is
`Ĉ_B(v) = Ĉ_A(v) + Ĉ_A(1 − v)`.  Consequently the closure needs **two** separations, not one:
a vertical one across the critical line and a horizontal one across the real axis.

Supporting layers, all unconditional and axiom-clean:

- `HTGeometry.CompactOpenDualCarrier` — a continuous functional on a subspace of `C(X, ℂ)` is
  dominated by the supremum seminorm of a single compact set.
- `HTGeometry.FactorThroughRange`, `HTGeometry.CarrierComplexFunctional` — factoring through a
  range, Hahn–Banach, and complexification: a dominated real functional is the real part of a
  complex functional on `C(K, ℂ)`.
- `HTGeometry.QuadrantReflectedCarrier` — every compact subset of the quadrant sits in a rectangle
  inside it; the conjugation-symmetric double; preconnectedness of the complements of a rectangle
  and of a doubled rectangle; the separating strip.
- `HTGeometry.ContinuousMapCauchyTransform` — the Cauchy transform as the functional of the
  resolvent unit of the Banach algebra `C(K, ℂ)`, its holomorphy off the carrier, its size, and its
  vanishing outside a disc when every power of the coordinate is killed.
- `HTGeometry.ReflectedCarrierFunctional` — conjugation transfer, the doubled functional, the
  conjugate functional, the reflection pullback, and the three Cauchy-transform identities.
- `HTGeometry.CauchyTransformGluing`, `HTGeometry.CauchyTransformGluingVertical` — two transforms
  opposite on a separating strip glue to an entire function which Liouville and the identity
  theorem force to vanish.
- `HTGeometry.CarrierAnnihilatesHolomorphic` — the rectangle Cauchy formula in boundary-integral
  normalisation, and: a functional with vanishing Cauchy transform annihilates every function
  holomorphic on a rectangle containing its carrier.
- `RHTower.WeightedEulerCarrierTangent`, `…CarrierSetup`, `…CarrierBlocks`, `…CarrierFunctionals`,
  `…CarrierGraph`, `…CarrierVanishing` — the carrier data of a quadrant functional, its four
  blocks, the doubled/reflected/total functionals, the discharge of the carrier elimination, and
  the vanishing of the transform off the carrier.

Sections 1–3 and 5 of this card are now formalized end to end; Section 4 is a negative audit of a
literature argument, not a theorem.

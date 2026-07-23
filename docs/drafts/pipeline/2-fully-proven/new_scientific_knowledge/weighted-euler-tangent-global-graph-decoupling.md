# Weighted Euler tangent and global strip germ decouple jointly

- **ID:** `weighted-euler-tangent-global-graph-decoupling`
- **Stage:** 2-fully-proven / candidate-new
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

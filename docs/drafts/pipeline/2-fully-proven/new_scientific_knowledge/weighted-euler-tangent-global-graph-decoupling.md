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

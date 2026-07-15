# Gamma--Meixner star-Kadison curvature trace and the Landau RH boundary

- **ID:** `gamma-meixner-kadison-curvature-landau-rh`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / HTGEOMETRY-TO-RHTOWER TRANSFER / RH ROUTE
- **Scientific status:** `[CONJECTURE] [DOWNSTREAM IMPLICATION PROVED]
  [TARGET CLOCK FACTORIZATION PROVED ON PAPER] [FINITE CLOCK ALGEBRA FORMALIZED]
  [SOURCE TRACE OPEN] [NOVELTY UNVERIFIED]`
- **HT parents:**
  - `calibrated-gamma-mertens-zero-orbit-comparison-rh.md`
  - `../3-formalized/finite-clock-star-kadison-observability.md`
  - `../3-formalized/gamma-periodic-constraint-corona.md`
  - `calibrated-clock-curvature-class.md`
  - `constraint-curvature-integration-stack.md`
- **RH parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/archimedean-meixner-root-seam-scale.md`
  - `../2-fully-proven/not_new_scientific_knowledge/meixner-root-prime-laplace-value-frame.md`
  - `../2-fully-proven/not_new_scientific_knowledge/xi-global-meixner-shape-landau-rh.md`
  - `../2-fully-proven/not_new_scientific_knowledge/xi-reciprocal-translation-prime-seam-norm-law.md`
  - `../2-fully-proven/not_new_scientific_knowledge/xi-gamma-shape-completely-monotone-rh.md`
  - `../2-fully-proven/not_new_scientific_knowledge/gamma-meixner-abel-mertens-corona-probe.md`
  - `../2-fully-proven/not_new_scientific_knowledge/rational-hurwitz-lorentz-boost-colligation.md`
  - `../2-fully-proven/not_new_scientific_knowledge/local-euler-valuation-lorentz-log-colligation.md`
  - `../2-fully-proven/not_new_scientific_knowledge/gamma-factorial-fock-polarization-boundary-charge.md`
  - `../2-fully-proven/not_new_scientific_knowledge/prime-laplace-gamma-jet-incidence-phase-transition.md`
  - `../2-fully-proven/not_new_scientific_knowledge/time-one-gamma-jet-fock-rh-criterion.md`
  - `../2-fully-proven/not_new_scientific_knowledge/prime-laplace-gamma-clock-descent-anomaly.md`
  - `../2-fully-proven/not_new_scientific_knowledge/mertens-corona-shift-conormal.md`
- **Statement:** Realize the global Xi prime-seam series as the cofinal reflected
  star-Kadison trace of the source-derived Gamma--Meixner clock-curvature field.  If this trace is
  a locally bounded holomorphic family for every positive Gamma shape, then Landau's theorem
  excludes every off-line Xi zero and proves RH.

## Exact RH consumer

For a prime `p`, let

```text
lambda_p=(1/2) log(cosh(2 log p)),
w_z(p)=exp(-z lambda_p),                                  (1)
```

and let the nonnegative coefficient `A_p` be the complete multiplicity-weighted Xi seam energy
from `xi-global-meixner-shape-landau-rh.md`.  On `Re(z)>1` the series

```text
G_Xi(z)=sum_p A_p w_z(p)                                  (2)
```

converges absolutely.  The proved Landau theorem gives

```text
G_Xi has a holomorphic continuation to Re(z)>0
  -> RH.                                                  (3)
```

Indeed, any off-line zero forces a strictly positive abscissa of convergence, which is a real
singularity because every `A_p` is nonnegative.

For real `theta>0`, `w_theta(p)` is not an artificial damping.  It is the pointed prime diagonal
of the Gamma--Meixner convolution measure with characteristic function

```text
phi_theta(t)=cosh(t)^(-theta/2),
phi_(theta+eta)=phi_theta phi_eta.                         (4)
```

Thus `(2)` asks for analytic control in an actual archimedean source parameter.

## Exact target-side two-cycle clock `[PROVED ON PAPER]`

The target trace already has a canonical star-Kadison factorization; the problem is to obtain it
from the source before constructing the divisor metric.

Let `q` run over Xi divisor copies, let `iota(q)` be critical-line reflection, and put

```text
y_q=Im(xiSpectralPoint(q)),
r_q=|xiSpectralPoint(q)|,
x_L(q)=exp(L y_q)/r_q.                                   (5)
```

The reflection laws give `y_(iota q)=-y_q` and `r_(iota q)=r_q`.  Let `R` be the linear isometry
which permutes coordinates by `iota`, and let

```text
P=(1+R)/2.                                                (6)
```

Since `R^2=1`, `P` is the stationary projection of the two-cycle clock.  Direct summation gives

```text
||(1-P)x_L||^2
 =1/4 sum_q |x_L(q)-x_L(iota q)|^2
 =1/2 (N(L)-N(0)),                                      (7)
```

where `N(L)` is the reciprocal-Cauchy translation norm.  Consequently, at `L=log p`,

```text
A_p=4(log p)^2/p * ||(1-P)x_(log p)||^2.                 (8)
```

The finite-clock star-Kadison theorem realizes the last norm exactly as

```text
Re <psi,D*_R(X_p)psi>,
X_p psi=(2 log p/sqrt(p)) x_(log p),                     (9)
```

for any fixed unit vector `psi` and a rank-one bounded operator with the displayed value.  Thus
the constants, reflection clock, and erased vector are forced.  This is not an RH proof: `x_L`
and its norm in `(5)` are divisor-defined.  The source problem is precisely to construct the same
clock vector and metric from the prime--Gamma constraint and then prove the trace identification.

## Source-trace conjecture

`[CONJECTURE]` There is a source-defined cofinal family

```text
T_N(z),       Re(z)>0,                                   (10)
```

of finite-rank reflected star-Kadison curvature traces with these properties.

1. **Pre-divisor construction.**  `T_N(z)` is formed only from:

   - the prime-power Euler tangent and its finite observation clocks;
   - the Gamma translation constraint and its calibrated rank-one clock curvature;
   - the Gamma--Meixner shape kernel `(4)`;
   - the completed reflection and affine contact normalization.

   No Xi zero, Xi divisor Hilbert space, or fitted contraction is used in its definition.

2. **Finite positive realization.**  For real `theta>0`, there are finite cyclic clock unitaries
   `U_(N,theta)`, stationary source states `psi_(N,theta)`, and source observables
   `X_(N,theta)` such that

   ```text
   T_N(theta)
    =Re <psi,
       [Phi_U(X^* X)-Phi_U(X)^* Phi_U(X)] psi>
    =||(1-P_U)X psi||^2 >=0.                            (11)
   ```

   The erased vector in `(11)` must be the reflected prime--Gamma curvature seam, not an abstract
   realization of an already positive scalar.

3. **Safe trace identity.**  On `Re(z)>1`, the cofinal source trace exists and satisfies

   ```text
   lim_(N->infinity) T_N(z)=G_Xi(z).                    (12)
   ```

   The proof of `(12)` must pass through the completed logarithmic source or an equivalent
   source-divisor trace formula; expanding the right side and defining the left from its
   coefficients is not accepted.

4. **Thin-curvature normality.**  The family `(T_N)` is locally uniformly trace-bounded on every
   half-plane `Re(z)>=epsilon>0`.  Hence its cofinal limit

   ```text
   T(z)=lim_N T_N(z)                                    (13)
   ```

   is holomorphic on `Re(z)>0`.

   **Positive real-shape alternative.**  It is enough instead to construct a finite completely
   monotone limit `T(theta)` for every real `theta>0`, agreeing with `(12)` for `theta>1`.  This
   version is preferred if the Gamma--Meixner integration stack produces positive radial
   semigroups but not a complex operator family.

Equations `(12)`--`(13)` and the identity theorem continue `(2)` to `Re(z)>0`; `(3)` then proves
RH.

## Why this is an HT application rather than an RH restatement

The proposed finite field uses two independently formalized HTGeometry features.

1. Gamma unit translation has rank-one curvature under backward finite-jet observation:

   ```text
   kappa_N(a)_i=a_N/(N-i)!.                             (14)
   ```

   This supplies a canonical thin archimedean boundary vector rather than an arbitrary operator
   ideal assumption.
2. A finite-clock star-Kadison defect is exactly erased vector energy for every bounded
   observable, without self-adjointness.  It supplies the positive trace in `(11)` and its
   polarized cross-prime covariance.

The prime-power differential-matroid results supply the complementary fact that every finite
prime direction remains source-visible over any finite-prime coefficient field.  Together these
pieces specify the finite clocks and the thin boundary field.  They do **not** by themselves
prove the local trace bound in item 4; that is the proposed integration theorem for the actual
source-curvature field.

The Gamma--Meixner shape is also fixed by the HT source topology.  The proved Abel-corona theorem
shows that

```text
L_theta(b)=theta sum_p (log p)/p w_theta(p)b_p            (14c)
```

is uniformly bounded on the logarithmic Marcinkiewicz source field, tends to zero on its complete
finite-gauge layer `M_0`, and tends to one on the actual unit Euler field.  Hence `theta down to 0`
approaches the exact Mertens corona class `[one]` left by the weighted Euler joint-graph no-go.
The parameter is an observation of a singular source boundary, not a propagation law for Xi.

There is an important refinement.  The factorial transfer in `(14)` is universal Taylor
translation kinematics: by itself it does not distinguish Gamma from an arbitrary analytic germ.
The source-specific object must therefore be the complete anomaly--boundary colligation

```text
C_N=(T_N,beta_N,delta_N,alpha_N),                         (14a)
```

not bare curvature.  Here `beta_N` is the outgoing factorial transfer, `delta_N` the new-boundary
self-symbol, and `alpha_N=T_N q_N-q_N S` the source descent anomaly.  The finite reconstruction
theorem for `(14a)` is Lean-formalized in the ongoing HTGeometry work.

The finite reflected block is no longer conjectural.  After the common phase and critical
normalization are removed, the FE and Schwarz rational-Hurwitz responses form the exact Lorentz
colligation

```text
B_a(p)=[cosh(a log p) sinh(a log p);
        sinh(a log p) cosh(a log p)],
a=Re(rho)-1/2.                                            (14b)
```

It is `J`-conservative for `J=diag(1,-1)`, reflection sends it to its inverse, and its
anti-invariant transfer is the exact source value

```text
(log p)(p^(-conj rho)-p^(-(1-rho)))=C_p(rho).             (14d)
```

`[CONJECTURE — REFLECTED ANOMALY PASSIVITY]` The completed colligation upgrades this canonical
Krein-conservative block to reflection-passivity in the source Mackey metric, with its
anti-invariant star-Kadison defect dominated uniformly by the factorial Gamma boundary after the
canonical factor `2log(p)/sqrt(p)`.  Cofinal residue evaluation preserves this quadratic value.

The pointwise equality `(14d)` is already formalized through finite rational-Hurwitz fibres, and
the Lorentz colligation is proved on paper.  Its interpretation as the completed descent-anomaly
block, reflection-passivity, and metric preservation remain conjectural.  This formulation is
stronger than naming an abstract positive metric: it fixes the two source coordinates, the
reflection, the boundary transfer, the indefinite conservation law, and the normalization before
any divisor norm is introduced.  A block and its reflected inverse can be contractions in one
positive metric only when `a=0`; hence the proposed metric upgrade is exactly the confinement
mechanism.

## Smallest non-circular theorem

There is now a second, strictly time-one formulation of the smallest theorem.  Define

```text
V_rho(z)=M_1(z+rho)-M_1(z+1-conjugate(rho)),              (14e)
```

where `M_1` is the actual time-one Gamma--Meixner weighted prime-zeta derivative.  For any fixed
`x_0>1`, the proved factorial-jet criterion is

```text
sup_N sum_(j<N)|V_rho^(j)(x_0)|^2/j!<infinity
  iff Re(rho)=1/2.                                       (14f)
```

Off the line, one of the two terms in `(14e)` has an uncancelled simple pole at
`-rho` or `conjugate(rho)-1`; finite factorial jet energy would make its Taylor germ entire.
Therefore it is enough to realize the finite jets in the source anomaly colligation and prove the
uniform bound in `(14f)` on every Xi-zero fibre.  This alternative uses the actual time-one Gamma
measure and all HT observation clocks, replacing the all-root deconvolution by one cofinal clock
estimate.

The coordinate part of the fixed-prime source/divisor incidence is already proved.  Put

```text
B_L(z)=rectangularWindowAmplitude(L,i*z).
```

Sharp-window tomography identifies `B_(log 2)(alpha_q)` with the normalized trailing coefficient
of the continued dyadic prime source at the corresponding reflected pole.  If `b_L` is the vector
of these residue values, then

```text
N(L)-N(0)
 =||b_L||^2+2*Im <v_0,b_L>,                              (15)
```

and the right side is unconditionally nonnegative in the divisor metric.  Thus neither the
individual residue coordinates nor their algebraic identification with `A_2` is open.

The smallest missing theorem is a **source metric contraction**.  Construct, before divisor
insertion, a Gamma-clock completion in which the same normalized dyadic residue current satisfies

```text
Q_source(b_(log 2),v_0)
 =||b_(log 2)||^2+2*Im <v_0,b_(log 2)> <=0,              (15a)
```

and prove that its cofinal metric is the residue metric in `(15)`.  Then the target nonnegativity
and `(15a)` force equality, `A_2=0`, and RH.  The construction must remain defined after a rational
FE--Schwarz orbit insertion, with its quadratic value changing by the inserted residue seam.  This
gauge-covariance test makes `(15a)` orbit-sensitive and rules out a divisor-blind Euler Gram.

A quantitative all-prime alternative is enough.  If `X_(p,N)` is the source curvature observable
with the canonical normalization `2 log(p)/sqrt(p)` and

```text
sup_(p,N) ||X_(p,N) psi||^2 * p/(4(log p)^2) <= C,       (15b)
```

then star-Kadison contractivity bounds its defect by `4C(log p)^2/p`.  An orbit-sensitive safe
trace identification with `A_p` would make the Gamma--Meixner sum finite for every positive shape,
so the completely-monotone criterion below gives RH.  The factorial Gamma boundary proves the
corresponding bare-clock constant is finite; the open point is that the source/residue incidence
preserves this bound.

The next theorem is a two-shape normal-family estimate:

```text
for every epsilon>0 and compact K subset {Re z>=epsilon},
sup_N sup_(z in K)|T_N(z)|<infinity.                   (16)
```

Unlike checking all fibrewise root-domain norms, `(16)` is one source-trace estimate.  It is the
proof-bearing statement.

## Attacks

1. **Hypertranscendence does not orient a metric.**  Maximal differential-algebraic clock
   capacity is compatible with arbitrary reflected Krein index.  The positivity in `(11)` comes
   from the source-selected conditional expectation; it cannot be inferred from HT alone.
2. **Arbitrary star-Kadison redressing.**  Every nonnegative finite scalar can be represented as
   erased energy after choosing `X` and `P`.  Such an existence theorem has no content.  The
   prime-power/Gamma curvature formula and orbit-insertion covariance are mandatory.
3. **Time one does not descend to every root.**  The factorization

   ```text
   w_1(p)=w_theta(p)w_(1-theta)(p)                     (17)
   ```

   requires an unbounded deconvolution by the complementary half-density.  Positivity or
   trace-class control at `theta=1` gives no automatic estimate for `0<theta<1`.
4. **Rank-one Gamma curvature is not a nuclear cofinal theorem.**  Equation `(14)` concerns each
   adjacent jet truncation.  Summability of the complete prime--Gamma curvature trace and local
   boundedness in complex shape remain separate analytic obligations.
5. **Finite-stage holomorphy is insufficient.**  Every finite prime trace is entire in `z`.
   Without `(16)`, its cofinal limit may have exactly the positive Landau boundary forced by an
   off-line zero.
6. **Target-metric circularity.**  Defining the Hilbert norm in `(11)` from the Xi divisor makes
   `(12)` tautological and item 4 equivalent to RH.  The norm must come from the source Mackey
   interval or another pre-divisor completion and then be identified with the divisor trace.
7. **Reflection is not confinement.**  The completed source makes `T_N` self-dual, but a
   self-dual curvature field can retain paired off-fixed degeneracies.  The positive
   star-Kadison orientation and the normal-family theorem are both load-bearing.
8. **Bare Gamma curvature is kinematic.**  Rank-one factorial curvature and its finite Euclidean
   energy occur for universal Taylor translation.  They cannot, without the source anomaly and
   boundary self-symbol, control the arithmetic prime coupling.
9. **Prime-dependent rescaling.**  Even a rank-one curvature vector of uniformly finite energy
   may be multiplied at prime `p` by `p^b`.  Finite rank and levelwise nuclearity survive while
   the Gamma-shape abscissa moves by `2b`.  Thinness at each clock is therefore not the required
   cofinal estimate.
10. **Fixed-shape continuity is gauge-blind.**  At every positive shape, the Gamma--Meixner field
    lies in the vanishing-tail Euler layer whose joint graph with the regular strip germ is dense.
    A selector continuous only at fixed positive shape cannot see the actual Mertens corona class.
11. **Finite refinement is Lorentz-flat.**  The modulus law `n -> n^2` does not create a source
    obstruction: in rapidity coordinates the reflected Hurwitz block is a homomorphism into
    `SO^+(1,1)`.  The positive square refinement remainder is Euclidean growth of a perfectly
    coherent indefinite colligation.
12. **Local valuation completion remains off-line analytic.**  Adding every prime-power layer
    does not force the Lorentz rapidity to vanish.  The normalized transfer has spectral radius
    `p^(-1/2+|a|)<1` throughout the open strip, so its complete Euler logarithm exists locally at
    every off-line point.
13. **A canonical positive Gamma metric is not yet passivity.**  The opposite-variance jet
    generators are adjoints in the source-selected factorial Fock metric, but finite Taylor
    translation is expansive in that metric and the reflected Euler fibre has not yet been
    embedded into it.  Naming the Fock form without the all-prime incidence does not orient the
    Lorentz block.
14. **The raw Gamma colligation is necessarily expansive at its boundary.**  Its boundary
    self-symbol is the identity and its outgoing factorial transfer is nonzero.  Hence a pure new
    boundary input gains exactly the squared transfer norm.  The required reflected contraction
    cannot be the untransformed Taylor colligation.
15. **The factorial Fock direct limit rejects the all-prime incidence.**  Prime--Laplace
    derivative evaluation enters every finite Gamma clock, but the infinite coherent jet of a
    prime has squared norm `w_theta(p)p^(-2x_0)exp((log p)^2)`.  Hence no fixed positive shape makes
    the natural cofinal map bounded into the standard factorial Fock space.
16. **Finite clock bounds do not imply a cofinal clock bound.**  Every time-one seam transform has
    finite energy at every fixed jet resolution, including off-line fibres.  Only a bound uniform
    in the resolution can rule out its finite left-half-plane pole.
17. **An unpinned boundary comparison transports the obstruction for free.**  The two time-one
    Mertens pole germs are abstractly isomorphic after recentering, for every strip point.  Their
    support coincidence is selective only if the completed source comparison preserves the
    Gamma-normalized global Laplace origin.
18. **The raw product clock cannot carry the source constraint.**  Finite HT freedom makes the
    homogeneous source tangent dense in the product topology, so any Hausdorff
    product-continuous conormal vanishing on it is zero.  A proof in that topology necessarily
    erases the very Mertens boundary it needs.

## Positive residues of the attacks

Each no-go above leaves a usable positive theorem or a stricter construction target.

1. **Capacity/orientation separation `[PROVED]`.**  Hypertranscendence and prime-power packet
   independence certify maximal finite source visibility even though they do not choose a
   positive metric.  A successful proof may therefore use HT to establish faithfulness and use
   star-Kadison only for orientation; neither role has to be falsely attributed to the other.
2. **Canonical target clock `[PROVED ON PAPER]`.**  The redressing attack does not merely reject
   arbitrary clocks.  Equations `(5)`--`(9)` identify the exact two-cycle reflection clock,
   normalization, and erased vector whose source realization is required.  Its energy vanishes
   at any one prime if and only if RH.
3. **Root-domain phase diagram `[PROVED ON PAPER]`.**  Failure of automatic time-one
   deconvolution leaves the exact theorem

   ```text
   seam(rho) lies in H_theta
     iff Re(rho)=1/2 or theta>|2Re(rho)-1|.             (18)
   ```

   The common prime-Laplace frame is dense in every `H_theta`, so the unbounded inverse has a
   concrete finite Gram test rather than an undefined domain problem.
4. **Finite Gamma curvature energy `[PROVED IN LEAN SCRATCH]`.**  Put

   ```text
   E_N=sum_(i=0)^(N-1)|1/(N-i)!|^2.
   ```

   The file `/tmp/GammaClockCurvaturePositive.lean` proves

   ```text
   E_(N+1)=1/((N+1)!)^2+E_N,
   sum_(n>=0)1/((n+1)!)^2<infinity,
   E_N -> sum_(n>=0)1/((n+1)!)^2.                       (19)
   ```

   The proofs use only the standard Lean axioms.  Thus the Gamma rank-one curvature is not only
   thin at each resolution: its canonical factorial boundary has a finite cofinal Euclidean
   energy.  Any failure of `(16)` must therefore enter through the prime coupling, the changing
   shape metric, or the source/divisor incidence—not through divergence of the bare Gamma
   conormal.
5. **Exact Landau localization `[PROVED ON PAPER]`.**  Put

   ```text
   a_Xi=sup_q |Im(xiSpectralPoint(q))|.
   ```

   Then the abscissa of convergence of `G_Xi` is exactly

   ```text
   alpha_G=2 a_Xi.                                       (20)
   ```

   For `theta>2a_Xi`, the exact seam formula is uniformly bounded by a constant times
   `(log p)^2 p^(-1-theta+2a_Xi)` and the multiplicity weights have finite sum, proving
   convergence.  For `theta<2a_Xi`, one divisor fibre has horizontal charge greater than
   `theta`, and the root-domain threshold forces divergence.  Landau makes `2a_Xi` a real
   singularity whenever it is positive.  Thus failure of locally uniform cofinal holomorphy is
   not unstructured: the normal-family problem is localized at the exact maximal horizontal
   displacement.
6. **One-prime metric detector `[PROVED ON PAPER]`.**  Although a divisor-defined metric is
   circular as a source, its required comparison value is minimal:

   ```text
   sourceTrace_2=A_2=0  iff RH.                          (21)
   ```

   Hence a source construction need not recover a complete spectral metric; it may prove one
   orbit-sensitive dyadic trace identity and one zero-loss theorem.
7. **Reflected curvature coefficient `[PROVED ON PAPER]`.**  Self-duality makes the reciprocal
   norm orbit `N(L)` even and convex, with

   ```text
   N'(0)=0,
   N''(0)=4 sum_q Im(alpha_q)^2/|alpha_q|^2,
   N''(0)=0 iff RH.                                      (22)
   ```

   Reflection therefore supplies a canonical second-order horizontal curvature even though it
   does not supply its vanishing.  This is the scalar tangent which the source clock curvature
   must match.
8. **Full colligation reconstruction `[PROVED IN LEAN]`.**  The kinematic-curvature no-go leaves
   an exact positive finite theorem: lower action, outgoing curvature transfer, and boundary
   compression uniquely reconstruct the next clock action.  The source descent anomaly obeys a
   Bianchi identity with curvature.  Hence the RH construction target is finite and checkable:
   build the reflected anomaly colligation `(14a)` and test passivity; no unspecified global
   integration stack is needed at the first stage.
9. **Quantitative strip theorem `[PROVED ON PAPER]`.**  If an orbit-sensitive source incidence
   proves, for some `beta>=0`,

   ```text
   A_p=O((log p)^k p^(-1+beta))                           (22a)
   ```

   for one finite `k`, then the exact abscissa law `(20)` forces `2a_Xi<=beta`.  The desired uniform factorial
   bound is the sharp case `beta=0` and gives RH.  Thus any imperfect source estimate still yields
   a nontrivial horizontal zero-free strip rather than a binary failure.
10. **Canonical singular radial path `[PROVED ON PAPER]`.**  The fixed-shape no-go leaves the
    explicit Abel family `(14c)`, which detects `[one]` only in the singular limit.  Therefore the
    source theorem should be formulated as boundary compatibility of the complete family, or as
    complete monotonicity for every positive shape, rather than as continuity of a single damped
    Euler observable.
11. **Canonical finite anomaly colligation `[PROVED ON PAPER]`.**  The refinement no-go leaves the
    explicit Lorentz block `(14b)`, whose off-diagonal energy is the rational-Hurwitz seam and whose
    rapidity is the horizontal displacement.  Thus the finite source operator is constructed; the
    exact open core is the positive-metric upgrade supplied by the completed Gamma--Mertens
    boundary.
12. **Canonical valuation-completed logarithmic colligation `[PROVED ON PAPER]`.**  The local
    completion no-go leaves the exact source object

    ```text
    C_p(rho)=sum_(m>=1) p^(-m/2)exp(i*m*t*log p)B_a(p)^m/m
            =-Log(I-p^(-1/2)exp(i*t*log p)B_a(p)).       (22b)
    ```

    Its anti-reflection entry vanishes exactly when `a=0`, and its Gamma--Meixner prime energy
    converges exactly for `theta>2|a|`.  This supplies an alternative RH consumer directly on the
    completed valuation module.  The theorem also proves that only the cofinal all-prime metric or
    singular Mertens-corona boundary can orient it; no local completion theorem can do so.
13. **Canonical factorial Fock polarization `[PROVED ON PAPER]`.**  If `D_N` is the raw-jet
    derivative clock and `A_N` the Leibniz coordinate-multiplication clock, then the metric

    ```text
    <x,y>_(F,N)=sum_(j<N)x_j conjugate(y_j)/j!            (22c)
    ```

    is the unique diagonal positive metric, up to scale, with `D_N^*=A_N`.  It also gives the
    positive boundary identity

    ```text
    I-[D_N,A_N]=N P_top>=0.                              (22d)
    ```

    Hence the Gamma side already supplies a non-divisor positive metric and boundary charge.  The
    remaining statement is now the polarized Euler--Gamma incidence which carries the completed
    anti-reflection logarithm into this top-boundary current and preserves its metric cofinally.
14. **Exact Gamma boundary Green law `[PROVED ON PAPER]`.**  In the factorial orthogonal split,
    the full translation colligation is `[E_N,beta_N;0,I]`, so

    ```text
    ||E_(N+1)(0,b)||_F^2-||(0,b)||_F^2=||beta_N b||_F^2. (22e)
    ```

    The failed raw-passivity claim therefore leaves the precise positive loss which a
    source-canonical characteristic/scattering transform or star-Kadison compression must encode.
    This removes ambiguity about the sign and normalization of the Gamma boundary channel while
    keeping construction of that transform in the open core.
15. **Faithful finite prime--Gamma incidence `[PROVED ON PAPER]`.**  For every positive shape and
    base point `x_0>1/2`, the first `N` derivative values of the weighted prime--Laplace transform
    define a Hilbert--Schmidt map into the `N`-jet factorial clock.  The intersection of the
    kernels over all `N` is zero by holomorphy and Dirichlet-series uniqueness.  Thus the HT clocks
    already observe the entire prime source faithfully at finite resolution.  Failure of the
    factorial Fock colimit leaves the precise positive replacement required by `(16)`: a locally
    trace-bounded projective or relative-graph completion, not a bounded infinite jet operator.
16. **Time-one factorial-jet RH criterion `[PROVED ON PAPER]`.**  The actual time-one weighted
    seam transform `(14e)` is identically zero on the critical line and has one uncancelled simple
    pole off it.  Its finite raw-jet energies increase to a finite limit exactly on the line, as in
    `(14f)`.  This supplies a source-facing alternative to the all-shape theorem: construct the
    on-shell Euler anomaly in the existing Gamma clocks and prove one uniform all-resolution
    factorial bound.
17. **Reflected Mertens support law `[PROVED ON PAPER]`.**  The rightmost singular part of `(14e)`
    is

    ```text
    sqrt(2)[1/(z+rho)-1/(z+1-conjugate(rho))],            (22f)
    ```

    the anti-reflection doublet of the actual unit-field Mertens corona.  Its two supports are
    `-rho` and `conjugate(rho)-1`, and coincide exactly on the critical line.  The resulting source
    conjecture is now precise: the full anomaly colligation must identify these boundary germs in
    one affine-pinned Gamma/Laplace chart.  An abstract comparison up to translation is explicitly
    excluded and leaves no RH content.
18. **Forced source-topology refinement `[PROVED IN LEAN]`.**  Every nonzero Hausdorff-valued
    source conormal annihilating a finite-observably free HT tangent forces a strict minimal
    refinement of the product clock topology.  The RH route must therefore construct the intrinsic
    zeta Mertens corona conormal and a framed section of its Mackey interval.  This is a positive
    topology theorem, not a request to guess another Hilbert completion.

## Completely monotone positive successor `[PROVED ON PAPER]`

The nonnegative shape trace has more unconditional structure than holomorphy on a right
half-plane.  On its exact convergence interval `theta>2a_Xi`, termwise differentiation gives

```text
(-1)^n d^n/dtheta^n G_Xi(theta)
 =sum_p A_p lambda_p^n exp(-theta lambda_p)>=0.          (23)
```

Hence `G_Xi` is completely monotone there.  For every finite real family `theta_i>a_Xi`,

```text
[G_Xi(theta_i+theta_j)]_(i,j)
 =sum_p A_p
    [exp(-theta_i lambda_p)exp(-theta_j lambda_p)]_(i,j)
 >=0.                                                    (24)
```

Thus the maximal safe Gamma-shape carrier is already a reflection-positive radial Hankel
semigroup.  It is the transverse radial object required by the formalized
phase--radial Toeplitz--Hankel polarization law; the prime phases alone could not supply it.

`[PROVED]` The following are equivalent:

```text
RH;
G_Xi extends from theta>1 to a finite completely monotone function on theta>0;
the safe radial Hankel kernel in (24) extends to all positive theta_i
  as a Laplace-positive kernel with nonnegative generator spectrum.         (25)
```

Under RH the extension is zero.  Conversely, Bernstein's theorem represents a completely
monotone extension as the Laplace transform of a unique positive measure.  On `theta>1` it agrees
with the discrete measure

```text
nu_Xi=sum_p A_p delta_(lambda_p).
```

Choose `theta_0>1` and tilt both measures by `exp(-theta_0 lambda)`; they are then finite and have
equal Laplace transforms on a neighborhood of zero.  Uniqueness identifies the tilted measures,
and hence the original measures.  Finiteness of the extension at every `theta>0` forces the
Laplace abscissa of `nu_Xi` to be nonpositive.  Equation `(20)` gives `a_Xi=0`, hence RH.

Plain positive-semidefinite Hankel extension is deliberately not asserted: a kernel such as
`exp(theta_i+theta_j)` is positive semidefinite but has a negative generator frequency.  The
nonnegative radial spectrum, equivalently complete monotonicity, is load-bearing.

This is the nontrivial positive replacement for the failed claim that finite-stage entire
functions automatically have a holomorphic cofinal limit.  The source proof may now target a
reflection-positive Gamma-shape integration theorem rather than complex normality.  It must still
construct the cofinal trace from pre-divisor data; postulating the extension is RH-equivalent.

## Lean boundary

The reusable finite algebra is already formalized:

- rank-one Gamma clock curvature and its boundary vector;
- factorial recurrence, summability, and convergence of its Euclidean boundary energy in
  `/tmp/GammaClockCurvaturePositive.lean`;
- star-Kadison erased-energy, resolution, polarization-in-scratch, and zero-set laws;
- prime-seam reflection energy and its exact horizontal charge;
- the local Euler tangent identifying the prime seam;
- prime-power source visibility and finite-packet independence.

No new Lean wrapper should be added until `(15)` is proved without divisor-defined data or a
genuine finite source observable is constructed.  The holomorphic normal-family passage in
`(16)` is the mathematical core and is outside the present Lean analytic infrastructure.

## Novelty boundary

Ramanujan's Gamma Fourier transform, Meixner convolution semigroups, star-Kadison inequalities,
Landau's nonnegative Dirichlet-series theorem, and rank-one displacement curvature all have
established parent theories.  A targeted search found no primary source combining them into
`(10)`--`(16)`.  The candidate-new content is only the source-derived trace identity, its
presentation-invariant curvature construction, and the positive-shape normal-family theorem.
Vocabulary or an abstract existence theorem does not clear the novelty gate.

## Gates

- [x] exact scalar Landau RH consumer available on paper
- [x] Gamma--Meixner root scale and prime diagonal available on paper
- [x] finite star-Kadison energy and Gamma rank-one curvature formalized
- [x] prime-seam local Euler tangent and source visibility formalized
- [x] derive the exact target-side two-cycle clock factorization `(5)`--`(9)` on paper
- [x] prove Gamma factorial-curvature energy recurrence and convergence in Lean scratch
- [x] construct every fixed-prime residue coordinate from the sharp-window source
- [x] identify its anchored divisor quadratic current with `(15)`
- [ ] construct the source metric and prove the dyadic contraction `(15a)`
- [ ] alternatively prove the uniform source-incidence bound `(15b)`
- [ ] construct the cofinal shape family `(10)`
- [ ] prove orbit-insertion covariance
- [ ] prove the local normal-family bound `(16)`
- [ ] alternatively construct the completely monotone positive-shape extension `(25)`
- [ ] continue `G_Xi` to `Re(z)>0`
- [ ] deduce RH by Landau
- [ ] independent parent-theory novelty and significance audit

## Log

- 2026-07-15 -- Opened after the Gamma--Meixner root-domain, global Landau trace, Gamma clock
  curvature, and finite star-Kadison results were compared.  The comparison isolates `(15)` and
  `(16)` as the smallest source-pure proof obligations; no RH claim is made.

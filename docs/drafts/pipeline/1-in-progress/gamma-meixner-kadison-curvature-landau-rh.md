# Gamma--Meixner star-Kadison curvature trace and the Landau RH boundary

- **ID:** `gamma-meixner-kadison-curvature-landau-rh`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / HTGEOMETRY-TO-RHTOWER TRANSFER / RH ROUTE
- **Scientific status:** `[CONJECTURE] [DOWNSTREAM IMPLICATION PROVED]
  [TARGET CLOCK FACTORIZATION PROVED ON PAPER] [FINITE CLOCK ALGEBRA FORMALIZED]
  [SOURCE TRACE OPEN] [NOVELTY UNVERIFIED]`
- **HT parents:**
  - `../3-formalized/finite-clock-star-kadison-observability.md`
  - `../3-formalized/gamma-periodic-constraint-corona.md`
  - `calibrated-clock-curvature-class.md`
  - `constraint-curvature-integration-stack.md`
- **RH parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/archimedean-meixner-root-seam-scale.md`
  - `../2-fully-proven/not_new_scientific_knowledge/meixner-root-prime-laplace-value-frame.md`
  - `../2-fully-proven/not_new_scientific_knowledge/xi-global-meixner-shape-landau-rh.md`
  - `../2-fully-proven/not_new_scientific_knowledge/xi-reciprocal-translation-prime-seam-norm-law.md`
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

## Smallest non-circular theorem

Before constructing the complete family, prove one fixed-prime trace identity.  For a rational
prime `p`, the source-built curvature observable must have star-Kadison trace

```text
sourceTrace_p
 =A_p
 =2(log p)^2/p * (N(log p)-N(0)),                      (15)
```

where `N(L)` is the reciprocal-Cauchy translation norm.  The first equality must be proved from
the completed source graph; the second is already proved on paper.  The observable must remain
defined after a rational FE--Schwarz orbit insertion, with its trace changing by the inserted
residue seam.  That gauge-covariance test makes `(15)` orbit-sensitive and rules out a
divisor-blind Euler Gram.

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
the safe radial Hankel kernel in (24) extends to all positive theta_i.       (25)
```

Under RH the extension is zero.  Conversely, Bernstein's theorem represents a completely
monotone extension as the Laplace transform of a unique positive measure.  On `theta>1` it agrees
with the discrete measure

```text
nu_Xi=sum_p A_p delta_(lambda_p).
```

Uniqueness of Laplace transforms identifies the two measures.  Finiteness of the extension at
every `theta>0` then forces the Laplace abscissa of `nu_Xi` to be nonpositive.  Equation `(20)`
gives `a_Xi=0`, hence RH.

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
- [ ] construct the fixed-prime source observable in `(15)`
- [ ] prove the source/divisor trace identity `(15)`
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

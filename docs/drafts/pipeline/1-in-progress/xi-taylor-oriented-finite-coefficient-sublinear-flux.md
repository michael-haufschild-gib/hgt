# Xi Taylor orientation-sensitive finite-coefficient sublinear flux

- **ID:** `xi-taylor-oriented-finite-coefficient-sublinear-flux`
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET / RH SOURCE PRODUCER
- **Scientific status:** `[OPEN CORE] [NOVELTY UNVERIFIED]`
- **Parent card:**
  `../3-formalized/not_new_scientific_knowledge/xi-taylor-anisotropic-rational-mesh-sublinear-flux.md`
- **Statement:** Prove, directly from the canonical finite Taylor coefficients of `XiC`, an
  orientation-sensitive estimate forcing sublinear upper logarithmic-derivative flux on the
  anisotropic Gaussian-rational meshes, without using Xi zero locations, real-rootedness,
  anti-Herglotz positivity, or an RH-equivalent limiting measure.

## Exact target

Let

```text
P_k(z) = xiCTaylorApprox(k,z),
z(s)   = (s-1/2)(-i),
```

and let `N` be a source-selected super-accurate schedule. For every integer `R >= 4`, define

```text
G_(n,R) = {a/n + i b/n^2 : a,b in Z}
          intersect {1/R <= Re(s) <= 1/2-1/R, |Im(s)| <= R}.
```

The required conclusion is

```text
max { Im(P_(N(n))'(z(s))/P_(N(n))(z(s))) :
      s in G_(n,R), P_(N(n))(z(s)) != 0 } = o(n).             (1)
```

An acceptable coefficient theorem must state a finite predicate or inequality on the actual
coefficients of `P_(N(n))`, prove that the canonical Xi coefficients satisfy it from their
prime--Gamma or theta-moment source, and derive `(1)` by a finite argument.

## Non-circularity firewall

The producer may not assume or invoke:

1. locations of Xi zeros or zero-freeness in the open left critical strip;
2. real-rootedness, Hermite--Biehler status, or Jensen-polynomial hyperbolicity strong enough to
   imply the limiting zero localization;
3. anti-Herglotz/Pick positivity of `XiC'/XiC`;
4. positivity of a limiting measure equivalent to RH;
5. a finite selector defined using the target flux inequality or an RH-equivalent predicate.

## Existing proved infrastructure

`[PROVED]` The paper criterion shows that `(1)` for a super-accurate schedule implies RH and that RH
implies `(1)`.

`[FORMALIZATION]` The Lean tree already contains:

- the super-accurate source schedule and its moving anisotropic lookup;
- the `1/n` by `1/n^2` rational mesh and positive reciprocal orientation;
- local Xi value lower bounds and derivative upper bounds on each mesh fibre;
- linear logarithmic-derivative growth at any hypothetical Xi zero;
- the terminal implication from sublinear anisotropic Xi flux to RH.

`[FORMALIZATION]` The finite-Taylor quotient transfer near a hypothetical zero and the terminal
finite-Taylor sublinear-flux implication to RH are now complete.  The remaining research theorem
is the unconditional coefficient producer `(1)`.

## Medalist lens

The smallest finite object is the oriented Hermitian numerator

```text
J_P(z) = Im(P'(z) * conjugate(P(z))),                         (2)
```

because

```text
Im(P'(z)/P(z)) = J_P(z)/|P(z)|^2                             (3)
```

when `P(z) != 0`. Coefficient sign information controls individual axes; `(2)` is a combination
mode coupling every coefficient pair and retaining orientation. The target is therefore a
finite lower-denominator/upper-current inequality, not coefficient positivity by itself.

## Candidate moves

1. `[CONJECTURE] Oriented Bezoutian minor.` Rewrite
   `J_P(z)-eta |P(z)|^2` as one explicit Hermitian coefficient form and seek a theta-source
   factorization whose negative part is `o(n)|P(z)|^2` uniformly on the finite mesh.
2. `[CONJECTURE] Truncated cosine two-point current.` Insert the theta-moment representation of the
   coefficients into `(2)`, obtaining a finite double integral. Isolate the antisymmetric kernel
   before integration and test whether completed prime--archimedean orientation supplies its sign
   or only its axis marginals.
3. `[CONJECTURE] Constraint residual rather than positivity.` Use the exact coefficient recurrences
   to show that any mesh point with current at least `epsilon*n` creates a finite residual violating
   one completed theta constraint. This must be a direct finite contradiction, not a compactness
   limit that reconstructs an RH-equivalent measure.
4. `[CONJECTURE] Denominator exclusion by source-conditioned resultants.` Construct a finite
   coefficient resultant separating the Taylor polynomial and its oriented derivative on the mesh,
   with a source lower bound stronger than the super-accurate error near a hypothetical Xi zero.

## Initial attacks and retired shortcuts

- `[PROVED ROUTE FAILURE]` Positive Taylor coefficients or positive theta moments alone cannot
  control `(2)`: axis positivity does not imply the first nontrivial Hankel/Schur combination sign.
- `[PROVED ROUTE FAILURE]` Fixed Taylor moduli, Newton geometry, HT status, and any bounded finite
  local passport do not select real-rootedness or global divisor orientation.
- `[PROVED ROUTE FAILURE]` An unrestricted nonlinear finite selector is an oracle unless its source
  formula and transfer theorem are supplied independently of the target.
- `[PROVED BRIDGE]` The oriented current `(2)` has an exact finite polynomial normal form and the
  strict inequality `J_P(z) < epsilon*n*|P(z)|^2` automatically excludes `P(z)=0` and implies the
  desired flux bound.  This is denominator clearing, not a source proof; treating it as the
  coefficient producer would merely rename the target.
- `[PROVED ROUTE FAILURE]` The theta two-point current kernel is not pointwise oriented.  For the
  full cosine kernel, one source coordinate at `u=0` and another at `v>0` contributes a cross term
  proportional to `-v cos(xv)sinh(yv)`; choosing `xv=pi` makes it positive for `y>0`.  Hence
  positivity of the theta weights cannot prove the current sign atom by atom.
- `[PROVED ROUTE FAILURE]` Positive even Schwartz source structure and all raw-moment Hankel
  inequalities are insufficient.  The density
  `g_epsilon(x)+a g_epsilon(x-1)+a g_epsilon(x+1)`, `0<a<1/2`, is strictly positive, even, and
  Schwartz and has a uniform strict log-concavity floor for `epsilon>1`, while its Fourier transform
  `exp(-epsilon z^2/2)(1+2a cos z)` has the explicit simple nonreal zeros
  `pi +/- i arcosh(1/(2a))`.  Any live inequality must distinguish the exact theta source from
  this family.
- `[PROVED ROUTE FAILURE]` A source-conditioned resultant or arithmetic lower bound at the
  Gaussian-rational nodes cannot exclude the pole amplifier: every complex target has the
  explicit `1/n` by `1/n^2` right approximants, and a hypothetical Xi zero makes the polynomial
  values naturally of order `n^{-m}`, not arithmetically exceptional.
- `[PROVED ROUTE FAILURE]` The finite Cauchy-jet, Toeplitz, and inverse-Cholesky frames in
  `HTGeometry/CauchyJetFrame.lean`, `CayleyMomentFrame.lean`, and
  `CofinalCholeskyFiniteFrame.lean` change coordinates but supply no orientation.  Congruence
  preserves the inertia of the indefinite coefficient-current form, every finite frame prefix
  retains a nontrivial carrier fibre, and only the complete compatible tower selects the measure.
  The concurrent `HTGeometry/CofinalCholeskySelection.lean` now formalizes that last statement:
  equality at every canonical inverse-Cholesky level determines the probability measure.  Using
  precisely that complete-tower selector here would reintroduce the forbidden limiting-measure
  route; the new finite-frame uniqueness theorems still do not orient the current.
- `[PROVED BRIDGE]` The exact theta-tail differential constraint gives a finite coefficient
  telescope.  If `c_k=2(2k)!^(-1) integral_0^infinity x^(2k)T(x)dx`, then the Xi Taylor
  magnitudes satisfy `b_0=1/2-c_0/4` and `b_(k+1)=c_k-c_(k+1)/4`.  Hence
  `B_(d+1)(w)=1/2+(w-1/4)Q_d(w)-(c_(d+1)/4)w^(d+1)`, and the actual odd-cutoff Xi Taylor section is
  `B_d(-z^2)`.  This is proved on paper and in
  `XiCTaylorThetaTailTelescope.lean`.  It isolates one explicit top defect but does not by itself
  sign the full oriented current, so it is not the producer.
- `[PROVED BRIDGE]` After `w=-z^2`, the top defect is a real monomial
  `E_d(z)=((-1)^(d+1)c_(d+1)/4)z^(2d+2)`, and every real monomial has
  `J_(az^m)(z)=-m a^2 |z|^(2m-2) Im z <= 0` in the upper half-plane.  Thus the defect itself is
  favorable.  Writing the theta-tail core as `U_d`, the exact polarization gives
  `J_(U_d-E_d) <= J_(U_d)+|U_d'||E_d|+|E_d'||U_d|`.  The open estimate is now localized to the
  core current and these two explicit cross-interference terms.  This is proved on paper and in
  `XiCTaylorThetaTailOrientedDefect.lean`.
- `[PROVED BRIDGE]` The explicit raw theta tail decays at every prescribed natural exponential
  rate: `|T(x)| <= C_p exp(-p x)`.  Hence its normalized moments satisfy
  `|c_n| <= 2C_p/p^(2n+1)`.  The top defect and its derivative therefore decay geometrically on
  every fixed compact set once `p` exceeds the evaluation radius.  The source coefficient bound
  and compact-uniform value/derivative decay are proved on paper and in
  `XiCTaylorThetaTailRapidDecay.lean`; no zero information is needed for them.
- `[PROVED BRIDGE]` A source-selected super-accurate schedule can be chosen entirely at odd
  cutoffs.  On that schedule, the explicit finite theta-tail envelope
  `J_(U_d)+|U_d'||E_d|+|E_d'||U_d|` forces polynomial nonvanishing and the desired pointwise
  logarithmic-flux bound; its eventual sublinear mesh version implies RH.  This exact finite
  coefficient gate is proved on paper and in `XiCTaylorThetaTailFiniteCoefficientGate.lean`.
  The gate deliberately leaves satisfaction of the core-current inequality open.
- `[PROVED REDUCTION]` The odd schedule can be selected jointly so that the Taylor error, top
  defect, and top-defect derivative all obey the same super-accurate expanding-ball tolerance.
  On every anisotropic fibre the two cross terms are then
  `o((n+1)|P|^2)` unconditionally.  The proof uses the local analytic order only for a polynomial
  value lower bound and does not assume whether the target is a zero.  Thus the top defect is now
  completely discharged: the sole remaining producer is sublinear upper current of `U_d` itself.
  This reduction is proved in `XiCTaylorThetaTailFiniteCoefficientGate.lean`.
- `[PROVED BRIDGE]` The remaining core now has a literal finite source coordinate.  With
  `C_d(z,x)=sum_(k<=d)(-1)^k(zx)^(2k)/(2k)!`, one has
  `Q_d(-z^2)=2 integral_0^infinity T(x)C_d(z,x)dx` and
  `U_d(z)=1/2-(z^2+1/4)Q_d(-z^2)`.  This is proved on paper and in
  `XiCTaylorThetaTailCoreIntegral.lean`.  Polarizing this formula recovers a mixed two-point
  kernel; positive theta weights alone still do not orient it.
- `[PROVED BRIDGE]` Two further integrations by parts expose a normalized positive source density
  `rho(x)=4T''(x)`.  Its atom polynomial is
  `4pi^2u^4-6pi u^2+1/4`, which is strictly positive for `u>=1`, and
  `integral_0^infinity rho=1`.  The tail coefficients satisfy
  `c_k=(1/2) integral rho(x)x^(2k+2)/(2k+2)! dx`, so the remaining core is the exact finite convex
  mixture
  `U_d(z)=(1/2) integral rho(x)[1-(z^2+1/4)S_d(z,x)]dx`.
  This is proved on paper and in `XiCTaylorThetaTailConvexCore.lean`.  The representation is
  source-pure and finite, but its current still polarizes to a mixed two-point kernel; probability
  positivity alone is not the missing orientation law.
- `[PROVED ROUTE FAILURE]` Finite prime Pólya--Schur scalings preserve a pre-existing hyperbolic
  section, but the renormalized infinite-prime identification with the canonical Xi coefficients
  is the already recorded RH-sized limit wall.  It supplies no finite current estimate for the
  present canonical Taylor sections.
- `[PROVED ROUTE FAILURE]` A convex-tail theorem giving only `Re Q(z)>0` cannot exclude the Xi zero
  equation `Q(z)=1/(2(z^2+1/4))`.  If `z=x+iy` with `0<y<1/2`, then
  `Re(z^2+1/4)=x^2+1/4-y^2>0`, so the reciprocal on the right also has positive real part.  A live
  theorem must control the argument of `Q`, or the full oriented cross-current, not one Cartesian
  component.
- `[PROVED STRUCTURAL WARNING]` The seam reflection fixes every odd boundary derivative of the
  one-sided tail, so repeated integration by parts cancels the rational seam contribution to all
  algebraic orders.  The surviving Xi term is beyond that formal inverse-frequency expansion.
  Bounds that retain only finitely many monotonicity or convexity derivatives therefore estimate
  the cancelled carrier rather than the residual whose orientation decides the target.
- `[OBSERVED, NOT A PRODUCER]` The concurrent rectangular CCM observable continuation recovers the
  off-line Xi divisor as poles of a log-sampled Weil-tail L-series.  Its continuation is explicitly
  built from the Xi divisor carrier; transporting it here would violate the zero-location firewall.
- `[OBSERVED, NOT A PRODUCER]` The concurrent `HTGeometry/HamburgerBoundaryKernel.lean` and
  `HTGeometry/NevanlinnaBoundaryAlgebra.lean` formalize barycenters preserving a complete
  Hamburger moment sequence and projective labels for complete Nevanlinna boundary families.
  They do not orient a finite Taylor current.  Their selective content belongs to the complete
  moment/boundary family and therefore cannot replace the required finite source inequality.
- `[OPEN CORE]` Prove that the actual finite theta-tail core current is sublinear relative to the
  canonical Taylor value on every anisotropic mesh fibre.  The top defect's self-current is
  nonpositive and its coefficients have arbitrary geometric decay, so its cross-interference is
  a removable compact-uniform error rather than the source obstruction.  If the core remains
  indefinite, isolate the first explicit theta-tail coefficient obstruction and retire that source
  predicate rather than weakening the theorem.

## Gates

- [x] prior pipeline, failed routes, and formal theorem surface audited
- [x] exact RH-equivalent endpoint separated from the requested source producer
- [x] several genuinely different coefficient mechanisms constructed and attacked
- [ ] finite source predicate stated without target-oracle content
- [ ] canonical Xi coefficients proved to satisfy the predicate
- [ ] predicate proved to imply `(1)` on every compact anisotropic mesh
- [ ] complete paper proof independently checked
- [ ] exact theorem formalized in Lean with no forbidden declarations
- [ ] parent-theory, literature, novelty, and significance gates passed

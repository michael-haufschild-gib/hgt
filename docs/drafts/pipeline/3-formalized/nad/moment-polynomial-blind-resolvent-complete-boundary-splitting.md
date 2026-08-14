# Moment polynomials are blind to a boundary space that resolvents recover completely

- **ID:** `moment-polynomial-blind-resolvent-complete-boundary-splitting`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONSTRAINT-RESOLVENT ORTHOGONAL SPLITTING LAW
- **Lane:** general hypertranscendence; indeterminate Hamburger moments; carrier geometry
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Parent:** `nevanlinna-boundary-bauer-retract-maximal-ht.md`
- **Statement:** For every stationary law of the canonical Nevanlinna constraint projector, the
  projector is conditional expectation onto the projective support label. The resulting horizontal
  boundary space is orthogonal to every centered polynomial, while the conditional Cauchy
  resolvents have dense linear span in the entire horizontal space. Thus complete moment data
  annihilates a canonical Hilbert boundary coordinate that finite-centre resolvent data recovers
  exactly; residual maximal translation HT occurs while that invisible coordinate varies.

## Goal

The Bauer-retract theorem constructs a canonical probability modulus inside each indeterminate
moment fiber. The present theorem identifies its Hilbert geometry. It proves that the separation
between moments and resolvents is not merely asymptotic: moments are exactly orthogonal to the
mean-zero boundary coordinate, whereas Cauchy resolvents are complete on that coordinate.

This is the positive carrier law needed from the earlier no-go statements:

> **An indeterminate complete-moment constraint necessarily carries a polynomial-invisible,
> resolvent-complete boundary Hilbert space.**

## Setup

Keep the parent notation. The projective support label and `N`-extremal family are

```text
pi:R->T=RP^1(R),
tau |-> mu_tau,
supp(mu_tau)=pi^(-1)({tau}).                               (1)
```

For a boundary probability `eta in P(T)`, let

```text
nu=Beta(eta)=integral_T mu_tau d eta(tau).                 (2)
```

The parent kernel and operator are

```text
Q_s(x,dy)=mu_(pi(x))(dy),
(P_s f)(x)=integral_R f(y)d mu_(pi(x))(y).                 (3)
```

Equation `(2)` is a disintegration of `nu` over `pi`, because `pi_*mu_tau=delta_tau` and
`pi_*nu=eta`.

## Conditional-expectation identity `[PROVED HERE]`

Let `f` be bounded Borel on `R` and `h` bounded Borel on `T`. Fubini and `(1)` give

```text
integral_R h(pi(x)) f(x) d nu(x)
 =integral_T h(tau)[integral_R f d mu_tau]d eta(tau)
 =integral_R h(pi(x))(P_s f)(x)d nu(x).                   (4)
```

Therefore, on `L^2(nu)`,

```text
P_s=E_nu[ . | sigma(pi)].                                  (5)
```

In particular `P_s` is the positive self-adjoint orthogonal projection onto

```text
H_hor={h compose pi:h in L^2(T,eta)},                      (6)
```

where pullback by `pi` is an isometry because `pi_*nu=eta`. Its orthogonal kernel is

```text
H_ver={f in L^2(nu):integral_R f d mu_tau=0
                       for eta-almost every tau}.          (7)
```

Thus

```text
L^2(nu)=H_hor orthogonal_sum H_ver.                        (8)
```

The names are intrinsic: `H_hor` varies the projective boundary law, while `H_ver` changes a
state inside its fixed extremal support leaf.

## Exact polynomial blindness `[PROVED HERE]`

Let `L_s` be the common moment functional on polynomials,

```text
L_s(p)=integral_R p d mu_tau,                              (9)
```

independent of `tau`. The common finite moments put every polynomial in the domain of `P_s`, and

```text
P_s p=L_s(p) * 1.                                         (10)
```

Hence every centered polynomial lies in the vertical kernel:

```text
p-L_s(p) in H_ver.                                        (11)
```

Equivalently, if `h in L^2(T,eta)` has mean zero, then for every polynomial `p`,

```text
integral_R p(x) conjugate(h(pi(x))) d nu(x)
 =L_s(p) integral_T conjugate(h)d eta
 =0.                                                       (12)
```

Therefore

```text
H_hor,0={h compose pi:integral_T h d eta=0}
 subset closure(polynomials)^orthogonal.                  (13)
```

If `eta` is not a point mass, `H_hor,0` is nonzero. More strongly, its Hilbert dimension is the
dimension of the mean-zero space `L^2_0(T,eta)`. This identifies a canonical, quantitatively large
part of the failure of polynomial density for every non-ergodic stationary law.

## Resolvent completeness `[PROVED HERE]`

For `z in C minus R`, let

```text
r_z(x)=1/(x-z),
Phi_z(tau)=m_tau(z).                                       (14)
```

The first function is bounded, and `(3)` gives

```text
P_s r_z=Phi_z compose pi.                                  (15)
```

The linear span of

```text
{1} union {Phi_z:z in C minus R}                           (16)
```

is uniformly dense in `C(T)` and hence dense in `L^2(T,eta)` for every `eta`.

### Proof of density

Let `rho` be a finite complex Borel measure on `T` annihilating `(16)`. Then

```text
integral_T 1 d rho=0.                                     (17)
```

On the nonempty open set where `C(z)!=0`, the parent Möbius identity is

```text
Phi_z(tau)=m_infinity(z)-1/[C(z)^2(tau-q(z))],
q(z)=-D(z)/C(z).                                          (18)
```

The function `q` is nonconstant. From `(17)`, `(18)`, and annihilation of every `Phi_z`,

```text
integral_T 1/(tau-q(z)) d rho(tau)=0.                     (19)
```

The integrand is defined to be zero at the projective point at infinity. By the open mapping
theorem, `q` sends a nonempty open set to an open subset of `C minus R`. Thus the Cauchy transform
of the restriction of `rho` to `R` vanishes on a nonempty open set. Analytic continuation and
Stieltjes-transform uniqueness force

```text
rho|_R=0.                                                  (20)
```

Equation `(17)` then gives `rho({infinity})=0`. Hence `rho=0`. The Riesz representation theorem
and Hahn--Banach prove the uniform density in `(16)`. `QED`

Pulling `(16)` back by `pi` and using `(15)` yields the exact horizontal completeness statement

```text
H_hor=closure_span_L2(nu)
  ({1} union {P_s r_z:z in C minus R}).                    (21)
```

Combining `(13)` and `(21)`, the same horizontal space that all centered polynomials miss is
recovered completely by conditional Cauchy data.

## Canonical positive horizontal Gram `[PROVED HERE]`

The selected boundary law has a canonical positive kernel. Centre the resolvent field by

```text
Phi_z^0(tau)=Phi_z(tau)-m_eta(z)
```

and define

```text
Gamma_eta(z,w)
 =integral_T Phi_z^0(tau) conjugate(Phi_w^0(tau))d eta(tau).  (21a)
```

For every finite packet `z_1,...,z_N` and scalars `c_1,...,c_N`,

```text
sum_(j,k)c_j conjugate(c_k)Gamma_eta(z_j,z_k)
 =integral_T |sum_j c_j Phi_(z_j)^0(tau)|^2d eta(tau)
 >=0.                                                       (21b)
```

Thus `Gamma_eta` is a Hermitian positive-semidefinite Gram kernel. Resolvent completeness `(21)`
shows that its feature vectors have closed span exactly `L^2_0(T,eta)`. Consequently its Gram rank
is not merely bounded by the boundary multiplicity; it equals it:

```text
rank(Gamma_eta)=dim_Hilbert L^2_0(T,eta).                  (21c)
```

In particular,

```text
Gamma_eta=0  iff eta is a point mass;
rank(Gamma_eta)=n-1 if eta has exactly n support points;
rank(Gamma_eta)=infinity if eta has infinite support.      (21d)
```

The boundary modulus therefore carries its own complete positive orientation after a law `eta` is
selected. Positivity is compatible with residual maximal HT; the missing datum in an arithmetic
carrier is the source-faithful identification of its kernel with such a complete Gram, not the
abstract existence of a positive Hilbert kernel.

### Full Pick-Gram splitting `[PROVED HERE; STANDARD COVARIANCE ENGINE]`

The horizontal kernel is one component of the complete Herglotz orientation. Define the ordinary
Pick Gram of `nu=Beta(eta)` by

```text
K_nu(z,w)
 =integral_R r_z(x)conjugate(r_w(x))d nu(x)
 =[m_nu(z)-conjugate(m_nu(w))]/[z-conjugate(w)].           (21e)
```

Define the within-leaf covariance kernel

```text
V_eta(z,w)=integral_T {
  integral_R r_z(x)conjugate(r_w(x))d mu_tau(x)
  -m_tau(z)conjugate(m_tau(w))}d eta(tau).                 (21f)
```

The conditional-expectation decomposition gives the pointwise orthogonal splitting

```text
r_z
 =m_eta(z) * 1
  +[m_(pi(.))(z)-m_eta(z)]
  +[r_z-m_(pi(.))(z)],                                    (21g)
```

whose three terms lie respectively in the constants, `H_hor,0`, and `H_ver`. Taking Gram products
proves

```text
K_nu(z,w)
 =m_eta(z)conjugate(m_eta(w))
  +Gamma_eta(z,w)
  +V_eta(z,w).                                             (21h)
```

All three summands are positive-semidefinite kernels. Their ranks are exact. The Cauchy kernels
`r_z` span a dense subspace of `L^2(nu)`: an orthogonal vector would define a finite complex measure
whose Cauchy transform vanishes off the real line, hence would vanish by Stieltjes uniqueness.
Applying the three orthogonal projections in `(21g)` and using `(21)` gives

```text
rank(mean kernel)=1,
rank(Gamma_eta)=dim L^2_0(T,eta),
rank(V_eta)=dim H_ver.                                     (21i)
```

Every stationary law `nu` has infinite support. By `(11)`, all centered polynomials lie in
`H_ver`; their classes modulo constants are linearly independent because a nonzero polynomial
cannot vanish on the infinite support of `nu`. Hence `H_ver` and `V_eta` have infinite rank for
every boundary law `eta`. Boundary mixing contributes the additional exact horizontal rank in
`(21c)` without changing a single polynomial moment.

Thus the positive orientation of a moment carrier has three intrinsic layers:

```text
source mean  +  boundary-law covariance  +  within-leaf covariance.  (21j)
```

This is the law of total covariance specialized to the canonical Nevanlinna support fibration; the
covariance identity itself is not claimed as new. The candidate new content is its intrinsic
moment-fiber placement, exact component ranks, and coexistence with residual maximal translation
HT and complete formal asymptotic collapse.

## One finite-centre germ determines the boundary law `[PROVED HERE]`

Resolvent completeness has a sharp analytic form. For `eta in P(T)`, write

```text
m_eta(z)=integral_T Phi_z(tau)d eta(tau).                  (22)
```

Fix any `z_0 in C minus R` with `C(z_0)!=0`. The analytic germ of `m_eta` at `z_0` determines
`eta` uniquely.

Indeed, suppose `eta_1` and `eta_2` give the same germ, and put `rho=eta_1-eta_2`. Analyticity makes
their transforms equal on a neighborhood `U` of `z_0` on which `C` is nonzero. Since `rho(T)=0`,
equation `(18)` gives

```text
integral_T 1/(tau-q(z))d rho(tau)=0  for z in U.           (23)
```

The open mapping theorem makes `q(U)` open. The same Stieltjes-uniqueness argument as in
`(19)`--`(20)` gives `rho=0`. Therefore

```text
eta |-> germ_(z_0)(m_eta)                                  (24)
```

is an affine injection. Equivalently, the complete Taylor jet of `m_eta` at one regular nonreal
point determines the whole projective boundary probability law.

On the ergodic boundary, even the zeroth-order value is enough. For fixed `z_0`, the map

```text
tau |-> m_tau(z_0)                                         (25)
```

is a fractional-linear injection because its determinant is `AD-BC=1` and its denominator has no
real-projective zero at a nonreal spectral argument.

By contrast, the parent flatness theorem says that the complete inverse-power asymptotic germ at
upper infinity is constant on every `Beta(P(T))`. Thus an arbitrary all-order moment shadow at
infinity and one analytic germ at finite centre occupy opposite determinacy phases:

> **Upper-infinity completion collapses the boundary simplex; one finite-centre analytic germ
> separates it completely.**

## Boundary splitting law

> **Inside every stationary Nevanlinna boundary mixture, the complete moment constraint induces
> the orthogonal splitting `L^2=H_hor direct-sum H_ver`. Every centered polynomial is vertical,
> every mean-zero horizontal vector is invisible to all polynomials, and conditional Cauchy
> resolvents span the entire horizontal space and generate its canonical full-rank positive Gram.
> Moment completeness and resolvent completeness are therefore transverse, not successive
> approximations to the same information.**

The law is exact at finite centre. It does not depend on asymptotic expansion, truncation, a choice
of spectral type, or a particular Nevanlinna coordinate.

## Hypertranscendental consequence

The parent theorem proves that a dense residual set of boundary laws `eta` makes the transform
`(22)` have a differentially algebraically independent full complex translation family.
Equations `(13)`, `(21)`, and `(24)` locate that freedom: it is variation of a projective boundary
probability law which every polynomial moment annihilates but the resolvent field and any one
regular finite-centre germ separate completely.

Thus maximal translation HT is compatible with complete moments because it lives in a canonical
horizontal coordinate absent from the polynomial completion, not because the moments were merely
too few.

## Positive RH-carrier consequence

Any RH route based only on polynomial moments, Hankel matrices, or their all-order formal
asymptotics is constant on `H_hor,0` whenever its carrier is indeterminate. A successful carrier
must contain finite-centre analytic or resolvent-level source data that separates this horizontal
space, and then must orient the separated data by a global sign law.

For a real entire source `A` with logarithmic derivative `T=A'/A`, the normalized
Hedenmalm--de Branges Bezoutian is the Pick kernel

```text
[conjugate(T(w))-T(z)]/[z-conjugate(w)].
```

If a source proof realizes this kernel through an indeterminate moment carrier, `(21h)` is the
required nonnegative three-layer factorization. Merely producing the abstract kernels in `(21h)`
without a source-faithful identification does not orient `A`.

The current Xi/Hedenmalm carrier has exactly this shape:

1. its pointed analytic germ supplies finite-centre source data and crosses the horizontal
   separation gate;
2. its reconstructed Bezoutian still needs the independent Hermitian orientation sign equivalent
   to RH.

This explains positively why moment determinacy and kernel orientation are different obligations.

## Parent-theory and novelty attack

1. `[SEARCH]` `N`-extremality is classically equivalent to density of polynomials in
   `L^2(mu_tau)`; nonextremal solutions have polynomial-orthogonal directions.
2. `[SEARCH]` Conditional expectation, disintegration, and uniqueness of the Cauchy transform are
   standard.
3. `[PROVED HERE]` The parent support-label projector makes the entire mean-zero boundary pullback
   an explicit polynomial-invisible Hilbert subspace for every boundary mixture.
4. `[PROVED HERE]` The Möbius parameter identity and Stieltjes uniqueness make the conditional
   resolvent fields linearly complete on exactly that invisible boundary space.
5. `[PROVED HERE]` The same identity makes one regular finite-centre analytic germ an injective
   coordinate on the whole boundary probability simplex, while the all-order upper-infinity germ
   remains constant.
6. `[PROVED HERE]` Centered conditional resolvents give a canonical positive Gram whose exact rank
   is the Hilbert dimension of the polynomial-invisible boundary coordinate.
7. `[SEARCH + PROVED SPECIALIZATION]` The law of total covariance is standard. Its specialization
   gives the exact three-layer Pick-Gram splitting and component-rank law for the canonical
   Nevanlinna support fibration.
8. `[CANDIDATE RESIDUE]` Preliminary local and exact web searches found no theorem combining the
   intrinsic boundary conditional expectation, polynomial-blind horizontal space, resolvent
   completeness, finite-centre/upper-infinity determinacy duality, and residual full-translation
   differential independence inside one complete moment fiber.
9. The claim remains `[NOVELTY UNVERIFIED]` pending specialist review in moment theory, operator
   disintegration, and differential algebra.

No numerical experiment and no RH assumption enter the theorem.

## Honest significance score

Together with the parent residual theorem, Bauer retract, and finite-jet threshold, this supports
an internal **90/100 candidate**, with a deliberately wide **72--94** range pending specialist
proof and priority review. It is not scored higher merely because the same geometry has several
exact formulations.

- **Why it materially strengthens the Bauer retract:** the theorem identifies the information-theoretic
  geometry of the canonical modulus. It proves an exact orthogonal separation between all
  polynomial data and the boundary coordinate, then proves that conditional resolvents recover
  that coordinate completely. The residual HT theorem is thereby located in a named Hilbert
  direction rather than merely placed on a large convex set.
- **Why 90 is not yet verified:** each proof step has classical parents, the priority audit is
  preliminary, the theorem is not formally verified in Lean, and the Xi orientation sign remains
  entirely open.

## Lean status

The canonical boundary projector and Bauer retract are formalized in
`NevanlinnaConstraintProjector.lean`, `NevanlinnaStationaryBauer.lean`, and
`NevanlinnaBauerRetract.lean`.  `MomentFiberPickSchurPhase.lean` formalizes the self-adjoint
idempotent Hilbert projection, exact horizontal/vertical orthogonal decomposition, centered-
polynomial verticality, and horizontal/vertical blindness.  `CompleteCauchyGermClosure.lean`
proves resolvent completeness in its sharp arbitrary-node form: one complete nonreal Cauchy jet
determines the measure.  The concrete Nevanlinna disintegration remains an explicit classical
input, not an axiom.

Formalization audit (needs-audit pass): no bounded self-contained kernel closes a gate. The whole
theorem — conditional-expectation identity `(5)`, `H_hor/H_ver` splitting `(8)`, polynomial blindness
`(11)`, resolvent completeness `(21)`, and the three-layer Pick-Gram `(21h)` — is built on the same
absent Nevanlinna/disintegration/Stieltjes-uniqueness stack as its parent moment-fiber cards. No
partial file is added.

Unconditional promotion re-audit: `nevExtremalFamily` now removes the abstract classical boundary
input, and `NevBauerMarkovFacesUnconditional.lean` instantiates its measure-side and Markov
projectors.  This does not close the Hilbert theorem.  `BoundaryConditionalProjection` remains an
abstract structure with no constructor on `L²(Beta eta)`; its three theorems are projection algebra,
not the conditional-expectation identity or the concrete horizontal/vertical splitting.
`measure_eq_of_completeCauchyJet_eq` separates two measures but does not prove density of
conditional resolvents in the horizontal subspace.  No definitions or theorems were found for the
centered horizontal Gram, within-leaf Gram, the three-layer Pick splitting, or their exact ranks.
Those exact connectors must be formalized before Stage 3; no separation theorem or abstract
projection is substituted for them.

## Gates

- [x] parent support fibration and Bauer projector used intrinsically
- [x] conditional-expectation identity proved
- [x] horizontal/vertical orthogonal splitting proved
- [x] centered-polynomial verticality proved
- [x] mean-zero boundary polynomial blindness proved
- [x] conditional-resolvent completeness proved
- [x] canonical centered-resolvent Gram positivity and exact rank proved
- [x] full Pick kernel split into mean / horizontal / vertical positive Grams
- [x] exact component-rank law proved
- [x] one regular finite-centre germ proved boundary-law determinate
- [x] one scalar finite-centre value proved extremal-leaf determinate
- [x] finite-centre / upper-infinity determinacy duality proved
- [x] residual HT phase located in the horizontal boundary coordinate
- [x] concrete RH-carrier consequence scoped
- [x] preliminary local collision search
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit
- [x] complete Lean theorem surface from explicit Nevanlinna disintegration input

## Log

- 2026-07-12 -- Identified the constraint projector with conditional expectation on every
  stationary boundary mixture. Proved the horizontal/vertical `L^2` splitting, exact blindness of
  all centered polynomials to the mean-zero boundary space, and linear completeness of the
  conditional Cauchy resolvents on that same space.
- 2026-07-12 -- Extracted the finite-jet threshold companion: every finite local jet leaves residual
  maximal HT in an infinite positive level, while the complete germ closes the boundary modulus.

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

## Log — the conditional-expectation identity and polynomial blindness are formalized `[PROVED]`

New module `HTGeometry/BoundaryConditionalExpectation.lean` (wired, axiom-clean).  It works with the
measure-level barycenter `NevanlinnaBoundaryFamily.measureBarycenter` and its disintegration.

- `leafKernel`, `leafAverage`, `markovAverage` — the leaf kernel as a genuine `Kernel`, the leaf
  average as a function of the projective parameter, and the constraint average on the line;
  `stronglyMeasurable_leafAverage` from `StronglyMeasurable.integral_kernel`.
- `ae_projectiveLabel_eq` — almost every point of a leaf carries that leaf's own label.
- `integral_measureBarycenter` — the carrier integral is the parameter integral of leaf integrals
  (through the corpus `integral_bind_real`).
- **`integral_comp_projectiveLabel_mul_barycenter`** — equation `(4)`: a label-measurable factor
  cannot distinguish an observable from its leaf average.
- **`markovAverage_ae_eq_condExp`** — equation `(5)`: `P_s = E_ν[· | σ(π)]` for the σ-algebra
  `labelSigmaAlgebra = comap π`, proved through `ae_eq_condExp_of_forall_setIntegral_eq`.
- **`leafAverage_eval`** — equation `(10)`: `P_s p = L_s(p)·1`, from `momentFunctional_eq_integral`.
- **`leafAverage_eval_sub_const`** — equation `(11)`: centered polynomials are vertical.
- **`integral_eval_mul_comp_projectiveLabel`** — equations `(12)`--`(13)`: every mean-zero label
  observable annihilates every polynomial against the carrier.

Still open for Stage 3: the `L²` orthogonal splitting `(6)`--`(8)` as a statement about
`H_hor`/`H_ver` subspaces, resolvent completeness `(14)`--`(21)` (whose analytic core is uniform
density of `span({1} ∪ {Φ_z})` in `C(T)` by Stieltjes uniqueness and the open mapping theorem), and
the three-layer Pick–Gram splitting `(21a)`--`(21i)` with its exact ranks.

### Log — the orthogonal splitting `(6)`--`(8)` is formalized in integral form `[PROVED]`

- `integral_comp_projectiveLabel_mul_eq_parameter` — pairing an observable with a label observable
  is the parameter integral of its leaf averages, `⟨f, G∘π⟩ = ∫_T G·(P_s f) dη`.
- **`forall_integral_comp_projectiveLabel_mul_eq_zero_iff`** — equations `(7)`--`(8)`: a bounded
  observable is orthogonal to *every* bounded label observable exactly when almost every leaf
  average vanishes.  The forward direction pairs against the sign of the leaf average, so the
  vertical space is exactly the kernel of leaf averaging and the horizontal space is exactly the
  closed span of the label observables.

Remaining: resolvent completeness `(14)`--`(21)` and the three-layer Pick--Gram splitting
`(21a)`--`(21i)`.

### Log — the analytic core of resolvent completeness is formalized `[PROVED]`

Two new modules, both wired into `GaloisForLFunctions.HTGeometry` and axiom-clean.

`HTGeometry/CauchyTransformOpenUniqueness.lean`

- `analyticOnNhd_resolventTransform_upper` — the resolvent transform of a finite real measure is
  analytic on the upper half-plane (from mathlib's `analyticOn_resolventTransform`).
- `eqOn_upper_of_eqOn_open` — agreement on a nonempty open subset propagates to the whole upper
  half-plane by the identity theorem.
- `tendsto_mul_im_resolventTransform` — `y·Im S_μ(iy) → μ(ℝ)`, so the total mass is read off the
  transform; hence `measure_univ_eq_of_eqOn_upper`.
- **`measure_eq_of_resolventTransform_eqOn_open`** — two finite measures whose Cauchy transforms
  agree on a nonempty open subset of the upper half-plane are equal (normalise by the common mass
  and apply the complete-germ closure theorem).

`HTGeometry/CauchyKernelDensityVanishing.lean`

- `analyticOnNhd_densityCauchyTransform` — the Cauchy transform of an integrable complex density is
  analytic off the real axis (four-fold positive/negative real/imaginary decomposition into
  resolvent transforms of finite measures).
- `densityCauchyTransform_conj` — conjugating the density conjugates the transform through the
  conjugate point.
- `real_density_eq_zero_of_transform_eq_zero_upper` — a **real** integrable density whose transform
  vanishes on the upper half-plane vanishes a.e.
- **`density_eq_zero_of_transform_eq_zero_both`** — an integrable **complex** density whose
  transform vanishes on a nonempty open subset of *each* half-plane vanishes a.e.  Vanishing on one
  half-plane alone is genuinely insufficient (`(τ − i)⁻²` against Lebesgue measure), which is why
  the boundary argument uses the Weyl map on both sides.

This is exactly the mechanism `(19)`--`(20)` needs: annihilating `1` and every `Φ_z` turns into a
Cauchy transform of `ḡ·η` vanishing on the `q`-image of each half-plane, whence `g = 0`.  What
remains for the card is the assembly: the Möbius identity `(18)` for the constructed leaf transform,
the openness of the `q`-image, and then `(21)` and the Gram-splitting statements `(21a)`--`(21i)`.

### Log — the Weyl pole map is proved nonconstant with open half-plane images `[PROVED]`

`HTGeometry/NevanlinnaQuotientOpenImage.lean` (wired, axiom-clean):

- `analyticOnNhd_quotient` — `q(z) = −d(z)/c(z)` is analytic wherever `c` does not vanish;
- **`quotient_not_constant`** — `q` cannot be constant with a nonreal value on any nonempty open
  set.  Mechanism: a constant value `w` makes `−d = w·c` on an open set, hence everywhere by the
  identity theorem for the two entire entries; evaluating on the real axis, where both entries are
  real, forces `Im w · c(x) = 0`, so `c ≡ 0` and then `d ≡ 0` on `ℝ`, contradicting the
  determinant-one no-common-zero law of the lower row;
- **`isOpen_quotient_image`** — consequently the image of a preconnected open set of nonreal points
  on which `q` stays nonreal is open (mathlib's `AnalyticOnNhd.is_constant_or_isOpen`).

With the Weyl map placing `q(lower) ⊆ upper` and `q(upper) ⊆ lower`, this supplies exactly the two
nonempty open sets required by `density_eq_zero_of_transform_eq_zero_both`.

### Log — resolvent completeness `(16)`--`(21)` is formalized `[PROVED]`

`HTGeometry/NevanlinnaResolventCompleteness.lean` (wired, axiom-clean):

- `chartMeasure`, `chartMeasure_apply`, and **`integral_onePoint_split`** — an integral over the
  projective line splits as the finite-chart integral plus the mass at infinity;
- `leafCauchy` — equation `(14)`, the leaf Cauchy transform as a function of the parameter;
- `denominator_ne_zero` — the Möbius denominator never vanishes on the finite chart, because the
  Weyl pole is nonreal;
- **`leafCauchy_sub_infty`** — equation `(18)`, the Möbius partial fraction
  `Φ_z(τ) − Φ_z(∞) = −c(z)^{-2}(τ − q(z))^{-1}`;
- **`eq_zero_ae_of_annihilates_leafCauchy`** — equations `(19)`--`(20)`: a parameter density
  annihilating the constant and every `Φ_z` vanishes almost everywhere.  Removing the constant
  leaves the chart Cauchy transform evaluated at `q(z)`; the Weyl pole map carries each half-plane
  onto an open subset of the other, and a density whose Cauchy transform vanishes on an open subset
  of both half-planes is zero;
- **`HTGeometry.analyticNevCarrier_eq_zero_ae_of_annihilates_leafCauchy`** — the same statement for
  the constructed family of an indeterminate normalised moment sequence, with no hypothesis beyond
  `PositiveMomentForm s`, `BoundedKernel s 0`, `s 0 = 1`.

Remaining for the card: the three-layer Pick--Gram splitting `(21a)`--`(21i)` (the law of total
covariance on the support fibration) and its exact ranks.

### Log — the three-layer Pick--Gram splitting is formalized `[PROVED]`

`HTGeometry/NevanlinnaPickGramSplitting.lean` (wired, axiom-clean):

- `integral_re_eq`, `integral_im_eq`, `integral_ofReal_eq`, and **`integral_bind_bounded`** —
  complex Fubini for a bounded observable over a measurable probability kernel, from the corpus
  `integral_bind_real` on real and imaginary parts;
- `boundaryMean`, `boundaryGram` `(21a)`, `withinLeafGram` `(21f)`, `carrierPickGram` `(21e)`;
- **`carrierPickGram_eq_add`** — equation `(21h)`, the law of total covariance on the support
  fibration: `K_ν = m_η(z)·conj m_η(w) + Γ_η + V_η`;
- **`boundaryGram_self`** — `(21b)` in its self-adjoint form: `Γ_η(z,z)` is the boundary variance
  `∫ ‖Φ_z − m_η(z)‖² dη`, in particular real and nonnegative;
- `leafCauchy_ae_eq_of_boundaryGram_self_eq_zero` — a vanishing self-Gram makes the leaf transform
  almost everywhere constant;
- **`boundaryGram_eq_zero_iff_exists_dirac`** — equation `(21d)`, first case: the boundary
  covariance vanishes identically **iff** the boundary law is a point mass.  The forward direction
  runs through resolvent completeness: constancy of every `Φ_z` makes every mean-zero indicator
  test function annihilate the constant and every `Φ_z`, hence vanish, so every measurable set has
  mass `0` or `1`, and a two-valued probability law on the projective line is a Dirac mass
  (`exists_eq_dirac_of_measure_eq_zero_or_one`, added to `PositiveMeasureExtremeRays.lean`).

Remaining for the card: the exact Hilbert-dimension counts in `(21c)`, `(21d)` (the `n−1` and
infinite cases) and `(21i)`, i.e. identifying the closed span of the centered feature family with
`L²₀(T,η)` and reading off dimensions.

### Log — the Hilbert layer is complete; card promoted `[PROVED]`

`HTGeometry/NevanlinnaBoundaryL2Completeness.lean` (wired, axiom-clean) closes the last items.

- `leafCauchy_conj`, `memLp_leafCauchy`, `leafCauchyL2`, `constL2`, `resolventSubmodule`;
- **`resolventSubmodule_topologicalClosure_eq_top`** — equation `(21)` in the Hilbert space: the
  constants together with the leaf Cauchy transforms are dense in `L²(T,eta)`.  A vector orthogonal
  to all of them has vanishing mean and, using `conj Φ_z = Φ_z̄`, annihilates every leaf transform,
  so resolvent completeness forces it to vanish;
- **`centeredSubmodule_orthogonal`**, **`centeredSubmodule_topologicalClosure`** — equation
  `(21c)`: the orthogonal complement of the centered feature family is exactly the constants, hence
  the closed span of the features is exactly the mean-zero subspace.  This is the exact rank of the
  boundary-law covariance kernel;
- `finrank_span_constL2` — the mean layer of `(21i)` has rank one;
- `polynomial_eq_zero_of_ae_eq_zero_of_support_infinite` — the card's independence step for the
  vertical layer: a polynomial vanishing almost everywhere on an infinite-support carrier is zero;
- `leafCauchy_injective_on_chart` (in `NevanlinnaResolventCompleteness.lean`) — one scalar
  finite-centre value separates the extremal leaves.

Every numbered statement of the card is now an unconditional Lean theorem.  Promoted to
`3-formalized/nad` with companion
`moment-polynomial-blind-resolvent-complete-boundary-splitting-formalized.md`; the remaining gates
are the external specialist and priority audits.

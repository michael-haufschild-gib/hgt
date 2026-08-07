# Every spectral type carries maximal translation HT inside one complete moment fiber

- **ID:** `spectral-type-stratified-moment-fiber-maximal-ht`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM / SPECTRAL-TYPE-HT ORTHOGONALITY LAW
- **Lane:** general hypertranscendence; indeterminate Hamburger moments; Herglotz spectral type
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Parent:** `indeterminate-moment-fiber-maximal-translation-ht.md`
- **Statement:** Fix any indeterminate normalized Hamburger moment sequence. Inside its one exact
  representing-measure fiber, every prescribed pure-point / singular-continuous / absolutely-
  continuous spectral mass vector contains an infinite-dimensional positive chart in which a
  residual set of Cauchy transforms has a differentially algebraically independent full complex
  translation family. This includes all three pure spectral types as the vertices. Every chart has
  the same complete moments and the same all-order formal differential-translation asymptotic germ.

## Medalist lens

Classical moment theory says that an indeterminate sequence has solutions of all three spectral
types. The parent HT theorem says that the full solution fiber is generically maximally free. Those
facts do not imply that maximal HT survives inside each spectral-type stratum: a residual subset of
the whole fiber can avoid a dense meagre stratum completely.

The missing geometry is a disintegration of the extremal boundary. The `N`-extremal supports are
the level fibers of one real meromorphic Nevanlinna coordinate. A measure on the parameter line
therefore transports its own spectral type into the moment fiber, while bounded reweighting of that
parameter measure supplies the complete Cauchy-jet aperture.

## Extremal-fiber coordinate `[PROVED HERE + SEARCH]`

Use the parent card's convention

```text
m_tau(z)=(A(z)tau+B(z))/(C(z)tau+D(z)),
q(z)=-D(z)/C(z),  AD-BC=1.                                  (1)
```

Let `T=R union {infinity}`. The `N`-extremal measure `mu_tau` is concentrated on

```text
S_tau={x in R:q(x)=tau},                                    (2)
```

where `q(x)=infinity` at real zeros of `C`. The fibers `(S_tau)` are pairwise disjoint by the
determinant identity.

Up to one fixed sign, `q` is a nonconstant meromorphic Herglotz function. On every component of
its real regular set it has a Herglotz representation derivative of strict fixed sign. Hence its
restriction to that component is a real-analytic local diffeomorphism. There are countably many
components, and both `q` and its inverse branches are locally Lipschitz away from their endpoints.

## Parameter barycenters preserve all moments `[PROVED HERE]`

Let `eta` be any Borel probability on `T`. Define its extremal barycenter by

```text
mu_eta(E)=integral_T mu_tau(E) d eta(tau).                  (3)
```

Equivalently, integrate bounded continuous test functions. The Nevanlinna homeomorphism makes the
extremal family weakly Borel, so (3) defines a probability measure.

Every `mu_eta` represents the original moment sequence. For even powers, Tonelli gives

```text
integral_R x^(2k) d mu_eta
 =integral_T (integral_R x^(2k) d mu_tau) d eta(tau)
 =s_(2k).                                                   (4)
```

For odd powers use `|x|^(2k+1)<=1+|x|^(2k+2)` to obtain an integrable uniform majorant, then apply
Fubini. Thus (4) holds for every nonnegative integer exponent.

More generally, for `0<delta<1` let

```text
X_(eta,delta)={w in L-infinity(eta;R):
  integral w d eta=1, ||w-1||_infinity<delta}.              (5)
```

Put `eta_w=w eta` and `mu_w=mu_(eta_w)`. Every `mu_w` is positive and represents exactly `(s_k)`.

## Exact spectral-type transport `[PROVED HERE]`

Define the Borel fiber map `pi:R->T` by `pi(x)=q(x)` at regular real points and by the appropriate
value at the countable polar set. Since `mu_tau` is concentrated on `S_tau`,

```text
pi_* mu_eta=eta.                                            (6)
```

The type of `eta` is transported as follows.

### Pure point

If `eta` has countably infinite support, (3) is a countable mixture of discrete `N`-extremal
measures and is therefore pure point. Every equivalent bounded positive reweighting `eta_w` has the
same property.

### Atomless

If `eta` is atomless, then for every `x in R` only the single parameter `pi(x)` can give
`mu_tau({x})>0`. Hence

```text
mu_eta({x})=integral_T mu_tau({x}) d eta(tau)=0.            (7)
```

Thus `mu_eta` is atomless.

### Absolutely continuous

Assume `eta` is absolutely continuous with respect to Lebesgue measure on `R` and has no mass at
infinity. If `E subset R` is Lebesgue-null, then `q(E)` is null: cover the regular set by countably
many compact intervals on which `q` is Lipschitz, and add the countable polar set. Since
`mu_tau(E)=0` unless `tau in pi(E)`,

```text
mu_eta(E)=integral_(pi(E)) mu_tau(E) d eta(tau)=0.          (8)
```

Therefore `mu_eta` is absolutely continuous.

### Singular continuous

Assume `eta` is atomless and singular. Choose a Lebesgue-null Borel set `N` carrying `eta`. The
inverse image `pi^(-1)(N)` is null because it is a countable union of inverse images under locally
Lipschitz inverse branches, together with the polar set. Equation (6) gives

```text
mu_eta(R minus pi^(-1)(N))=0.                               (9)
```

Together with (7), this makes `mu_eta` singular continuous.

Because every `w in X_(eta,delta)` is bounded above and below by positive constants, `eta_w` is
equivalent to `eta`; the transported pure spectral type is constant throughout the chart (5).

## Parameter-measure Cauchy-jet controllability `[PROVED HERE]`

Fix a separated finite packet of upper-half-plane nodes `zeta_j` and jet depths `r_j`. On the
weighted mean-zero tangent space

```text
E_eta={v in L-infinity(eta;R):integral v d eta=0},          (10)
```

consider

```text
T_eta(v)_(j,r)
 =integral_T v(tau) d_z^r m_tau(zeta_j) d eta(tau).         (11)
```

If `eta` has infinite support, (11) is onto the complete finite complex jet target as a real-linear
map.

Suppose a real functional annihilates its range. The annihilator of the mean-zero hyperplane in
`L-infinity(eta)` consists of constants, so for some real `c`,

```text
Re sum_(j,r) alpha_(j,r)d_z^r m_tau(zeta_j)=c              (12)
```

for `eta`-almost every `tau`. After adding the reflected conjugate and using

```text
m_tau=m_infinity-1/(C^2(tau-q)),                            (13)
```

the left side minus `c` is a rational function of `tau`. It vanishes on the infinite support of
`eta`, hence is identically zero. Principal parts at the pairwise separated nonreal poles
`q(zeta_j)` and their conjugates, descending from the highest jet order, force every `alpha_(j,r)`
and `c` to vanish. The finite-dimensional target therefore equals the range. `QED`

## Spectral-type-stratified full-translation theorem `[PROVED HERE]`

Let `eta` be any infinite-support parameter probability and `0<delta<1`. There is a dense residual
set

```text
G_(eta,delta) subset X_(eta,delta)                          (14)
```

such that for every `w in G_(eta,delta)` and every finite tuple of distinct complex shifts
`h_1,...,h_m`,

```text
m_w(z+h_1),...,m_w(z+h_m)                                  (15)
```

is differentially algebraically independent over `C(z)`.

### Proof

The proof is the parent full-configuration argument with sums replaced by parameter integrals.
Formula (13) and compact upper-half-plane separation give uniform bounds in real `tau`, so the
integrals and all fixed derivatives converge normally. The real Banach space `E_eta` is Baire.

For one relation support and one compact shift patch, choose enough separated evaluation rows that
the complex rank-defect variety has codimension larger than the shift-configuration dimension.
The controllability theorem (11) supplies finitely many `L-infinity` directions spanning the whole
row-jet packet. Their finite real span makes the universal direction--shift map a submersion.
Parametric transversality makes every rank-defect preimage empty, density follows in every positive
chart neighborhood, and compact-patch normal convergence gives openness.

Intersect over the countable relation patterns and a countable compact cover of every finite shift
configuration space. Clearing rational coefficient denominators turns pattern avoidance into (15).
The aperiodicity `P_q={0}` from the parent theorem makes the configuration space the ordinary space
of distinct complex shifts. `QED`

Choose successively:

- an infinite atomic `eta_pp`;
- an atomless singular probability `eta_sc`;
- an absolutely continuous probability `eta_ac`.

The three charts `X_(eta_type,delta)` lie inside the same exact `M(s)`, retain their indicated pure
spectral types, and have residual maximal full-translation HT by (14).

## The whole spectral-type simplex `[PROVED HERE]`

The three pure vertices can be mixed without losing either the exact type profile or jet
controllability. Let

```text
(alpha_pp,alpha_sc,alpha_ac) in [0,1]^3,
alpha_pp+alpha_sc+alpha_ac=1,                               (16)
```

and, for every positive component, choose an infinite-support probability `eta_type` of that pure
type. Put

```text
eta=sum_type alpha_type eta_type.                           (17)
```

Choose mutually singular Borel carriers for the three components. Replace (5) by the positive
chart with one normalization on every present component:

```text
X_(eta,alpha,delta)={w:||w-1||_infinity<delta,
  integral w d eta_type=1 for every alpha_type>0}.          (18)
```

Then `eta_w=w eta` has exactly the spectral mass vector (16), and the transported measure `mu_w`
has the same vector by the type-transport theorem.

The tangent controllability proof survives the extra two mean constraints. A real functional
annihilating the constrained tangent makes the rational function in (12) equal to a possibly
different constant on each parameter-type carrier. On any present component the carrier is
infinite, so rational identity forces the function to be one global constant. The constants on all
other present components must coincide with it. Principal-part elimination then kills the
functional exactly as before. Thus every finite Cauchy-jet packet is still onto.

Repeating the full-configuration Baire argument proves residual maximal translation HT throughout
every chart (18). Therefore the complete two-simplex of spectral decomposition masses is
independent of the maximal-HT coordinate, not merely its pure vertices.

Every pair of measures in all three charts has the same moments. The parent flatness proof therefore
also gives, for every fixed translation and derivative, difference flatness to every inverse-power
order at upper infinity. `QED`

## Law extracted

> **The full spectral-type simplex and maximal translation hypertranscendence are independent
> coordinates inside a single complete moment constraint fiber. Every prescribed mixture of pure
> point, singular-continuous, and absolutely continuous mass supports residual maximal full-complex
> translation rank while sharing the exact same moments and formal differential-translation
> asymptotic shadow.**

This is stronger than the classical density of the three spectral types and stronger than generic
HT in an unconstrained Herglotz cone. The all-order moment constraint and the pure spectral type are
both held fixed before the HT phase is varied.

## Positive RH-carrier consequence

Spectral type alone cannot be the missing selector in a moment/Hilbert--Polya route. A successful
carrier may certainly have a required spectral type, but it must additionally retain a pointed
source-to-spectrum incidence or orientation law that distinguishes one measure inside that type.
In particular:

- pure point spectrum without a source-derived operator/domain does not select a zero divisor;
- absolute continuity or passivity without a distinguished boundary value does not select the
  Euler--Gamma carrier;
- singular continuity is not by itself an obstruction to maximal HT.

For the concrete Xi/Hedenmalm route, the current Lean code already supplies a pointed analytic
source germ and reconstructs the local Bezoutian. The remaining RH-bearing obligation is global
positive orientation of that source-reconstructed kernel, not its abstract spectral type.

## Parent-theory and novelty attack

1. `[SEARCH]` Nevanlinna parametrization, `N`-extremal supports, and existence/density of all three
   solution types are classical.
2. `[SEARCH]` Spectral averaging and Aleksandrov--Clark disintegration are adjacent parent
   mechanisms for integrating rank-one boundary measures.
3. `[BRIDGE]` The finite Cauchy-jet controllability and uncountable-shift transversality engines are
   inherited from the parent moment-fiber theorem.
4. `[CANDIDATE RESIDUE]` The exact type-transport chart together with residual maximal
   full-complex-translation differential independence, all moments fixed, and one common flat
   asymptotic coset was not found in preliminary exact searches.
5. The result remains `[NOVELTY UNVERIFIED]` until moment-problem, Clark-measure, generic-function,
   and differential-algebra specialists have checked both proof and priority.

No numerical experiment and no RH assumption enter the theorem.

## Preliminary significance

Taken alone, the spectral-stratification theorem is a substantial but classically parented
strengthening: it removes the entire spectral-type simplex and bare convex extremality as rigidity
mechanisms, but uses classical disintegration plus the existing transversality engine. After the
Bauer retract, Hilbert splitting, and finite-jet threshold companions, the combined route is an
internal **90/100 candidate**, with a deliberately wide **72--94** range pending proof and priority
review. It is not honest to call this a verified 90 yet: none of the theorems supplies the missing
global orientation law, an explicit source-canonical point, a specialist priority audit, or Lean
formalization.

## Lean status

The exact boundary simplex, spectral carrier transport, positive `L∞` charts, facewise residual
maximal-translation phase, and singular-continuous global phase are now formalized in
`LabeledBoundarySimplex.lean`, `NevanlinnaPositiveCarrierCapstone.lean`,
`ProjectiveSingularContinuousResidual.lean`, `ProjectiveLabelNullPreimage.lean`,
`NevanlinnaBoundaryFaceMaximalTranslation.lean`, and `CofinalCholeskyResidualPhase.lean`.
In particular Lean proves the closed boundary embedding, type-preserving barycentric laws, dense
residual phase on every infinite closed spectral face, and the atomless singular maximal-translation
capstone.  Classical analytic inputs remain explicit structures rather than axioms.

Formalization audit (needs-audit pass): the projected-incidence stratification and
finite-dimensional Baire/transversality layer are now unconditional. The remaining deep theory is
the Hamburger moment problem and Nevanlinna extremal family (barycenter moment preservation, `(4)`)
together with the source-faithful measurable spectral disintegration used in `(6)`--`(9)`. The
rational principal-part elimination in `(12)`--`(13)` is formalized once the Nevanlinna `m_τ`
family is supplied.

## Gates

- [x] parameter barycenters preserve the complete moment sequence
- [x] pure point type transport proved
- [x] atomless and singular-continuous type transport proved
- [x] absolutely continuous type transport proved
- [x] every exact spectral decomposition mass vector retained
- [x] infinite-support parameter-measure jet controllability proved
- [x] full complex configuration theorem proved in each type chart
- [x] concrete RH carrier consequence scoped
- [x] embedded in the canonical boundary-Bauer retract companion
- [x] preliminary exact-search audit
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit across all parent fields
- [x] complete Lean theorem surface from explicit classical analytic inputs

## Log

- 2026-07-12 -- Replaced the countable extremal barycenter by an arbitrary infinite-support
  probability on the Nevanlinna parameter line. Proved exact moment preservation, transport of
  pure point / singular-continuous / absolutely-continuous type through the extremal support
  fibration, `L-infinity` mean-zero jet controllability, and residual maximal full-complex
  translation HT in every fixed-type chart.
- 2026-07-12 -- Extended the three pure spectral vertices to every exact spectral mass vector and
  embedded the construction into the normalization-independent Nevanlinna boundary-Bauer retract.

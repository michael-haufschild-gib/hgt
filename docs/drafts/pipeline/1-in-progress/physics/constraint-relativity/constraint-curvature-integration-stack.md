# The integration stack of the hypertranscendental constraint-curvature field

- **ID:** `constraint-curvature-integration-stack`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT CONJECTURE / UNIFIED REALIZATION OBJECT
- **Scientific status:** `[CONJECTURE] [LINEAR FIBER SKELETON LEAN-FORMALIZED] [RAW LIM1 CARRIER KILLED] [CURVATURE-ONLY FIBER KILLED] [ANOMALY-COLLIGATION REFINEMENT] [NOVELTY OPEN]`
- **Parents:**
  - `source-transgression-field.md`
  - `calibrated-clock-curvature-class.md`
  - `hypertranscendental-constraint-corona-motive.md`
- **Statement:** The common object is not an ordinary derived limit of finite clocks. It is the
  source-curvature field together with the derived moduli space of its global integrations in
  each realization category. Continuation, boundary conditions, monodromy, spectral
  incompleteness, and positivity are five invariants of that one integration fiber.

## Ordinary finite-clock `lim^1` no-go

Suppose every calibrated gauge space `G_N` is finite-dimensional over a field. For fixed `N`, the
images of all later transition maps in `G_N` form a descending chain of finite-dimensional
subspaces and therefore stabilize. The tower is Mittag--Leffler, so its ordinary countable
algebraic `lim^1` vanishes.

Hence a nonzero class in

```text
lim^1_N G_N                                                   (1)
```

cannot be the general thin boundary field when the gauges are genuinely finite-clock linear data.
A nonzero `(1)` would require infinite-dimensional gauges, nonclosed topological images, partial
transition maps, or another singular completion. Merely declaring one of these does not construct
the source object.

**Positive theorem-shape.** In a Mittag--Leffler realization, every compatible affine obstruction
is effective after gauge. This defines a positive clock-effective phase rather than a failed
boundary theory.

## Source curvature

Let `A_x` be the independently given algebra of nonlocal source constraints of a point `x`. Let
`O_N(x)` be its finite observable clocks and let `T_N(a)` be the calibrated `N`-shadow of
`a in A_x`. Define

```text
kappa_N(a)=p_N T_(N+1)(a)-T_N(a) p_N.                       (2)
```

The exact formal laws are

```text
p_01 kappa_12+kappa_01 p_12=kappa_02,                       (3)
kappa(a b)=kappa(a) T(b)+T(a) kappa(b),                     (4)
kappa(T+g)=kappa(T)+kappa(g).                               (5)
```

Equations `(3)`--`(5)` are Lean-formalized. They are respectively the clock Bianchi law, the
constraint-algebra Leibniz law, and gauge additivity.

**[CONJECTURE — CANONICAL SOURCE CURVATURE]** Source symbol, affine normalization, and source
relations canonically select `(2)` up to a contractible calibrated choice. When the shadows are
forward-compatible, the intrinsic finite field is the Lean-formalized quotient transfer
`O_(N+1)/range(i_N) -> O_N`, not a split boundary vector. The resulting nonlinear higher-curvature
field `bold_kappa_x` is invariant under analytic source-presentation equivalence.

The curvature field can be nonzero and still globally integrable. Nonzero curvature and
nonintegrability are distinct.

## Pointed Spencer--Helmholtz sharpening `[FINITE MODEL PROVED; HT TOTALIZATION CONJECTURAL]`

The phrase “source curvature” is too loose until its local equations and primitive are named.
Let `F=(F_i)` be a finite source map on jet coordinates `u_j^b`, and let

```text
J_(i;a,b,j)=partial(D^a F_i)/partial(u_j^b).                (5c)
```

Two independent compatibility tensors are forced.

```text
Helmholtz_(i;a,b,j,c,k)
  = partial_(u_k^c) J_(i;a,b,j)
    - partial_(u_j^b) J_(i;a,c,k),                         (5d)

Spencer_(i;a,b,j)
  = J_(i;a+1,b,j)-D J_(i;a,b,j)-J_(i;a,b-1,j),             (5e)
```

with the last term zero at `b=0`.  Equation `(5d)` is vertical closedness of the variational
one-form.  Equation `(5e)` is the commutator identity

```text
[partial_(u_j^(b+1)),D]=partial_(u_j^b).                   (5f)
```

Every actual finite differential-polynomial source map satisfies `(5d)`--`(5e)`.  Conversely, at
the finite complex polynomial level the full Jacobian field plus one calibrated value reconstructs
the source map exactly.  The Jacobian without the calibration is nonfaithful already for `x` and
`x+1`.  This pointed reconstruction and a nonlinear noncommuting Hénon/translation source pair are
Lean-formalized in `MvPolynomialJacobianFDeriv.lean`; the Spencer commutator core is already
Lean-formalized in `DifferentialUnitEquation.lean`.

The infinite HT object should combine vertical variation and source descent rather than treating
them as unrelated curvatures.  On the bifiltered Kähler--Tate correspondence object, let

```text
d_tot=d_src+(-1)^p d_var,
omega_F=(vertical Frechet form, source-boundary increments) in Tot^1.   (5g)
```

The mixed component of `d_tot omega_F` is precisely the typed compatibility between source
restriction and variational realization.  A global source operation `Phi_F` is a calibrated
primitive

```text
omega_F=d_tot Phi_F.                                       (5h)
```

> **[CONJECTURE -- POLARIZED INTEGRAL SPENCER--HELMHOLTZ EFFECTIVITY.]**  For regular
> source-minimal constrained HT germs, the refined effectivity fibration is the moduli of
> source-pure primitives `(5h)` of critically bornologically completed forms `(5g)` satisfying:
>
> 1. Helmholtz and Spencer closedness;
> 2. source-face descent and differential-birational covariance;
> 3. integral/ramified period structure;
> 4. reflected Hermitian polarization;
> 5. maximal vertical Kolchin growth and thin source-relative amplitude.
>
> The observation functor from such primitives to analytic HT germs is an equivalence on its
> essential image.  The analytic germ or its divisor is not part of `omega_F`.

This gives the obstruction report a single explicit dictionary.

| Report class | Exactness face of `(5g)`--`(5h)` |
|---|---|
| `O1` orientation | the primitive or its tangent misses the positive real polarized locus |
| `O2` critical all-scale estimate | `d_tot` fails to have closed/effective range in the critical product bornology |
| `O3` spectral realization | the realized primitive complex is nonperfect or its distinguished section is not effective |
| `O4` multiplicity/divisibility | the closed form has no lift to the integral/ramified lattice |
| `O5` non-circular comparison | `omega_F` is not constructed source-purely before the target divisor |
| `O6` typed bridge | the mixed Spencer component of `d_tot omega_F` does not vanish |
| `O7` arithmetic rigidity | the primitive lies outside the arithmetic essential image despite complex exactness |

Continuation, monodromy, and noncanonical boundary conditions are respectively failure to extend
the primitive, a closed non-exact period class, and a noncontractible primitive fibre.  They are
not declared equal scalar invariants.

The finite model also sharpens the map/correspondence boundary.  One-sided degree-expanding scalar
rational protocols force every persistent HT tail into a finite-holonomy parabolic current.
Persistent projective curvature requires two-sided correspondence topology satisfying

```text
degree * hyperbolic excess <= 2 genus + puncture budget - 2.  (5i)
```

Thus the source differential `d_src` in `(5g)` must live on a correspondence/face category, not
only on an iteration category of maps.

### Parent collision and surviving novelty residue

Variational bicomplexes, Spencer complexes, formal integrability, Helmholtz conditions, global
inverse problems, and difference variational bicomplexes are parent mathematics.  In particular:

- Giachetta--Mangiarotti--Sardanashvily compute the infinite-jet variational bicomplex and solve
  the finite-order global inverse problem, https://arxiv.org/abs/math/0006074;
- Bucataru--Constantinescu formulate global Helmholtz conditions,
  https://arxiv.org/abs/0908.1631;
- Peng--Hydon construct the difference variational bicomplex,
  https://arxiv.org/abs/2307.13935;
- differential substitutions and their Fréchet operators are established parent theory, for
  example https://arxiv.org/abs/solv-int/9509006.

Therefore `(5d)`--`(5h)` as generic jet geometry are `[BRIDGE]`, not new science.  The
novelty-unverified residue is the HT essential-image theorem with the simultaneously forced
critical bornology, source correspondence descent, integral periods, polarization, maximal
Kolchin growth, and thin nonholonomic boundary, followed by conservative comparison of genuinely
different analytic realizations.

## First natural analytic effectivity object: the irrational elliptic-gamma boundary class

The paired elliptic-gamma source makes the degree-zero effectivity mechanism literal.  Let `M` be
the field of meromorphic functions, let `B` be its differential-algebraic subfield over `C(z)`,
and work in the 1-periodic sector with translations by `tau` and `sigma`.  For

```text
F=partial_z log Gamma(z;tau,sigma)
```

the source boundary is

```text
boundary(F)=(Delta_sigma F,Delta_tau F)
           =(lambda_tau,lambda_sigma) in B x B.             (5j)
```

When `1,tau,sigma` are `Q`-independent, the actual elliptic-gamma theorem now proves:

```text
F notin B,
M^(T_tau,T_sigma)=C subset B.                               (5k)
```

Consequently `(5j)` has a primitive in `M` but no primitive in `B`.  It is a nonzero relative
effectivity class: locally finite-law, globally hypertranscendental.  Equivalently, the coset of
`F` in `M/B` is a nonzero joint-fixed class whose connecting cocycle is `(5j)`.

At the same time, the pair of boundary observations plus one scalar calibration reconstructs `F`
uniquely.  Each single boundary is nonconservative because it forgets a nonconstant elliptic
field; the pair forgets only constants; calibration kills that final fibre.  The abstract kernel,
calibration, and relative-effectivity equivalences are Lean-formalized in
`DifferenceDifferential.lean`.  The analytic theorem and exact defect matroid are proved on paper
in
`../2-fully-proven/new_scientific_knowledge/irrational-elliptic-gamma-hypertranscendence-matroid.md`.

This is the first natural analytic positive model of “different representations of one object”:
the two boundary functors are individually nonconservative but jointly conservative on the
calibrated primitive fibre.  It also corrects a false intuition: hypertranscendence does not force
infinitely many source constraints.  Finite nonlocal compatibility can determine a primitive with
maximal differential-jet freedom.

> **[CONJECTURE -- RELATIVE EFFECTIVITY CORE.]**  Every regular source-minimal HT function selected
> by finite-law nonlocal constraints determines a nonzero invariant class in a source-relative
> complexity quotient `M/B_src`, or equivalently a nonzero class in the kernel
>
> ```text
> H^1(G_src,B_src) -> H^1(G_src,M),                          (5l)
> ```
>
> and the full six-channel HT object is the minimal polarized, critically completed, integral,
> source-pure refinement of `(5l)` on which the analytic realization family is jointly
> conservative.

The plain cohomology class `(5l)` is not yet the unified field theory: it is abelian and forgets
source-labelled higher presentations, critical bornology, polarization, integral structure, and
the distinguished effective section.  The normal-crossing exterior-coherence no-go proves that
an ordinary DA quotient can erase essential higher source data.  **Positive successor:** use
`(5l)` as the unavoidable degree-zero truncation of the derived source-presentation object, not as
its replacement.

## Curvature-fiber no-go and positive refinement

Curvature does not determine a finite clock action. For a split edge with `b=1-i p`, every
perturbation `b g b` has zero curvature and preserves forward assembly. Consequently the fiber
`(8)` identifies global realizations having different boundary self-symbols. A curvature-only
integration stack is therefore too coarse to be the common object. This no-go and the following
positive finite theorem are Lean-formalized:

```text
T_1=i T_0 p+i kappa+b T_1 b.                              (5a)
```

**Positive replacement.** Replace curvature by the complete source-anomaly boundary colligation

```text
C_x=(T_N,beta_N,delta_N,alpha_N)_N,                       (5b)
```

where `delta_N=b_N T_(N+1)b_N` is the boundary self-symbol and
`alpha_N=T_N q_N-q_N S` is the source-specific descent anomaly. Equation `(5a)` gives exact finite
reconstruction and uniqueness. The refined integration object must be the homotopy fiber over
`C_x`, not over curvature alone.

The same correction gives a second positive statement: universal Taylor translation is an
integrable vacuum colligation, while the HT source is a source-specific anomalous section over
that vacuum. This separates observation kinematics from source constraint.

## The integration stack

For an admissible realization category `R`, let

```text
Global_R(x)                                                 (6)
```

be the derived groupoid of source operations on the completed source object, with its domain,
topology, affine calibration, and reflection retained. Let

```text
curv_R : Global_R(x) -> Curv_R(x)                           (7)
```

send a global operation to its finite-clock curvature field.

Define the **constraint-curvature integration stack**

```text
I_x(R)=hofib_(bold_kappa_x)(curv_R).                        (8)
```

It is the moduli object of global source realizations integrating the prescribed finite-clock
field. This is the proposed precise meaning of the "same interval" seen by different obstruction
chains.

At the linear level, if `curv_R` is a linear map `P -> C`, the fiber over `kappa` is empty exactly
when `kappa` is outside its range. Once a primitive exists, the fiber is canonically an affine
torsor under `ker(curv_R)`. These two facts are Lean-formalized.

The notation `(8)` is now only a curvature truncation. The complete object replaces `curv_R` by
the colligation realization

```text
coll_R : Global_R(x) -> Coll_R(x),
I_x^full(R)=hofib_(C_x)(coll_R),                            (8a)
```

because the curvature-only fibre has already been proved nonconservative.

## Residual-gauge observability spectrum `[PROVED LINEAR LAW; HT ASSIGNMENT CONJECTURAL]`

The Gamma periodic-gauge collision shows that a nonempty integration fibre still does not select a
canonical primitive. The exact common-kernel theorem identifies algebraic conservativity but not
its stability. Let `G_x` be the completed normalized automorphism space of one fibre of `(8a)`, and
let

```text
A_x(R):G_x -> H_R,
Delta_x(R)=A_x(R)^* A_x(R).                                (8b)
```

Lean proves the exact abstract trichotomy for `(8b)`:

```text
ker A_x(R) != 0;                                           exact gauge ambiguity
ker A_x(R) = 0 but unit g_n satisfy A_x(R)g_n -> 0;        nonclosed-range instability
A_x(R) anti-Lipschitz.                                     stable conservativity       (8c)
```

For an injective reporter, the middle condition is equivalent to nonclosed range. If `G_x` is
infinite-dimensional and the reporter is compact, the stable phase is impossible: even an
algebraically injective compact reporter has normalized approximate-null gauges. Therefore the
positive successor to the bare-source no-go is a **noncompact transverse realization theorem**, not
another completion or topology functorially derived from the forgotten source.

This refines the five-face dictionary. Exact automorphisms and spectral incompleteness are the
point-zero and approximate-zero phases of the same Gram field. Positivity is its reflected/Krein
orientation; monodromy is holonomy of the zero-mode family; continuation is graph-domain descent.
The full colligation is still needed because a Gram operator alone forgets descent anomaly,
integral structure, and boundary self-symbol.

The source-normalized Gamma factorial conormal now realizes the middle phase exactly. On the
square-summable clock completion it is an injective Hilbert--Schmidt diagonal reporter with unit
mode scales `1/(n+1)!`, hence compact with nonclosed range. This proves that the natural HT target
need not be stable observability: a nonlinear all-scale positivity/incidence condition can select a
unique section on a critical `P1` boundary while every finite clock remains well conditioned only
at its own fixed depth. The new invariant to transport is the decay law of the approximate-zero
field, not merely whether its kernel vanishes.

See `hypertranscendental-conservativity-spectrum.md` and
`../../../3-formalized/not_new_scientific_knowledge/source-gauge-observability-trichotomy.md`.

## Conjecture I: the five-face theorem

**[CONJECTURE — FIVE FACES OF ONE FIBER]** Whenever `(8)` is a perfect derived analytic stack with
reflection, the five obstruction languages are the following literal invariants:

1. **continuation failure:** `I_x(R)` is empty after extension to the requested domain;
2. **boundary-condition ambiguity:** `pi_0 I_x(R)` has more than one point;
3. **monodromy:** `pi_1 I_x(R)` or the holonomy of its integration torsor is nontrivial;
4. **spectral incompleteness:** the tangent complex of `I_x(R)` has nonzero homology;
5. **positivity failure:** the reflected Hermitian orientation on that tangent homology is not
   positive.

This is stronger than matching five scalar spectra. A valid comparison must be an equivalence of
integration fibers carrying source curvature, affine origin, algebra action, and reflection.

**Falsifier.** One claimed realization has the correct degeneracy set but no functor from `(8)`, or
two realizations carry inequivalent curvature derivations despite having the same determinant.

## Conjecture II: thin boundary, infinite capacity

Let

```text
c_x(N)=trdeg_F F(x,delta x,...,delta^N x).                 (9)
```

**[CONJECTURE — THIN INTEGRATION FIELD]** A regular source-minimal constrained HT point satisfies

```text
c_x(N)=N+1 for all N,                                     (10)
```

while the cotangent complex of `(8)` is perfect of finite source-constraint rank and bounded
amplitude. Infinite algebraic clock capacity and thin boundary are therefore independent but
simultaneous properties.

The whole analytic/formal completion cokernel may be enormous; thinness applies only to the
source-generated integration stack.

## Conjecture III: nonlinear clock-corona correspondence

The unary curvature field cannot reconstruct a nonlinear constraint. Let

```text
bold_kappa_x=kappa_x^(1)+kappa_x^(2)+kappa_x^(3)+...       (11)
```

be the complete hierarchy obtained from the Taylor layers and syzygies of the analytic source
constraint.

**[CONJECTURE — CLOCK-CORONA CORRESPONDENCE]** The formal deformation category of regular
source-minimal constrained HT germs is equivalent to the category of integrable, affine-calibrated,
maximal-capacity thin curvature fields satisfying:

1. the higher Bianchi identities;
2. the constraint-algebra Leibniz identities;
3. analytic source-growth conditions;
4. presentation descent;
5. reflection coherence when present.

Full faithfulness is nonlinear source reconstruction. Essential surjectivity is the inverse
problem: every abstract field satisfying these integrability conditions comes from a nonlocal HT
source constraint.

Formal moduli, curved `L_infinity` structures, and derived integration stacks are parent languages.
The candidate-new assertion is this source-forced correspondence and the maximal-capacity/thin-
boundary essential image.

**Falsifiers.** Two inequivalent analytic source germs yield equivalent complete fields and
integration stacks; or an integrable field satisfying all five conditions has no source
realization.

## Gamma point-normalization no-go and calibrated positive vacuum

Gamma's unit translation has nonzero rank-one finite-clock curvature, but the factorial tail sums
to the actual analytic translation operator in its source topology.

Point normalization does not make the Gamma integration object contractible. Two nonzero solutions
of one multiplicative shift constraint differ by a nonzero period-one multiplier, and the
multiplier may equal one at the normalization point. The solution-torsor statement is already
Lean-formalized generically in `CarrierDichotomy.lean`.

**Positive exact replacement.** Before analytic calibration, the Gamma solution space is a torsor
under the nonzero period-one gauge group. A source asymptotic or positivity condition is a reduction
of that torsor. For the additive digamma cocycle, the project already Lean-formalizes the complete
model:

```text
same unit-shift cocycle + same logarithmic asymptotic
  => identical source on the right half-plane.             (11a)
```

The explicit digamma source supplies existence, so the asymptotically calibrated integration fiber
is a singleton even though the uncalibrated fiber has the full periodic ambiguity.

**[CONJECTURE — GAMMA COLLIGATION INTEGRABILITY]** The opposite-variance Gamma Weyl seam identifies
the parameterized-Galois periodic torsor with this analytic integration torsor, and asymptotic
source selection defines a single comparison point. Its outgoing factorial channel, incoming
Leibniz channel, and periodic gauge are respectively the finite field, algebraic prolongation, and
automorphism group of that comparison object.

This corrects the earlier guess that Gamma should carry a nonzero ordinary `lim^1` obstruction.
Gamma is the solvable vacuum model showing that a thin nonzero field need not obstruct global
integration.

**Falsifier.** Two asymptotically calibrated digamma/Gamma realizations survive as distinct points,
or the algebraic periodic automorphism torsor cannot map to the analytic periodic gauge torsor.

## Conjecture V: nonlinear and singular phases

Gamma cannot test higher curvature because its tangent shift constraint is linear. A raw Böttcher
power constraint has higher Taylor layers, but local logarithmic linearization transfers them to a
period-lattice cocycle. Böttcher is therefore the first curvature--holonomy transfer test, not yet
a genuinely higher minimal-curvature example.

**[CONJECTURE — PHASE STRUCTURE]** The general constrained HT theory contains at least four phases:

1. **integrable:** `(8)` is contractible after calibration;
2. **multiboundary:** `(8)` is nonempty with nontrivial `pi_0`;
3. **holonomic:** `(8)` is connected with nontrivial `pi_1`;
4. **singular:** `(8)` is empty or has nonperfect tangent because integration is nonclosable,
   noncompact, or obstructed by a quotient ideal.

These phases can share the same finite algebraic capacity. Hypertranscendence does not choose the
phase; the source constraint does.

**Positive no-go.** A route that lands in the integrable phase has discovered a global source
operation, not failed to discover an obstruction. Its positive statement should be an integration
or uniqueness theorem.

## Conjecture VI: self-dual degeneracy spectrum

For a reflected parameter family `x_s`, suppose

```text
I_(s^vee)(R) ~= dual(I_s(R))                               (12)
```

coherently, with a source-defined orientation line.

**[CONJECTURE — COMMON SELF-DUAL DEGENERACY]** The common degeneracy spectrum is the support where
the self-dual integration stack ceases to be transversely a single oriented point. Fixed
parameters are self-dual degeneracies; nonfixed degeneracies occur in reflected pairs.

Reflection alone does not exclude the paired off-fixed case. Fixed-locus confinement requires a
new positive-orientation theorem on the actual tangent complex of `(8)`.

## RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A completed-zeta source may determine `bold_kappa_zeta` from its
prime and archimedean constraint algebra before any divisor is examined. The Sonin/Calkin,
Hedenmalm/nonclosability, continuation, positivity, boundary-extension, and Böttcher/monodromy
chains represent the same object only if they are functorial realizations of one integration stack
`I_zeta` preserving `(3)`--`(5)` and `(12)`.

The critical zeros would then be fixed-locus degeneracies of that stack. No zeta function,
completed xi function, zeros, or zero-indexed operator may be used to define the curvature field.
No such common realization has yet been constructed.

## Parent-theory and manufacture attacks

- Homotopy fibers, derived moduli, deformation complexes, boundary triples, and integration
  groupoids are established parent structures.
- Choosing `Curv_R` after seeing the desired global object makes `(8)` tautological. The finite
  curvature must be source-derived first.
- Taking the full completion defect loses HT specificity.
- Allowing arbitrary topological completions manufactures empty or nonempty fibers at will.
- Low displacement rank is classical structured-operator theory.
- A self-dual stack may have off-fixed degeneracies.
- Gamma can validate integrability and calibration, but not nonintegrability, nonlinear coherence,
  or spectral realization.

The candidate-new residue is the canonical source construction of `bold_kappa_x`, the
clock-corona correspondence, and a theorem identifying genuinely different analytic obstruction
chains as invariants of the same source integration stack.

## Gates

- [x] ordinary finite-dimensional algebraic `lim^1` carrier killed
- [x] nonzero curvature separated from nonintegrability
- [x] Bianchi, gauge-additivity, and constraint-algebra Leibniz laws Lean-formalized
- [x] linear fiber nonemptiness/range criterion Lean-formalized
- [x] nonempty linear fiber identified with the kernel torsor in Lean
- [x] canonical finite Taylor shadows and rank-one Gamma curvature constructed
- [ ] source-presentation invariance of the Gamma calibration proved
- [ ] Gamma rank-one field proved to integrate uniquely
- [x] raw Böttcher higher curvature rejected as coordinate-invariant data
- [ ] Böttcher curvature--holonomy transfer class constructed
- [ ] higher minimal curvature constructed for a genuinely non-linearizable source
- [ ] one noncontractible source integration stack constructed
- [ ] presentation invariance proved for two source descriptions
- [ ] nonlinear clock-corona full faithfulness proved in one class
- [ ] essential-image integrability criterion proved
- [ ] self-dual tangent pairing constructed in one parameterized non-RH family
- [ ] two distinct obstruction realizations proved equivalent as integration fibers
- [ ] independent novelty and significance audit

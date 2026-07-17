# The normal-crossing critical ideal is the squarefree coface boundary

- **ID:** `hypertranscendental-critical-locus-universality`
- **Stage:** 3-formalized algebraic core / cross-family application open
- **Type:** ALGEBRAIC THEOREM / CONDITIONAL CROSS-FAMILY HT ARCHITECTURE TEST
- **Scientific status:** `[PROVED HERE] [ALGEBRAIC CORE LEAN-FORMALIZED] [MEG PARENT OPEN]`
- **Parents:**
  - `../new_scientific_knowledge/barnes-multiple-gamma-translation-annihilator.md`
  - `../new_scientific_knowledge/all-order-multiple-sine-stanley-reisner-differential-matroid.md`
  - `../new_scientific_knowledge/all-order-multiple-elliptic-gamma-structural-differential-matroid.md`
  - `multiple-elliptic-gamma-codimension-two-boundary-reconstruction.md`
- **Exact threshold child:** `barnes-reflection-cotangent-singularity-threshold.md`
- **Statement:** The derivational critical ideal of the normal-crossing polynomial
  `f_N=product_i x_i` is the squarefree coface ideal `I_crit=(product_(j != i)x_j)_i`, which is also
  the cotangent degeneracy ideal and has a length-two boundary resolution. Identifying this
  algebraic object with the complete structural differential matroids of multiple-sine and
  multiple-elliptic-gamma families is a separate analytic theorem; the elliptic-gamma input is not
  yet proved.

## 1. Constraint coordinates

Fix `N>=2`, a characteristic-zero coefficient field `F`, and the localized structural translation
ring

```text
A=F[t_1^(+-1),...,t_N^(+-1)],
x_i=t_i-1.
```

Put

```text
f_N=product_(i=1)^N x_i,
m_i=product_(j != i)x_j,
I_crit=(m_1,...,m_N).
```

Localization at the `t_i=1+x_i` does not change any calculation below. The point `x=0` is the
augmentation point of the structural translation torus.

The proposed parent exact-annihilator identifications are

```text
Ann_DA(Psi_Barnes,N)=(f_N),                              (1)
Ann_DA(L_sine,N)=I_crit,                                 (2)
Ann_DA(Psi_ell,N-1)=I_crit.                             (3) [OPEN]
```

Here `(1)` is asserted for rationally independent Barnes periods and `(2)` for the generic
positive-real multiple-sine regime. Equation `(3)` for generic multiple elliptic-gamma parameters
is not proved by the current Lean corpus or by the current all-order paper proof: the available
elliptic-gamma theorem gives `C[delta]`-linear freeness of bottom defects, which does not imply
nonlinear differential independence. Consequently the claimed complete nonlinear
`A/I_crit`-matroid identification for the elliptic family remains open.

## 2. Critical-locus theorem `[PROVED]`

For every `i`, direct differentiation gives

```text
partial_i f_N=m_i.                                      (4)
```

Therefore

```text
Jac(f_N)=(partial_1 f_N,...,partial_N f_N)=I_crit.       (5)
```

Moreover `f_N=x_i m_i` for every `i`, hence `f_N` already belongs to `Jac(f_N)`. The
scheme-theoretic critical locus of the Barnes hypersurface `f_N=0` is consequently

```text
Crit(V(f_N))=V(f_N,Jac(f_N))=V(I_crit).                  (6)
```

Combining a proved parent identification with `(4)`--`(6)` yields the corresponding
criticalization identity. In particular, the proposed cross-family identities are

```text
Ann_DA(L_sine,N)=Jac(generator(Ann_DA(Psi_Barnes,N))),  (7)
Ann_DA(Psi_ell,N-1)=Jac(generator(Ann_DA(Psi_Barnes,N))). (8)
```

Equation `(7)` is the exact sense in which Barnes reflection **criticalizes** the source
constraint, conditional on its stated parent annihilator theorems. Equation `(8)` would show that
multiple elliptic completion reaches the same critical boundary through a different analytic
construction, but `(8)` remains conditional on the open elliptic-gamma exact-matroid input.

### 2.1 Presentation no-go and intrinsic positive replacement `[PROVED]`

The bare Jacobian ideal is not the correct invariant for a general principal source law. Let

```text
B=k[x,(1+x)^(-1)],      f=x^2,      g=(1+x)f,
```

over a characteristic-zero field. The two equations define the same hypersurface because
`1+x` is a unit, but

```text
Jac(f)=(x),
Jac(g)=(x(2+3x)).                                      (8a)
```

The ideals in `(8a)` are unequal: `2+3x` is not a unit of `B`. Thus

```text
[NO-GO] the bare coordinate Jacobian is invariant under source presentation.
```

For an `R`-algebra `A`, define instead the derivational critical ideal

```text
Crit_R(f)=(f, Df : D in Der_R(A,A)).                    (8b)
```

Leibniz gives `D(uf)=uDf+fDu`; if `u` is a unit, applying the same identity to
`u^(-1)(uf)` proves

```text
Crit_R(uf)=Crit_R(f).                                   (8c)
```

Every `R`-algebra isomorphism transports derivations by conjugation, so it transports `(8b)`.
Consequently `Crit_R(f)` is invariant under both coordinate isomorphism and unit change of the
principal generator. In a finite polynomial algebra, every derivation is the unique linear
combination of the coordinate partial derivatives with coefficients `D(x_i)`, hence

```text
Crit_R(f)=(f,partial_1 f,...,partial_N f).               (8d)
```

For the normal-crossing source `f_N`, one has `f_N=x_i partial_i f_N` for every `i`. Therefore

```text
Crit_F(f_N)=Jac(f_N)=I_crit.                             (8e)
```

The positive theorem is stronger than coordinate invariance: Barnes criticalization is an
intrinsic operation on the principal source scheme.

### 2.2 Cotangent-degeneracy theorem `[PROVED]`

Put `B_N=A/(f_N)`. The conormal presentation of the relative cotangent module is

```text
B_N --df_N--> B_N^N --> Omega_(B_N/F) --> 0,
1 |--> (m_1,...,m_N).                                   (8f)
```

Since `B_N` is an equidimensional hypersurface of relative dimension `N-1`, its nonsmooth
scheme is cut out by the `(N-1)`st Fitting ideal of `Omega_(B_N/F)`. From `(8f)`, this is the
ideal of the one-by-one minors, namely `(m_1,...,m_N)B_N`. Pulling it back to `A` gives

```text
pi^(-1) Fitt_(N-1)(Omega_(B_N/F))
  =(f_N,m_1,...,m_N)=I_crit.                             (8g)
```

Combining `(8g)` with any separately proved exact-annihilator identification gives an intrinsic
criticalization theorem. The desired pair of identities is

```text
Ann_DA(L_sine,N)
  =pi^(-1) Fitt_(N-1)(Omega_(A/Ann_DA(Psi_Barnes,N)/F)),

Ann_DA(Psi_ell,N-1)
  =pi^(-1) Fitt_(N-1)(Omega_(A/Ann_DA(Psi_Barnes,N)/F)). (8h)
```

The algebraic equality `(8g)` is proved. The multiple-sine instance depends on its parent theorem;
the multiple-elliptic-gamma instance is open because `(3)` is open. Thus the current certificate
does not yet prove that elliptic completion realizes the cotangent singular support of the Barnes
dependence scheme.

There is also a canonical exact restriction sequence.  With `B_N=A/(f_N)` and
`J_N=Fitt_(N-1)(Omega_(B_N/F))=I_crit/(f_N)`,

```text
0 -> J_N -> B_N -> A/I_crit -> 0.                         (8i)
```

The final algebra computes the quotient geometry of the abstract critical ideal. Once a reflected
family is independently shown to have that exact complete structural matroid, reflection acts on
its dependence geometry by restriction from the Barnes hypersurface to the intrinsic singular
scheme, with loss module the cotangent Fitting ideal. The order-one smooth algebraic model has
empty target, while every higher normal-crossing order has nonzero singular support. The exact
threshold is recorded in `barnes-reflection-cotangent-singularity-threshold.md`.

## 3. Geometry and resolution `[PROVED]`

The Jacobian ideal is radical and has the prime decomposition

```text
I_crit=intersection_(1<=i<j<=N)(x_i,x_j).                (9)
```

Thus its support is the union of pairwise intersections of the coordinate hypersurfaces: exactly
the singular locus of the normal-crossing divisor `V(f_N)`. It has pure codimension two.

The boundary matrix

```text
H(b_2,...,b_N)
  =(-x_1 sum_(i=2)^N b_i, x_2b_2,...,x_Nb_N)            (10)
```

gives the exact minimal complex

```text
0 -> A^(N-1) --H--> A^N --(m_1,...,m_N)--> A
  -> A/I_crit -> 0.                                    (11)
```

Its maximal minors recover all partial derivatives of `f_N`; its Betti ranks are
`(1,N,N-1)`; and it has no higher syzygies. Hence criticalization raises the minimal boundary
amplitude from one for the Barnes hypersurface `(f_N)` to two for its critical scheme, even though
it adds DA relations and shrinks the constraint support.

This gives a sharp no-go and positive replacement:

```text
[NO-GO] more finite constraints => lower homological complexity.
[THEOREM] finite constraint compression can expose intersections and raise boundary amplitude;
          amplitude is controlled by the singularity type of the source law.
```

## 4. Complete cross-family differential-matroid universality `[CONDITIONAL]`

If their exact-matroid parents are proved, the generic multiple-sine order-`N` and generic multiple
elliptic-gamma order-`N-1` structural differential matroids are both the linear matroid of

```text
F(delta) tensor A/I_crit.                                (12)
```

The current algebra proves the consequence from those inputs, but it does not prove the inputs.
In particular, equality of every finite-packet differential transcendence rank across the two
analytic theories is not yet established.

**[CONJECTURE]** Once the analytic exact-matroid identifications are supplied, the Fitting
degeneracy type of the source cotangent module will be a presentation-independent coarse invariant
shared by the two constrained hypertranscendental realizations.

## 5. Exact form of thin infinite capacity

The monomial basis of `A/I_crit` consists of the structural monomials using at most `N-2` distinct
constraint directions. For `N>=3`, every surviving coordinate face carries arbitrarily high
powers, so the structural observable space is infinite-dimensional while its support is confined
to the codimension-two critical boundary. At `N=2`, the structural quotient collapses to one
common hypertranscendental coordinate, whose derivative tower remains algebraically unbounded.

Thus the original heuristic has a precise non-temporal form:

```text
hypertranscendental capacity = unbounded observables in A/I,
thin constraint boundary     = support and amplitude of the source-critical complex.
```

The capacity and the boundary are independent axes. Visible hierarchy order does not determine
either one.

## 6. Derived criticalization tower

Let `X_k` be the reduced union of coordinate subspaces on which at least `k+1` of the `x_i`
vanish. Its radical ideal is

```text
I(X_k)=(squarefree monomials of degree N-k).             (13)
```

At a point with exactly `k+1` vanishing coordinates, precisely one component of `X_k` passes
through the point, so `X_k` is smooth there. At a point with at least `k+2` vanishing coordinates,
multiple distinct components meet and the reduced local ring has multiple minimal primes, hence
is not regular. Therefore

```text
Sing(X_k)_red=X_(k+1),       0<=k<=N-2.                 (14)
```

The first step `X_0 -> X_1` is exactly the proved Barnes-to-multiple-sine criticalization.

### Objectwise realization of the whole tower `[PROVED BY FORMALIZED PARENT]`

For every `k`, the ideal in `(13)` is the Stanley--Reisner ideal of a finite simplex skeleton.
The formal universal facet-palette theorem therefore supplies, inside one fixed meromorphic
differential field, a non-Gamma Herglotz structural system whose complete nonlinear differential
matroid is exactly

```text
A/I(X_k).                                                  (15)
```

This holds simultaneously for every finite `N`, every stage `k`, and every finite residue-sign
orientation. Hence every object in the normal-crossing singularity tower is already analytically
realizable by a genuine HT system. More strongly, every finite simplicial constraint scheme is
objectwise realizable.

The missing theorem is not existence of deeper constraint topologies. It is a source-canonical
morphism realizing

```text
X_k -> Sing(X_k)_red=X_(k+1)                              (16)
```

as a natural operation on analytic HT sources. Barnes reflection proves `(16)` only for
`k=0` in the special-function class.

This gives a second sharp no-go and positive replacement:

```text
[NO-GO] A unified HT theory should classify which finite constraint topologies are allowed.
[THEOREM] All finite simplicial constraint topologies are allowed, even in one universal field.
[POSITIVE TARGET] Classify source-canonical criticalization morphisms and calibrated couplings.
```

**[CONJECTURE — DERIVED CRITICALIZATION PRINCIPLE]** Every regular finitely sourced constrained
hypertranscendental class admits a minimal source scheme `X_0` whose derived singularity tower
controls all finite-observable dependence strata. Source symmetries such as reflection,
completion, or boundary pairing act by functorial criticalization on a calibrated perfect complex,
not by propagation of the function. Two analytic realizations have the same complete structural
differential matroid exactly when their calibrated critical complexes are quasi-isomorphic.

For the normal-crossing class this predicts analytic HT realizations of every deeper `X_k`, not
only the known `X_0` and `X_1`. Producing `X_2` from a natural special-function operation is the
first falsifiable test.

## 7. Unified-obstruction hypothesis

**[CONJECTURE]** Continuation failure, monodromy, noncanonical boundary conditions, spectral
incompleteness, and positivity failure are not five properties of a function. They are five
realization failures of one calibrated critical complex:

1. continuation is extension of an analytic realization across its critical strata;
2. monodromy is the holonomy of the realization torsor;
3. boundary ambiguity is nonuniqueness of derived extension data;
4. spectral incompleteness is surviving realized homology;
5. positivity failure is failure of a self-dual polarization on that homology.

The proved theorem supplies an actual common object for two nonidentical HT hierarchies. It does
not yet prove that all five failures are equivalent.

## 8. RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A zeta-side application would require a prime--archimedean
source scheme and calibrated perfect complex constructed without using the Xi zeros. Different RH
proof chains could be representations of one obstruction only if their continuation, monodromy,
boundary, spectral, and positivity defects are realization invariants of that source complex. The
critical zeros would then be the self-dual degeneracy support of the realized complex.

No zeta source complex, cross-chain equivalence, or RH implication is proved here.

## 9. Lean formalization

`formal/GaloisForLFunctions/HTGeometry/SquarefreeVeroneseIdeal.lean` now proves:

- `derivationalCriticalIdeal_unit_mul`: the intrinsic critical ideal is unchanged by unit
  replacement of a principal source equation;
- `derivationalCriticalIdeal_eq_coordinateCriticalIdeal`: all derivational derivatives in a
  finite polynomial algebra are generated by the coordinate gradient together with the source
  equation;
- `normalCrossingDerivationalCriticalIdeal_eq_veroneseIdeal`: the intrinsic normal-crossing
  critical scheme is exactly the squarefree Veronese boundary;
- `veroneseIdeal_eq_top_iff`: the squarefree boundary is empty exactly in degree zero;
- `normalCrossingDerivationalCriticalIdeal_eq_top_iff`: the intrinsic normal-crossing critical
  scheme is empty exactly in the one-coordinate case;
- `pderiv_normalCrossingPolynomial`: every partial derivative of `product_i X_i` is its
  complementary face monomial;
- `normalCrossingJacobianIdeal_eq_veroneseIdeal`: the Jacobian ideal is exactly the squarefree
  degree-`N-1` constraint ideal;
- `cofaceRelation_eq_zero_iff`: all first syzygies are generated by the star boundary;
- `cofaceBoundary_injective`: there are no higher syzygies of the boundary presentation.

The touched file passes direct Lean verification against cached dependencies. No Lake build was
run.

`formal/GaloisForLFunctions/HTGeometry/NormalCrossingCriticalDerivedPhase.lean` contains a
conditional assembly theorem. `NormalCrossingFamilyCriticalizationInput` has fields
`sine_exact`, `ellipticGamma_exact`, `sine_rank_exact`, and `ellipticGamma_rank_exact`; these are
hypotheses, not proved special-function calculations. The theorem
`normalCrossing_crossFamily_criticalization` derives the cross-family conclusion from those exact
inputs. It must not be cited as evidence for them. The unconditional Lean content is the intrinsic
critical-ideal algebra, its resolution, and unit-presentation invariance derived from
`derivationalCriticalIdeal_unit_mul`.

## 10. Novelty and anti-theatre gate

### Established parents `[SEARCH]`

- Barnes multiple-gamma and multiple-sine functional equations and reflection formulas are
  classical.
- Narukawa establishes analytic correspondences between multiple sine and multiple elliptic gamma
  functions.
- Parametrized difference Galois theory supplies established mechanisms for detecting differential
  dependence of difference-equation solutions.
- Normal-crossing singular loci, Jacobian ideals, squarefree Veronese ideals, Hilbert--Burch
  resolutions, conormal sequences, cotangent modules, and Fitting supports are classical
  commutative algebra.

### Exact combination not located `[NOVELTY UNVERIFIED]`

Exact-phrase and mechanism searches have not located a theorem that computes the complete
structural differential matroids of these families and identifies Barnes reflection with passage
from a normal-crossing annihilator hypersurface to the Fitting degeneracy scheme of its cotangent
module. No located source identifies multiple sine and multiple elliptic gamma as two analytic
realizations of the same complete cotangent-degeneracy differential matroid.

The algebraic identities behind `(8b)`--`(8g)` are standard singularity theory and are not new.
The candidate new knowledge is the cross-family special-function statement `(7)`, `(8)`, `(8h)`,
and `(12)`, which depends on the parent exact-matroid theorems surviving their independent
analytic and literature audits.

### Significance verdict

This identity alone does not warrant an independent paper. Combined with complete proofs of the
three parent annihilator/matroid theorems, it can be the organizing theorem of a substantial paper:
it replaces formula-based classification by a representation-independent critical-complex
invariant and makes the deeper criticalization tower a concrete research program.

The Fields-scale claim is the derived criticalization principle plus reconstruction and
cross-realization equivalence, not the first normal-crossing example.

## Gates

- [x] remove the time/clock motif from the architecture
- [x] identify the Barnes constraint as a normal-crossing hypersurface
- [ ] prove the analytic Barnes/reflection exact-annihilator input and instantiate the algebraic
      criticalization theorem
- [x] replace the presentation-dependent bare Jacobian by the intrinsic derivational critical
      ideal
- [x] prove unit-presentation and polynomial-coordinate invariance
- [x] identify the abstract normal-crossing critical ideal with the cotangent Fitting degeneracy
      scheme
- [ ] prove the actual multiple-sine exact structural matroid input
- [ ] prove the actual multiple-elliptic-gamma nonlinear order-one atomicity and all-order exact
      structural matroid input
- [x] prove the codimension-two critical boundary complex
- [x] formalize the Jacobian/Veronese identity and its exact syzygy complex in Lean
- [x] realize every deeper normal-crossing stratum objectwise by the formal universal HT palette
- [x] state no-go and nontrivial positive successor
- [x] run exact-phrase and mechanism literature searches
- [ ] independently verify the Barnes exact-annihilator parent against full Nishizawa literature
- [ ] independently verify the multiple-sine and multiple-elliptic-gamma complete matroid parents
- [ ] construct a natural source operation realizing the criticalization morphism `X_1 -> X_2`
- [ ] extend source-presentation invariance from principal hypersurfaces to nonprincipal perfect
      source complexes
- [ ] prove analytic reconstruction from a calibrated critical complex in one nontrivial class

## Primary literature checked

- C. Hardouin and M. F. Singer, *Differential Galois Theory of Linear Difference Equations*,
  Mathematische Annalen 342 (2008), 333--377, `arXiv:0801.1493`.
- A. Narukawa, *The modular properties and the integral representations of the multiple elliptic
  gamma functions*, `arXiv:math/0306164`.
- N. Kurokawa and M. Wakayama, *Period deformations and Raabe's formulas for generalized gamma and
  sine functions*, Kyushu Journal of Mathematics 62 (2008), 171--187.
- R. Perez-Marco, *On the definition of higher Gamma functions*, `arXiv:2101.01291`.
- F. Galetto, *On the ideal generated by all squarefree monomials of a given degree*,
  `arXiv:1609.06396`.

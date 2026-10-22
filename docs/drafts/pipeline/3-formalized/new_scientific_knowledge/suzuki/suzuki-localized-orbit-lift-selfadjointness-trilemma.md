# Localized Suzuki orbit lifts cannot be bounded, covariant, and self-adjoint

- **ID:** `suzuki-localized-orbit-lift-selfadjointness-trilemma`
- **Stage:** 3 — formalized in Lean 4
- **Type:** SOURCE-CARRIER NO-GO / POSITIVE SINGULAR-SURVIVOR CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [LEAN CORE PROVED] [UNCONDITIONAL]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-support-pruned-evaluation-rigging-fracture.md`,
  `suzuki-exterior-residual-rigged-wiener-realization.md`,
  `suzuki-root-retained-exterior-dilation.md`

## 1. Result

The missing completed-mode-to-seam connector cannot be a bounded Hilbert-space lift obtained by
placing the physical profile at every translated valuation coordinate.

Let \(G\) be an infinite discrete group, let \(H\ne0\) be a Hilbert space, and let
\((U_g)_{g\in G}\) be a unitary representation.  For a scalar weight \(w:G\to\mathbb C\), the
localized orbit lift is

```text
(J_w x)_g=w_g U_g x.                                      (1)
```

Then:

1. \(J_wx\in\ell^2(G;H)\) for one, equivalently every, nonzero \(x\) exactly when
   \(w\in\ell^2(G)\);
2. projective covariance with the coordinate translations forces \(|w|\) to be
   translation-invariant;
3. a nonunitary diagonal weighting of a connected constant-coefficient self-adjoint adjacency
   remains self-adjoint only when \(|w|\) is constant along every active edge.

An \(\ell^2\) weight of constant nonzero modulus cannot exist on an infinite connected component.
Consequently a nonzero localized orbit lift cannot simultaneously be

```text
bounded into ell2
+ translation/projective covariant
+ compatible with a self-adjoint constant-coefficient seam adjacency.        (2)
```

For Suzuki, \(G\) is the prime-valuation lattice and \(U_\nu\) is translation by
\(\sum_p\nu_p\log p\).  Hence the proposed exact connector

```text
physical completed mode
 -> all support-localized translated seam profiles in ell2
 -> self-adjoint Gamma--prime adjacency                              (3)
```

does not exist as a bounded operator on any infinite valuation component.  Decaying coordinate
weights repair square summability but necessarily break exact translation covariance or
self-adjointness in the unweighted middle Hilbert metric.

The first positive survivor is strict:

```text
source-dependent coefficient relation in ell1
    subset ell2
    subset ellInfinity,
with physical reconstruction only on its graph domain.                 (4)
```

It must be built from resolvent/parametrix coefficients, not by duplicating physical translates.
Thus the remaining E1 object is a singular closed relation or a source-dependent graph-space
correspondence.  A bounded localized Hilbert intertwiner is now ruled out.

**Subsequent correction.**  The last sentence is true only with ordinary self-adjoint adjacency
retained.  `suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy.md` constructs a second
positive survivor: exponential orbit weights give a bounded localized Hilbert lift, exact prime
intertwining with a bounded **nonnormal** conjugated adjacency, and norm-one reconstruction by the
root coordinate.  Terminal Gamma coercivity uses only the coupling norm, so self-adjointness is
dispensable there.  This does not contradict `(2)`; it selects the nonselfadjoint corner of the
trilemma.  Its sharp remaining obstruction is prime-log recurrence of the aperture.

## 2. Square-summability law

For \(x\in H\), unitarity gives

```text
sum_(g in G) ||(J_w x)_g||^2
 =sum_g |w_g|^2 ||U_gx||^2
 =||x||^2 sum_g |w_g|^2.                                (5)
```

If \(x\ne0\), equation `(5)` is finite exactly when \(w\in\ell^2(G)\).  When this holds,

```text
||J_w||=||w||_(ell2).                                    (6)
```

This is not the previously proved synthesis obstruction.  That theorem says unit-phase physical
evaluation is not bounded from the infinite seam \(\ell^2\) carrier to a scalar profile.  Equations
`(5)`--`(6)` concern the opposite arrow: bounded analysis of one physical profile into all its
localized orbit copies.

## 3. Covariance forces constant modulus

Let the coordinate reindexing be

```text
(S_s F)_g=F_(g+s).                                       (7)
```

Suppose the lift is projectively covariant:

```text
J_w U_s=zeta_s S_s J_w,       |zeta_s|=1.                (8)
```

At coordinate \(g\), equations `(1)`, `(7)`, and `(8)` give, for every \(x\),

```text
w_g U_(g+s)x=zeta_s w_(g+s)U_(g+s)x.                    (9)
```

Since \(U_{g+s}\) is injective and \(H\ne0\),

```text
w_g=zeta_s w_(g+s),
|w_g|=|w_(g+s)|.                                         (10)
```

If the active shifts generate a connected component \(G_0\), \(|w|\) is constant on \(G_0\).
If \(G_0\) is infinite and \(w\) is nonzero there, `(5)` diverges.  Thus every projectively
covariant square-summable orbit weight vanishes on every infinite active component.

The same conclusion holds if covariance is imposed only for a symmetric generating alphabet:
iterate `(10)` along a word joining two vertices.

## 4. Self-adjointness forces the same obstruction

Let \(A=A^*\) be a bounded constant-coefficient adjacency on \(\ell^2(G)\), with a nonzero matrix
entry on every edge of one connected Cayley component.  Let

```text
(D F)_g=d_g F_g,       d_g=|w_g|>0.                     (11)
```

The adjacency seen after the weighted orbit identification is

```text
A_w=D A D^(-1).                                          (12)
```

Because \(D=D^*\) is positive,

```text
A_w^*=D^(-1) A D.                                        (13)
```

Therefore \(A_w=A_w^*\) is equivalent to

```text
D^2 A=A D^2.                                             (14)
```

Take the matrix coefficient of `(14)` across an active edge \(g\leftrightarrow h\).  Its adjacency
coefficient is nonzero, so

```text
d_g^2=d_h^2.                                             (15)
```

Connectivity makes \(d\) constant.  On an infinite component, nonzero constancy contradicts
\(w\in\ell^2\).  Hence diagonal decay cannot be hidden by changing coordinates while retaining
the literal self-adjoint prime adjacency in the ordinary Hilbert metric.

Zeros do not produce an escape.  If covariance is retained, `(10)` makes the zero set a union of
whole active components.  On a component reached from a nonzero endpoint port, no weight can
vanish.

## 5. Suzuki specialization

At aperture \(a\), put

```text
G_a=Z^((P_a)),
ell(nu)=sum_(p in P_a) nu_p log p,                       (16)
U_nu u(x)=u(x-ell(nu)).                                  (17)
```

Suzuki's prime term is a finite real symmetric Laurent adjacency generated by
\(\pm j e_p\), with nonzero weight \((\log p)/p^{j/2}\).  Its unpruned component is infinite as
soon as one prime is visible.  Once the \(2\)- and \(3\)-directions are visible, the
support-pruned orbit has an infinite connected component; for \(a>\log3\), the proved admissible
reachability theorem makes it dense in the central corridor.

The exact support-localized lift would have coordinates

```text
(J_w u)_(root,nu)(x)
 =w_(root,nu) u(x-s_(root,nu)),                          (18)
```

so prime translation becomes coordinate adjacency without a cutoff defect.  Equations
`(5)`--`(15)` apply separately to each oriented root component.  Therefore:

```text
nonzero bounded localized lift        -> weight decay,
exact prime covariance                -> constant modulus,
self-adjoint ordinary ell2 adjacency  -> constant modulus.                 (19)
```

Any two properties on the right of `(19)` conflict with the first on an infinite component.

This explains the previously unresolved mismatch between the two exact constructions:

1. the global valuation-Wiener inverse is square summable because its coefficients decay by
   inverse logarithmic grade, but its components are delocalized Fourier parametrices;
2. literal translated physical profiles are localized and exactly covariant, but duplicating them
   is not square summable;
3. componentwise interval cutoff of the delocalized inverse creates the nonzero boundary
   commutator/Feshbach source.

There is no bounded natural transformation identifying these three models while preserving the
ordinary self-adjoint carrier.

## 6. Corrected E1 target

The former wording

```text
construct the completed mode in ell1 subset ell2 and intertwine the cutoff equation
```

is too permissive: it can be misread as a bounded orbit lift, which `(2)` rules out.  The valid
target is now:

```text
construct a source-dependent closed relation R_a
  subset H(S_(a,mu)) times
         L2_log(ell1 subset ell2 subset ellInfinity)

such that
  (a) its ell1 evaluation is the physical mode,
  (b) its graph norm retains the interval-cutoff commutator,
  (c) the middle ell2 equation is self-adjoint before evaluation,
  (d) trace-zero graph vectors enter the weighted Gamma domain.              (20)
```

The relation may not be replaced by duplicated orbit profiles while still presenting the
conjugated adjacency as self-adjoint.  It may be replaced, at finite prime-log recurrence type, by
the explicitly weighted nonselfadjoint orbit carrier of
`suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy.md`.  That carrier has bounded root
reconstruction and retains exact covariance; its unresolved source theorem is the literal
boundary-log normal identity, not evaluation.

This is the singular source-pointed survivor predicted by the biaxial source-conservation theorem.
It is not killed by that theorem; rather, `(20)` proves that its exceptional relation-valued
category is forced already by the literal completed Suzuki connector.

## 7. Hostile audit

1. **Not the synthesis theorem.**  The earlier codiagonal fracture concerns
   `ell2 -> physical`.  This theorem concerns the reverse localized orbit analysis and the
   compatibility of its weights with covariance and self-adjointness.
2. **No claim against coefficient carriers.**  A resolvent coefficient state can lie in
   \(\ell^1\cap\ell^2\).  It is not the orbit duplication `(1)` and survives.
3. **No claim against weighted/Krein spaces.**  A weighted adjacency can be symmetric in a changed
   metric.  Equation `(14)` proves that the metric then cannot simultaneously be the ordinary
   translation-invariant Suzuki \(\ell^2\) metric unless the weight is constant.  A bounded
   nonselfadjoint weighted adjacency survives and is now constructed explicitly.
4. **No cutoff deletion.**  The positive exterior Feshbach return and physical cutoff commutator
   are precisely the graph data that `(20)` must retain.
5. **No RH or whole-Connes verdict.**  This closes one impossible formulation of E1.  A singular
   relation remains live; prolate class P and noncompact-incidence class I are untouched.

## 8. Novelty boundary

Formula `(5)` is elementary orbit-frame theory, and `(14)` is elementary similarity algebra.
Neither is claimed as new separately.  Candidate-new knowledge is their source-exact conjunction:

```text
Suzuki valuation localization
+ infinite support-pruned orbit
+ literal self-adjoint prime adjacency
+ completed-domain connector
 -> bounded/covariant/self-adjoint trilemma
 -> forced relation-valued E1 category.                  (21)
```

The corpus contained the dual evaluation nonclosability theorem and the positive
\(\ell^1\subset\ell^2\subset\ell^\infty\) rigging, but not the analysis-side orbit-lift obstruction
or the self-adjoint diagonal-similarity classification.  External priority remains unaudited.

## 9. Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiLocalizedOrbitLiftTrilemma.lean
```

The formal core proves unconditionally that a square-summable weight on an infinite additive group
with translation-invariant modulus is zero, including projective unit-modulus covariance and the
Suzuki prime-valuation specialization.  No analytic source theorem or RH hypothesis is packaged
behind an implication.

## Gates

- [x] prove exact orbit-lift norm identity
- [x] prove projective covariance forces invariant modulus
- [x] prove diagonal self-adjoint similarity forces edgewise constant modulus
- [x] specialize to infinite prime-valuation components
- [x] identify duality with physical-evaluation nonclosability
- [x] replace bounded-Hilbert E1 wording by closed rigged relation
- [x] formalize invariant-modulus square-summability obstruction unconditionally
- [ ] construct the source-dependent relation `(20)`
- [ ] prove its cutoff graph is closed
- [ ] prove trace-zero weighted Gamma-domain entry
- [ ] prove completed Evans injectivity
- [ ] RH

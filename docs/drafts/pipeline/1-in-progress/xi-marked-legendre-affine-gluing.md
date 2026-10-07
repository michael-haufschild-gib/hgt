# Marked Legendre pencils and arithmetic affine gluing

- **ID:** RH-MLAG-20261006
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / source-gluing audit
- **Source:** `xi-conductor-nearby-cycle-degeneration.md`; `rh-nonmetric-infinite-geometry-loop.md`
- **Statement:** Classify flat comparisons of additive Legendre pencils under affine changes of their auxiliary coordinate, then identify the exact prime-deletion repair and its retained normal class.
- **Scientific status:** paper argument below; parent-theory novelty audit active; no RH claim.

## Why this is the current problem

The reduced-node route lacks a source-natural global comparison. A marked additive pencil retains the source function, but retaining its base coordinate may prevent the required arithmetic comparisons. This card tests that incompatibility. It does not abandon the unresolved arithmetic comparison because it is difficult.

The relevant existing corpus is stronger than a generic node calculation:

- `XiNodalConductorHolonomyNaturalityClassification.lean` identifies the old pointwise naturality square with critical-line placement.
- `XiReducedConductorRoosRegulatorClassification.lean` proves reduced multiplicity data cannot realize the reflection-odd Roos class unless RH holds; an oriented source coordinate gives a regulator which preserves the defect.
- `RamifiedNodeConductor.lean` now contains the coefficient-torsion classification for powers of the nodal shear. This card does not duplicate that work.

## Exact objects

Let `L` be the complex rank-two homology local system of the proper Legendre family

```
E_lambda : Y^2 Z = X(X-Z)(X-lambda Z),
lambda in C \ {0,1}.
```

For `c in C`, put `L_c = (w |-> w+c)^* L`, on `C \ {-c,1-c}`. For `a != 0` and `b in C`, let `alpha(w)=a*w+b`. Comparisons are morphisms of complex local systems on the common smooth locus of `L_c` and `alpha^*L_d`. A base change is part of the comparison, never silently forgotten.

## Frozen affine comparison claim

```
Hom(L_c, alpha^* L_d) != 0
iff
  (a=1 and b=c-d) or (a=-1 and b=1-c-d).
```

In the two surviving cases the Hom space is one-dimensional. In particular, on the identical marked base, `Hom(L_c,L_d)=0` whenever `c != d`.

### Paper proof

The classical Legendre monodromies, in a suitable integral basis, are

```
T0 = [[1,2],[0,1]],
T1 = [[1,0],[-2,1]].
```

Their only invariant complex lines are respectively the first and second coordinate lines. Hence they have no common invariant line, and the rank-two representation is irreducible. Removing finitely many additional ordinary points does not change this image: loops around the original two punctures still occur; loops about additional points act trivially. An affine pullback has the same property.

A nonzero map between these two irreducible rank-two representations is an isomorphism: its kernel and image are invariant subspaces. At each finite puncture of the source the local monodromy is nonidentity. If that point is not a puncture of the target, the target extends across a disc and its monodromy there is identity, contradicting the isomorphism. Reversing source and target gives equality of the two finite puncture sets.

Thus `alpha` bijects `{-c,1-c}` with `{-d,1-d}`. There are exactly two cases. Preserving the order of the displayed pair gives `a=1`, `b=c-d`; exchanging the pair gives `a=-1`, `b=1-c-d`.

In the first case the Legendre parameters agree identically. In the second they sum to one; the fibre map `x' = 1-x`, `y' = i*y` identifies the affine cubics and extends to their smooth projective completions, fixing the point at infinity. Thus both cases provide an isomorphism.

Finally an endomorphism commuting with `T0` has equal diagonal entries and zero lower-left entry; commuting also with `T1` forces its upper-right entry to vanish. The endomorphism is scalar. Composing with either displayed isomorphism proves the one-dimensional Hom assertion.

No estimate, positive form, eigenvalue confinement, or Fourier argument is used. This is an elementary consequence of classical geometric monodromy, so the general statement must not be presented as a newly discovered field.

### Finite and profinite covers do not repair a forbidden affine comparison

The Hom vanishing persists after restriction to every finite-index subgroup `H` of the fundamental group `G` of the common smooth locus. For each original loop, some positive power belongs to `H`. In the source representation this supplies nontrivial powers of both `T0` and `T1`, whose fixed lines are unchanged and distinct. Thus the restriction remains irreducible; the target restriction does too. A loop about an unmatched puncture has some positive power in `H`; that power still acts nontrivially on one side and trivially on the other. The preceding isomorphism contradiction therefore applies unchanged. This includes finite covers ramified at the deleted punctures.

There is an exact infinite-level version with its topology specified. Let `X=lim_i X_i` be an inverse system of finite `G`-sets, with its inverse-limit topology. Let `V,W` be the two stalk representations. A morphism between the pulled-back **locally constant** sheaves is described on the fibre by a locally constant map

```
A : X -> Hom_C(V,W),
A(g*x) = rho_W(g) A(x) rho_V(g)^(-1).
```

Fix `x`. Local constancy supplies a finite-level cylinder around `x` on which `A` is constant (a finite intersection of cylinders refines to one level in the cofiltered system). The stabilizer `H` of the coordinate `x_i` has finite index in `G`, and `h*x` remains in this cylinder for every `h in H`. The displayed equation says that `A(x)` intertwines the restrictions to `H`. Finite-index Hom vanishing gives `A(x)=0`. Since `x` was arbitrary, `A=0`.

This covers arbitrary cofiltered systems of finite covers, not just a sequential root tower. It does **not** cover arbitrary continuous matrix-valued functions with the usual complex topology, nor arbitrary infinite covers. The locally constant topology is load-bearing.

The boundary is sharp: on the ordinary universal cover both rank-two local systems become constant, and their Hom space is all `2 x 2` complex matrices. On the discrete fibre `G`, any matrix `M` defines

```
A(g)=rho_W(g) M rho_V(g)^(-1).
```

These maps need not descend through a finite-index subgroup. Infinite covering alone therefore does not provide a canonical arithmetic comparison: it can remove precisely the descent information that excluded arbitrary maps.

## Literal source application and exact repair

Let `S` be the critical strip, let `f=xi` in the uncentered coordinate, and let

```
u_p(s)=1-p^(-s),
f_p(s)=u_p(s)*f(s).
```

The two marked pencils have parameters `f(s)+w` and `f_p(s)+w`. At every `s` where `f(s)!=0`, their shifts differ because `p^(-s)!=0`. The fixed-base Hom vanishes on each such auxiliary line. In particular, a comparison which is nonzero on every such line cannot be a map of these local systems over the identity of `(s,w)`.

There is an exact affine repair:

```
A_p(s,w) = (s, w + p^(-s)*f(s)),
f_p(s) + pr_w(A_p(s,w)) = f(s)+w.
```

Keeping `(X,Y,Z)` unchanged therefore gives an isomorphism of the proper families covering `A_p`. The map is a biholomorphism of the whole base, with inverse subtracting `p^(-s)*f(s)` from `w`.

For finite prime sets `F,G`, write `f_F=u_F*f` and define

```
A_(F,G)(s,w) = (s, w + f_F(s)-f_G(s)).
```

Then `A_(G,H) o A_(F,G)=A_(F,H)`, without a limiting or summability assumption. In the conductor-preserving branch of the affine classification this is the unique affine base repair: the alternative exchanges the `lambda=0` and `lambda=1` degenerations.

The repair moves the distinguished source slice `w=0`. Its intersection with its image has equation `p^(-s)*f(s)=0`, which defines exactly the Cartier divisor `(f)`, including multiplicity, because `p^(-s)` is a unit. At a zero `rho` of order `m`, if

```
f(rho+z)=j*z^m + terms of higher degree,
```

then the displacement has first coefficient `p^(-rho)*j`. For enlargement `F -> F union {p}` with `p notin F`, it is `u_F(rho)*p^(-rho)*j`. This follows by multiplication of germs; no derivative below order `m` contributes.

Thus the geometric repair preserves a nonzero first normal class. It does not force that class to vanish or locate the divisor. The arithmetic coefficients now live in the difference of marked sections. Treating the affine base repair as a fixed-base cycle map would discard precisely this distinction.

## Hostile audit

- The proposed fixed-base, nonzero comparison is false whenever the two shifts differ. Its positive replacement is the complete affine classification and the unique conductor-preserving repair, not a restated negation.
- The repair is an additive coboundary of the functions `f_F`. It is not an unexplained new cohomology class.
- The application currently proves fibrewise Hom vanishing. It does not claim a theorem about arbitrary maps supported only on the Xi divisor, or about all possible geometric realizations of arithmetic action.
- The known monodromy representation is an external geometric input. No Lean verification of the proper-family/local-system identification is claimed.
- Novelty is unverified for the source application; the parent monodromy argument is classical. A search miss is not a novelty certificate.
- General source gluing remains open. A surviving construction must retain the moved section or its normal/extension data, and still prove the required arithmetic comparison; existence of these explicit affine maps alone is insufficient.

## Sources and checks

- Bogdan Zavyalov, [Notes for the big monodromy lemma](https://bogdanzavyalov.com/refs/notes/Big_Monodromy.pdf), Section 3: geometric Legendre monodromy and the marked two-torsion structure. The note also separates pullback from the family obtained by collecting Legendre curves at roots of the parameter; these are different constructions.
- Nicholas Katz, [Convolution and Equidistribution, author draft](https://web.math.princeton.edu/~nmk/mellin324book.pdf), Chapter 15 and Theorem 17.2: the singular-support obstruction to nontrivial translates is already an established mechanism for Legendre sheaves. The characteristic-zero affine calculation here is consequently a **BRIDGE**; no novelty is claimed for that parent argument. No weight or positivity theorem from this book is used.
- Corpus queries inspected candidate lemmas and source arguments for conductor global monodromy, ramification/coefficient exchange, and additive Legendre pencils. Index warnings include unmeasured semantic coverage and stale/source-only compiler evidence.
- No numerical experiment, no new axiom, and no claimed Lean theorem.

## Next work

- [x] Freeze the comparison category and prove the affine classification on paper.
- [x] Construct the literal prime-deletion repair and its terminal normal coefficient.
- [x] Audit the parent mechanism: classical singular-support/irreducibility rigidity; no novel general theorem certified.
- [ ] Determine whether the first normal term is canonically carried by a degeneration extension, rather than forced into the invariant cycle line.
- [ ] Formalize a qualifying dependency-closed result; keep geometric identifications distinct from algebraic models.
- [ ] Continue the actual arithmetic comparison. RH remains unresolved and the goal remains active.

## Continuous compact-fibre refinement

The locally constant qualification above can be removed for these affine coefficient targets. The stronger statement concerns a continuous equivariant field

```
A : X -> Hom_C(V,W)
```

on **any compact** `G`-space `X`, with the usual finite-dimensional complex topology on the target. It is not a statement about arbitrary projective-valued fields, discontinuous fields, or noncompact fibres.

### Closed-lattice lemma and positive factorization

Let `K` be a compact subset of a Hausdorff complex topological vector space `E`. If `v + n*w` lies in `K` for every integer `n`, then `w=0`.

Proof: if `w!=0`, the map `C -> E`, `z |-> z*w`, is a closed embedding (a finite-dimensional subspace of a Hausdorff topological vector space has its usual topology and is closed). The integer lattice is closed and discrete in `C`. Translation by `v` therefore identifies the displayed orbit with a closed discrete copy of `Z` in `E`. It would be a closed subset of the compact set `K`, hence compact, whereas an infinite discrete space is not compact. This uses a closed-orbit obstruction, not an estimate of an orbit or a positive form.

Suppose `h in G` acts trivially on `W` and acts on `V` by `1+N`, with `N^2=0`. Equivariance gives, at every `x`,

```
A(h^n*x) = A(x) - n*A(x)*N.
```

The left side lies in the compact image of `A`, so the lemma gives `A(x)*N=0`. Apply this also to every conjugate of `h`. Consequently `A(x)` factors uniquely through

```
V / span { rho_V(g)(im N) : g in G }.
```

This quotient is the positive survivor: it is the maximal source quotient left after the unmatched vanishing-cycle orbit is annihilated. If `V` is irreducible and `N!=0`, the displayed span is a nonzero invariant subspace, hence all of `V`; therefore `A=0`.

For forbidden affine comparisons of marked Legendre pencils, choose a finite puncture occurring only on the source side. Its monodromy is a nontrivial rank-one shear on `V` and the identity on `W`; Legendre irreducibility supplies the spanning condition. Thus the same Hom vanishing holds for continuous coefficient fields on arbitrary compact covering fibres, in particular arbitrary inverse limits of finite covers. The noncompact universal-cover fibre remains outside the theorem.

**Verdict:** `BRIDGE`. The parent mechanism is classical affine unipotent orbit rigidity, consistent with Kostant–Rosenlicht (Milne, *Algebraic Groups*, Theorem 17.64). The precise compact-fibre application strengthens this card's model audit; it is not a novel general rigidity theorem or an RH proof. The proper-family identification is still a paper argument. Formalization will distinguish the exact topological factorization from that geometric identification.

## Derived comparison trial: what survives in degree one

For `c!=d`, put `M=Hom(L_c,L_d)` on the common smooth locus. The ordinary `Hom` vanishing does not imply that extension classes vanish. On the punctured sphere the parabolic group is `H^1(P^1,j_*M)`, the image of compactly supported in ordinary cohomology.

The following dimension calculation is a **paper candidate**, not yet a completed geometric comparison. For `d-c` outside `{0,1,-1}`, there are four finite singular points and infinity. At each finite point the rank-four local system `M` has a two-dimensional fixed subspace. At infinity the two signed nodal monodromies induce a tensor action with a two-dimensional fixed subspace. Thus the Euler characteristic is `2*4 - 5*2 = -2`. Global invariants and dual invariants vanish by the direct Hom theorem, giving parabolic dimension two. At `d-c=1` or `-1`, the collision leaves four punctures in total with the same local fixed dimensions, giving dimension zero. At `c=d`, global scalar endomorphisms and their dual contribute one dimension each; the same calculation gives parabolic dimension zero. These assertions require the usual parabolic Euler characteristic and duality identifications; no proof has been formalized here.

A geometric candidate for the surviving rank-two channel is the quartic

```
Q_delta: y^2 = x*(x-1)*(x+delta)*(x+delta-1),
delta = d-c.
```

For `delta` outside `{0,1,-1}`, set

```
t = (1+delta)*x/(x+delta),
v = delta*(1+delta)*y/(x+delta)^2.
```

Direct substitution gives `v^2=t*(t-1)*(t-(1-delta^2))`. The inverse on the corresponding open chart is `x=delta*t/(1+delta-t)` with `y` recovered from the displayed nonzero factor. The smooth projective quartic is therefore a Legendre curve with parameter `1-delta^2`. This birational identity is exact; identifying its cohomology with the parabolic extension channel is **OPEN**, and matching dimensions alone is not that identification.

The connection to the two-pencil fibre product is concrete: eliminating their common parameter produces the conic

```
y1^2/[x1*(x1-1)] - y2^2/[x2*(x2-1)] = x1-x2+delta.
```

Over the discriminant line `x2=x1+delta`, the two components are distinguished by the square root of `x1*(x1-1)*x2*(x2-1)`, yielding exactly `Q_delta`. Compactification, the other discriminant components, the cylinder correspondence, and its compatibility with degeneration must still be proved before transferring a cohomology class.

For the literal prime displacement `delta=p^(-s)*xi(s)`, the resulting Legendre parameter is `1-p^(-2s)*xi(s)^2`. It retains the prime normal coefficient but also introduces degenerations at `delta=1,-1`. It does not yet construct a canonical extension class, remove the arithmetic obstruction, or establish any zero-location statement.

External parent check: Collas–Dettweiler–Reiter–Sawin, [*Monodromy of Elliptic Curve Convolution*](https://collas.perso.math.cnrs.fr/documents/Collas,Dettweiler,Reiter,Sawin-EllipticConvolutionG2-motives.pdf), gives the established parabolic-cohomology/cocycle framework. Its base is an elliptic curve; its results are not silently substituted for the present punctured-sphere calculation.

## Current audit and next exact target

No significant novelty beyond the literature has been certified in this cycle. The affine comparison, closed-orbit argument, and quartic change of variables have classical parents. They narrow a specific source-gluing attempt; routine formalization alone would not meet the research goal.

The next hard target is an actual source-defined comparison class with its degeneration law. The quartic discriminant construction is a concrete candidate, but its missing cylinder comparison and canonical class are not assumptions to be granted. The compact-fibre obstruction must be kept when testing whether such a class can return to an ordinary direct comparison.

## Verification checkpoint

`formal/GaloisForLFunctions/HTGeometry/CompactShearDescent.lean` now proves the closed-lattice lemma, exact annihilator classification, unique quotient descent, preservation of evaluation-continuity, and vanishing when the shear images span the source. The module is imported by the HTGeometry umbrella. These are the topological/algebraic statements; the proper Legendre-family identification is not formalized.

- Final module audit: `lake env lean GaloisForLFunctions/HTGeometry/CompactShearDescent.lean` exited 0.
- Separate `/tmp` axiom audit of the lattice, unique quotient, zero-family and continuous quotient theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py index` completed and regenerated the standard indexes.
- Global `scripts/formal_tools.py lint` exited 1 on five unrelated HTGeometry umbrella omissions: `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. No error named the new module. No clean global lint claim is made; other threads' modules were not altered.

The bridge is verified, but the significant-novelty gate and the RH goal remain unmet. The integral cylinder comparison is continued in `xi-legendre-integral-cylinder-comparison.md`.

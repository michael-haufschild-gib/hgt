# Symmetric formation homology, observer-created overlap, recovery duality, and Fisher-nullity law

- **ID:** ULF-TFIM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / ROUTE-INDEPENDENT FORMATION MECHANISM
- **Source:** `../../../1-in-progress/universal-law-field/ternary-formation-interference-mechanics/field-programme.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [SYMMETRIC THREE-FORMATION LAW]`
  `[OBSERVER-CREATED OVERLAP] [EXACT RECOVERY CONSERVATION] [DUAL REPORTER]`
  `[POSITIVE HODGE CARRIER] [FOURTH-ORGAN FISHER PREDICTION]`
  `[COFINAL PROPERNESS SELECTION] [LEAN CORE FORMALIZED] [HODGE/FISHER LEAN OPEN] [NOT RH]`
- **Statement:** Three relation formations carry a canonical first homology.  Choosing one formation
  as an observer kernel identifies that homology with overlap created by observation, with excess
  joint recovery loss, with a dual reporter quotient, and with the exact missing rank of the fused
  Fisher information.  Isometric symmetry transports this charge but cannot erase it; persistent
  nonzero charge is excluded by a divergent cofinal action.

## 1. Goal and mechanism

The corpus contains many instances of the same failure pattern:

1. two formation legs are individually exact or recoverable;
2. their fusion creates a relation invisible on either leg;
3. an observer turns distinct source directions into a common target direction;
4. positive scalarization records only a missing rank or energy;
5. symmetry transports the defect without selecting its vanishing.

The theorem below makes this one mechanism.  It does not postulate curvature or a new geometric
object.  It starts from the formation laws themselves and forms their incidence complex.  Failure
of exact fusion is homology.  Observer overlap, recovery loss, reporter legality, and Fisher
degeneracy are different realizations of the same class.

Let `k` be a field, `V` a `k`-vector space, and `U,W,Z` subspaces of `V`.  Write sums and
intersections as `+` and `cap`.  All vector spaces in Sections 5--8 are finite-dimensional.

## 2. Symmetric three-formation complex

Define

\[
 C_2=(U\cap W)\oplus(U\cap Z)\oplus(W\cap Z),
 \qquad C_1=U\oplus W\oplus Z,
 \qquad C_0=U+W+Z,
 \tag{TFIM.1}
\]

and

\[
 \begin{aligned}
 d_2(a,b,c)&=(a+b,-a+c,-b-c),\\
 d_1(u,w,z)&=u+w+z.
 \end{aligned}
 \tag{TFIM.2}
\]

### Theorem 2.1 -- symmetric formation homology

The following statements hold.

1. `d_1 d_2=0` and `d_1` is surjective.
2. The map
   \[
    U\cap W\cap Z\longrightarrow\ker d_2,
    \qquad x\longmapsto(x,-x,x)
    \tag{TFIM.3}
   \]
   is an isomorphism.
3. The first formation charge
   \[
    \mathsf H(U,W,Z):=\ker d_1/\operatorname{im}d_2
    \tag{TFIM.4}
   \]
   is invariant under every permutation of `U,W,Z`.
4. There are canonical isomorphisms
   \[
   \boxed{
    \mathsf H(U,W,Z)
    \simeq
    \frac{U\cap(W+Z)}{(U\cap W)+(U\cap Z)}
    \simeq
    \frac{W\cap(U+Z)}{(W\cap U)+(W\cap Z)}
    \simeq
    \frac{Z\cap(U+W)}{(Z\cap U)+(Z\cap W)}.}
    \tag{TFIM.5}
   \]
5. In finite dimension its rank is the symmetric inclusion--exclusion defect
   \[
   \boxed{
   \begin{aligned}
    h(U,W,Z):=\dim\mathsf H(U,W,Z)
      ={}&\dim U+\dim W+\dim Z-\dim(U+W+Z)\\
       &-\dim(U\cap W)-\dim(U\cap Z)-\dim(W\cap Z)\\
       &+\dim(U\cap W\cap Z).
   \end{aligned}}
   \tag{TFIM.6}
   \]

### Proof

For `(a,b,c) in C_2`, the three coordinates of `d_2(a,b,c)` sum to zero, proving
`d_1 d_2=0`.  Surjectivity of `d_1` is the definition of `U+W+Z`.

If `d_2(a,b,c)=0`, then `b=-a` and `c=a`; membership of `a,b,c` in the three
pairwise intersections forces `a in U cap W cap Z`.  Conversely `(x,-x,x)` is in the kernel.
This proves item 2.

Permuting the three subspaces relabels the direct summands of `(TFIM.1)`.  The usual orientation
sign on the pairwise terms makes these relabellings chain isomorphisms.  Hence they induce
isomorphisms on `H_1`; no leg is intrinsically privileged.

For the first isomorphism in `(TFIM.5)`, project a cycle `(u,w,z)` to the class of `u`.  Since
`u+w+z=0`, the vector `u` belongs to `U cap (W+Z)`.  Adding `d_2(a,b,c)` changes `u` by
`a+b in (U cap W)+(U cap Z)`, so the map is defined on homology.

It is surjective: if `u=w'+z'` with `u in U`, `w' in W`, `z' in Z`, then
`(u,-w',-z')` is a cycle.  It is injective: if `u=a+b` with `a in U cap W` and
`b in U cap Z`, subtract `(a+b,-a,-b)=d_2(a,b,0)`.  The remaining cycle is
`(0,c,-c)=d_2(0,0,c)` for some `c in W cap Z`.  Cyclic permutation proves the other
two isomorphisms.

Finally,

\[
 \dim\ker d_1=\dim U+\dim W+\dim Z-\dim(U+W+Z),
\]

while item 2 gives

\[
 \dim\operatorname{im}d_2
 =\dim(U\cap W)+\dim(U\cap Z)+\dim(W\cap Z)-\dim(U\cap W\cap Z).
\]

Subtracting proves `(TFIM.6)`.  QED.

### Meaning

`H(U,W,Z)` is not another measurement attached after the fact.  It is the failure of the three
formation legs and their pairwise gluing relations to generate an exact local-to-global complex.
It vanishes exactly when any, hence every, distributivity quotient in `(TFIM.5)` vanishes.

## 3. Observer-created overlap

Let

\[
 L:V\longrightarrow Y,
 \qquad U=\ker L.
 \tag{TFIM.7}
\]

Define the target overlap manufactured by `L` from `W,Z`:

\[
 \mathsf O_L(W,Z)
 :=\frac{L(W)\cap L(Z)}{L(W\cap Z)}.
 \tag{TFIM.8}
\]

The denominator is contained in the numerator, so this is canonical.

### Theorem 3.1 -- observer-overlap realization

There is a canonical isomorphism

\[
 \boxed{
 \mathsf H(\ker L,W,Z)
 \simeq
 \frac{L(W)\cap L(Z)}{L(W\cap Z)}.}
 \tag{TFIM.9}
\]

Equivalently,

\[
 \boxed{
 \frac{\ker L\cap(W+Z)}{(\ker L\cap W)+(\ker L\cap Z)}
 \simeq
 \frac{L(W)\cap L(Z)}{L(W\cap Z)}.}
 \tag{TFIM.10}
\]

Thus image formation preserves the intersection of `W,Z` exactly iff the ternary formation charge
vanishes.

### Proof

Take `u in ker L cap (W+Z)` and choose `u=w+z`.  Since `L(u)=0`,
`L(w)=-L(z)` belongs to `L(W) cap L(Z)`.  Send the class of `u` to the class of `L(w)`.

If `u=w'+z'` is another decomposition, then `w-w'=-(z-z') in W cap Z`; hence the target
class is independent of decomposition.  Changing `u` by elements of `ker L cap W` and
`ker L cap Z` changes nothing in the target.

For surjectivity, let `y=L(w)=L(z')` belong to `L(W) cap L(Z)`.  Then `u=w-z'` belongs to
`ker L cap (W+Z)` and maps to `y`.

For injectivity, suppose `L(w)=L(a)` for some `a in W cap Z`.  Then
`w-a in ker L cap W` and, because `L(z)=-L(w)`, `z+a in ker L cap Z`.  Hence
`u=(w-a)+(z+a)` is zero in the source quotient.  QED.

### Corollary 3.2 -- exact local-to-joint recovery criterion

Assume `L|_W` and `L|_Z` are injective.  Then

\[
 \mathsf H(\ker L,W,Z)=\ker(L|_{W+Z}).
 \tag{TFIM.11}
\]

Consequently

\[
 \boxed{
 L|_{W+Z}\text{ is injective}
 \iff
 L(W)\cap L(Z)=L(W\cap Z)
 \iff
 \mathsf H(\ker L,W,Z)=0.}
 \tag{TFIM.12}
\]

Pairwise recoverability is therefore not joint recoverability.  The missing premise is exact
preservation of overlap.

### Corollary 3.3 -- quotient-created overlap form

There is also a canonical isomorphism

\[
 \boxed{
 \mathsf H(U,W,Z)
 \simeq
 \frac{(U+W)\cap(U+Z)}{U+(W\cap Z)}.}
 \tag{TFIM.13}
\]

Indeed, the quotient map `q:V -> V/U` has kernel `U`; apply `(TFIM.9)` and use
`q(W)=(U+W)/U`.  Formula `(TFIM.13)` says precisely that quotienting can create an intersection.

### Corollary 3.4 -- exact submodularity-slack identity

Assume finite dimension and put

\[
 r_L(A)=\dim L(A),
 \qquad
 n_L(A)=\dim A-r_L(A)=\dim(\ker L\cap A).
 \tag{TFIM.13a}
\]

Because `L(W+Z)=L(W)+L(Z)`, the observer-overlap theorem and the dimension formula for two
subspaces give

\[
 \boxed{
 \begin{aligned}
 \dim\mathsf H(\ker L,W,Z)
   &=r_L(W)+r_L(Z)-r_L(W+Z)-r_L(W\cap Z)\\
   &=n_L(W+Z)+n_L(W\cap Z)-n_L(W)-n_L(Z).
 \end{aligned}}
 \tag{TFIM.13b}
\]

Thus formation homology is exactly the submodularity slack of observer rank and, equivalently, the
supermodularity slack of observer nullity.  The usual inequalities do not merely bound the charge;
their failure of equality is its dimension.

### Theorem 3.5 -- observer image creates Mayer--Vietoris homology

The source sequence

\[
 0\longrightarrow W\cap Z
 \xrightarrow{a\mapsto(a,-a)}W\oplus Z
 \xrightarrow{(w,z)\mapsto w+z}W+Z
 \longrightarrow0
 \tag{TFIM.13c}
\]

is exact.  Apply `L` to each *formed subspace*, rather than applying the exact functor to an
already-fixed sequence.  The resulting observer-formation complex is

\[
 0\longrightarrow L(W\cap Z)
 \xrightarrow{y\mapsto(y,-y)}L(W)\oplus L(Z)
 \xrightarrow{(y_1,y_2)\mapsto y_1+y_2}L(W+Z)
 \longrightarrow0.
 \tag{TFIM.13d}
\]

Its left map is injective, its right map is surjective, and its only possible homology is the
middle group

\[
 \boxed{
 H_{\rm mid}(L\mathsf{MV}(W,Z))
 =\frac{L(W)\cap L(Z)}{L(W\cap Z)}
 \simeq\mathsf H(\ker L,W,Z).}
 \tag{TFIM.13e}
\]

### Proof

The source sequence is the ordinary two-subspace Mayer--Vietoris sequence.  In `(TFIM.13d)`, the
kernel of addition is formed by pairs `(y,-y)` with `y in L(W) cap L(Z)`.  The image of the left
map consists of those pairs with `y in L(W cap Z)`.  Their quotient is `(TFIM.8)`, and
Theorem 3.1 supplies the final isomorphism.  QED.

This is the generative grammar in its smallest exact form: formation is exact before observation;
the observer-image operation preserves the join and endpoints but not the intersection; the
resulting failure of exactness is a new homology class.

## 4. Reduced fusion complex and exact recovery conservation

The ordinary Mayer--Vietoris sequence for `W,Z` is exact:

\[
 0\to W\cap Z\xrightarrow{a\mapsto(a,-a)}W\oplus Z
 \xrightarrow{(w,z)\mapsto w+z}W+Z\to0.
 \tag{TFIM.14}
\]

Reduce each local leg by the common recovery kernel `U`, but reduce the fused target only after
formation.  This gives

\[
 \begin{aligned}
 M_2&=(W\cap Z)/(U\cap W\cap Z),\\
 M_1&=W/(U\cap W)\oplus Z/(U\cap Z),\\
 M_0&=(U+W+Z)/U,
 \end{aligned}
 \tag{TFIM.15}
\]

with the evident maps

\[
 \delta_2[a]=([a],[-a]),
 \qquad
 \delta_1([w],[z])=[w+z].
 \tag{TFIM.16}
\]

### Theorem 4.1 -- exact excess-kernel conservation

The map `delta_2` is injective, `delta_1` is surjective, and

\[
 \boxed{H_1(M_\bullet)\simeq\mathsf H(U,W,Z).}
 \tag{TFIM.17}
\]

Equivalently, with `K=ker delta_1`, there are exact sequences

\[
 0\longrightarrow
 \frac{W\cap Z}{U\cap W\cap Z}
 \longrightarrow K
 \longrightarrow\mathsf H(U,W,Z)
 \longrightarrow0,
 \tag{TFIM.18}
\]

and

\[
 0\longrightarrow K\longrightarrow M_1\xrightarrow{\delta_1}M_0\longrightarrow0.
 \tag{TFIM.19}
\]

The first term in `(TFIM.18)` is pre-existing overlap.  The quotient is overlap born only after
local reduction and fusion.

### Proof

Injectivity of `delta_2` and surjectivity of `delta_1` are immediate from their definitions.  Send
`([w],[z]) in K` to the class of `w+z` in
`[U cap (W+Z)]/[(U cap W)+(U cap Z)]`.  Changing representatives changes the sum only by the
denominator.  The map is surjective because every vector in `U cap (W+Z)` has a decomposition
`w+z`.

Its kernel consists exactly of pairs represented by `([a],[-a])` with `a in W cap Z`: if
`w+z=u_W+u_Z` with `u_W in U cap W` and `u_Z in U cap Z`, put
`a=w-u_W=-(z-u_Z)`.  The kernel of `a -> ([a],[-a])` is
`U cap W cap Z`.  This proves `(TFIM.18)` and `(TFIM.17)`; `(TFIM.19)` is tautological.  QED.

### Finite-dimensional conservation identity

Put `D=U cap (W+Z)` and `E=(U cap W)+(U cap Z)`.  Then

\[
 \boxed{
 \dim D
 =\dim(U\cap W)+\dim(U\cap Z)-\dim(U\cap W\cap Z)
  +\dim\mathsf H(U,W,Z).}
 \tag{TFIM.20}
\]

This is the exact local-loss plus generated-loss budget.

## 5. Coordinate-free reporter duality

Assume `V` finite-dimensional and write `A^\circ subset V^*` for the annihilator of a subspace
`A subset V`.  Since `E subset D`, restriction gives

\[
 (D/E)^*\simeq E^\circ/D^\circ.
 \tag{TFIM.21}
\]

The annihilator identities

\[
 (A\cap B)^\circ=A^\circ+B^\circ,
 \qquad
 (A+B)^\circ=A^\circ\cap B^\circ
 \tag{TFIM.22}
\]

give the following law.

### Theorem 5.1 -- dual distributivity quotient

There is a canonical perfect pairing

\[
 \boxed{
 \mathsf H(U,W,Z)\times
 \frac{(U^\circ+W^\circ)\cap(U^\circ+Z^\circ)}
      {U^\circ+(W^\circ\cap Z^\circ)}
 \longrightarrow k.}
 \tag{TFIM.23}
\]

Equivalently,

\[
 \boxed{
 \mathsf H(U,W,Z)^*
 \simeq
 \frac{(U^\circ+W^\circ)\cap(U^\circ+Z^\circ)}
      {U^\circ+(W^\circ\cap Z^\circ)}.}
 \tag{TFIM.24}
\]

### Proof

For `D=U cap (W+Z)` and `E=(U cap W)+(U cap Z)`, `(TFIM.22)` gives

\[
 \begin{aligned}
 E^\circ&=(U^\circ+W^\circ)\cap(U^\circ+Z^\circ),\\
 D^\circ&=U^\circ+(W^\circ\cap Z^\circ).
 \end{aligned}
\]

Substitute in `(TFIM.21)`.  QED.

The dual class is a legal reporter on the pairwise-generated relation space `E` which still detects
the fused relation space `D`.  Reporter loss and relation birth are not two independent defects;
they are perfect duals.

## 6. Positive Hodge carrier

Assume `k=R` or `C` and choose inner products on the finite-dimensional chain spaces in
`(TFIM.1)`.  Define the degree-one Hodge Laplacian

\[
 \Delta_1=d_2d_2^*+d_1^*d_1:C_1\to C_1.
 \tag{TFIM.25}
\]

### Theorem 6.1 -- positive carrier and exact rank

The operator `Delta_1` is positive semidefinite and

\[
 \boxed{
 \ker\Delta_1
 =\ker d_1\cap(\operatorname{im}d_2)^\perp
 \simeq\mathsf H(U,W,Z).}
 \tag{TFIM.26}
\]

Hence the orthogonal projection `P_harm` onto `ker Delta_1` satisfies

\[
 P_{\rm harm}^2=P_{\rm harm}=P_{\rm harm}^*,
 \qquad
 P_{\rm harm}\succeq0,
 \qquad
 \operatorname{rank}P_{\rm harm}=h(U,W,Z),
 \tag{TFIM.27}
\]

and `P_harm=0` exactly when formation is exact.

### Proof

For every `x in C_1`,

\[
 \langle\Delta_1x,x\rangle=\|d_2^*x\|^2+\|d_1x\|^2.
\]

Thus its kernel is `ker d_1 cap ker d_2^*`, which equals
`ker d_1 cap (im d_2)^perp`.  Every coset in `ker d_1/im d_2` has a unique orthogonal
representative in this subspace.  The projection statements follow.  QED.

There is also a one-leg positive representative.  For
`E=(U cap W)+(U cap Z) subset D=U cap(W+Z)`, nested orthogonal projections satisfy

\[
 \boxed{P_D-P_E=P_{D\cap E^\perp}\succeq0,
 \qquad \operatorname{rank}(P_D-P_E)=\dim\mathsf H(U,W,Z).}
 \tag{TFIM.28}
\]

The metric chooses a harmonic representative.  It does not change charge rank or zero locus.

## 7. Equivariance and functional-equation neutrality

Let `A:V -> V` be an invertible linear map.  Transporting all three subspaces gives a chain
isomorphism

\[
 C_\bullet(U,W,Z)\simeq C_\bullet(AU,AW,AZ),
 \tag{TFIM.29}
\]

and therefore

\[
 \boxed{\mathsf H(U,W,Z)\simeq\mathsf H(AU,AW,AZ).}
 \tag{TFIM.30}
\]

If `A` permutes the triple, it acts on the same charge space.  If it is unitary, it conjugates the
Hodge projector.  An involution can reverse or exchange representatives without forcing the charge
to vanish.

### Minimal functional-equation-fixed countermodel

Take `k=R` or `C` and `V=k^2`, with basis `e_1,e_2`, and put

\[
 U=k e_1,
 \qquad W=k(e_1+e_2),
 \qquad Z=k e_2,
 \qquad L(xe_1+ye_2)=y.
 \tag{TFIM.31}
\]

All three pairwise intersections vanish, `W+Z=V`, and

\[
 \mathsf H(U,W,Z)=U,
 \qquad \dim\mathsf H=1.
 \tag{TFIM.32}
\]

Both `L|_W` and `L|_Z` are injective, but `L|_{W+Z}` is not.  Target images satisfy

\[
 L(W)=L(Z)=k,
 \qquad L(W\cap Z)=0,
 \tag{TFIM.33}
\]

so the observer creates one full overlap direction.

Define

\[
 A(e_1)=-e_1,
 \qquad A(e_2)=e_1+e_2.
 \tag{TFIM.34}
\]

Then `A^2=1`, `A(U)=U`, `A(W)=Z`, `A(Z)=W`, and

\[
 L\circ A=L.
 \tag{TFIM.35}
\]

The observer is exactly fixed by the involution while the hidden charge is nonzero; `A` acts by
`-1` on it.  Averaging any inner product over `{1,A}` makes `A` unitary, so even the positive Hodge
carrier is equivariant.  Functional-equation symmetry is information-neutral here, not selective.

## 8. Fourth-organ prediction: fused Fisher nullity

Let `V,Y` be finite-dimensional real or complex Hilbert spaces.  For a subspace `A subset V`, write

\[
 L_A=L|_A,
 \qquad G_A=L_A^*L_A.
 \tag{TFIM.36}
\]

Then

\[
 \ker G_A=\ker L_A=\ker L\cap A.
 \tag{TFIM.37}
\]

Combining this with `(TFIM.20)` gives a theorem not used in the construction of the charge.

### Theorem 8.1 -- local-positive/fused-singular law

\[
 \boxed{
 \begin{aligned}
 \operatorname{nullity}G_{W+Z}
  ={}&\operatorname{nullity}G_W+\operatorname{nullity}G_Z\\
    &-\operatorname{nullity}G_{W\cap Z}
      +\dim\mathsf H(\ker L,W,Z).
 \end{aligned}}
 \tag{TFIM.38}
\]

In particular, if `L|_W` and `L|_Z` are injective, then

\[
 \boxed{\operatorname{nullity}G_{W+Z}=\dim\mathsf H(\ker L,W,Z).}
 \tag{TFIM.39}
\]

Thus every local Gram block can be positive definite while the fused Gram block is singular.  The
missing rank is exactly the ternary formation charge.

For the Gaussian location experiment

\[
 X\sim N(L a,I_Y),
 \qquad a\in A,
 \tag{TFIM.40}
\]

the Fisher information on parameter space `A` is `G_A`.  Therefore two separately identifiable
Gaussian submodels can fuse into a nonidentifiable model, with exact nonidentifiability rank
`dim H`.  This is a prediction in the positive/statistical organ derived solely from relation
formation and observer reduction.

## 9. Cofinal properness selection

The finite theorem supplies a charge but not its vanishing.  The missing global producer can be
stated without reference to any RH route.

Let `H_n` be formation-charge Hilbert spaces at increasing apertures and let

\[
 j_n:H_n\longrightarrow H_{n+1}
 \tag{TFIM.41}
\]

be injective noncontracting transports: `||j_nx|| >= ||x||`.  A coherent history satisfies
`h_{n+1}=j_nh_n`.  Choose weights `a_n>0` with every tail sum divergent and define truncated action

\[
 \mathcal A_N(h)=\sum_{n=0}^{N}a_n\|h_n\|^2.
 \tag{TFIM.42}
\]

### Theorem 9.1 -- persistent-charge properness selection

For every coherent history,

\[
 \boxed{
 \sup_N\mathcal A_N(h)<\infty
 \iff
 h_n=0\text{ for every }n.}
 \tag{TFIM.43}
\]

### Proof

If `h_m != 0`, noncontraction and coherence give `||h_n|| >= ||h_m||` for all `n>=m`.  Hence

\[
 \mathcal A_N(h)\ge\|h_m\|^2\sum_{n=m}^{N}a_n\longrightarrow\infty.
\]

The converse is immediate.  QED.

This is the required selection mechanism in abstract form:

1. local formation creates a homology charge;
2. source coherence transports it without contraction;
3. symmetry can act isometrically and remains neutral;
4. global finite-action admission forces the persistent charge to vanish.

An RH application must still prove that literal arithmetic formation classes instantiate the same
coherent charge system and that the physical source action is the stated cofinal action.  Neither
premise is inserted here.

## 10. Exact fusion across four organs

The theorem is one mechanism with four nonisomorphic realizations:

| Organ | Realization of the same charge |
|---|---|
| relation formation | `H_1` of the symmetric three-subspace incidence complex |
| observation/recovery | created overlap `[L(W) cap L(Z)]/L(W cap Z)` and excess joint kernel |
| matroid/rank | exact submodularity slack of `A -> dim L(A)` |
| homological descent | middle homology created by degreewise observer-image formation |
| reporter duality | annihilator distributivity quotient `(TFIM.24)` |
| positive/statistical | harmonic projector rank and fused Fisher nullity `(TFIM.38)` |

The exact sequence `(TFIM.18)`, the perfect pairing `(TFIM.23)`, and the nullity law
`(TFIM.38)` are reconstruction/conservation identities.  The Fisher theorem is a fourth-organ
prediction.  The properness theorem supplies a route-independent selection gate.

## 11. Hostile collision audit

### 11.1 Classical parent mathematics

The following ingredients are classical and carry no standalone novelty claim:

- modular, nondistributive subspace lattices;
- the two-subspace Mayer--Vietoris sequence;
- homology of a finite chain complex and finite-dimensional Hodge decomposition;
- annihilator duality and Gram/Fisher rank-nullity;
- compact/proper weighted persistence arguments.

Relevant parent directions include:

- Przytycki--Putyra, [*Homology of Distributive Lattices*](https://arxiv.org/abs/1111.4772),
  which develops chain complexes and Mayer--Vietoris methods for distributive structures;
- Emamy-K.--Melendez Rios,
  [*ST-Distributive and ST-Modular Lattices*](https://arxiv.org/abs/2312.03098), which studies
  relative distributivity identities of exactly the lattice-theoretic shape behind `(TFIM.5)`;
- Derksen, [*Hilbert series of subspace arrangements*](https://arxiv.org/abs/math/0510584), for
  intersection lattices and homological invariants of subspace arrangements;
- Sorensen--Kanatsoulis--Sidiropoulos,
  [*Generalized Canonical Correlation Analysis: A Subspace Intersection Approach*](https://arxiv.org/abs/2003.11205),
  for multiview identifiability through subspace intersections;
- Chicharro--Panzeri,
  [*Redundancy and synergy in dual decompositions of mutual information gain and information loss*](https://arxiv.org/abs/1612.09522),
  for the information-theoretic distinction between redundancy and synergy.

### 11.2 Internal collisions and exact residue

1. **Finite-quotient interaction cohomology.** That corpus theorem is an incidence-graph quotient
   of joint observables by marginal observables and realizes it as relative hypertranscendence.
   The present theorem is the source-linear dual situation: local relation formations become
   nonexact after one common observer quotient.  Its exact residue is `(TFIM.9)` plus the recovery
   and Fisher laws.  No equivalence between the two corpus theorems is claimed.
2. **Quotient--fusion genesis.** That theorem compares shared versus independently optimized
   gauge energies.  Here no minimization or chosen gauge slope appears; the charge is algebraic
   `H_1`, and energy arrives only after Hodge realization.
3. **Positive false overlap.** That theorem measures meet lost by positive pushforward of
   nonnegative profiles.  Here overlap is a quotient of linear image intersections, can carry
   signed reporters, and has a symmetric three-formation source complex.
4. **Critical triples.** The three-state theorem proves pairwise-compatible identifications can be
   jointly incompatible.  The present result classifies the linear obstruction, its exact rank,
   dual reporter, and fourth-organ Fisher consequence.
5. **Formation--quotient interchange.** That operator theorem concerns infinite assembled maps,
   compact quotients, and semi-Fredholm recovery.  The present finite law identifies the local
   derived charge which a later global properness theorem must transport.
6. **Linear-family defect supermodularity.** The Lean corpus already proves that image formation
   preserves joins, only laxly preserves intersections, and makes deficiency supermodular.  Formula
   `(TFIM.13b)` strictly sharpens that inequality for one observer: its slack is the rank of a
   canonical homology space, not merely a nonnegative integer.

### 11.3 Anti-theatre tests

1. Remove the homology language: `(TFIM.9)`, `(TFIM.18)`, `(TFIM.24)`, and `(TFIM.38)` remain
   exact, nontrivial statements.
2. Remove the observer: the symmetric complex and permutation-invariant charge remain.
3. Remove positivity: the algebraic charge and perfect reporter dual remain.
4. Remove symmetry: the recovery and Fisher predictions remain.
5. Keep only symmetry: the explicit involutive countermodel prevents a false selection theorem.
6. Keep only pairwise data: the same countermodel proves pairwise injectivity does not determine
   joint injectivity.

The honest status is `[BRIDGE] [NEW-TO-CORPUS COUPLING] [NOVELTY UNVERIFIED]`.  The mathematical
advance for the field programme is not a claim that subspace homology is new.  It is the exact
identification of one symmetric formation charge across relation, recovery, reporter, positive,
and properness laws.

## 12. RH pressure test and next gate

This theorem does not prove RH.  It changes the open problem from “find another source-native
relation” to two typed tasks:

1. construct from the literal pre-zero arithmetic source a coherent three-formation complex whose
   `H_1` maps to the unresolved route defects;
2. prove that the arithmetic source transports any nonzero class noncontractingly through a
   cofinal family whose physical action has divergent tails.

If both hold, Theorem 9.1 forces exactness.  If either fails, the failure names the missing law:
formation compatibility in task 1, or global action/properness in task 2.  Functional equation,
positivity, and recurrence are then consumers of the same charge, not independent selectors.

## 13. Lean status

`GaloisForLFunctions.HTGeometry.ConstitutiveSymmetricFormationHomology` now certifies the
route-independent algebraic core:

1. the canonical distributivity quotient `FormationCharge`;
2. the symmetric inclusion--exclusion rank conservation `(TFIM.6)`;
3. exact observer-overlap rank conservation, identifying the charge rank with
   `dim((L(W) cap L(Z))/L(W cap Z))`;
4. vanishing charge iff image formation preserves the intersection;
5. under pairwise injectivity, vanishing charge iff the fused observer is jointly injective.

Scratch elaboration, direct leaf elaboration, and the targeted leaf build pass.  Axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.  The module is imported by
`HTGeometry.UniversalLawField`; that umbrella was not built.  Explicit chain-complex permutation
isomorphisms, reporter duality, Hodge projector, and Fisher-nullity realization remain Lean-open.

## Gates

- [x] 0 -> 1: source-pure mechanism, falsifiers, and corpus collision search
- [x] 1 -> 2: complete coordinate-free paper proof and sharp countermodel
- [~] 2 -> 3: algebraic charge, overlap conservation, and joint-recovery criterion formalized;
  explicit complex, duality, Hodge carrier, and Fisher-nullity theorem remain
- [ ] 3 -> 4: publication paper and literal arithmetic three-formation realization

## Log

- 2026-08-14 -- symmetric formation complex discovered from the marked distributivity quotient;
  observer-created overlap, reduced-fusion homology, reporter duality, Hodge carrier, Fisher
  prediction, functional-equation countermodel, and cofinal properness selector closed on paper.

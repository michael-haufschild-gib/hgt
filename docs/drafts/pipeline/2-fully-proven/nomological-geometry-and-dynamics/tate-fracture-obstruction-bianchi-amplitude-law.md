# Tate fracture obstruction, Bianchi, and amplitude law

- **ID:** `cmr-tate-fracture-obstruction-bianchi-amplitude`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / HIGHER-DEFECT OBSTRUCTION LAW
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [CURVATURE/ADMISSION/COHERENCE]`
  `[STANDARD SUM/PRODUCT TOTALIZATION BOUNDARY] [POSITIVE STRICTNESS NO-GO] [NOT RH]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Statement:** In a filtered twisted complex, curvature is the first closed extension
  obstruction, higher Bianchi defects form its obstruction tower, and finite vertical amplitude
  forbids both indefinitely migrating coherence and a direct-sum/product completion boundary.

## Goal

Replace the untyped phrase “all no-gos are curvature” by one exact higher obstruction mechanism.
The mechanism must retain ordinary cohomology, permit nonzero curvature as an extension class,
distinguish missing morphisms, and expose the completion/order data that no ordinary complex can
contain by itself.

## 1. Why one ordinary defect complex is impossible

A bare ordinary chain/cotangent/tangent complex cannot encode all corpus organs. If the **same**
degree-one operator is required both to define cohomology and to represent curvature by its square,
then square-zero kills that curvature while non-square-zero destroys ordinary cohomology. A
separate connection can of course have nonzero curvature while commuting with an ordinary chain
differential. Moreover a bare complex does not determine completion topology, polarization,
admission, or holonomy; finite perfect complexes do not see an unbounded sum/product
totalization boundary; and an absent typed comparison is not an element of an existing Hom-space.

Therefore the universal carrier, if it exists, must be a higher partial totalization rather than
one defect class.

## 2. Filtered twisted complex

Let `A^(p,q)` be a bigraded `k`-module, or an object of a pretriangulated dg category, with the
relevant products and coproducts. Use total-degree signs. Let

\[
 D_r:A^{p,q}\longrightarrow A^{p+r,q+1-r},
 \qquad r\ge0,
\tag{1}
\]

have total degree one. Formally put

\[
 D=\sum_{r\ge0}D_r.
\tag{2}
\]

The full twisted-complex law is the Maurer--Cartan equation

\[
 \boxed{D^2=0,}
\tag{3}
\]

equivalently

\[
 \sum_{r+s=m}D_rD_s=0
 \qquad(m\ge0).
\tag{4}
\]

Here `D_0^2=0` supplies ordinary local cohomology. The higher `D_r` are coherence fields, not
components of one curved differential whose cohomology has been discarded.

For each weight `n`, define the endomorphism complex

\[
 \mathcal E_n^j=
 \prod_{p,q}\operatorname{Hom}
 \left(A^{p,q},A^{p+n,q+j-n}\right),
 \qquad
 \partial f=D_0f-(-1)^jfD_0.
\tag{4a}
\]

Then `D_n in E_n^1` and the obstruction below lies in `E_n^2`.

## 3. Obstruction--Bianchi theorem

Let `n>=2`. Assume `D_0,...,D_(n-1)` satisfy `(4)` for `0<=m<n`. The weight-one identity
`D_0D_1+D_1D_0=0` is therefore already assumed. Define the weight-`n` obstruction

\[
 \mathcal O_n=
 \sum_{\substack{r+s=n\\1\le r,s\le n-1}}D_rD_s.
\tag{5}
\]

### Theorem 3.1

1. `D_0 O_n=O_n D_0`; hence `O_n` is closed in `E_n^2`.
2. A map `D_n` of bidegree `(n,1-n)` extends `(4)` through weight `n` exactly when

   \[
   [\mathcal O_n]=0
   \tag{6}
   \]

   in `H^2(E_n,partial)`.
3. The first two obstructions are

   \[
   \mathcal O_2=D_1^2,
   \qquad
   \mathcal O_3=D_1D_2+D_2D_1.
   \tag{7}
   \]

Thus `O_2` is the first curvature/extension obstruction; its closedness is the corresponding
Bianchi identity; a choice of `D_2` is its nullhomotopy; and `O_3` is the secondary coherence
obstruction rather than an automatically canonical second Bianchi invariant.

### Proof

Let `t` be central of degree zero and work coefficientwise in `End(A)[t]`. Put

\[
 E(t)=\sum_{r<n}D_rt^r.
\]

The lower identities give the congruence

\[
 E(t)^2\equiv t^n\mathcal O_n\pmod {t^{n+1}}.
\tag{8}
\]

Associativity `E(E^2)=(E^2)E` and comparison of the `t^n` coefficient yield
`D_0O_n=O_nD_0`, proving closedness. Adding `D_nt^n` changes the weight-`n` coefficient of the
square to

\[
 \mathcal O_n+D_0D_n+D_nD_0.
\tag{9}
\]

It vanishes exactly when `O_n` is a coboundary in the endomorphism complex. Formula `(7)` is
direct substitution in `(5)`. QED.

### Indeterminacy

`O_n` is canonical only after the partial data `D_0,...,D_(n-1)` have been fixed. Changing a lower
nullhomotopy changes later obstructions. For example replacing `D_2` by `D_2+Z`, with
`partial Z=0`, changes

\[
 \mathcal O_3\longmapsto
 \mathcal O_3+D_1Z+ZD_1.
\tag{9a}
\]

Higher obstruction classes therefore carry Massey-type indeterminacy. Strict filtered
isomorphisms transport the tower by conjugation; general gauge or Morita invariance is not proved.

## 4. Amplitude/completion theorem

Assume

\[
 A^{p,q}=0\qquad\text{outside }a\le q\le b.
\tag{10}
\]

### Theorem 4.1

Put `w=b-a`.

1. `D_r=0` for every `r>w+1`.
2. `O_n=0` for every `n>2w+2`. For `w+1<n<=2w+2`, a nonzero `O_n` is terminal because the
   required `D_n` is forced to vanish.
3. For standard total degree `p+q`, only finitely many bidegrees occur in each degree; therefore

   \[
   \operatorname{Tot}_{\oplus}A
   \cong
   \operatorname{Tot}_{\prod}A.
   \tag{11}
   \]

Consequently a nonzero direct-sum/product completion boundary or coherence migrating through
arbitrarily high weights forces unbounded vertical amplitude.

### Proof

A nonzero `D_r` maps `q` to `q+1-r`. Both must lie in `[a,b]`. Taking the largest possible source
degree `q=b` gives `b+1-r>=a`, hence `r<=w+1`. Every summand of `O_n` has `r,s<=w+1`, so
`O_n=0` for `n>2w+2`; if `n>w+1`, the extension component `D_n` is zero. For fixed standard total
degree and bounded `q`, only finitely many `p` occur, so direct sum and product totalizations
coincide degreewise. QED.

This provides a precise role for HT-type growth: unbounded prolongation amplitude can make an
infinite obstruction/completion tower possible. It does not force any `O_n` to be nonzero.
The totalization statement does not exclude completion boundaries internal to individual
`A^(p,q)` or arising from a different topology/realization.

## 5. Positive strictness no-go

### Theorem 5.1

Let `H` be a finite-dimensional Hilbert space and let `T in End(H)` satisfy `T^*=-T` and
`T^2=0`. Then `T=0`.

### Proof

For every `x`,

\[
 \|Tx\|^2
 =\langle T^*Tx,x\rangle
 =\langle-T^2x,x\rangle=0.
\]

Hence `Tx=0` for every `x`. QED.

Nontrivial transport therefore cannot simultaneously be a skew-adjoint square-zero operator on one
positive Hilbert space. If one identifies `T` with a twisted-complex component, the weight grading
must first be forgotten or totalized modulo two; in an orthogonal `Z`-grading a weight `+1`
operator and its adjoint have opposite weights, so `D_1^*=-D_1` already forces zero. A survivor
needs higher homotopies, indefinite/Krein structure, or unitary phase transport whose positivity
appears only after an observer quotient.

## 6. Self-dual Tate fracture design target

The proposed higher carrier is a **self-dual Tate fracture totalization**, but this theorem does
not construct the Tate structure, self-duality, fracture diagram, or integration. A valid CMR
realization must additionally construct:

- realization maps identifying local isotropy and derived thickness with specified negative/positive
  `D_0`-cohomology groups;
- realization maps identifying curvature and admission/effectivity with selected obstruction
  classes `[O_n]`, including their lower-coherence indeterminacy;
- higher holonomy, if `(D_r)` is realized as a complete representation up to homotopy of a
  specified Lie algebroid or groupoid and integrated;
- one candidate sum/product totalization boundary,

  \[
  \operatorname{cofib}(\operatorname{Tot}_{\oplus}A
  \longrightarrow\operatorname{Tot}_{\prod}A);
  \tag{12}
  \]

- order/inertia from Witt/signature data of a separately source-derived self-duality on a genuine
  Tate object;
- an absent comparison cell is a fracture/type defect and is not renamed curvature.

This is a candidate field primitive, not constructed HGT source data. The theorem proves the
obstruction logic and one totalization boundary that such a construction may realize; it does not
identify either with a corpus invariant.

## 7. Predictions and falsifiers

1. Arbitrarily high obstruction migration implies unbounded vertical amplitude.
2. A nonzero sum/product totalization boundary cannot arise in a finite-amplitude perfect model.
3. Vanishing first curvature does not imply the higher tower or global holonomy is trivial.
4. A positive strict square-zero transport is trivial in the one-layer Hilbert model.
5. Missing typed comparisons must remain fracture defects, not fabricated zero/cofiber classes.
6. A valid field realization must place at least two nonisomorphic publication invariants in one
   `D_r` tower and predict a third invariant or vanishing not used to construct it.

## Literature boundary

The algebra is established parent mathematics: twisted complexes, representations up to homotopy,
Tate objects, and relative self-duality. Relevant interfaces:

- Arias Abad--Crainic, representations up to homotopy:
  <https://arxiv.org/abs/0901.0319>.
- Arias Abad--Schatz, integration by the `A_infinity` de Rham theorem:
  <https://arxiv.org/abs/1011.4693>.
- Higher holonomy for curved `L_infinity` algebras:
  <https://arxiv.org/abs/2408.11157>.
- Hennion, Tate objects in stable infinity-categories:
  <https://arxiv.org/abs/1606.05527>.
- Brav--Dyckerhoff, relative Calabi--Yau structures:
  <https://arxiv.org/abs/1606.00619>.

No novelty claim is made. New mathematics, if any, must be the source-canonical HGT totalization
and its cross-doctrine realization theorem.

## Gates

- [x] ordinary-one-object impossibility audit
- [x] obstruction--Bianchi theorem
- [x] amplitude/completion theorem
- [x] positive strictness no-go
- [ ] construct and type a genuine self-dual Tate fracture realization
- [ ] construct one source-canonical fracture totalization
- [ ] prove presentation invariance
- [ ] compute two publication invariants and predict a third from one obstruction tower
- [ ] formalize only after field-level target stabilizes

## Lean-return note

No Lean code was written or built. Later formalization can separate finite obstruction identities,
bounded-support totalization, and the finite-dimensional Hilbert no-go.

## Log

- 2026-08-09 — higher pivot from a defect list to one partial Maurer--Cartan obstruction tower.

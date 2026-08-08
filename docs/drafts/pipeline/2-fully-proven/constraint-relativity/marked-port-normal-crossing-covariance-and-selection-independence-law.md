# Marked-port normal-crossing covariance and selection-independence law

- **ID:** `marked-port-normal-crossing-covariance-and-selection-independence-law`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / FOUNDATIONAL NO-GO AND POSITIVE SURVIVOR
- **Status:** `[PAPER-PROVED] [MARKED-PORT NECESSITY] [FOUNDATIONAL NO-GO]`
  `[CLASSICAL ALGEBRA] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH] [NO LEAN WRITTEN]`
- **Statement:** Full support of a multi-port observer is not invariant under general linear chart
  change. Over an infinite field, exact linear symmetry group of coordinate normal-crossing
  discriminant is monomial group; for two block ports it is block-monomial group, and ordered ports
  remove permutation. Two-port diagonality and nonerasure are independent requirements. Arbitrary
  declared observer sections generate arbitrary topology, and raw nontermination is destroyed by
  contractible stabilization.
- **Parent:**
  `../../1-in-progress/constraint-relativity/constraint-relativity-curved-relative-observer-geometry.md`.

## Goal

Determine minimum additional structure required before observer-support strata, source Gauss laws,
or hypertranscendental towers can be called invariant geometry. Close exact countermodels rather
than repair vocabulary informally.

## 1. Marked-port discriminant

Let `k` be infinite field and let

\[
 V=k^n,\qquad n\ge2.
 \tag{MPN.1}
\]

Let ordered ports be coordinate projections `pi_i:V->k`, and define full-support complement and
normal-crossing discriminant

\[
 V^\times=\{v:\pi_i(v)\ne0\text{ for all }i\},
 \qquad
 \mathfrak D=V\setminus V^\times
 =\bigcup_{i=1}^nH_i,\quad H_i=\ker\pi_i.
 \tag{MPN.2}
\]

### Theorem A — exact covariance group

For `A in GL_n(k)`, following are equivalent:

1. `A(mathfrak D)=mathfrak D`;
2. `A(V^times)=V^times`;
3. `A` is monomial matrix, product of invertible diagonal matrix and permutation matrix.

If every ordered component `H_i` must be preserved individually, `A` is diagonal. If one specified
reflection may swap two ports, allowed group is diagonal torus extended by that reflection.
Equivalently,

\[
 \operatorname{Stab}(\mathfrak D)=(k^\times)^n\rtimes S_n.
 \tag{MPN.2a}
\]

If permitted port permutations form `G subset S_n`, allowed group is
`(k^times)^n semidirect-product G`.

### Proof

Let

\[
 p(x)=x_1\cdots x_n,\qquad q(x)=p(Ax).
 \tag{MPN.3}
\]

Assume `A(mathfrak D) subset mathfrak D`. For every `i`, polynomial `q` vanishes on hyperplane
`x_i=0`. Since `k` is infinite, restriction of `q` to that hyperplane is zero polynomial; hence
`x_i` divides `q`. Pairwise coprimality of variables gives `p|q`. Both are homogeneous degree `n`,
so

\[
 q=c p,\qquad c\in k^\times.
 \tag{MPN.4}
\]

Substitution by `A in GL_n(k)` is polynomial-ring automorphism, so `q ne0` and `c in k^times`.

Rows of `A` define nonzero linear factors `ell_1,...,ell_n` with

\[
 \ell_1\cdots\ell_n=cx_1\cdots x_n.
 \tag{MPN.5}
\]

Unique factorization in `k[x_1,...,x_n]` forces each `ell_i` to be scalar multiple of some
coordinate `x_j`; invertibility forces permutation of coordinates. Thus `A` is monomial. Converse
is immediate. Statements for ordered components and specified reflection follow by restricting
permutation. `[PROVED HERE]`

### Sharp counterexample to unmarked covariance

For `n=2`, vector `(1,1)` avoids axes, but shear

\[
 A(x,y)=(x-y,y)
 \tag{MPN.6}
\]

sends it to `(0,1)`. Hence axis avoidance is not invariant under full `GL_2(k)`. Any RH-bearing
two-orientation criterion must retain two fixed ideals/ports and restrict gauge accordingly.

### Theorem A' — exact block-port covariance group

Let `W` be nonzero vector space and

\[
 D_W=(W\oplus0)\cup(0\oplus W)\subset W\oplus W.
 \tag{MPN.6a}
\]

Then

\[
 \boxed{
 \operatorname{Stab}_{\operatorname{GL}(W\oplus W)}(D_W)
 \cong(\operatorname{GL}(W)\times\operatorname{GL}(W))\rtimes C_2.}
 \tag{MPN.6b}
\]

If two ports are ordered, stabilizer is block-diagonal
`GL(W) times GL(W)`; declared reflection supplies `C_2` swap.

### Proof

Let `L_+=W direct-sum 0` and `L_-=0 direct-sum W`. If subspace `S` is contained in
`L_+ union L_-`, then `S` is contained in one component: otherwise choose
`x in S intersection (L_- setminus L_+)` and `y in S intersection (L_+ setminus L_-)`; then
`x+y` lies in neither component, contradiction. For `A` preserving `D_W`, each `A(L_+)` and
`A(L_-)` is therefore contained in one component. Invertibility and equal dimensions force
permutation of components. Component restrictions are arbitrary invertible maps `W->W`.
Conversely every block-diagonal map and block swap preserves `D_W`. `[PROVED HERE]`

## 2. Selection requires two independent laws

For doubled observer `s=(s_+,s_-) in W direct-sum W`, define

\[
 \beta(s)=s_+-s_-.
 \tag{MPN.7}
\]

### Theorem B — diagonality is not nonerasure

Neither of following implies other data needed for full support:

1. `beta(s)=0` does not imply `s` avoids discriminant, since `s=(0,0)`;
2. `s ne0` does not imply full support, since `s=(w,0)` for `w ne0`;
3. `beta(s)=0` together with `s ne0` does imply full support, because then
   `s=(w,w)` with `w ne0`.

All statements are direct. `[PROVED HERE]`

Thus a valid two-port selection theorem needs logically distinct outputs:

\[
 \boxed{s_+=s_-}
 \qquad\text{and}\qquad
 \boxed{s\ne0}.
 \tag{MPN.8}
\]

After first box, second is equivalent to common value being nonzero.

In Route R, flux/Gauss relation can at most supply first box unless separate source charge or index
proves nonerasure. Origin avoidance from explicit physical construction supplies second ingredient
only after that construction is admitted; abstract duality does not.

### Literal Route-R corollary

Let `W=C^P/ell1`, let `c_rho ne 0`, and for `|t|<1` put

\[
 s_t=(c_\rho[F_{-t}],c_\rho[F_t])\in W\oplus W.
 \tag{MPN.8a}
\]

Using proved summability law `[F_u]=0 iff u<0`:

1. `s_t ne0` for every `|t|<1`;
2. `s_t` has full block-port support iff `t=0`;
3. `beta(s_t)=0` iff `t=0`.

Indeed, for `t>0` exactly first coordinate vanishes; for `t<0` exactly second vanishes; for `t=0`
both coordinates equal nonzero `c_rho[F_0]`. `[PROVED HERE FROM PAPER-PROVED SUMMABILITY INPUT]`

## 3. Static non-descent is not curvature

Let `C` be nonzero vector space, `X=0`, and `f:C->X` zero. Then

\[
 \ker f=C,qquad
 \operatorname{coker}[\operatorname{Hom}(X,W)\to\operatorname{Hom}(C,W)]
 =\operatorname{Hom}(C,W).
 \tag{MPN.9}
\]

There is no parameter space, loop, transport, or nonzero square of differential. Therefore observer
non-descent can be nonzero while every reporter/transport curvature is absent. It is a static
factorization obstruction, not curvature without further transgression map. `[PROVED HERE]`

## 4. Arbitrary-section topology no-go

Let `B` be any set and `Z subset B`. Take one-dimensional value `V_b=k` and section

\[
 \sigma_b=
 \begin{cases}
 0,&b\in Z,\\
 1,&b\notin Z.
 \end{cases}
 \tag{MPN.10}
\]

Then `Z={b:sigma_b=0}`. Hence allowing arbitrary declared sections makes every subset a zero locus
and can generate arbitrary topology, including discrete topology. `[PROVED HERE]`

Design constraint: observer horizon should be rank/Fitting degeneracy of coherent, source-derived,
finitely generated constitutive map. This card proves arbitrary-section no-go, not existence of such
coherent map.

## 5. Presentation nontermination no-go

Let `C` be bounded finite-dimensional complex and let every `K_i` be two-term contractible complex
`0 -> k ->^(id) k -> 0` in fixed degrees. Tower

\[
 C_n=C\oplus K_1\oplus\cdots\oplus K_n
 \tag{MPN.11}
\]

has strictly increasing graded dimension and hence never stabilizes as literal presentations, while
every `C_n` is quasi-isomorphic to `C`. Therefore raw tower nontermination is not invariant.
`[PROVED HERE]`

Positive survivor: any HT law geometry must localize contractible stabilization and redundant
presentation, then impose source-minimal observer class. Candidate carrier is pro-derived/persistence
object, not raw tower length.

## 6. Consequences for Constraint Relativity

Any non-theatrical field must include at least:

1. marked port flag/normal-crossing divisor and restricted gauge group;
2. source-derived coherent constitutive section, not arbitrary observer;
3. distinct diagonality and nonzero-charge laws;
4. typed transgression before calling static obstruction curvature;
5. Morita/quasi/pro invariance before calling presentation depth geometry.

These conditions are necessary, not sufficient. They do not construct source selector or prove RH.

## 7. Novelty and collision boundary

Monomial stabilizer of coordinate hyperplane arrangement, zero-vector countermodel, arbitrary
zero-locus construction, and contractible stabilization are classical. Candidate new-to-corpus
content is exact use of these results to delimit RH observer-discriminant geometry and force two
separate field equations. No external priority claim.

## Lean-return note

No Lean code was written or built. If later formalized, Theorem A can be reduced to polynomial
divisibility/unique factorization or finite hyperplane permutation; Theorems B--D are elementary.
Formalization is low priority until source-derived constitutive section exists.

## Gates

- [x] exact port-covariance group
- [x] diagonality/nonerasure independence
- [x] static-obstruction countermodel
- [x] arbitrary-topology countermodel
- [x] presentation nontermination countermodel
- [x] independent hostile audit
- [ ] literal Route-R marked constitutive map
- [ ] cross-route transgression theorem

## Log

- 2026-08-08 — hostile field audit forced marked-port covariance and two-law selection split;
  dependency-closed paper proofs recorded.
- 2026-08-08 — hostile repair added exact block-port stabilizer, literal Route-R corollary, and
  finite-dimensional contractible-stabilization quantifiers.

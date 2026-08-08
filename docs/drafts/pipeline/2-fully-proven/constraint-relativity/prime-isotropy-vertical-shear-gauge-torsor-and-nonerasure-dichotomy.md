# Prime-isotropy vertical-shear gauge torsor and nonerasure dichotomy

- **ID:** `prime-isotropy-vertical-shear-gauge-torsor-and-nonerasure-dichotomy`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / CONSTITUTIVE-RIGIDITY CLASSIFICATION
- **Status:** `[PAPER-PROVED] [LITERAL ROUTE-R SOURCE] [COORDINATE-FIXING VERTICAL GAUGE GROUP]`
  `[STOKES TORSOR] [NONERASURE DICHOTOMY] [FOURIER ACTION MISSING]`
  `[NEW-TO-CORPUS BRIDGE] [NOVELTY UNVERIFIED] [NOT RH] [NO LEAN WRITTEN]`
- **Statement:** Literal prime-isotropy complex has full coordinate-fixing vertical shear subgroup
  isomorphic to algebraic dual of source coinvariants. It acts simply transitively on Stokes
  primitives. Treating shears as gauge forces every invariant observer to erase retained class;
  marking a splitting avoids erasure but leaves arbitrary target coefficient. Constitutive rigidity
  is fixed-point problem for ambiguity representation, not consequence of abstract naturality.
- **Parents:**
  `rational-adelic-h1-observer-coefficient-freedom-and-discriminant-law.md`,
  `two-endpoint-prime-orbit-stokes-moduli-and-infinite-coinvariant-law.md`.

## 1. Literal complex and notation

Fix ordinary prime `p`. Let `A` be actual rational-adelic Bruhat core and

\[
 T=\alpha_p-1,
 \qquad
 \varepsilon=\varepsilon_0,
 \qquad
 h=\varepsilon_1.
 \tag{VSG.1}
\]

Literal complex is

\[
 C_p^0=A,
 \qquad C_p^1=A\oplus\mathbb C,
 \qquad C_p^2=\mathbb C,
 \tag{VSG.2}
\]

\[
 D_0x=(Tx,\varepsilon x),
 \qquad
 D_1(y,z)=\varepsilon y.
 \tag{VSG.3}
\]

Corpus proves

\[
 \varepsilon T=0,
 \qquad
 hT=0,
 \tag{VSG.4}
\]

and retained cocycle is `eta=(0,1)`.

All vector spaces and duals are algebraic over `C`; in particular `A^*=Hom_C(A,C)`.

## 2. Full vertical gauge group

Let `G_p^vert` be subgroup of complex-linear cochain automorphisms fixing degrees zero and two,
fixing `eta`, and fixing first projection `A direct-sum C -> A` in degree one. “Full vertical gauge
group” means full subgroup subject to these coordinate conditions, not full automorphism group of
`C_p^bullet`.

### Theorem A

\[
 \boxed{
 \mathcal G_p^{\mathrm{vert}}
 \cong\operatorname{Ann}(\operatorname{im}T)
 \cong(A/\operatorname{im}T)^*}
 \tag{VSG.5}
\]

as additive groups. Functional `ell` with `ell T=0` acts by

\[
 G_\ell^0=\operatorname{id},
 \qquad
 G_\ell^1(y,z)=(y,z+\ell(y)),
 \qquad
 G_\ell^2=\operatorname{id}.
 \tag{VSG.6}
\]

### Proof

Since `ell T=0`,

\[
 G_\ell^1D_0x=(Tx,\varepsilon x+\ell(Tx))=D_0x,
 \]

and `D_1G_ell^1(y,z)=epsilon y=D_1(y,z)`. Inverse is `G_(-ell)` and `G_ell eta=eta`.

Conversely, if `U` satisfies coordinate conditions, then

\[
 U^1(y,z)=(y,a(y)+bz)
\]

for unique `a in A^*`, `b in C`. Since `U^1(0,1)=(0,1)`, `b=1`. Equation
`U^1D_0=D_0U^0=D_0` gives `a(Tx)=0` for every `x`. Conversely every such `a` defines `G_a`, whose
inverse is `G_(-a)`. Composition satisfies `G_aG_b=G_(a+b)`. Pullback along quotient map identifies
`(A/im T)^*` with `Ann(im T)`. `[PROVED HERE]`

## 3. Stokes primitives are gauge torsor

Let

\[
 \mathscr P_p=\{R\in A^*:RT=\varepsilon\}.
 \tag{VSG.7}
\]

Explicit bilateral orbit regulator proves nonempty.

### Theorem B

For fixed primitive `R_p`,

\[
 \boxed{
 \mathscr P_p=R_p+\operatorname{Ann}(\operatorname{im}T).}
 \tag{VSG.8}
\]

For `R in P_p`, normalized relative reader

\[
 I_R(y,z)=z-R(y),
 \qquad
 I_R(\eta)=1
 \tag{VSG.9}
\]

satisfies

\[
 I_R\circ G_\ell=I_{R-\ell}.
 \tag{VSG.10}
\]

Thus vertical group acts simply transitively on chain-level Stokes primitives. Effective
cohomological ambiguity is affine over

\[
 \boxed{
 \mathcal A_p
 =\operatorname{Ann}(\operatorname{im}T)/\mathbb C\varepsilon
 \cong Q_p^*,
 \qquad
 Q_p=\ker\varepsilon/\operatorname{im}T.}
 \tag{VSG.11}
\]

### Proof

Difference of two primitives kills `im T`, and adding any such functional preserves equation
`RT=epsilon`; this proves `(VSG.8)`. Formula `(VSG.10)` is direct substitution. Put
`B=A/im T`, and let `bar epsilon:B->C` be induced by `epsilon`. Then `Q_p=ker(bar epsilon)`.
Restriction `B^*->Q_p^*` is surjective because every algebraic functional on subspace extends to
ambient vector space. Its kernel is `C bar epsilon`: if `bar epsilon=0`, both are zero; otherwise
choose `b_0` with `bar epsilon(b_0)=1`, and for `L|_(Q_p)=0`,

\[
 L(b)=L(b_0)\bar\varepsilon(b).
\]

Pullback along `A->B` identifies `B^*` with `Ann(im T)` and `C bar epsilon` with `C epsilon`.
Define additive action by `ell dot R=R-ell`; `(VSG.10)` then proves simple transitivity.
`[PROVED HERE]`

Haar endpoint defines nonzero class in `A_p`: `hT=0`, and explicit paper witness
`y in ker epsilon` has `h(y) ne0`. Since `hT=0`, restriction to `ker epsilon` descends to

\[
 \bar h:Q_p\to\mathbb C,
 \qquad \bar h([y])=h(y).
 \tag{VSG.11a}
\]

Witness gives `q_0=[y]` with `bar h(q_0) ne0`. Hence `R_p+lambda h` is nontrivial line inside full
torsor.

## 4. Known symmetries do not remove Haar shear

### Theorem C

Let `G_lambda=G_(lambda h)`.

1. It commutes with all rational scaling maps induced by `alpha_q`, because `h alpha_q=h` and
   rational scalings commute.
2. It commutes with literal anti-linear Real endpoint structure exactly when `lambda` is real.
3. It preserves strict resolved Xi comparison up to explicit cochain homotopy.

For `k in Q^x`, define rational-scaling cochain automorphism

\[
 S_k^0=\alpha_k,
 \qquad S_k^1(y,z)=(\alpha_ky,z),
 \qquad S_k^2=\operatorname{id}.
 \tag{VSG.11b}
\]

Commutativity of rational scalings, `epsilon alpha_k=epsilon`, and `h alpha_k=h` show `S_k` is a
cochain automorphism and

\[
 S_kG_{\lambda h}=G_{\lambda h}S_k.
 \tag{VSG.11c}
\]

Let `J_A` be literal Real involution and define

\[
 J^0=J_A,
 \qquad J^1(y,z)=(J_Ay,\bar z),
 \qquad J^2(w)=\bar w.
 \tag{VSG.11d}
\]

Corpus identities `J_A alpha_p=alpha_pJ_A`, `epsilon J_A=conj epsilon`, and
`hJ_A=conj h` make `J` anti-linear cochain involution, with

\[
 JG_{\lambda h}=G_{\bar\lambda h}J.
 \tag{VSG.11e}
\]

Since `h ne0`, commuting Haar-shear subgroup is exactly `lambda in R`.

### Proof of item 3

Strict comparison degree-one component is

\[
 \Phi_p^1(y,z)=z\,\delta L_p.
 \tag{VSG.12}
\]

For any `ell T=0`,

\[
 (\Phi_pG_\ell-\Phi_p)^1(y,z)=\ell(y)\delta L_p.
 \tag{VSG.13}
\]

Let `X^bullet` denote resolved target and `L_p in X^0`. Define degree-minus-one homotopy by

\[
 H^1:C_p^1\to X^0,
 \qquad H^1(y,z)=\ell(y)L_p,
 \qquad H^0:C_p^0\to X^{-1}=0,
 \qquad H^2:C_p^2\to X^1=0.
 \tag{VSG.14}
\]

Degree zero gives `H^1D_0x=ell(Tx)L_p=0`; degree one gives
`d_XH^1(y,z)=ell(y)d_XL_p`, which is `(VSG.13)`; degree two is zero. Thus

\[
 \Phi_pG_\ell-\Phi_p=\delta H+HD.
 \tag{VSG.15}
\]

Items 1--2 follow from explicit `(VSG.11b)`--`(VSG.11e)`. `[PROVED HERE FROM LITERAL CORPUS
INPUTS]`

Existing fixed-ideal/Gamma maps used here act only on target coefficients and impose no equation on
`R`. Hence those particular maps cannot distinguish `R_p` from `R_p+lambda h`. This does not
classify possible future Gamma-natural source-history arrows.

## 5. Full-gauge invariance forces erasure

### Theorem D

Let `V` be complex vector space and

\[
 P\in\operatorname{Hom}_{\mathbb C}(H^1(C_p),V)
\]

satisfy `P circ H^1(G_(lambda h))=P` for every `lambda in C`. Then

\[
 \boxed{P([\eta])=0.}
 \tag{VSG.16}
\]

### Proof

Use Stokes splitting

\[
 H^1(C_p)\cong Q_p\oplus\mathbb C\eta.
\]

Choose `q in Q_p` with `bar h(q) ne0`. Shear acts by

\[
 G_{\lambda h}(q,c)=(q,c+\lambda\bar h(q)).
\]

Gauge invariance and linearity give

\[
 0=P(q,c+\lambda\bar h(q))-P(q,c)
 =\lambda\bar h(q)P(\eta)
\]

for all `lambda`; hence `(VSG.16)`. `[PROVED HERE]`

### Constitutive-rigidity dichotomy

For physical family `P_v([x])=bar I_p([x])v`:

1. treating vertical shear as gauge forces `v=0` and erases retained class;
2. excluding shear by marking chosen Stokes splitting leaves every `v in V` possible.

Thus current source data give no nonerasing gauge-invariant constitutive observer.

## 6. Target coefficient no-go

Complex-linear natural transformations form complex vector space. Scalar multiples `c sigma` are
natural for every `c in C`; for `c in C^x`, scalar multiplication is target automorphism commuting
with stated linear Gamma transports. Therefore homogeneous linear naturality alone never selects
one nonzero target coefficient. It needs independent inhomogeneous source normalization/charge.

In literal fixed-ideal construction `P_v(eta)=v` for arbitrary `v`. Reflection/Gamma relate chosen
vectors but do not produce `v=c_rho[F_(-t)]`.

## 7. Fourier/Poisson boundary

No literal full adelic Fourier cochain automorphism

\[
 \mathcal F:C_p^\bullet\to C_{p'}^\bullet
 \tag{VSG.17}
\]

is currently constructed. Corpus has archimedean Schwartz Fourier/Poisson identities and
pure-tensor/periodic endpoint consequences, but no operator on adelic tensor prime-isotropy H1 and
ambiguity representation `A_p`. Claiming Fourier kills ambiguity now is theatre.

Even future endpoint-swapping involution need not select: it may conjugate shear to matching shear
on reflected object. Required theorem is fixed-point/holonomy classification of full source-operation
group on `A_p` plus existence of one normalized affine section.

## 8. Strongest positive survivor

`[OPEN CORE]` Conditional on constructing source-operation holonomy representation `mathsf S` on
`A_p`, constitutive rigidity becomes exact target

\[
 \boxed{\mathcal A_p^{\mathsf S}=0}
 \tag{VSG.18}
\]

together with existence of normalized affine section, an independent condition. This fixed-space
claim is not proved here because full source-operation action is not yet constructed. Known
operations leave nonzero Haar direction invariant at least over real subspace. Future rigidity claim
fails if:

1. Haar class stays fixed;
2. its orbit spans nonzero invariant subspace;
3. vertical shears transport conjugately around every new arrow;
4. target naturality remains homogeneous without source charge.

This is exact, falsifiable replacement for vague “source naturality.”

## 9. Novelty boundary

Mapping-cone shears, affine splittings, quotient duals, gauge invariants, and natural-transformation
homogeneity are classical. New-to-corpus bridge is literal Route-R classification and exact
nonerasure dichotomy. External priority unverified; no new general-theorem claim.

## Lean-return note

- No Lean code was written or built.
- Literal complex, endpoints, regulator, Real structure, and strict Xi comparison already exist.
- If later formalized, suggested file:
  `formal/GaloisForLFunctions/RHTower/CCMRationalAdelicPrimeIsotropyVerticalGauge.lean`.
- First formal theorem should classify coordinate-fixing cochain automorphisms; next prove homotopy
  `(VSG.15)`.

## Gates

- [x] full vertical group
- [x] Stokes primitive torsor
- [x] Haar shear source-symmetry compatibility
- [x] resolved-comparison homotopy
- [x] full-gauge nonerasure no-go
- [x] target homogeneous-naturality no-go
- [x] independent hostile audit
- [ ] full adelic Fourier cochain operator
- [ ] ambiguity holonomy/fixed-point classification
- [ ] independent nonzero source charge

## Log

- 2026-08-08 — exact vertical gauge/torsor classification and nonerasure dichotomy proved from
  literal source complex.
- 2026-08-08 — hostile repair closed algebraic-dual scope, coordinate-fixing subgroup, quotient-dual
  kernel, descended Haar covector, explicit scaling/Real maps, typed Xi homotopy, and invariant-reader
  hypothesis.

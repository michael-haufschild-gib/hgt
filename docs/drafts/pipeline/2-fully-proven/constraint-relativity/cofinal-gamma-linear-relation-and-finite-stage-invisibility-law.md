# Cofinal Gamma linear relation and finite-stage invisibility law

- **ID:** `cofinal-gamma-linear-relation-and-finite-stage-invisibility-law`
- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [BRIDGE] [LINREL PACKAGING] [NOVELTY UNVERIFIED] [NOT RH] [NO LEAN WRITTEN]`
- **Scope:** Algebraic fixed-summable-subspace target used by Route R; no Xi zero, divisor
  specialization, or RH
  premise.
- **Statement:** Full all-prime radial Gamma multiplier always descends as canonical linear relation
  on fixed quotient. It is a forward graph on exactly one closed half-line, an inverse graph on the
  opposite half-line, and a graph in both orientations exactly at radial center. Every finite-prime
  truncation induces diagonal relation for every radial grade. Hence two-sided cofinal descent is a
  singular relation-level event invisible at every finite stage.

## 1. Fixed summable-subspace target

Let `P` be set of ordinary primes and

\[
 S=\mathbb C^{\mathcal P},\qquad
 I=\ell^1(\mathcal P),\qquad
 V=S/I,
 \tag{CGR.1}
\]

with quotient map `q:S->V`. All vector spaces and relations are algebraic over `C`; topology enters
only through distinguished linear subspace `I`. It is not an ideal of pointwise algebra `S`.

For `t in R`, define cofinal radial multiplier

\[
 (C_ta)_p=p^{-2t}a_p.
 \tag{CGR.2}
\]

It is linear automorphism of `S` with inverse `C_(-t)`. Define canonical quotient relation

\[
 \Gamma_t=(q\oplus q)(\operatorname{graph}C_t)
 =\{(q(a),q(C_ta)):a\in S\}\subset V\oplus V.
 \tag{CGR.3}
\]

No ideal-preservation premise is required for `(CGR.3)`.

## 2. Graph criterion

### Lemma A

For any linear automorphism `C:S->S`, relation

\[
 \Gamma_C=\{(q(a),q(Ca)):a\in S\}
 \tag{CGR.4}
\]

is graph of linear map `V->V` iff `C(I) subset I`.

### Proof

Relation has full domain because `q` is surjective. It is single-valued exactly when

\[
 q(a)=q(a')\Longrightarrow q(Ca)=q(Ca').
\]

Writing `i=a-a'`, this is equivalent to `q(Ci)=0` for every `i in I`, hence to `C(I) subset I`.
When condition holds, map is `q(a) mapsto q(Ca)`. `[PROVED HERE]`

Directly `Gamma_C^(-1)=Gamma_(C^(-1))`; therefore inverse relation is graph iff
`C^(-1)(I) subset I` by same argument.

## 3. Exact radial trichotomy

### Lemma B

\[
 C_t(I)\subset I\quad\Longleftrightarrow\quad t\ge0.
 \tag{CGR.5}
\]

### Proof

If `t>=0`, weights satisfy `0<p^(-2t)<=2^(-2t)<=1`, so `C_t` is bounded multiplier of `ell1`.

If `t<0`, write `u=-t>0` and enumerate primes `p_n`. Define

\[
 b_{p_n}=\frac{p_n^{-2u}}n.
 \tag{CGR.6}
\]

Take increasing enumeration `p_n`. Since `p_n>=n+1`,

\[
 \sum_n\frac{p_n^{-2u}}n
 \le\sum_n n^{-1-2u}<\infty,
\]

so `b in I`. But

\[
 (C_tb)_{p_n}=p_n^{2u}\frac{p_n^{-2u}}n=\frac1n,
\]

which is not in `ell1`. Therefore `C_t(I) not subset I`. `[PROVED HERE]`

### Theorem C — cofinal relation trichotomy

For every `t in R`:

1. `Gamma_t` is graph of forward quotient map iff `t>=0`;
2. `Gamma_t^(-1)` is graph of quotient map iff `t<=0`;
3. both orientations are graphs iff `t=0`;
4. `Gamma_0=Delta_V`.

### Proof

Items 1 and 2 follow from Lemmas A--B and `C_t^(-1)=C_(-t)`. Both inequalities hold exactly at
`t=0`, where `C_0=id_S`. `[PROVED HERE]`

This is not RH: `t` is free radial parameter. It says only that demanding ordinary quotient maps in
both orientations would assume center before arithmetic supplies it. Relation `(CGR.3)` is correct
pre-divisor carrier away from center.

## 4. Finite-stage invisibility

For finite `K subset P`, define finite-prime multiplier

\[
 (C_{t,K}a)_p=
 \begin{cases}
 p^{-2t}a_p,&p\in K,\\
 a_p,&p\notin K.
 \end{cases}
 \tag{CGR.7}
\]

and relation `Gamma_(t,K)=(q direct-sum q)(graph C_(t,K))`.

### Theorem D

For every finite `K` and every `t in R`,

\[
 \boxed{\Gamma_{t,K}=\Delta_V.}
 \tag{CGR.8}
\]

### Proof

For every `a in S`, difference `C_(t,K)a-a` is supported on finite set `K`, hence belongs to `I`.
Thus `q(C_(t,K)a)=q(a)`, so `(CGR.8)` follows. `[PROVED HERE]`

### Corollary E — finite equalizer nonselection

Any finite-source constitutive equalizer whose target generators consist only of finite-prime
Gamma relations sees those generators as identities on `V`. If retained source class `eta` is fixed
by other declared source arrows, every assignment

\[
 P_v(\eta)=v,\qquad v\in V,
 \tag{CGR.9}
\]

that already intertwines non-Gamma arrows continues to intertwine all finite Gamma arrows. Finite
Gamma stages therefore impose no additional equation selecting `v`.

This corollary is conditional only on stated invariance of `eta` under non-Gamma generators; it
does not assert that a not-yet-defined full finite category has no other selector.

## 5. Rank transmutation into relation excess

For `t<0`, forward relation is multivalued. Its vertical fibre at zero is

\[
 M_t=\{v\in V:(0,v)\in\Gamma_t\}=q(C_tI).
 \tag{CGR.10}
\]

For `t>0`, inverse relation has vertical fibre `q(C_(-t)I)`. These excess fibres vanish precisely
on functional side of trichotomy. Thus radial crossing does not destroy cofinal information; it
moves information between map and multivalued excess. This is exact local model of constraint
relativity: obstruction changes mathematical type under observer change.

No dimension or closure claim about `M_t` is made here.

## 6. Consequences for MCTG

1. Fixed-quotient cofinal Gamma transport must be valued in linear relations, not ordinary modules
   and maps, before radial center is known.
2. Requiring two ordinary maps is circular because Theorem C makes that equivalent to `t=0`.
3. Finite stages cannot approximate selection algebraically: every finite relation is already
   diagonal, while full cofinal relation can be multivalued.
4. Any multiplicity-one theorem must use `Gamma_t` as singular generator and prove an intertwiner
   statement in `LinRel`.
5. A topology in which cofinal relation is forced as closed limit of diagonals would erase this
   singular information; such topology is a falsifier for proposed selector.

## 7. Hostile conjecture loop

1. **Full multiplier gives quotient endomorphism for every `t`.** `FALSE` by Lemma B.
2. **Use inverse orientation instead.** `FALSE AS GLOBAL REPAIR`: inverse works exactly on opposite
   half-line.
3. **Demand both orientations.** `CIRCULAR`: equivalent to `t=0`.
4. **Recover cofinal behavior from finite stages.** `FALSE ALGEBRAICALLY`: every finite relation is
   `Delta_V`.
5. **Replace map by relation.** `SURVIVES`: `(CGR.3)` exists canonically for all `t`.
6. **Relation-level multiplicity one selects arithmetic observer.** `OPEN`: requires literal source
   category and equalizer computation.

## 8. Novelty boundary

Quotient relations, graph criteria, weighted `ell1` multipliers, and finite-support invisibility are
classical ingredients. Claimed result is exact new-to-corpus coupling to Route-R cofinal Gamma
target. External novelty unverified. No RH consequence follows without source-defined constitutive
intertwiner and portwise nonerasure.

## Lean-return note

- No Lean code was written or built.
- Future formalization may use relations as submodules of `V direct-sum V`; avoid forcing quotient
  map for `t<0`.
- Suggested future file:
  `formal/GaloisForLFunctions/RHTower/RouteRCofinalGammaLinearRelation.lean`.

## Gates

- [x] dependency-closed paper proof
- [x] exact graph criterion
- [x] ideal-preservation trichotomy
- [x] finite-stage diagonal theorem
- [x] circularity boundary stated
- [ ] independent hostile audit
- [ ] external priority verification
- [ ] relation-level cofinal equalizer

## Log

- 2026-08-08 — `Mod`-valued cofinal transport rejected; canonical `LinRel` replacement and exact
  finite/cofinal discontinuity proved.

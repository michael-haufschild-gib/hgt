# Valuation-coframe operation-defect rank and determinant-line law

- **ID:** `cmr-valuation-coframe-operation-defect-rank-determinant-line`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / ROUTE-INDEPENDENT CONSTRAINT LAW
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [NOT RH]`
  `[NO SOURCE PRODUCER CLAIM] [LEAN-FORMALIZED UNCONDITIONALLY]`
- **Formalized companion:**
  `valuation-coframe-operation-defect-rank-and-determinant-line-law-formalized.md`.
- **Arithmetic instance:**
  `../constraint-relativity/prime-valuation-cyclic-coframe-and-diagonal-dagger-defect-law.md`.
- **Field successor:**
  `../../1-in-progress/constraint-motive-relativity/determinantal-constraint-holography-and-singular-reporter-correspondence-conjecture.md`.

## 1. Result in one sentence

Relative to an admitted target family of closed coframes indexed by the same `N` labels,
exactifying `N` independently coframed source classes forces the coframe-transport anomaly to have
rank `N` on their span. Its top exterior power is a canonical one-dimensional nondegenerate
shadow; it is not a rank-one linear factorization.

## 2. Setup

Let `k` be a field. Let `(C_*,d_C)` and `(E_*,d_E)` be homological chain complexes and
`T:C_* -> E_*` a chain map. Fix a degree `n`, a finite set `F`, cycles

\[
 u_p\in Z_n(C),\qquad p\in F,
\tag{VOD.1}
\]

and degree-`n` cocycles, meaning linear maps

\[
 \phi_\ell:C_n\longrightarrow k,
 \qquad \phi_\ell\circ d^C_{n+1}=0,
 \qquad \phi_\ell(u_p)=-\delta_{\ell p}.
\tag{VOD.2}
\]

Let `U_F=span_k{[u_p]:p in F} subset H_n(C)`. Suppose the target has linear maps
`hat phi_l:E_n -> k` satisfying `hat phi_l circ d^E_(n+1)=0`. Define the
coframe-transport anomaly on homology by

\[
 \mathcal A_T([x])_\ell
 :=\widehat\phi_\ell(Tx)-\phi_\ell(x),
 \qquad
 \mathcal A_T:H_n(C)\longrightarrow k^F.
\tag{VOD.3}
\]

It is well defined: for `y in C_(n+1)`, replacing `x` by `x+d^C_(n+1)y` changes the first term by
`hat phi_l(d^E_(n+1)T_(n+1)y)=0` and the second by `phi_l(d^C_(n+1)y)=0`.

## 3. Coframe rank theorem

### Theorem 3.1

Under `(VOD.1)--(VOD.3)`:

1. the classes `[u_p]`, `p in F`, are linearly independent;
2. if `T_*[u_p]=0` for every `p in F`, then

   \[
   \mathcal A_T([u_p])=e_p,
   \qquad
   \mathcal A_T|_{U_F}:U_F\xrightarrow{\sim}k^F;
   \tag{VOD.4}
   \]
3. consequently `rank(A_T|U_F)=|F|`;
4. if `A_T|U_F` factors through a vector space `P` of dimension `r`, exactification of all
   `[u_p]` forces `|F|<=r`.

#### Proof

If `sum_p a_p[u_p]=0`, then `sum_p a_pu_p=d_Cy`. Applying `phi_l` gives
`-a_l=0`; hence all coefficients vanish. This proves independence.

If `T_*[u_p]=0`, write `Tu_p=d_Ev_p`. Closedness of `hat phi_l` gives
`hat phi_l(Tu_p)=0`, while `(VOD.2)` gives `phi_l(u_p)=-delta_lp`. Therefore

\[
 \mathcal A_T([u_p])_\ell=0-(-\delta_{\ell p})=\delta_{\ell p}.
\]

This is `(VOD.4)`. Its matrix in the displayed source and target bases is the identity, so it has
rank `|F|`. A factorization `U_F -> P -> k^F` has rank at most `dim P=r`; hence `|F|<=r`.
QED.

### Corollary 3.2 — one-port impossibility

For `|F|>=2`, no anomaly factoring through one scalar line can exactify every independently
coframed class in `U_F`.

This does not say a scalar observer cannot detect a wall. It says a scalar observer cannot be the
raw coefficient-faithful exactification mechanism for those classes.

## 4. Coframe preservation and composition

### Theorem 4.1 — preservation implies nonerasure

If `T^*hat phi_l=phi_l` for every `l in F`, then `A_T=0`, and `T_*|U_F` is injective.

#### Proof

The equality of cochains makes every component of `(VOD.3)` zero. If
`T_*(sum a_p[u_p])=0`, apply `hat phi_l` to a target boundary representative. It gives zero. Pulling
back gives

\[
 0=\phi_\ell\!\left(\sum_pa_pu_p\right)=-a_\ell.
\]

Thus every `a_l=0`. QED.

### Theorem 4.2 — anomaly cocycle

Let `C --T--> E --S--> G` be chain maps, with source, intermediate, and target closed coframes
`phi`, `hat phi`, and `tilde phi`. Then

\[
 \mathcal A_{S T}=\mathcal A_T+T^*\mathcal A_S,
\tag{VOD.5}
\]

where `(T^*A_S)([x])=A_S(T_*[x])`.

#### Proof

For every cycle `x`, insert and subtract `hat phi_l(Tx)`:

\[
 \widetilde\phi_\ell(STx)-\phi_\ell(x)
 =\bigl(\widetilde\phi_\ell(STx)-\widehat\phi_\ell(Tx)\bigr)
 +\bigl(\widehat\phi_\ell(Tx)-\phi_\ell(x)\bigr).
\]

The two terms are respectively `(T^*A_S)([x])_l` and `A_T([x])_l`. QED.

This is a genuine transport law. It is not called curvature unless the maps arise as two sides of
a represented comparison square.

## 5. Determinant-line positive survivor

Let

\[
 \det(U_F):=\bigwedge^{|F|}U_F,
 \qquad
 \det(k^F):=\bigwedge^{|F|}k^F.
\]

### Theorem 5.1

Under the exactification hypothesis of Theorem 3.1, the top exterior map

\[
 \det(\mathcal A_T|_{U_F})
 :=\bigwedge^{|F|}(\mathcal A_T|_{U_F}):
 \det(U_F)\xrightarrow{\sim}\det(k^F)
\tag{VOD.6}
\]

is an isomorphism. After choosing an ordering of `F` and using that same ordering for the
generators `([u_p])_(p in F)` and coframe basis `(e_p)_(p in F)`, its scalar is `1`.

#### Proof

The matrix of `A_T|U_F` is the identity by `(VOD.4)`. The top exterior power of an isomorphism is
an isomorphism, and the determinant of the identity is `1`. QED.

### Interpretation boundary

`(VOD.6)` is the exact positive survivor of the rank-one no-go:

- a full-rank anomaly cannot pass faithfully through a one-dimensional **linear** port;
- its top exterior power is nevertheless a one-dimensional **determinant** port retaining a
  nonzero determinant pairing, with a scalar trivialization only after matched ordered bases.

Without matched ordered bases, `(VOD.6)` is an isomorphism of determinant lines, not a preferred
number. Under aperture enlargement the exterior degree changes. This theorem constructs no
canonical cofinal line, determinant gerbe, or Tate polarization.

## 6. Algebra-map derivation defect

Let `A,B` be unital `k`-algebras with `k`-linear traces `tau_A,tau_B`, `k`-linear derivations
`D_l^A,D_l^B`, and a trace-preserving unital algebra homomorphism `f:A->B`. Define the
trace--derivation Hochschild one-cochains

\[
 \phi_\ell^A(a,b)=\tau_A(aD_\ell^A b),
 \qquad
 \phi_\ell^B(c,d)=\tau_B(cD_\ell^B d),
\tag{VOD.7}
\].

If additionally `tau_A circ D_l^A=0` and `tau_B circ D_l^B=0`, these cochains are
antisymmetric. Indeed,

\[
 \phi_\ell(a,b)+\phi_\ell(b,a)
 =\tau(aDb)+\tau((Da)b)
 =\tau(D(ab))=0,
\]

using traciality and Leibniz. Hence they kill the signed cyclic relations.

Define the derivation-transport defect

\[
 Q_{\ell,f}:=D_\ell^Bf-fD_\ell^A:A\longrightarrow B.
\tag{VOD.8}
\]

### Proposition 6.1

For all `a,b in A`,

\[
 (f^*\phi_\ell^B-\phi_\ell^A)(a,b)
 =\tau_B\bigl(f(a)Q_{\ell,f}(b)\bigr).
\tag{VOD.9}
\]

#### Proof

Trace preservation and multiplicativity give

\[
 \begin{aligned}
 (f^*\phi_\ell^B)(a,b)-\phi_\ell^A(a,b)
 &=\tau_B(f(a)D_\ell^Bf(b))-\tau_B(f(a)f(D_\ell^A b))\\
 &=\tau_B(f(a)(D_\ell^Bf-fD_\ell^A)(b)).
 \end{aligned}
\]

QED.

Whenever these cochains instantiate Theorem 4.1 on a bar or presentation complex and `f` induces
the corresponding chain map, `(VOD.9)` identifies its coframe anomaly. Under those hypotheses,
`Q_(l,f)=0` for every `l` implies coframe preservation and hence nonerasure on the independently
detected prime span.

## 7. Exact split countermodel: the Arakelov graph

Let `F` be finite, `D=k^F`, and fix nonzero weights `lambda_p` (in the arithmetic model `k=R` and
`lambda_p=Real.log p`). Define

\[
 L:D\longrightarrow k,
 \qquad L(d)=\sum_{p\in F}\lambda_pd_p,
\]

and the graph inclusion

\[
 B:D\longrightarrow D\oplus k,
 \qquad B(d)=(d,-L(d)).
\tag{VOD.10}
\]

Define

\[
 \operatorname{Tr}:D\oplus k\longrightarrow k,
 \qquad \operatorname{Tr}(d,x)=L(d)+x.
\tag{VOD.10a}
\]

View all three spaces as complexes concentrated in degree zero. The sequence

\[
 0\longrightarrow D\xrightarrow{B}D\oplus k
 \xrightarrow{\operatorname{Tr}}k\longrightarrow0
\tag{VOD.10b}
\]

is exact: `Tr B=0`; its kernel consists of `(d,-L(d))`; and `Tr` is split by
`s(x)=(0,x)`. Let `pi:D direct-sum k -> D` be projection. Then `pi B=id_D`, so `B` is split
injective. Every
coordinate reporter `epsilon_p(d)=d_p` extends to `hat epsilon_p(d,x)=d_p`; hence

\[
 B^*\widehat\epsilon_p=\epsilon_p,
 \qquad \mathcal A_B=0.
\tag{VOD.11}
\]

Therefore the extension class and its connecting morphisms vanish, and adjoining the common
infinity coordinate `-sum d_p Real.log p` in the real arithmetic specialization creates no
coframe anomaly or exactification. A
prime--infinity graph is not a source event merely because it couples every prime to one line.

## 8. Literal arithmetic calibration

Let `V=C_1(A)`, let `tau_cyc:C_1(A)->C_1(A)` be degree-one cyclic reversal, and let
`b_2:C_2(A)->C_1(A)` be the Hochschild boundary. Put

\[
 R=\operatorname{im}(\tau_{\rm cyc}+1)+\operatorname{im}(b_2)\subset V.
\]

Form the presentation complex

\[
 C^{\rm pres}_1=R\xrightarrow{\iota}C^{\rm pres}_0=V,
\tag{VOD.12}
\]

with all other terms zero. Then `H_0(C^pres)=V/R=mathscr H`. Every `u_p in V` is a degree-zero cycle,
and each valuation functional is a closed degree-zero cochain because it annihilates `R`. The
parent theorem gives

\[
 \phi_\ell([u_p])=-\delta_{\ell p}.
\tag{VOD.13}
\]

Therefore Theorems 3.1--5.1 apply at `n=0` to any proposed chain map out of this presentation
complex equipped with admitted target coframes. This does not assert that the raw tensor is a
Hochschild one-cycle or defines an `HH_1` class. The established scalar Kummer cocycle is a contraction
`sum_l(log l)phi_l`; it does not replace the full coframe.

This calibration proves:

1. any such chain-map enlargement preserving the full closed valuation coframe cannot kill a
   nonzero finite prime combination;
2. if such a chain map kills all `N` aperture classes, its mismatch against any admitted target
   coframe family has rank `N`;
3. no scalar linear port factors that raw anomaly for `N>=2`. The determinant is one canonical
   later exterior shadow; the theorem does not identify it with a Stokes/Fredholm port.

It does not construct that correspondence and does not prove any prime class null-homologous.

## 9. Hostile conjecture loops

1. **One infinity line can absorb all prime classes.** False for `N>=2` by Corollary 3.2.
2. **The weighted Arakelov sum supplies the missing anomaly.** False by the split graph
   `(VOD.10)--(VOD.11)`.
3. **Preserve every valuation coframe and still exactify the prime span.** False by Theorem 4.1.
4. **The determinant is automatically a scalar.** False without two determinant-line
   trivializations.
5. **Finite determinants stabilize cofinally.** Not proved and generally false without
   polarization/lattice transition data.
6. **Rank theorem proves RH.** False: it is a necessary constraint on a missing source operation,
   not its construction.

## 10. Scope and formalization note

Theorems 3.1--5.1 are elementary homological linear algebra; Proposition 6.1 is elementary
trace--derivation algebra. Their significance here is the exact restriction they impose on any
route-spanning source event. The field-level claim that a cofinal
determinant object unifies Fredholm, Stokes, epsilon, positivity, and recurrence remains Stage 1.

The generic rank theorem is now formalized independently of any source instantiation; see the
formalized companion.

## Gates

- [x] anomaly typed on homology
- [x] finite coframe independence proved
- [x] exactification rank lower bound proved
- [x] finite-port factorization bound proved
- [x] preservation/injectivity law proved
- [x] composition cocycle proved
- [x] determinant-line survivor proved without scalar overclaim
- [x] derivation-intertwining formula proved
- [x] Arakelov split countermodel proved
- [x] literal source applicability and RH boundary stated
- [x] Lean formalization complete and unconditional

## Log

- 2026-08-11 — unconditionally formalized in Lean 4 and promoted to `3-formalized`.
- 2026-08-09 — proved after hostile audit of all pre-Xi Fourier, Poisson, Gamma, Cartier,
  Bockstein, and prime--infinity candidates found no existing non-diagonal source event. The rank
  theorem replaces “find another scalar source selector” by a full reporter-anomaly requirement.

# Observer curvature, false flatness, and serial irreversibility law

- **ID:** `nhg-observer-curvature-false-flatness`
- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [UNIVERSAL FIELD THEOREM] [OBSERVER FUNCTORIALITY]`
  `[FALSE FLATNESS CLASSIFIED] [SERIAL IRREVERSIBILITY] [PARALLEL REPAIR]`
  `[NO ROUTE INPUT] [NOT RH] [NO LEAN WRITTEN OR BUILT]`

## 1. Structured observer

Let `L` and `L'` be finite-dimensional nilpotent nonpositive `L_infinity` algebras, and let

\[
 \Phi:L\longrightarrow L'
\tag{OC.1}
\]

be a strict filtered `L_infinity` morphism. Work over the same smooth base `M`, and assume `Phi`
intertwines the total law connections and the induced flat internal-homology connections. Thus

\[
 a'=\Phi a,
 \qquad
 \operatorname{Curv}(a')=\Phi\operatorname{Curv}(a).
\tag{OC.2}
\]

Let `P_n(a)` and `Ob_(n+1)(a)` be the partial-flattening spaces and curvature obstruction spectra
from the secondary-curvature law. Write

\[
 \Phi_{H,*}:
 H^{n+1}_{\mathrm{dR}}(M;\mathcal H_{1-n}(L))
 \longrightarrow
 H^{n+1}_{\mathrm{dR}}(M;\mathcal H_{1-n}(L'))
\tag{OC.3}
\]

for the induced cohomology map.

## 2. Functoriality of the full curvature tower

### Theorem 2.1

For every `n`:

1. `beta mapsto Phi beta` defines a map

   \[
   \Phi_n:P_n(a)\longrightarrow P_n(a');
   \tag{OC.4}
   \]

2. every next obstruction satisfies

   \[
   \boxed{
   o_{n+1}(\Phi\beta)=\Phi_{H,*}o_{n+1}(\beta);}
   \tag{OC.5}
   \]

3. consequently

   \[
   \boxed{
   \Phi_{H,*}\operatorname{Ob}_{n+1}(a)
   \subseteq\operatorname{Ob}_{n+1}(a').}
   \tag{OC.6}
   \]

### Proof

Strictness gives

\[
 \operatorname{Curv}(\Phi(a+\beta))
 =\Phi\operatorname{Curv}(a+\beta).
\tag{OC.7}
\]

Hence curvature vanishing through degree `n` is preserved, proving `(OC.4)`. Taking the degree
`n+1` component, passing to internal homology, and then to twisted de Rham cohomology proves
`(OC.5)`. Taking the image over every `beta in P_n(a)` proves `(OC.6)`. QED.

Equality in `(OC.6)` need not hold. The target can possess flattening branches not induced by any
source correction.

## 3. False-flatness classification

Fix `beta in P_n(a)`.

### Definition 3.1

The observer has **class erasure at `(beta,n+1)`** when

\[
 o_{n+1}(\beta)\neq0,
 \qquad
 \Phi_{H,*}o_{n+1}(\beta)=0.
\tag{OC.8}
\]

It has **flattening non-effectivity through degree `n`** when a target partial flattening in
`P_n(a')` has no lift, even up to the declared homotopy, from `P_n(a)`.

### Theorem 3.2 — the two false-flatness mechanisms

1. Class erasure makes the pushed source branch falsely extendible:

   \[
   o_{n+1}(\beta)\neq0,
   \quad
   o_{n+1}(\Phi\beta)=0.
   \tag{OC.9}
   \]

2. Suppose:
   - `Phi_(H,*)` reflects zero on every obstruction represented by `P_n(a)`; and
   - every target branch `beta' in P_n(a')` with `o_(n+1)(beta')=0` lifts to a source branch up to
     the declared homotopy.

   Then

   \[
   \boxed{
   P_{n+1}(a')\neq\varnothing
   \quad\Longrightarrow\quad
   P_{n+1}(a)\neq\varnothing.}
   \tag{OC.10}
   \]

Therefore, among represented strict observer morphisms, false flatness is caused exactly by
cohomological class erasure or failure of effective lifting of flattening branches.

### Proof

Part 1 is `(OC.5)` plus the recursive extension theorem. For Part 2, target extendibility gives a
target branch with zero obstruction. Lift it to `beta in P_n(a)`. Naturality makes the source
obstruction map to zero; zero reflection makes the source obstruction zero; the recursive extension
theorem then gives a source extension. QED.

An absent observer morphism, a nonclosed domain, or a topology mismatch is not class erasure. Those
remain admission/type defects until a structured morphism such as `(OC.1)` exists.

## 4. Serial irreversibility

Let

\[
 L\xrightarrow{\Phi}L'\xrightarrow{\Psi}L''
\tag{OC.11}
\]

be strict structured observers.

### Corollary 4.1

If `Phi` erases an obstruction class, every later observer erases it:

\[
 \Phi_{H,*}o=0
 \quad\Longrightarrow\quad
 (\Psi\Phi)_{H,*}o=0.
\tag{OC.12}
\]

No serial post-processing can reconstruct a curvature class already sent to zero. Likewise, a
source flattening branch absent from the image of `Phi_n` cannot be manufactured as a lifted source
branch by composing with `Psi`.

### Proof

Equation `(OC.12)` is functoriality of cohomology. The branch statement is functoriality of images.
QED.

## 5. Parallel observer repair

Let `Phi_i:L->L_i` be a finite family of strict observers and let `Phi=(Phi_i)` be their product.

### Corollary 5.1

For every represented obstruction class `o`,

\[
 \boxed{
 \Phi_{H,*}o=0
 \quad\Longleftrightarrow\quad
 o\in\bigcap_i\ker(\Phi_{i,H,*}).}
\tag{OC.13}
\]

Thus parallel observers jointly repair class erasure on a subspace `W` exactly when

\[
 W\cap\bigcap_i\ker(\Phi_{i,H,*})=0.
\tag{OC.14}
\]

This repairs only cohomological detection. Effective lifting of partial-flattening branches remains
a separate descent condition.

### Corollary 5.2 — finite observer curvature horizon

Let

\[
 W_{n+1}=\operatorname{span}\operatorname{Ob}_{n+1}(a)
\tag{OC.15}
\]

be finite-dimensional, and suppose the total observer cohomology available in degree `n+1` has
dimension at most `d`. If

\[
 \dim W_{n+1}>d,
\tag{OC.16}
\]

then the parallel observer family has a nonzero kernel on the curvature span. In particular, if
`dim W_n` is unbounded with `n`, no fixed finite-rank observer family separates every curvature
layer.

### Proof

Restrict the joint cohomology map to `W_(n+1)` and apply rank--nullity. QED.

## 6. Exact countermodel

Use the two-step nilpotent graded Lie algebra and law connection from Counterexample 4.2 of the
secondary-curvature card:

\[
 [x,x]=v,
 \qquad
 \mathfrak o_4(a)
 =[\omega_1\wedge\omega_2\,v]\neq0.
\tag{OC.17}
\]

Let `L'=L/(v)`. The quotient is a strict `L_infinity` observer and

\[
 \Phi_{H,*}\mathfrak o_4(a)=0.
\tag{OC.18}
\]

The source connection is obstructed at degree four while its observer image is flat. This is false
flatness by exact class erasure, with no analytic, topological, or global-monodromy ambiguity.

## 7. Field consequences

1. Two proof presentations are local gauges only if they induce equivalences of partial-flattening
   spaces and their obstruction spectra, not merely equal scalar invariants.
2. Every represented no-go that kills curvature factors through a specific cohomology kernel or a
   failure of effective lifting. Other no-gos must retain their own type.
3. Observer completeness is page-dependent. First-order tangent faithfulness does not imply
   curvature-tower faithfulness.
4. Serial reduction is irreversible; parallel reduction can be jointly conservative.
5. A valid NHG atlas must record both obstruction-class maps and flattening descent. Recording only
   one loses information.

## 8. Scope

- Strict `L_infinity` morphisms are used for the exact theorem. General infinity morphisms require
  their coherent Maurer--Cartan pushforward and homotopy-level partial-flattening spaces.
- The result concerns represented observer morphisms. Missing maps, nonclosability, and completion
  changes are not silently converted into zero curvature.
- Zero reflection on cohomology does not imply effective lifting.
- No positivity, properness, source selection, global holonomy, physical dynamics, or RH statement
  follows.

# Arithmetic endpoints and relative middle reduction

- **ID:** `deninger-arithmetic-endpoint-relative-middle-reduction`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_ARITHMETIC_ENDPOINT_RELATIVE_MIDDLE_REDUCTION`
- **Parent:** `deninger-true-to-approximate-derived-coefficient`
- **Statement:** the rational Milnor--Arakelov core supplies exactly
  Deninger's degrees zero and two; every nontrivial middle class lies
  in the canonical relative analytic cone.

## Algebraic endpoint complex

For a number field \(K\), put
\[
 P_K=(K^\times/\mu_K)\otimes_{\mathbb Z}\mathbb R
\]
and let
\[
 D_K=\operatorname{Div}_{\mathrm{Ar}}(K)_{\mathbb R}
\]
be the real Arakelov divisor space, with principal-divisor map
\(\operatorname{pr}:P_K\to D_K\).  Define
\[
 C_{\mathrm{end}}(K)
 =
 \mathbb R[0]\oplus
 \left[
   P_K\xrightarrow{\operatorname{pr}}D_K
 \right]_{[1,2]}.                                                   \tag{1}
\]

`DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT` proves the exact sequence
\[
 0\longrightarrow P_K
 \xrightarrow{\operatorname{pr}}D_K
 \xrightarrow{\deg}\mathbb R(-1)
 \longrightarrow0.                                                 \tag{2}
\]

## Theorem

`[PROVED HERE] [DAC_ARITHMETIC_ENDPOINT_RELATIVE_MIDDLE_REDUCTION]`

1. The cohomology of `(1)` is
   \[
   H^i(C_{\mathrm{end}}(K))
   =
   \begin{cases}
     \mathbb R,&i=0,\\
     0,&i=1,\\
     \mathbb R(-1),&i=2,\\
     0,&\text{otherwise}.
   \end{cases}                                                       \tag{3}
   \]
2. For \(K=\mathbb Q\), `(1)` is the real realization of the
   rational Milnor generic/finite localization core:
   degree one is
   \((\mathbb Q^\times/\{\pm1\})\otimes\mathbb R\), and its finite
   residue coordinates are the valuations
   \(\operatorname{ord}_p\); the real coordinate is forced by product
   formula.
3. Let \(C_{\mathrm{Den}}\) be any three-term arithmetic cohomology
   complex and suppose there is a flow-equivariant map
   \[
     \iota:C_{\mathrm{end}}(K)\longrightarrow C_{\mathrm{Den}}       \tag{4}
   \]
   inducing the prescribed isomorphisms on \(H^0\) and \(H^2\).
   For
   \[
     C_{\mathrm{mid}}
       :=\operatorname{Cone}(\iota),                                \tag{5}
   \]
   one has
   \[
     H^i(C_{\mathrm{mid}})
     =
     \begin{cases}
       H^1(C_{\mathrm{Den}}),&i=1,\\
       0,&i\ne1.
     \end{cases}                                                     \tag{6}
   \]
   Thus the spectral middle cohomology is canonically a relative
   analytic defect after removing the algebraic endpoints.

## Proof

Equation `(2)` says that the degree-one differential of `(1)` is
injective and has cokernel \(\mathbb R(-1)\).  The direct degree-zero
summand has zero differential.  This proves `(3)`.

For \(K=\mathbb Q\), unique factorization identifies
\[
 (\mathbb Q^\times/\{\pm1\})\otimes\mathbb R
 \cong\bigoplus_p\mathbb R[p].
\]
Its coordinates are precisely the Milnor \(K_1\) residues.  The
archimedean component and degree map are the product-formula completion
in `(2)`, proving clause 2.

Apply the long exact cohomology sequence to the triangle
\[
 C_{\mathrm{end}}
 \xrightarrow{\iota}C_{\mathrm{Den}}
 \longrightarrow C_{\mathrm{mid}}
 \longrightarrow C_{\mathrm{end}}[1].
\]
The endpoint maps are isomorphisms, both complexes vanish outside
degrees \(0,1,2\), and `\(H^1(C_{\mathrm{end}})=0\)`.  Exactness gives
`(6)`.

## Structural consequence

The theory has a forced two-layer form:
\[
 \boxed{
 C_{\mathrm{Den}}
 \text{ is an extension of }
 C_{\mathrm{end}}
 \text{ by }H^1_{\mathrm{Den}}[-1].
 }
\]
Milnor/Steinberg and Arakelov data determine the endpoints.  They
cannot by themselves create the nontrivial zero spectrum.  The latter
must be constructed as the relative smooth/leafwise part of
\(\mathscr E_{\mathrm{Den}}\).  Coarse/stack and Frobenius-coherence
defects may map into this relative object but are not its definition.

## Gates

- [x] endpoint complex constructed
- [x] endpoint cohomology computed
- [x] relative middle isolation proved
- [ ] construct the sheaf-level endpoint map `(4)`
- [ ] identify `(5)` with reduced arithmetic leafwise cohomology
- [ ] construct positive Hodge form and source trace on `(5)`
- [ ] Lean formalization of the abstract relative reduction

## References

- `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`
- `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`
- `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`
- Christopher Deninger, *Some analogies between number theory and
  dynamical systems on foliated spaces*:
  https://emis.de/ft/10155

## Log

- 2026-07-26 — Isolated the unique canonical location of Deninger's
  spectral \(H^1\) after constructing the rational generic coefficient
  and real endpoint.

# EDQ: primitive interference and the missing signed contraction

- **ID:** edq-primitive-interference
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Composite deletion's strictly negative coefficient overlap becomes a strictly positive overlap of the corresponding normalized cumulative sources.

## Place in the proof chain

Euler deletion → cofinal subpower control of the complete signed physical source → off-line exclusion → RH. The subpower estimate remains open. This test concerns whether the already formalized negative overlap in `EulerDeletionCompositeInterference` supplies that estimate after passing to the physical primitive. It does not establish a new bound for the complete Möbius source.

## Exact paper proof

Write \(c_p(n)=1-p\mathbf1_{p\mid n}\). Its sum over \(1\le n\le k\) is \(k\bmod p\). The inserted coefficient in composite deletion is \(c_{pq}-c_p\), whose cumulative sum is

\[
 k\bmod(pq)-k\bmod p=p((k/p)\bmod q)\ge0.
\]

Here divisions inside residues are integer divisions. This follows from Euclidean division and requires no coprimality. Thus the product of the two cumulative sums is nonnegative in every cell, although the weighted same-index coefficient overlap is negative.

Let \(b_m(u)=(\{u/m\}-\{u\}/m)/u\), and use the corpus's physical Gram form \(G(m,n)=\langle b_m,b_n\rangle\). On \(k<u<k+1\),

\[
 b_m(u)=\frac{k\bmod m}{mu},\qquad
 b_{pq}(u)-\frac{b_p(u)}q=\frac{(k/p)\bmod q}{qu}.
\]

The second function also equals \(b_q(u/p)/p\), by cancellation of the fractional-part terms. The existing discrete Gram theorem and subtraction of convergent series give the exact full-ray identity

\[
 \Delta(p,q):=G(p,pq)-\frac{G(p,p)}q
 =\sum_{k\ge1}\frac{(k\bmod p)((k/p)\bmod q)}{pqk(k+1)}.
\]

For \(p,q>1\), every summand is nonnegative and the cell \(k=p+1\) has the two residues equal to one. Consequently

\[
 \Delta(p,q)\ge\frac1{pq(p+1)(p+2)}>0.
\]

More generally, every entry of the physical dilation pairing has the formula

\[
 K_p(m,n):=G(m,pn)-\frac{G(m,p)}n
 =\sum_{k\ge1}\frac{(k\bmod m)((k/p)\bmod n)}{mnk(k+1)}.
\]

Indeed \(D_pb_n=b_{pn}-b_p/n\); applying Euclidean division to the second Gram entry gives the displayed series. For \(p\ge1\) and \(m,n>1\),

\[
 K_p(m,n)\ge\frac1{mn(p+1)(p+2)}>0.
\]

If \(p\bmod m>0\), use the cell \(k=p\): its second residue is one, its first residue is at least one, and \(p(p+1)\le(p+1)(p+2)\). If \(p\bmod m=0\), then \(p\ge m\ge2\); the cell \(k=p+1\) has both residues one. All other terms are nonnegative. This proves the bound without selecting primes or assuming coprimality.

The exact three-parameter kernel, rather than just failure of negativity, is the positive survivor. It identifies which physical cells contribute and quantifies positive overlap throughout the generator family. This is a statement about the unweighted primitive underlying the physical source; it is not a claim that every weighted Mellin partial-sum operator reverses signs.

## Next contraction test

Möbius subtraction changes the sign of the cross term again. For the actual dilation \(D_pf(u)=f(u/p)/p\),

\[
 \|(I-D_p)f\|^2-\|f\|^2
 =\|D_pf\|^2-2\operatorname{Re}\langle f,D_pf\rangle.
\]

Positive overlap alone does not show that it pays for the first term. More seriously, repeated subtraction need not preserve pointwise positivity: \((I-D_3)b_2\) is negative on the cell \(4<u<5\). If \(f=\sum_m a_m b_m\), its overlap is the signed form \(\sum_{m,n}a_ma_nK_p(m,n)\). Positivity of every kernel entry does not prove the required bound on this form. Any successful iteration must control that inequality on the actual signed intermediate sources and retain interactions between different generators. No such control is proved here.

## Method transfer audit

The broad newest-first arXiv search "pinning" led to Lu–Wang, [Energy diffusion in a pinned harmonic chain](https://arxiv.org/pdf/2609.08138), submitted 8 September 2026. Lemma 5.5 first pairs boundary errors with a decaying test function; equation (5.20) uses their boundary support to gain an exponential factor. The proof also uses a bound on the conserved expected energy. This suggests retaining pairings before estimating boundary errors, but does not supply EDQ's complete source bound: its physical tail is part of the energy being estimated, and no corresponding conserved-energy input or boundary-only localization has been established. No stochastic model or numerical result is imported.

The preceding broad search "entrainment" led to Massas–Margaliot, [Gain of Entrainment in Nonlinear Cascades](https://arxiv.org/html/2608.15214v1), August 2026. Its downstream incremental gains determine how local Jensen gaps contribute to the output. That prompted testing sign transport through the actual primitive, rather than assuming it. The residue proof above is independent of that paper's dynamical hypotheses.

Corpus deep searches covered joint signed coercivity, primitive preservation of negative covariance, Bellman methods, and accretive dilation subtraction. All returned hits used here as discovery leads had source-only compiler status. The Bellman request finished but reported incomplete source/semantic coverage; the other requests were deadline-partial. No returned ingredient set supplied the missing signed contraction. The new kernel theorem passed separate verification in the installed Lean toolchain.

## No-go closure scope

- **Failed transfer:** treating coefficient-space negative overlap as negative physical primitive overlap.
- **Positive survivor:** exact physical overlap series and uniform positive cell lower bound above.
- **Status:** dependency-closed paper proof and Lean leaf. EDQ itself remains open and is not retired.

## Lean closure

Module: `GaloisForLFunctions.RHTower.EulerDeletionPrimitiveInterference`.
Namespace: `RHTower.DeletionPrimitiveInterference`.

- `generator_dilation`: exact pointwise identity for the physical fractional-part generators.
- `hasSum_overlap`: complete three-parameter physical residue series.
- `kernel_nonneg`, `overlap_nonneg`, `kernel_le_overlap`: cell sign and lower-bound transfer.
- `overlap_lower`, `overlap_pos`: uniform positive bound for every positive dilation and nontrivial pair of generators.
- `composite_primitive_overlap_lower`: quantitative specialization to composite Euler deletion.

Validation: scratch `lake env lean` passed; final leaf-only `lake build --old GaloisForLFunctions.RHTower.EulerDeletionPrimitiveInterference` passed (73 seconds for the new leaf). The umbrella imports the new leaf and was not built. A separate temporary-file axiom audit of these eight new theorems returned only `propext`, `Classical.choice`, and `Quot.sound`. No computation, experimental input, added axiom, or unproved premise supplies any theorem above.

The generated index was refreshed once; `python3 scripts/formal_tools.py lint --check-generated` passed. Temporary searches and audit files were removed after recording their results. No frontier-map or universal-ledger entry was changed by this work.

The open signed-source inequality is unchanged. This result closes the coefficient-to-primitive sign transfer and gives its exact positive replacement; it does not improve the known growth exponent of the full Möbius source.

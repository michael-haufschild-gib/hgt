# SQB prime-cell Hecke correspondence

- **ID:** sqb-prime-cell-hecke-correspondence
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** For a source of principal level \(M\) and a prime \(p\nmid M\), the rational correspondence \(g_p=\operatorname{diag}(1,p)\) has a canonical \(p+1\)-element right-coset presentation. Its \(p\) unipotent branches and one Weyl branch give a finite, explicit candidate for the missing all-cusp Hecke Fourier action.

## Proof chain

\[
\text{actual Maass source}
\to \text{explicit all-cusp Hecke Fourier action}
\to \text{global phase orientation}
\to \text{adjointable commuting Hecke algebra}
\to \text{finite spectral decomposition/local factors}
\to \text{symmetric-power lift}
\to \text{RH criterion}.
\]

This card attacks the second arrow. It supplies a concrete correspondence; it does not establish its Hilbert adjoint, commutation, phase sign, spectral finiteness, or any RH conclusion.

## Candidate arithmetic theorem

Let \(\Gamma=\Gamma(M)\), \(g_p=\operatorname{diag}(1,p)\), and
\[
 K_p=\Gamma\cap g_p^{-1}\Gamma g_p.
\]
For \(\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\Gamma\),
\[
 \gamma\in K_p\quad\Longleftrightarrow\quad p\mid b.
\]
The forward direction is integrality of the upper-right entry of
\(g_p\gamma g_p^{-1}\). Conversely, \(b\equiv0\pmod M\), \(p\mid b\), and
\(p\nmid M\) imply \(b/p\equiv0\pmod M\), so the conjugate is again in
\(\Gamma(M)\).

Put \(U=T^M\). Choose \(t\) with \(Mt\equiv1\pmod p\), let
\(V=T^{Mt}\), and set
\[
 W=V(SVS^{-1})V.
\]
Normality of \(\Gamma(M)\) puts \(V,W\) in \(\Gamma\); modulo \(p\),
\(W=\begin{pmatrix}0&1\\-1&0\end{pmatrix}\). The right-coset representatives are
\[
 \{U^j:0\le j<p\}\ \sqcup\ \{W\}.
\]

For coverage, if \(d\not\equiv0\pmod p\), choose
\(j\equiv b(Md)^{-1}\pmod p\). Then the upper-right entry of
\((U^j)^{-1}\gamma\) is \(b-Mjd\), hence that product lies in \(K_p\).
If \(d\equiv0\pmod p\), the upper-right entry of \(W^{-1}\gamma\) is
\(-d\), again putting it in \(K_p\). Distinctness follows because
\((U^i)^{-1}U^j\in K_p\) forces \(p\mid(j-i)\), while
\((U^j)^{-1}W\) has upper-right entry \(1\) modulo \(p\).

The trace quotient in the current Lean construction is exactly the quotient by this
right relation: \(r\sim r'\) when \(r^{-1}r'\in K_p\). Thus these are the
representatives required by `maassTraceQuotientFunc`, whose summand uses \(r^{-1}\).

## Identity-cusp Fourier consequence

For a source horizontal period \(M\), the unipotent cells give
\[
 g_p(U^j)^{-1}\begin{pmatrix}x\\1\end{pmatrix}
 =\begin{pmatrix}(x-Mj)/p\\1\end{pmatrix}.
\]
At target period \(M\), their \(p\) Fourier windows tile one source period. For
an \(M\)-periodic slice with coefficients \(a_n(y)\), their exact aggregate is
\[
 \sum_{j=0}^{p-1} C_{M,n}\!\left(x\mapsto
 f\!\left((x-Mj)/p+i y/p\right)\right)=p\,a_{pn}(y/p).
\]
The Weyl cell satisfies
\[
 g_pW^{-1}=S\operatorname{diag}(p,1),
\]
so it is the Fourier window at the \(S\)-translated source cusp, with horizontal
scale \(p\) and height \(py\). This identifies the exact off-cusp term rather than
hiding it in an existential quotient representative.

## Remaining proof target

For every finite deck coordinate \(q\), aggregate the same \(p+1\) canonical
windows at the common target period. `Deck` and `quotientForm` already make the
source cusp labels finite; `rationalGL_pullback_cusp_fourier_windowed` supplies
one exact window for each branch. The missing theorem is their finite common-period
aggregation, yielding an explicit transfer on `coefficientVector`.

The Lean implementation must first formalize the displayed right-coset equivalence
at the `SL2Z` principal subgroup, then transport it to the existing GL trace
quotient. It must use no nonconstructive selection of coset representatives in the
final formula. No new module is imported by an umbrella until this proof is checked.

## Gates

- [x] 0 -> 1: candidate has an explicit arithmetic cover, disjointness argument, and source Fourier mechanism.
- [ ] 1 -> 2: all-cusp common-period aggregation has a complete dependency-closed paper proof.
- [ ] 2 -> 3: Lean coset theorem and finite-deck window aggregation are checked and imported by their proper umbrella.
- [ ] 3 -> 4: the resulting adjoint, local-factor, lift, and RH chain are complete.

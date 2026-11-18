# One multiplicity per square conductor

For $D_n=e_1+2e_{n^2}-e_{(2n+1)^2}$ and its positive rational ordinary-prime generator $d$, RH is equivalent to
\[
  \exists B\in\mathbb Z_{>0}\quad\forall n\ge1,\qquad d(nD_n)\le B^{n^2}.
\]
Any prescribed multiplicity $\mu(n)\ge n$ works with allowance $B^{\mu(n)^2}$. The uniform base is open.

Let $P_n$ be the integrated ordinary-prime contact of $D_n$. The signed floors lose between zero and the Chebyshev mass of the prime window, at most $7L$ for endpoint $L$. Adding their exact weighted fractional parts back leaves mesh error $O(m^2\sqrt L/r)$ at resolution $r$. Indeed for each bounded Lipschitz log profile $G$, the variation of $G(\log x)/x$ on $[1,1+L]$ is bounded independently of $L$. The prime weights then sum to at most $34\sqrt L$ after division by $\sqrt p$. Here $L=O(n^2)$ and $r\ge m$, so
\[
 |\log d(mD_n)-m^2P_n|\le C(n^2+nm).
\]
Thus any two multiplicities at least $n$ give normalized log generators within a fixed constant. Passing to the signed section degree also gives $|P_n+Q(D_n)|\le C'$ for all $n$.

For $0\le s<1/2$, set $m_s(n)=\lceil(n+1)^{1-s}\rceil$. The same proof and the degree width law give $w\le s$ exactly when one integer $B>0$ bounds $d(m_s(n)D_n)$ by $B^{(n+1)^2}$ for every $n$. The established width bound proves this comparison at multiplicity exponent $15001/24000$.

Lean declarations include `ordinaryPrimeContact_sampling_error`, `successorSquare_contact_error_all`, `riemannHypothesis_iff_diagonal_successorSquare_power`, `zetaZeroWidth_le_iff_stripMultiplicity_power` and `subThreeEighths_stripMultiplicity_power`. [Uniform quadrature](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/UniformQuadratureForPrimeContacts.lean) · [Single-multiplicity criteria](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/OneMultiplicityPerSquareConductor.lean)

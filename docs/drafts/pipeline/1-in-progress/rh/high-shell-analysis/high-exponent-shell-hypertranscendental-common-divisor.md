# High-exponent shell hypertranscendental common-divisor law

Status: publication-ready; manuscript at
`docs/drafts/pipeline/4-publication-ready/positive-hypertranscendental-riemann-divisor-frame/`

## Target

For
\[
a_m(n)=1_{\text{$(m+1)$-free}}(n)-1_{\text{$m$-free}}(n),\qquad m\ge 12,
\]
prove that the upper-end Dirichlet-series germs
\[
S_m(s)=\sum_{n\ge1}a_m(n)n^{-s}
\]
are jointly differentially algebraically independent over the genuine coordinate field
\(\mathbb C(s)\). Combine this with the
already formalized factorization
\[
S_m(s)=\zeta(s)\bigl(\zeta((m+1)s)^{-1}-\zeta(ms)^{-1}\bigr)
\]
and zero-freeness of the multiplier on \(\Re s>1/2\).

The strengthened final law is: the complete adjacent multiplier family \(H_m\), \(m\ge2\), is
jointly differentially independent even over \(\mathbb C(s)\langle\zeta\rangle\). Its zero-free
subfamily \(m\ge12\) gives infinitely many pairwise-disjoint nonnegative Dirichlet sources
carrying the full strict-right-half Riemann divisor with multiplicity.

## New core insight

Use the Dirichlet-convolution grading
\[
\Omega(n)=\sum_p v_p(n).
\]
For shell level \(m\), the lowest nonzero grade is \(m\), attained only at prime powers \(p^m\).
After applying a prime derivation, the lowest grade is \(m-1\), attained only on the selected
prime ray. Every mixed-prime shell term lies at least one grade higher.

For a finite shell-jet rectangle, take the arithmetic-function-valued prime-derivation Jacobian.
At total grade \(\sum(m_j-1)\), its determinant equals the existing prime-power block determinant.
Higher-grade shell tails cannot contribute to this coefficient. Existing prime-log
Vandermonde/tail-packet machinery makes that block determinant nonzero. The domain-valued Jacobian
criterion then gives algebraic independence of every finite jet rectangle.

## Proof obligations

- [x] Shell support bound: \(a_m(n)\ne0\Rightarrow m\le\Omega(n)\).
- [x] Equality classification: \(a_m(n)\ne0\) and \(\Omega(n)=m\Rightarrow n=p^m\).
- [x] Lowest-grade formula for every prime derivative of every rotated shell jet.
- [x] Generic determinant lemma: equal lowest graded layers imply equal determinant coefficient.
- [x] Finite shell-jet algebraic independence.
- [x] Arbitrary-family differential independence for all \(m\ge2\).
- [x] Faithful transfer to upper-end Dirichlet-series germs over \(\mathbb C(s)\).
- [x] Relative independence after adjoining zeta and all derivatives.
- [x] Joint synthesis with common-divisor and positivity/disjointness theorems.
- [x] Direct RH equivalences for one shell, every shell, and the common zero set.
- [x] Primary-literature novelty audit.
- [x] Antagonistic general-journal referee audit.

## Guardrails

- No RH assumption.
- No numerical computation.
- Paper must not mention formalization.
- Do not claim novelty until primary-literature audit is complete.
- If full shell-function differential independence fails, do not replace it by independence of an
  attached prime-power reporter without explicitly downgrading the result.

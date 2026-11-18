# Ordinary-prime mass at quotient zero

For the compensated one-factor reading, let \(L\) be the spline horizon, \(w_n(k)\) its sample and \(W(j)\) the centered quotient weight. Write \(H(n,q)\) for the sum of \((w_n(k)-w_n(k+1))W(\lfloor k/q\rfloor)\) over \(0\le k\le L\).

**Endpoint.** For \(1\le q\le L\), restricting that sum to \(q\le k\le L\) gives \(H(n,q)+w_n(q)\). Indeed \(W(0)=1\), and the deleted differences telescope to \(w_n(0)-w_n(q)=-w_n(q)\). With ordinary-prime weights the returned samples sum exactly to the dyadic prime contact. The rational price at conductor \(n\) differs from \(n^2\) times this sum by \(O(n^2)\). Summing gives \(O(M^3)\) on every fragment \(J<n\le M\).

**Completed mesh.** On the full Mangoldt measure, exchange the finite product and horizon sums. Since \(w_n(0)=w_n(L+1)=0\), the constant weight one contributes zero. At horizon \(k\) the remaining arithmetic coefficient is
\[
  \sum_{q\le k}\Lambda(q)\bigl(W(\lfloor k/q\rfloor)-1\bigr)=-k+O(1+\log k).
\]
This is the factorial pairing. Abel summation sends the linear term to the unweighted spline sum, of size \(O(1/n)\). The error is multiplied by first differences of size \(O(n^{-3})\) on \(O(n^2)\) horizons. Thus \(\sum_{q\le L}\Lambda(q)H(n,q)=O((1+\log(2n))/n)\). The ordinary-prime part of the returned endpoint still carries the signed price.

**Lean.** `first_quotient_endpoint`, `firstQuotientPrimeEndpoint_price`, `firstQuotientPrimeEndpoint_partial_prefix` and `complete_mangoldt_mesh_bound` passed the kernel check. All four depend only on `propext`, `Classical.choice` and `Quot.sound`. [Lean source](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheEndpointAtQuotientZero.lean)

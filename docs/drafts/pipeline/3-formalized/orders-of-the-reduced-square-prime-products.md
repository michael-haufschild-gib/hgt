# Orders of the reduced prime products on square conductors

For \(D_n=e_1+2e_{n^2}-e_{(2n+1)^2}\), write the ordinary-prime generator of \(mD_n\) as \(U/V\) in lowest terms. Uniformly for large \(n\) and every \(m\ge1\),
\[
 \log V\asymp n^2+nm^2,\qquad \log U\ll nm^2.
\]
For \(m^2\ge Cn\), one also has \(\log U\gg nm^2\). On the diagonal both logs have order \(n^3\), and \(\log U-\log V=o(n^3)\). RH is equivalent to the one-sided bound \(\log U-\log V\le An^2\) with a single constant \(A\).

Above lag \(9e^8\), the unrounded continuous contact at \(q\) is exactly
\[
 \frac{2}{\sqrt q}\big[2H(\log(n^2/q))-H(\log((2n+1)^2/q))\big],
\]
where \(H\) is the eight-box density. Since \(H(0)>0\) and \(H(t)\le H(0)\), a fixed relative interval near \(q=n^2\) supplies positive rows of size \(\gg m^2/n\) after sampling. The prime number theorem gives logarithmic mass \(\gg n^2\) there. For \(m^2\ge Cn\) the floor preserves a fixed fraction of this mass times the contact. The summable row bound gives the matching upper bound. Sublinear growth of the signed contact gives the same lower bound for the denominator above the threshold. Below it, the negative prime window already gives \(\log V\ge n^2/12\).

The Lean declarations are `successorSquare_denominator_order`, `successorSquare_products_upper`, `successorSquare_both_products_lower`, `diagonal_numerator_exceeds_every_quadratic_log`, and `successorSquare_log_negligible`. [Reduced products](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheNumeratorAboveSquareRootMultiplicity.lean) · [Exact prime profile](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeProfileOfThreeSquareConductors.lean) · [Signed comparison](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/OneMultiplicityPerSquareConductor.lean)

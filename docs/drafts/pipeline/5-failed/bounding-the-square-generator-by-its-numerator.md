# Bounding the square generator by its numerator

On the diagonal \(m=n\), the reduced positive valuation product \(U\) exceeds \(B^{n^2}\) eventually for every fixed \(B\ge1\). Primes near \(n^2\) alone contribute \(\gg n^3\) to \(\log U\). Discarding the negative valuations therefore loses the scale required by the section criterion.

**Surviving comparison.** The coprime denominator also has logarithm of order \(n^3\). The two logs agree to \(o(n^3)\), and RH is equivalent to a one-sided quadratic bound on their difference. More generally the denominator has logarithmic order \(n^2+nm^2\) for every positive multiplicity and the numerator has order \(nm^2\) above \(m^2\ge Cn\). The proof and Lean declarations are in the [product-order theorem](../3-formalized/orders-of-the-reduced-square-prime-products.md).

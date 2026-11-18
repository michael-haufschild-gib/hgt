# Small sections on signed spline rays

**Open target.** For each prime $p$, prove that the integral contact modulus of $m(e_1+e_p)$ fits inside its real radius for arbitrarily large $m$. An equivalent matrix target allows one negative square at cofinally many multiplicities for each fixed horizon. [Negative squares from sections](../3-formalized/negative-squares-from-rational-section-counts.md)

At all sufficiently large multiplicities $m$, every conductor $p\ge Km^4$ admits its full rational generator as a section of $m(e_1+e_p)$ at the original radius. On every signed integer divisor both sampled pole readings have bounded additive error, uniformly over conductor and multiplicity. [Effective sections at separated conductors](../3-formalized/acs-effective-divisors-at-separated-conductors.md)

For every δ < 1 and C > 0, every sufficiently large logarithmic window |log p − T| ≤ 32 log(T+2) contains more than C exp(δT) primes with a common tail of exact modulus fit. [Sections at every scale](../3-formalized/acs-sections-at-every-logarithmic-scale.md)

For every 7/12 < β < 1, arbitrarily large primes p start windows with at least p^β/(4 log p) further consecutive primes whose full moduli fit the original radius at one common multiplicity threshold. Anchored signed clusters of comparable positive masses and bounded relative total variation also realize the signed Weil form by ordinary counts on selected windows. A bound $m^2\exp((1+\eta)T)$ on the total dual height in arbitrarily late prime windows, for each $\eta>0$, is equivalent to RH. [Prime-centred rational sections](../3-formalized/acs-prime-windows-with-rational-sections.md) · [Aggregate dual height](../3-formalized/aggregate-dual-height-on-prime-windows.md)

At resolution n, sample the signed spline f at log(j/n). For each prime power k = pʳ in the support window, impose the integral valuation

    floor((2/√k) Σⱼ fⱼ fⱼₖ / j).

Negative valuations permit denominators. Let d be the positive rational generator of the resulting lattice. The logarithmic radius A is twice the product of the two sampled pole degrees minus the degree-point jet pairing with its diagonal counterterm. The small sections have coordinates z ∈ ℤ satisfying |dz| ≤ exp A.

On a fixed window, rounding all finite places changes the signed degree by at most Σₖ Λ(k), independently of the mesh and the coefficients. Before rounding, the signed degree converges to the full Weil form by logarithmic quadrature, including both poles. A nonzero section exists exactly when log d ≤ A. This leaves the arithmetic comparison of the least nonzero section with the real radius.

The primal and dual logarithmic section counts have quadratic coefficients $\max(Q(a),0)$ and $\max(-Q(a),0)$. It suffices to prove one comparison for the effective divisors $e_1+e_p$. A single constant $C$ must satisfy $\log d(m(e_1+e_p)) \le A(m(e_1+e_p))+Cm^2$ at arbitrarily large $m$ for each prime $p$. Here $d$ is an integer. [Signed section limits](../3-formalized/tate-limits-of-rational-small-sections.md) · [Prime-pair criterion](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/SmallSectionsOnPrimePairs.lean)

The same comparison suffices with only ordinary prime degrees in the modulus. For every signed divisor, omitting all higher powers changes the logarithmic generator by at most a universal constant times its squared total variation plus the horizon rounding allowance. [Uniform proper-power bound](../3-formalized/ordinary-prime-moduli-of-spline-sections.md)

The positive pole vanishes on $D_n=e_1+2e_{n^2}-e_{(2n+1)^2}$. A single integer $B>0$ bounding $d_{\rm ord}(nD_n)$ by $B^{n^2}$ for every $n>0$ is equivalent to RH. Every prime in $(W_n/3,W_n/2]$, $W_n=e^8(2n+1)^2$, divides the reduced denominator at every positive multiplicity. For $1\le m\le c\sqrt n$ the numerator is at most $B^{m^2}$, and the full lattice has at least $2\lfloor e^{n^2/48}\rfloor+1$ sections at its original radius for all sufficiently large $n$. [One multiplicity per square conductor](../3-formalized/one-multiplicity-per-square-conductor.md) · [Square-root range](../3-formalized/prime-contact-products-at-small-multiplicity.md) · [Denominator window](../3-formalized/the-multiplicity-scale-of-prime-contact-rounding.md) · [Original section count](../3-formalized/acs-original-sections-on-square-conductors.md)

For the reduced generator $U/V$ of $mD_n$, $\log V\asymp n^2+nm^2$ at every positive multiplicity. For $m^2\ge Cn$, $\log U\asymp nm^2$ as well. At $m=n$ the two logarithms have order $n^3$ and their difference is $o(n^3)$. The target is $\log U-\log V\le An^2$. [Reduced product orders](../3-formalized/orders-of-the-reduced-square-prime-products.md)

For all large $n$, every scale $1\le M\le c(n+1)^{1-w}$ contains an $m\in[M,3M]$ with at least $2\lfloor\exp(n^2/4608)\rfloor+1$ original sections, where $w$ is the zeta zero width. This reaches $M\asymp n^{5/8}$ unconditionally. [Floor loss across multiplicities](../3-formalized/acs-floor-loss-across-multiplicities.md)

The single signed spline $2e_1-5e_4+2e_{16}$ kills both poles. Its integer translates retain every distinct right zero in their negative index; on the golden model the index is infinite already at two primes. [Two-pole-free integer translates](../3-formalized/two-pole-free-spline-with-full-negative-index.md)

One fixed positive two-atom divisor also gives an ordinary-count test on three translates. For each signed displacement the normalized second difference of their log cardinalities tends to twice its Weil degree. Cofinal midpoint product injections for all displacements are equivalent to RH. [Midpoint injections](../3-formalized/midpoint-injections-for-spline-sections.md)

[Conductor graph resultants](../3-formalized/acs-vertical-contact-of-signed-divisors.md) independently realize the complete prime sum on every signed spline ray as a difference of logarithmic restriction orders. [Simultaneous jet interpolation](../3-formalized/acs-simultaneous-conductor-jets.md) gives a nonzero rational function prescribing all zero/one jets within every positive quadratic allowance for the unit-circle and normalized cyclotomic heights. Comparing these sections with the rational generator and the radius containing both pole moments remains open.

On every signed integer ray the pole product can be supplied by finite vertical restriction orders through all original multiplicities. The corrected rational ideal recovers the full Weil degree using the original jets alone. On effective rays the pole multiplier is an integer square. [Pole product from vertical orders](../3-formalized/acs-pole-from-separated-graph-contacts.md)

For every $B\ge1$, a fixed number of integer power sums cuts out a kernel of positive degree on $N/B<d\le N$ for every $N$. Its rational dimension is at least $N-\lfloor N/B\rfloor-k(B)$, and every nonzero integral ray in it has small sections at the original radius at all sufficiently large multiplicities. The prime pair has zeroth moment two. [Integer moment kernels](../3-formalized/acs-integer-moment-sections.md)

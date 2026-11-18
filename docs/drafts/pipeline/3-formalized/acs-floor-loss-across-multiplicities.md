# Prime floor loss across multiplicities

Let $D_n=e_1+2e_{n^2}-e_{(2n+1)^2}$ and let $w$ be the zeta zero width. There is an absolute $K$ such that, for all sufficiently large $n$, every scale $1\le M\le (n+1)^{1-w}/K$ has an integer $m\in[M,3M]$ for which the original section lattice of $mD_n$ contains at least $2\lfloor\exp(n^2/4608)\rfloor+1$ sections. This includes scales of order $n^{5/8}$.

## Proof

Fix a prime $k$ in $(W/3,W/2]$, where $W=e^8(2n+1)^2$. Its unrounded contact $x_m$ is strictly negative at every positive multiplicity. Write $b$ for its integrated contact on $D_n$. Uniform quadrature and $r(mD_n)\ge m$ give $|x_m-bm^2|\le Cm/\sqrt k$. The contact-size bound on the unit mesh gives $|b|\le C/\sqrt k$. Thus for $M\le\delta n$ with absolute $\delta>0$, we have $|b|M\le1/64$ and error at most $1/512$ throughout $[M,3M]$.

If $|b|M^2\le1/8$, each $x_m$ for $M\le m<2M$ lies strictly between $-3/4$ and zero, so its fractional part exceeds $1/4$. Otherwise take $h=\lceil1/(32|b|M)\rceil\le M$. For $M\le m<2M$, the ideal quadratic readings at $m$ and $m+h$ differ in absolute value by $|b|h(2m+h)\in[1/16,5/16]$. After both mesh errors, the difference stays between $1/32$ and $1/2$. The two fractional parts sum to at least $1/32$, since a smaller sum would put the difference within $1/32$ of an integer. Each index is used at most twice, giving $\sum_{m=M}^{3M}\{x_m\}\ge M/64$.

The negative window has prime logarithmic mass at least $W/12\ge n^2/12$ by the prime number theorem. Summing first over primes yields total ordinary floor loss at least $Mn^2/768$ over the multiplicities. Some multiplicity realizes loss at least $n^2/2304$.

Writing $g=(n+1)^w$, the integrated prime contact of $D_n$ is bounded above by $O(g^2)$ by the signed degree estimate. The global mesh error is $O(nm)$. The remaining prime powers and archimedean debit cost $O(m^2)$ because $D_n$ has zero positive pole degree. For $Km g\le 3(n+1)$ these three costs together are at most $n^2/4608$ after choosing $K$ large. The resulting logarithmic margin admits every integer coordinate of absolute value at most $\exp(n^2/4608)$.

## Lean

[FractionalPartsAcrossMultiplicities.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/FractionalPartsAcrossMultiplicities.lean) proves `negative_quadratic_floor_loss`. [PrimeFloorLossAcrossMultiplicities.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/PrimeFloorLossAcrossMultiplicities.lean) proves `successorSquare_mean_floor_loss` and `successorSquare_exists_floor_loss`. [SquareSectionsBeyondRootMultiplicity.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/SquareSectionsBeyondRootMultiplicity.lean) proves `square_sections_at_width_scales` and `square_sections_through_five_eighths`.

# A power saving for the unaveraged odd-quotient prime count

Put \(u(d)=\Lambda(d)\mathbf1_{d\text{ nonprime}}-\mathbf1_{d\text{ square}}-\mathbf1_{d\text{ cube}}\) on the positive integers. For every integer \(N\ge1\) consider
\[
S(N)=\sum_{d\le N}u(d)\bigl(\lfloor N/d\rfloor\bmod2\bigr).
\]
Its Mangoldt part is \(\log N!-2\log\lfloor N/2\rfloor!\) minus the odd-quotient ordinary-prime sum. The square and cube parts count the same parity over unrestricted powers.

If \(U(Y)=\sum_{d\le Y}u(d)=O(Y^b)\) for \(0<b<1/2\), then \(S(N)=O(N^{1/(3-2b)})\) at every cutoff. Indeed, \(\sum_{d\le Y}|u(d)|\le U(Y)+2(\lfloor\sqrt Y\rfloor+\lfloor Y^{1/3}\rfloor)=O(\sqrt Y)\). For \(d>Y\) write the parity as an alternating sum over \(j\le N/d\), then reverse the order. Each nonempty row is \(\pm[U(\lfloor N/j\rfloor)-U(Y)]\) and all rows have \(j\le N/(Y+1)\). Their absolute sum is \(O(N^b(N/(Y+1))^{1-b})\). Take \(Y=\lfloor N^{2/(3-2b)}\rfloor\).

The [proper-power bound](../3-formalized/a-finite-prime-multiple-count-at-the-quarter-exponent.md) supplies \(b=7/16\) unconditionally, hence exponent \(8/17\) for this unaveraged finite prime count. More generally the same argument gives every exponent above \(24000/51001\). Under RH it gives every exponent above \(2/5\). Reaching the half-ordinate of a right zero requires additional cancellation across the large-divisor rows or within the small-divisor sum.

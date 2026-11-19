# Exact Boolean fibres above an adaptively sifted tail

- **Stage** 1-in-progress
- **Question** Which integer rows actually contribute to the sharp prefix after repeatedly stripping an eligible least prime?

For a squarefree integer strip its least prime \(p\) whenever \(p\le b(n)\) at the current quotient. Stop at the unit or at a member of the fixed sifted set. The stripped primes increase strictly. If the last stripped prime is \(p\) and the final tail is \(r\), then \(p\le b(pr)\), \(r\) passes its own cutoff, and every prime factor of \(r\) exceeds \(p\). Conversely these three conditions suffice. The entire fibre is
\[
 \{cpr:c\mid P(p-1)\}.
\]
Indeed, each prime of \(c\) is smaller than \(p\) and each corresponding intermediate quotient is at least \(pr\). Monotonicity of \(b\) pays every earlier test. Unique factorization and the terminal stopping test disjointify all fibres. The fibre with no stripped prime consists of its tail alone.

At \(X\) the signed charge in this fibre is \(-\mu(r)\sum_{c\mid P(p-1),\ c\le X/(pr)}\mu(c)\). For \(p>2\) its complete charge vanishes, by divisor inversion or by toggling the factor 2. Each toggle is a genuine one-to-two prime exchange: retain the other factors and replace \(p\) by \(2p\). Consequently only the sharply truncated fibres \(pr\le X<prP(p-1)\) can contribute. The whole prefix is the fixed-tail charge plus these partial divisor sums and the \(p=2\) boundary. There are no retries or repeated integers. For any growing cutoff the \(p=2\) term agrees with minus the fixed-tail charge at \(\lfloor X/2\rfloor\) up to finitely many small exceptions.

At the log-square cutoff, \(p\le b(pr)\) implies \(p\ll 1+\log^2(r+1)\), since \(\sqrt p\le\log(pr+1)\le\log p+\log(r+1)\) and \(\log p\le\sqrt p/2\) for large \(p\). Hence every fixed tail labels only finitely many cubes. As \(\log P(p-1)\ll p\), all cubes above \(r\le\exp(c\sqrt{\log X})\) lie entirely below \(X\) for a sufficiently small absolute \(c>0\). For a fixed tail with \(b(r)\ge2\), the unstripped singleton cancels with its \(p=2\) branch, so the complete charge above that tail is exactly zero. The remaining difficulty is cancellation among the actual boundary fibres of larger tails.

The finitely many exceptional tails also cancel in aggregate. A squarefree even stopped tail \(2m\) passes only if \(b(2m)<2\). Its odd half \(m\) then passes, and precisely that inequality prevents the \(p=2\) branch over \(m\). Conversely, every odd stopped tail missing that branch pairs with its passing even double. This is an identity of signs, including the unit. Once both members of these finitely many pairs are below the tail cutoff, their total charge is zero. Thus, for the log-square cutoff, the contribution of **all** integers with terminal tail at most \(\exp(c\sqrt{\log X})\) vanishes exactly for every sufficiently large \(X\).

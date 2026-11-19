# The explicit log-square rough set

- **Stage** 3-formalized
- **Target** The square-root-plus-epsilon bounds for the full Möbius prefix are equivalent to those for the ordinary signed prefix of the fixed set
  \[
     S=\{1\}\cup\{n>1:P^-(n)>\lfloor\log(n+1)\rfloor^2\}.
  \]
  The set has density zero. Membership uses only the integer being tested.

Write \(R(t,y)=\sum_{n\le t,(n,P(y))=1}\mu(n)\), where \(P(y)\) is the product of primes through \(y\). For any nondecreasing integer cutoff \(b(n)\), let \(A(t)\) sum the individual terms with \((n,P(b(n)))=1\). Fix \(s>0\), and put \(E(y)=\prod_{p\le y}(1-p^{-s})^{-1}\). Adding a prime \(p\) to the cutoff gives the exact identity \(R(t,p)=R(t,p-1)+R(\lfloor t/p\rfloor,p)\).

**Recovering every cutoff from the fixed set.** If \(|A(t)|\le C t^s\), then for every \(y\ge b(t)\),
\[
 |R(t,y)|\le 2C(b(t)+1)t^s E(y).
\]
Induct in lexicographic order on \((t,y)\). For \(y>b(t)\) the prime recurrence closes with no branching loss because \(E(p-1)=(1-p^{-s})E(p)\). The smaller argument has \(b(\lfloor t/p\rfloor)\le b(t)\). At \(y=b(t)\), let \(l\) be just before the interval on which \(b\) first takes its current value. The exact identity \(R(t,y)=A(t)-A(l)+R(l,y)\) costs at most \(2Ct^s\) above the induction bound, paid by \(b(l)<b(t)\). If there is no earlier interval use \(R(t,y)=A(t)\).

At fixed \(X\), apply the uniform upper bound to all \(t\le X\) with \(y=b(X)\). Undo each prime deletion; in the truncated power norm removal costs at most \(1+p^{-s}\le(1-p^{-s})^{-1}\). Thus \(|M(X)|\le2C(b(X)+1)E(b(X))^2 X^s\). Conversely, from \(|M(t)|\le Ct^s\), adding the primes gives \(|R(t,y)|\le Ct^s E(y)\). Partition the fixed-set sum according to the value of \(b(n)\); at most \(b(X)+1\) sharp interval differences occur, giving the same transfer bound with one factor of \(E\).

**Critical growth of the cutoff.** For \(s>1/2\), choose \(0<r<1/2\) with \(s+r>1\). Then \(\log E(y)\ll_s\sum_{2\le k\le y}k^{-s}\le y^r\sum_{k\ge1}k^{-(s+r)}\). At \(b(X)=\lfloor\log(X+1)\rfloor^2\) both \(\log E(b(X))\) and \(\log(b(X)+1)\) are \(o(\log X)\). Both transfers lose at most an arbitrary positive power. For density, beyond a fixed starting point every member avoids every prime up to a fixed \(z\); the corresponding periodic density tends to zero with \(z\).

**Lean.** `log_square_deletion_cost`, `density_zero_of_log_square_rough_set`, `power_transfer_on_the_log_square_rough_set`, and `square_root_on_the_explicit_log_square_rough_set` in [TheExplicitLogSquareRoughSet](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheExplicitLogSquareRoughSet.lean).

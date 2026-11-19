# The power exponent of every unsigned exchange remainder

- **Stage** 3-formalized
- **Question** Can any single involution by genuine one-prime to two-prime exchanges have only \(O(X^\theta)\) fixed or crossing squarefree vertices at every cutoff, for some \(\theta<1\)?

Let \(U_F(x)\) count the fixed squarefree integers through \(x\) and the squarefree integers below that cutoff with partner above it. An interval \((a,b]\) containing no internal partner of a prescribed set \(S\) of moving vertices has \(|S|\le U_F(a)+U_F(b)\), also allowing fixed vertices in \(S\). A fixed vertex or upward exit contributes itself at \(b\). A downward exit contributes its partner at \(a\), injectively by involutivity.

Take all products of \(k\ge4\) distinct primes in \((2t,4t]\). They lie below \(Y=(4t)^k\), and their number is \(\binom{\pi(4t)-\pi(2t)}k\gg_k(t/\log t)^k\). In any genuine exchange changing such a product, its unchanged cofactor is at least \((2t)^k/(4t)^2\ge t^{k-2}\). The changed prime and semiprime differ by a nonzero integer, so the displacement is at least the cofactor. Partition \((0,Y]\) into \(4^kt^2\) equal cells of length \(t^{k-2}\). Summing the two-cutoff inequality gives
\[
 \max_{x\le Y} U_F(x)\gg_k \frac{t^{k-2}}{(\log t)^k}.
\]
For any \(0<\theta<1\), choose \(k(1-\theta)>2\). The right side exceeds every constant times \(Y^\theta\) eventually. Thus every global restricted involution has unsigned prefix exponent exactly one, including those with \(U_F(x)=o(x)\). This requires signed cancellation among the remaining vertices for any fixed power saving. The two-cutoff inequality and explicit grid witnesses apply to every matching with the same constants, independently of its construction.

**Positive survivor.** Sharp intervals expose the geometric cost via their two endpoint counts. A single density-one involution attains little-o of the linear bound, while no single involution can attain any smaller power. The separate fixed-set reduction tests the signed prefix without a crossing-count estimate.

**Lean.** `exists_large_unpaid_cutoff` supplies the finite grid witness. `unsigned_prefix_power_iff` classifies every positive unsigned power bound for every legal global involution. `unsigned_dyadic_power_boundary` gives a single map attaining the sublinear boundary. All three depend only on `propext`, `Classical.choice` and `Quot.sound`. [Two-cutoff inequality](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheTwoCutoffsAroundASmoothVertex.lean) · [Exact unsigned power exponent](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/ThePowerExponentOfEveryUnsignedPrefix.lean)

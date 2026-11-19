# The common main term of both signs on the log-square rough set

- **Stage** 3-formalized
- **Target** For the explicit rough set, center each sign count at one half of the sum of the individual local squarefree densities. The sum of the two centered counts has a square-root-plus-epsilon error unconditionally. Either sign alone then detects the Mertens square-root criterion.

At real cutoff \(x\), put \(H_y(x)=\#\{n\le x:n\text{ squarefree},(n,P(y))=1\}-x\delta_y\), where \(\delta_y=\zeta(2)^{-1}\prod_{p\le y}(1+1/p)^{-1}\). For the new prime \(p\) the exact identities for both the count and its density give \(H_{p-1}(x)=H_p(x)+H_p(x/p)\). Working at a real cutoff keeps the main term at the dilated argument exact. The ordinary squarefree discrepancy is \(O(\sqrt x)\) for \(x\ge1\); for \(x<1\), \(|H_y(x)|=\delta_y x\). For \(1/2\le s\le1\) induction on the prime cutoff and on \(\lfloor x\rfloor\) gives \(|H_y(x)|\le4 E_s(y)x^s\).

Let \(b(n)=\lfloor\log(n+1)\rfloor^2\) and \(W(X)=\sum_{n\le X}\delta_{b(n)}\). Partition by constant intervals of \(b\), taking the difference of discrepancies at both endpoints. The absolute error in the total squarefree count on the fixed rough set is at most \(8(b(X)+1)E_s(b(X))X^s\). The log-square Euler bound gives \(O_\varepsilon(X^{1/2+\varepsilon})\). Writing the two sign counts as half of this total plus or minus half of the signed prefix proves the two one-sign criteria, with the same explicit center \(W(X)/2\) at every cutoff. No matching choice or zero information enters the unsigned main term.

**Lean.** `primorial_squarefree_discrepancy`, `square_root_for_the_unsigned_rough_population`, `one_rough_sign_detects_the_signed_power`, and `square_root_from_one_explicit_rough_sign` in [The common main term of both rough sign counts](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheCommonMainTermOfBothRoughSignCounts.lean).

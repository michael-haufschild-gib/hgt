# Complete Vaughan cofactor signs — Lean audited

Paper proof: [complete cofactor signs](../2-fully-proven/bag-complete-vaughan-cofactor-signs.md).
Four public theorems added to ChiPrimeGaussianCubicPrimeOnlyVaughan:

- vaughanPrimeShort_eq_moebius_seam: V<n<=2V gives the exact mu(n) coefficient.
- vaughanPrimeTypeII_eq_moebius_seam: U>=1,n<=2UV classifies EVERY Type-II
  term, preserving the long-prime, short-support and coprimality tests.
- vaughanPrimeShort_twice_prime: at every odd prime cutoff p the actual
  coefficient at 2p is +1.
- exists_vaughanPrimeShort_positive_after: hypothesis-free cofinal positive
  family (apart from the universally quantified threshold K).

Final production70593, lake --old env lean on the changed leaf with its own
-o target: exit0, empty log. Scratch73180 passed before the cofinal corollary
was added; full production verifies all four. Axiom2264 exit0, all four use
only propext, Classical.choice, Quot.sound. Index87246 passed; all four API
entries verified, existing umbrella import occurs once. Lint60847:25
unrelated unreachable modules,174 large-file warnings; no finding in this
leaf and no forbidden proof declaration. Global lint NOT clean. No full or
umbrella build, subagent, computation experiment, added axiom or limit hack.

This corrects the sign premise of a potential full-source alias argument.
It does not prove a bound for the complete signed aliases or axes action.
The hard target remains o(N/log(N)^2) for the whole actual signed cubic.

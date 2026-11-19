# Perfect completion without increasing any unpaid prefix

- **Stage** 3-formalized
- **Target** Complete every global restricted involution to a matching of every squarefree integer greater than one, simultaneously decreasing its unsigned unpaid counts at all sharp cutoffs. The cost in old moving endpoints through \(X\) can grow arbitrarily slowly.

Process the integers in increasing order. If \(k>1\) is squarefree and currently fixed, replace a prime factor of \(k\) by two fresh primes to obtain a legal neighbor \(y\) as large as desired. Avoid the finite set of already protected vertices and their current partners. Pair \(k\) with \(y\); if \(z=F(y)\ne y\), fix \(z\). Choose both \(y,z\) above any prescribed threshold \(B(k)\ge k\). This is possible since an involution maps a finite interval onto a finite set, whereas the legal neighbors of \(k\) are unbounded. The old partner of a protected vertex and the vertex itself stay protected after its step.

For every cutoff \(X\), the unpaid count is the squarefree population through \(X\) minus twice the number of complete nontrivial pairs through \(X\). An old pair lost by the repair has endpoints \(y,z\); if both were within the cutoff, then so are \(k,y\), since \(k<y\). Thus **each repair weakly decreases every unpaid count simultaneously**. More precisely the decrease is two at \(y\le X<z\) when \(z\ne y\), or at every \(X\ge y\) when \(y\) was fixed. All other cutoffs retain their counts.

The limit exists pointwise. Every nonunit squarefree vertex acquires a partner by its own step and keeps it forever. An original moving endpoint that changes must first occur among the large vertices \(y,z\) of a repair; processing a previously untouched moving vertex leaves it alone. At most \(2\#\{k:B(k)<X\}\) such vertices occur through \(X\). Taking \(B(k)=2^k\) gives logarithmic cost. Arbitrarily faster thresholds are permitted.

Applied to the global logarithmic-saving involution, the resulting perfect matching inherits its unpaid bound at every cutoff. Its signed charge is exactly \(M(X)-1\) on the lower endpoints of crossing edges for \(X\ge1\). Almost every vertex retains the previous short displacement, since the old fixed population has density zero and only a sparse set of old moving vertices changes. Uniform displacement on the repaired vertices is a separate question.

**Lean.** `arbitrarily_large_restricted_partner`, `perfect_completion_at_every_cutoff`, `unpaid_signs_of_smaller_prefix`, and `logarithmic_saving_with_only_crossing_edges` in [PerfectCompletionAtEverySharpCutoff](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PerfectCompletionAtEverySharpCutoff.lean).

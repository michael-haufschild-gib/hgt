# The Mertens prefix on arbitrarily long crossing edges

- **Stage** 1-in-progress
- **Question** Can a single perfect restricted matching carry the full signed prefix, to arbitrarily slowly diverging additive error, entirely on orbits exceeding a prescribed separation?

Fix \(D(n)=\max(2n,T(n))\) for any requested threshold \(T\). Choose a restricted matching \(F\) with signed crossings at most \(w(X)/4\) and displacement \(o(n)\). For a nonnegative \(w\to\infty\), choose \(V\) so that \(\#\{n\le X:V(n)<X\}\le\min(\sqrt X,w(X)/4)\). Complete the matching at separation \(\max(D,V)\). Every new upward edge exceeds \(D\); a crossing with upper endpoint at most \(D(n)\) was retained from the original matching.

Closed orbits contribute zero. The signed population on the full long orbits through \(X\) equals the original fixed charge, less the compulsory unit, plus the old crossings lost from the short population. Such an old crossing either changed or already exceeded \(D(n)\). At most \(2\#\{n\le X:V(n)<X\}\) old moving vertices changed, and only finitely many old edges exceeded \(D\). The long-orbit charge differs from \(M(X)\) by at most \(w(X)\) for every sufficiently large \(X\). The long lower endpoints lie among the old fixed vertices, changed vertices and those finitely many exceptions. Their upper endpoints contribute at most one more vertex each. Both the long orbits and the completed matching's unpaid population have density zero.

The choice \(w(X)=\log X\) preserves exactly every positive power, including an attained endpoint. The square-root-plus-epsilon bound for the actual signed long-orbit prefix remains open.

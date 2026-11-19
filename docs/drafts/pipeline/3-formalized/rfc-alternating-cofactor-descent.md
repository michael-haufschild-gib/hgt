# Alternating descent between cofactor conventions

- **Stage** 3-formalized

Start at each old positive source outside the new sources. Follow its old edge, then the inverse new edge where present. Switch to old edges at reached positive vertices and retain new edges elsewhere. Injectivity of the two partner maps makes continuations unique and forbids merger of walks from distinct starts.

An old edge staying in its even-prefix fibre removes one prime factor; reversing a new largest-pair edge removes another. After \(k\) two-edge steps from \(a\) to \(x\), \(\omega(x)+2k=\omega(a)\). The resulting matching uses only edges of the two input matchings and covers all old positive sources and all transported negative targets.

**Lean** [Alternating cofactor descent](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/AlternatingCofactorDescent.lean), `cofactor_walks_do_not_merge` and `exists_combined_cofactor_descent`.

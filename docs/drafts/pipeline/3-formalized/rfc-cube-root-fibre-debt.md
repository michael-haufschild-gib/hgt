# Every empty ordered fibre can be evacuated

- **Stage** 3-formalized
- **Statement** In every sufficiently large octave one restricted matching covers all negative vertices whose ordered fibre has no positive vertex, while retaining every matched positive of any prescribed ordered matching.

Write a negative vertex as \(ar\) with \(r\) its largest prime. The scale \(X/a\) tends to infinity uniformly. Otherwise all prime factors of the squarefree integer \(ar\) would be bounded, so \(ar\) would divide a fixed primorial. If all primes of \(a\) are at most \(\sqrt{X/a}\), two primes in consecutive short windows above that threshold produce a positive vertex in the same ordered fibre. Emptiness therefore forces \(q=P^+(a)>\sqrt{X/a}\). Writing \(c=a/q\) puts \(q^3>X/c\).

At \(T=X/c=s^6\), count every product with smaller prime in \((s^2/2,2s^3]\). The bound for the larger prime in its sharp quotient window, summed using Mertens' first theorem for \(\sum_q(\log q)/q\), gives at most nine tenths of the available primes. The comparison holds throughout cells of every fixed logarithmic relative width. Ranked row transport covers every eligible \(cqr\) simultaneously. Alternating descent restores the old positives. The entire empty-fibre family, including fibres empty because of actual prime locations, has zero remaining debt.

**Lean** [Prime supply at the cube root](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PrimeSupplyAtTheCubeRootBoundary.lean), `eventually_cubeProducts_nine_tenths`. [The cube-root exchange](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheCubeRootExchange.lean), `exists_cube_root_exchange`. [Every empty ordered fibre](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/EveryEmptyOrderedFibre.lean), `eventually_every_empty_fibre_covered` and `eventually_transported_empty_fibre_mass`.

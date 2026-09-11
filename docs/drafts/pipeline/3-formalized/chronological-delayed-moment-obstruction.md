# Geometric recovery surgery: exact delayed moment failure

- **ID:** chronological-delayed-moment-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [dependency-closed paper proof](chronological-delayed-moment-obstruction-paper.md)
- **Statement:** arbitrarily small changes of an explicit planar domain preserve arbitrarily many actual quotient costs and strict adjacent curvature tests, but force a first negative moment square at an exactly prescribed degree; the thermal zeta zero divisor remains unchanged.

## Complete certificate

The main unconditional theorem is [`recoverySurgery_full_geometric_theorem`](../../../../formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor/RecoverySurgeryGeometry.lean). Its only parameter is a natural number `j`; every geometric and analytic condition is proved internally.

Set `N=2^(j+4)`, `d=N/2`, and `n=N−1`. Lean's surgery parameter `n` equals the paper's `m−2`, where `m=N+1`. The coordinate pair is `(u,c)`; nested polynomials use outer variable `c` and inner variable `u`.

The limiting wedge is `K₀={0≤c≤1, c≤u≤3c}`. The actual observation algebras are faithfully represented copies of `A=ℝ[u,c²,c³]⊂B=ℝ[u,c]`. Each modified domain is cut out by six explicit polynomial inequalities, including the homogeneous Chebyshev/cardinal sublevel constraint from the paper.

Lean proves:

1. Every modified domain is compact, radial, nonconvex, and has nonempty interior. Full polynomial evaluation is injective. An explicit homothetic wedge lies inside it.
2. Every homogeneous quotient norm is an attained infimum over actual polynomial representatives. The first `N` costs equal the wedge's actual costs `β_k=1/((k+1)2^(k+1))`. The next lies between the proved core and height multiples of `β_N`. Every adjacent strict log-convexity test through that cost passes.
3. For `γ_k=(Δ_k/Δ_0)²`, an explicit monic Chebyshev polynomial of degree `d` has `L_γ(P²)<0`. Every nonzero polynomial of smaller degree has strictly positive square value. The literal first failing Hankel quadratic form has positive index `d`, negative index one, and zero-dimensional radical. No positive measure on the real line represents these moments.
4. The domains converge to `K₀` in the ordinary Hausdorff metric, with bound `33/(32(n+2)²)`. The wedge's actual normalized costs are represented by the explicit law of the product of two independent uniform interval variables divided by four.
5. The actual algebraic quotient embeds densely and isometrically for the graded geometric norm into its Hilbert completion. On each homogeneous class this norm equals the attained geometric quotient infimum. Literal radial pullback induces a unique bounded flow extension. Its operator trace is `q/(1−q)`; continuum subtraction gives `−Γ(s)ζ(s)` on `0<Re(s)<1`, with exactly the same zeros and zero multiplicities.

The further theorem `recoverySurgery_arbitrarily_close_delayed_obstruction` combines the quantifiers: for any degree bound `r` and positive Hausdorff tolerance, there is a modified geometry within that tolerance whose every nonzero square test through degree `r` is positive, yet whose moments admit no positive representing measure. This expresses failure of openness at the positive-moment wedge without introducing an assumed sequence of costs.

## Proof map

All files are in `formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor/` and use the `RecoverySurgery` prefix.

| Leaves | Closed bridge |
|---|---|
| `Grid` (earlier), `Coefficients`, `Duality` | Explicit perturbation, preserved missing coefficient, sharp alternation-grid bound |
| `Domain`, `Faithful` | Actual planar sets, polynomial inequalities, interior, radiality, injective observation |
| `Norm`, `Costs`, `Wedge` | Attained geometric infima, exact unchanged prefix, first-drop bounds, actual limiting wedge and representing measure |
| `Moments`, `Obstruction` | Exact double integral, strict positivity, symbolic negative square, exact first failure, no representing measure |
| `Curvature`, `Inertia`, `Hausdorff` | Strict adjacent log-convexity, exact Hankel signature, quantitative geometric convergence |
| `Completion`, `Flow` | Actual graded norm and completion, unique radial-flow extension, trace and Mellin zero divisor |
| `Geometry` | Full theorem and arbitrarily close, arbitrarily delayed obstruction |

## Verification

- All **15 new individual leaf builds** passed. No umbrella or full build was run.
- All **219 new declarations** were audited: 177 theorems and 42 definitions. No missing declarations or unexpected axioms; only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Including the previously audited corpus: **122 chronological leaves, 1353 declarations** (1020 theorems, 333 definitions).
- All leaves are wired into `HTGeometry.lean`; refreshed corpus search retrieves the main theorem. Authoritative `scripts/formal_tools.py lint` passed, with existing file-size warnings.
- No numerical computation or numerical certificate was used. Scratch checks used `lake env lean`; final checks used the individual `lake build GaloisForLFunctions.HTGeometry.ChronologicalTensor.<Leaf>` targets. One earlier scratch/final overlap was corrected; the final audit used one foreground Lean process. No owned Lean process remains.

Audit artifacts: `/tmp/recovery_surgery_geometric_axioms.lean`, `/tmp/recovery_surgery_geometric_axioms.txt`, `/tmp/recovery_surgery_geometric_axiom_summary.json`, `/tmp/recovery_surgery_geometric_index.txt`, `/tmp/recovery_surgery_geometric_lint.txt`.

## Scope and open questions

This closes the full geometric theorem. It does not settle the numerical sign conjecture for the original cubic probe section. Chebyshev interpolation, cusp normalization, moment positivity, Sylvester inertia, Hilbert completion, and the Mellin identity are classical. Novelty and priority of this explicit geometric realization, and whether the broader program merits recognition as a new field, remain unestablished.

Gates: paper proof closed; Lean formalization and complete declaration audit passed; publication and novelty review remain open.

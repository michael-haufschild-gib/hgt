# Route L: complete strict-tail source separation

- **ID:** RH-L-C55a
- **Stage:** 3-formalized
- **Type:** positive source separation and pure-leading domination obstruction
- **Parent:** [Coupled source balance](../1-in-progress/route-l-coupled-source-balance.md)
- **Lean:** `formal/GaloisForLFunctions/RHTower/MobiusThetaStrictTailSourceSeparation.lean`
- **RH status:** UNPROVED; selected fixed-reader agreement remains open.

## Exact statement

For every positive ordinary index `p`, let `q` be the first larger integer with nonzero Möbius coefficient and let `T_(p,m)` be the complete strict Möbius–theta tail at native depth `m`. The forced normalized source

`N_(p,m) = (q/p)^(m/2) T_(p,m)`

converges weakly to zero in the actual source Hilbert space, while

`‖N_(p,m)‖ → ‖μ(q) Θ‖ > 0`.

One fixed projection `Q` onto the orthogonal complement of the leading Xi source `Θ` satisfies

`Q Θ = 0`, and `‖Q N_(p,m)‖ → ‖μ(q) Θ‖`.

Consequently the complete strict tail eventually lies outside the leading source line. For the actual countertransported pre-tensor Gamma-six source `S_m = L_m + T_m`, including its forced half-density, `Q L_m = 0` and `Q S_m ≠ 0` at every sufficiently large honest depth. There is no real constant `C`, even chosen separately at each such depth, for which

`|⟨g,S_m⟩|² ≤ C |⟨g,L_m⟩|²` for every source test vector `g`.

This is a statement about the complete source vectors, not finite head truncations, a Gaussian surrogate, or a divisor-selected source.

## Dependency-closed paper proof

The exact complete-tail successor transport gives `N_(p,m) = U(-a_m) R_(q,m)`, with `a_m = m log(q/p)/(2π) → +∞`. The established full residual convergence is `R_(q,m) → μ(q)Θ`. Translation is unitary, so its error after translation has the same norm and tends to zero.

For arbitrary fixed Hilbert vectors `g,f`, Plancherel identifies `⟨g,U(-a)f⟩` with the Fourier integral of the product `conj(Fourier(g))*Fourier(f)`. This product is integrable by the L² product theorem. Riemann–Lebesgue therefore makes every fixed correlation vanish as `a → +∞`. This proves weak convergence of the actual normalized tail after adding the norm-small translated residual error. Unitarity proves its norm limit, which is strictly positive because the successor Möbius coefficient and Xi source are nonzero.

Projection onto the leading line has the exact coefficient `⟨Θ,N⟩/‖Θ‖²`, hence tends strongly to zero. The reverse triangle inequality then transfers the normalized tail's norm limit to its orthogonal complement. Positive limiting norm gives eventual nonzero projection; a vector in the leading line would have zero projection.

At Gamma-six, apply the same fixed projection to the exact leading-plus-complete-tail decomposition. It kills the leading term and preserves a nonzero component of the strict tail because the original half-density is positive. Let `g=Q S_m`. Orthogonality gives `⟨g,L_m⟩=0`, while the projection identity gives `⟨g,S_m⟩=‖g‖²≠0`. This contradicts every proposed pure-leading quadratic domination bound. The nonzero projected source and its exact normalized norm limit are the positive survivor.

## Role in the reader-agreement attack

The chain remains complete original source → fixed physical-reader agreement → conormal vanishing → RH. Existing fixed quadratic combinations of the two scalarized boundary channels have only one source direction. C55 tested whether retaining the actual strict tail supplies another direction before divisor selection; this theorem answers yes.

The projection is fixed in the canonical countertransported source space. It has not been identified with the prescribed physical reader at its original horizontal anchor. The theorem gives neither equality of the cyclic and physical readers nor physical-boundary vanishing. A joint-channel comparison still needs an actual complementary environmental map, a separately derived domination bound there, and exact transport back to the selected physical reader. Using the full pure source itself as that environment fails by the proved separation.

No route is retired on this basis. The obstruction concerns domination by the pure leading source; it leaves independently constructed mixed environmental states and source-forced nonlinear comparisons open.

## Corpus and proof optimization

The parent card records five whole-corpus deep searches, all 100 returned candidates and 100 source methods, proposed ingredient groups, partial coverage, and the symbolic applicability check of the September 2026 broad arXiv result. The actual proof uses the existing complete-tail successor transport, full residual limit, Fourier–Plancherel translation, and the installed Riemann–Lebesgue and orthogonal-projection theorems.

Direct projection elaboration on the concrete source exceeded the default heartbeat budget. A general Hilbert-space projection-limit lemma with explicit scalar and vector limits removes that elaboration bottleneck. No heartbeat or recursion option is raised. The only code change after the successful scratch check removes one unused simp argument.

## Validation

- `lake env lean /tmp/route_l_tail_escape.lean`: exit 0; nine public theorems, two public source definitions, six private proof lemmas, and one private shift definition.
- New module wired into the RHTower umbrella; umbrella not built.
- `lake build GaloisForLFunctions.RHTower.MobiusThetaStrictTailSourceSeparation`: exit 0; named leaf built in 98 seconds, with dependencies replayed from cache. No full or umbrella build.
- `scripts/formal_tools.py lint`: exit 1; reported unrelated unreachable `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentFundamentalFactor`. No error reported for this module.
- The completed module contains no resource-limit overrides.
- Fresh lexical corpus search finds the new normalized-source definition and both main limit theorems. Its JSON omits compiler metadata, so this is source discoverability verification only.
- No numerical computations, axiom-print audit, new axioms, or unresolved proof placeholders.

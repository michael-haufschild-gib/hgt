# Literature capstones: facts

## Closed in Lean

- **Toeplitz:** PSD data admits exact nonnegative unit-circle atomic Vandermonde factorization.
- **CCM:** formal Lambert and finite normalized-determinant coefficients lie in `ℤ^cyc[1/2]`; no convergence theorem.
- **Burnol:** literal Riesz zero jets are complete iff aperture `a ≥ 1`; cosine closure detects exact completed jets.

## Q8 capstone

- SST field `N/ℚ`: `Gal(N/ℚ) ≃ Q8`; faithful irreducible `2D` representation; dyadic Artin conductor `6`.
- `N` is totally real.
- Every finite prime ramified in `N/ℚ` lies over `2`, `5`, or `41`; relative ramification is forced by the exact derivative `2z` and source norm `1025=5²·41`.
- Maximal abelian field `K=ℚ(√5,√41)`; `disc(K)` is supported on `{5,41}`.
- `D₅=I₅=Stab(√41)` and `D₄₁=I₄₁=Stab(√5)` are `C₄`; `P₅=P₄₁=1`.
- Actual `5` source/inverse have conductor `5`, literal Tate equations, unit phases, product `−1`.
- At `41`, direct `C₄→F₄₁×` pullback has exponent `≤2`. Reverse `F₄₁×→C₄≃I₄₁` is surjective and preserves both literal Artin eigenchannels.
- Actual `41` source/inverse have conductor `41`, literal Tate equations, unit phases, product `+1`.
- At `2`, every primitive quadratic conductor-`8` pair has phase product `χ(-1)`; parity uniquely selects `χ₈` (`+1`) or `χ₋₈` (`−1`).
- For every dyadic `E/K`, `E⊗_KN ≃ E[ω]/(ω²−δ)` and `u` is its determinant algebra norm, via `a²=u+δ(u+1)²`.
- The completed decomposition involution fixes each contracted dyadic prime and sends `u↦1−u`; hence the actual selected total local norm is `u(1−u)=−1`.
- Pinned Lean CFT supplies actual finite local Artin reciprocity, kernel = local norms, and concrete finite-place tensor-norm comparison.
- The completed Hensel witness is unit-valued; its norm `u` has trivial actual finite-place Artin symbol for `N/K` at every dyadic `K=ℚ(√5,√41)` place.
- Over `S=ℚ(√41)`, `u` has minimal polynomial `X²−X−1`; hence `N_{K/S}(u)=−1`.
- At `2`, source primes have `e=f=1` over `ℚ`; completed lower groups are `C₂` at `0,1,2`, then `1`; upper groups satisfy `G²=C₂`, `G³=1`; local conductor is `8`. Genuine filtered reciprocity transports a central depth-`2` witness to `ℤ₂ˣ`; the resulting modulo-`8` character is exactly even `χ₈`. Actual source/inverse Tate epsilon product is `+1`.
- Fröhlich 6(i)'s hypothesis holds; wild `2` is permitted; `α_Kβ_K=−1`.
- Specialized global Artin epsilon/root number is the actual source-channel Tate product: dyadic radial-independent, unit off `{2,5,41}` and at infinity, equal to `−1` and Fröhlich's sign.
- **Open:** construct the completed Artin `L` analytic family with this root number and its functional equation.

## RH frontier

- **RS phase audit:** Lean proves independent-circle log means only. Actual `Z=A+R`; dropping `R=O(t^-1/4)` in logarithmic averages requires a near-zero estimate. `(L): Σ mρ(β−1/2)⁺=o(T)` is an RH consequence, not an established equivalence; finite exceptional mass survives while its height-normalized value vanishes. Card/map corrected; no RH gate closed.
- **TCD:** actual `D1>0` remains open only for `0<x<137/2000`; generic/static Hankel, positive operator, and contravariant carriers are closed no-gos.
- **TCD scratch:** all 25 coefficient identities, box-polynomial positivity, and physical-orbit admission pass Lean. Rational recurrence maps to literal complex source; integer jets satisfy `Jₙ=8ⁿfₙ`, determinant scales by `8¹²`. Box/source polynomial identity remains unverified; normal forms checked through jet 3. No RH gate closed. Card: `theta-d1-refined-parabolic-box.md`.
- **C5:** exact orientation is derivative of normalized shifted `2×2` reflected minor; positive near seam and cofinally, compact actual-orbit sign open.
- **D1--C5 weld no-go:** source-positive seam `X=100` has `D1>0`, C5 orientation `0`, and C5 Lie derivative `<0`; any common producer must use actual theta-orbit dynamics.
- **C5×D1 dynamic weld:** `A²D1 + LΩ′ = R₇`; corridor is exactly `(C5 slope>0) ∧ (D1>0)`, hence circular and not a producer.
- **Suzuki:** actual CCM chord and Suzuki current are real/imaginary polarizations of one wall Gram; fixed-scale/head/bounded/sublinear corrections cannot semibound Ward defect. Live source needs unsummable signed atomic--continuous relative assembly before scalarization.
- **E×Gamma lcm:** distinct coprime Kloosterman columns have zero complete product-period correlation; every incomplete interval is exactly a residue-discrepancy boundary. Gamma pair weight stays positive, but synchronized `p*r` completion kills its cross-prime current. Live weld requires incomplete product-shell boundary control; complete lcm synchronization is terminal.
- **F2 scoped retirement:** Lean proves `¬ SoninAllPrimeExactTraceMomentWeld`; fixed-positive-aperture coupled-column exact matching also impossible. Both literal regularized assemblies have coefficient-faithful prefix `≤8‖Jₐ‖₁(1+log(N+1))+sqrt(512a²)`. Exact moments would force the multiplicity-exact Xi sequence with positive `log²` residue. Ordered moment determinacy closes the chain without misusing unsquared determinants. Nine source modules plus one standard moment lemma wired/audited. Principal Euler channels, projective/escaping-aperture variants, STC and CSB cofinal comparison remain outside the result. RH unproved. Card: `../../../3-formalized/sonin-regularized-spectrum-growth-firewall.md`.
- **C1 scoped retirement:** actual global-mean polarization has nuclear positive square root. Lean excludes its exact completed prime--Gamma moment landing with literal factor two, via doubled singular enumeration and ordered moment rigidity. Bounded nonlocal root mixing also fails. Positive survivor: coefficient-faithful prime/depth root-incidence budget. Five modules wired/audited; individual checks and lint pass. First-trace mismatch alone remains open; wider class-space/Weil C1 is not retired. Card: `../../../3-formalized/c1-global-mean-nuclear-root-firewall.md`.
- **Cofinal moment cost:** full Xi moment convergence forces nuclear-amplitude mass `Σ s_k(A_N) → ∞`, even with changing carriers; half-normalized landing retains both reflection copies. Every fixed root budget has a finite moment/error obstruction. Fixed nuclear source mixing must have `‖B_N‖‖C_N‖ → ∞`. Bounded energy trace alone is not excluded. Kernel-checked/wired; standard-axiom audit and lint passed. Classical compactness bridge, not a new RH architecture. Card: `../../../3-formalized/xi-moment-landing-root-budget-escape.md`.

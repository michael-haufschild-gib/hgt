# PW-B cross-clock source has unavoidable cusp mass

- **ID:** PWB-cross-clock-source-mean
- **Stage:** 1-in-progress
- **Type:** THEOREM (principal, mean/error transport, log-clock identity/nonresonance, normalized error `L¹`, translated principal/error tests Lean-closed; adjoint residue pending)
- **Chain:** literal complementary CTP legs → forced clock-`−6` metric/contact → ordered noncompact boundary current → oriented optical incidence → PW magnitude/extinction → RH.

## Statement

**[BRIDGE]** For every hypothetical left-half Xi copy, the actual two-branch particular cusp product has a nonzero normalized upper-cusp limit:
`(y:ℂ)^(-2p) · cuspResponse(q,true,[0,y]) · cuspResponse(q,false,[0,y]) → C_true C_false ≠ 0`, where `p=2−2q`. `ThetaCuspHawkingBMPWCrossClockPrincipalGrowth.lean` proves the actual source substitution and coefficient nonvanishing. `ThetaCuspHawkingBMPWCrossClockMeanEquation.lean` proves the exact periodic product mean equation `y²h″−20h=d`; `ThetaCuspHawkingBMPWCrossClockMeanError.lean` transfers the native weighted `L¹` cross-error into the full-width high-cusp mean. `ThetaCuspHawkingBMPWCrossClockLogIdentity.lean` proves exact conjugation to the constant-coefficient log-clock operator, the actual nonzero principal limit in log height, and nonresonance of its scalar multiplier. `ThetaCuspHawkingBMPWCrossClockLogError.lean` closes the exact `L¹` log change of variables for the full-minus-principal mean. `ThetaCuspHawkingBMPWCrossClockTranslatedTests.lean` proves that translated cusp-window pairing kills the actual correction and retains `C_true C_false` times positive window mass for the principal product. No pointwise limit for the full response is asserted. The remaining gap is second-order adjoint transposition and its contact-class obstruction.

Fix `q : XiZeroCopy`. Let `U_b=fullAngularField q b`, `H=U_true U_false`, `D=(Δ−20)H=crossBranchClockForcing q`, and `β=sourceGrowthExponent q∈[1,2)`. Select the extreme cusp index `i*=0` when `Re q≥1/2`, otherwise `i*=2`; put `p=sourcePower q i*` and `C_b=responseCoefficient q b i*`. The corpus implies `Re p=β` and `C_true C_false≠0`. Write `h(y)` and `d(y)` for the width-one horizontal means of `H` and `D`.

For any smooth compactly supported `φ:(0,∞)→ℝ` with `∫φ=1`, set `φ_T(t)=T⁻¹φ(t/T)`. The following **canonical renormalized source residue** is independent of `φ`:

`lim_{T→∞} ∫ φ_T(t) exp(−2p t) d(exp t) dt = ((2p)(2p−1)−20) C_true C_false ≠ 0`.

For the off-critical left-half contradiction needed by RH, a simpler stronger local probe suffices: any fixed smooth compact `ψ` with `∫ψ=1`, translated as `ψ(t−T)`, has the same source-residue limit. This avoids expanding-window derivative estimates; its Lean proof remains open.

Consequently, for every `α` with `β≤α≤2β−1`, `∫₃^∞ |d(y)|y^(−α−2)dy=∞`. Neither `D` nor its coexact covector can equal a scalar/coexact contact whose cusp mean is in this weighted `L¹` class. This includes any `L²` cusp contact or contact with mean `O(y^β)`, such as any finite square-scale source combination. A renormalized noncompact ordered current remains possible.

## Paper proof

On `y>3`, the corpus gives `U_b=K_b+R_b`, with `K_b(y)=cuspResponse q b ![0,y]` an exact three-power sum of exponents `2q,1,2−2q` and `R_b∈L²(dx dy/y²)` on the width-one modular cusp. The extreme coefficient is `C_b=(parameter_b/2) sourceCoefficient_i*/denominator_bi*`. Both branch parameters and denominators are nonzero. The extreme Weyl coefficient is nonzero by the corpus's zero-free-side laws for `Λ(2q)` (`Re q≥1/2`) and `Λ(2q−1)` (`Re q<1/2`). Hence `C_true C_false≠0`. Periodic horizontal averaging kills the horizontal second derivative exactly, giving `d(y)=y²h″(y)−20h(y)` in Lean.

Put `t=log y`. For the selected `p`, the principal product has

`exp(−2p t) K_true(exp t) K_false(exp t) = C_true C_false + Σ_j c_j exp(δ_j t)`, 

where every other `δ_j` has negative real part off the critical line. On the critical line they are nonzero imaginary multiples of `Im q`; the nonzero ordinate makes them distinct from zero. In both cases their `φ_T` averages tend to zero (dominated convergence or one integration by parts).

The response error `E(y)=h(y)−K_true(y)K_false(y)` satisfies `∫₃^∞|E(y)|y^(−β−2)dy<∞`: `|K_b(y)|≤C y^β`, the cusp cell has finite hyperbolic volume, and Cauchy–Schwarz handles the two `K R` and one `R R` terms. Because `2β≥β+1`, `exp(−2p t)E(exp t)∈L¹(dt)` on `t≥log 3`; its `φ_T` average is `O(T⁻¹)`. Thus `f(t)=exp(−2p t)h(exp t)` has `φ_T` average tending to `C_true C_false`.

Smoothness and periodicity give `d(y)=y²h''(y)−20h(y)`. With `r=2p`, the Lean-closed log conjugation gives

`exp(−r t)d(exp t)=f''(t)+(2r−1)f'(t)+(r(r−1)−20)f(t)`.

Integrate against `φ_T` and transfer both derivatives to the compactly supported test. The principal finite exponential sum is bounded after the normalization; the remainder is `L¹`. Since `‖φ_T'‖∞=O(T⁻²)` and `‖φ_T''‖∞=O(T⁻³)`, both transferred derivative terms tend to zero. This proves the residue formula. Its scalar multiplier is nonzero: `r(r−1)=20` has only roots `5,−4`, while `Re r=2β∈[2,4)`.

Off the line, the normalized principal product actually tends to `C_true C_false`. For a fixed translated compact `ψ`, integration by parts gives the adjoint test `ψ''−(2r−1)ψ'+(r(r−1)−20)ψ`. The principal term tends to its constant limit, with `∫ψ'=∫ψ''=0`; the `L¹` correction vanishes on the translated support. Thus the same nonzero charge follows without Cesàro scaling. This is the shortest Lean target for excluding off-line copies.

If `d` were in `L¹(y^(−α−2)dy)` for `α≤2β−1`, then `exp(−r t)d(exp t)∈L¹(dt)`, since `α+1≤2β`. Its `φ_T` average would tend to zero, contradicting the nonzero residue. If `coexact D=coexact T`, connectedness makes `D−T` constant; a constant has weighted-integrable mean. `L²` contacts also have weighted-integrable means by Cauchy–Schwarz and finite weighted cusp volume.

## Route consequence and audit

The nonzero residue is the positive survivor of the finite-energy/square-contact no-go. It strengthens the earlier nonzero-forcing and constant-square-separation paper proofs and identifies an explicit source charge that a viable noncompact boundary current must transport or cancel. The charge is not yet ordered; it is not a CTP/current equality or an RH proof.

Corpus dependencies checked: `ThetaCuspHawkingBMLiteralCyclicPeierlsCrossBranchBidegree` (exact clock equation), `ThetaCuspHawkingBMMixedParticularCuspFlux` (three-power coefficients and nonresonance), `ThetaCuspHawkingBMGlobalSmoothResponse` (actual `L²` remainder), `ThetaCuspHawkingBMFullSourceCircleGrowth` (`1≤β<2`), and the zero-free-side coefficient laws used in `pwb-cross-branch-clock-forcing-own.md`. `ThetaCuspHawkingBMPWCrossClockResidueCore.lean` closes all-copy coefficient nonvanishing. The principal, sharp-growth, weighted-`L²`, cross-error, exact mean-equation, native-to-mean, log-clock, normalized error `L¹`, and translated principal/error test leaves pass direct Lean and exact-module `lake --old build`; all are umbrella-wired. A generic compact whole-line double integration-by-parts theorem passes scratch Lean (`/tmp/PWIBPScratch.lean`), but its actual normalized-mean/window instantiation, source-charge limit, and weighted contact obstruction remain open in Lean.

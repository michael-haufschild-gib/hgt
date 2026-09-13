# Computation-derived facts

Compact interpretation ledger. `[proved]` means a paper/Lean argument was reconstructed independently of numerical output. `[certified]` means rigorous finite numerical bounds. `[observed]` means finite numerical evidence only. `[rejected]` means the stated mechanism failed; scope is exactly the named mechanism. `[exact candidate]` means exact symbolic/rational output awaiting independent proof. Slash-separated labels distinguish components of one claim. Run logs, provenance, and performance are omitted.

## Global constraints

- An exact finite counterexample can falsify a universal inequality. Finite computation can also locate dangerous faces and expose candidate exact identities; it cannot prove cofinal no-escape, all-order positivity, common-zero landing, or RH.
- Positive signs from floating-point scans remain conjectural. Near clustered atoms, high Hankel rank, large theta action, or tiny Galerkin energies, low precision routinely creates false negative eigenvalues/signs.
- Exact algebra discovered numerically is usable only after independent symbolic proof. Several such survivors below are now Lean-checked.
- Repeated lesson: scalar, diagonal, pointwise, fixed-block, or fixed-order control usually deletes the mixed cancellation carrying the actual source.

## Completed-theta C5 / CLG–TTF

- `[observed]` Literal completed-theta C5 stayed nonnegative on all tested domains; its only observed tight limit is coalescence `t→0`, with margin of order `t⁴`. The safe mechanism is cumulative compensation in the hard negative-elasticity chamber, not nonnegative elasticity.
- `[observed]` Completed-theta Bezoutian sections were positive through rank 20 after precision escalation; tiny high-rank eigenvalues reflect analytic-kernel conditioning, not detected sign failure.
- `[observed/rejected]` Numerics found no total-positivity violation through order 4 and a robust failure at order 5. Rank-≤4 C5 structure lies inside the observed free TP range; no `TP_m` mechanism with `m≥5` can close higher packets.
- `[observed]` Li coefficients stayed positive through degree 300; shifted zero-moment Hankel and support-side matrices stayed positive through size 12. High precision is mandatory because atom clustering creates false negative signs.
- `[rejected]` Endpoint-ratio confinement, local log-concavity, Riccati positivity, and positive finite theta-atom mixing do not imply C5: admissible 2–4 atom mixtures give negative balance. Exact modular coefficient coupling is essential.
- `[observed]` At fixed action, the direct transverse C5 Jacobian stayed positive. Reflection gives exact seam zero; the correct target is the desingularized sign `J(u,t)/u`, not the raw Jacobian at `u=0`.
- `[exact candidate]` The first nonzero fixed-action seam coefficient is governed by
  `A²D−18A³C+36A²B²−5ABC+4B³`. On the physical scale interval its modular reduction has a positive degree-12 Bernstein representation; the stronger half-line claim is false beyond a root near `X=56.86`.
- `[rejected]` Global center monotonicity of `J/u`, the old two-sign velocity/current split, and separate positivity of the eighth-jet residual block all fail. Compact, seam, and tail regions require signed compensation.
- `[proved]` First-atom base compensation is positive on the same half-line. Its seam margin first appears at order `t⁷` with an explicitly shifted-positive degree-7 polynomial. Termwise sign of the intermediate `P₂` polynomial is false.
- `[observed]` Modular-center C5 velocity stayed strictly positive from seam to far cusp; no stationary point was detected. Direct radial monotonicity is a stronger surviving target than stationary-locus reserve accounting.
- `[rejected]` Likelihood interpolation is not monotone: `M'(λ)` has both signs and interior margins can be below both endpoints.
- `[observed]` Likelihood compensation instead appears convex. Sharpened candidate: `M'''(λ)>0`, `M''(0)≥0`, and atom-tangent reserve `M'(0)≥−M(0)/5`; these imply full-tail positivity. Direct falsification tests found no failure and show higher-atom corrections are perturbative on the structural tail.
- `[proved/observed]` The seam germ of `M'''` reduces to the source inequality `F₂F₅−2F₃F₄>0`. A sufficient split is `3AF₂<−F₃` and `−F₅<6AF₄`; the first is proved, the dominant `n=2` reserve for the second is an explicit shifted-positive degree-9 polynomial, and sampled higher-atom opposition is tiny. Generic moment/log-convexity proofs fail.
- `[rejected]` Positive likelihood-jet signs plus existing pairwise tangent bounds do not imply atom-tangent reserve. The saturated adverse vertex is genuine. Surviving source information includes non-saturation coupling, the favorable third likelihood channel, and proved mixed trapezoid law `dm≤t·dn`.
- `[rejected/proved]` Lower-jet, master-reserved, and adaptive-reserved endpoint margins become negative near the collapsed seam. The adaptive margin has exact fifth seam derivative `600κ²(F₃+2AF₂)<0`; deleting the third-channel cooling excess destroys the needed cancellation.
- `[proved]` For normalized homotopy coordinates `b,r,s,h`, complete curvature balance is
  `(b²−1)[12(r−b/2)(s−b/2)−1]+3h[(6+4b)r−2(b²−1)]`.
  Hence the exact required curvature threshold is explicit; positivity of `h` alone is insufficient.
- `[rejected]` Even fixed mass, support gap, conditional first moment, and positive lower-transport curvature do not force the enlarged-source compensation inequality: a remote escaping atom makes compensation negative while preserving those data. Fixed first moment permits unbounded second moment.
- `[proved]` Holding the retained mixed coordinate `κ=s−r+h/(2r)` fixed, the curvature coefficient is positive because its quadratic `Q` has an exact square decomposition. This is coordinate monotonicity, not theta-source monotonicity.
- `[rejected]` Scalar center-independent damped Fourier corrections have incompatible required signs at different centers for tested dampings. Sufficiently fast damping fails analytically because its correction vanishes inside the formally negative native rank-three chamber; sufficiently slow damping also cannot close the zero-mass proposal. A full center-frequency flux still needs the signed positive-vs-negative mass comparison.
- `[observed]` A fixed canonical even correction and both endpoints of its coefficient band stayed positive on the tested middle interval, including complete entry/correction error majorants. Uniform signed interval control remains open.
- `[proved]` Exact moment identities, Horner/block incidences, and positive lower/remainder pieces of the compact even determinant are checked; the original-coordinate full determinant incidence is the remaining proof bottleneck. Generated coefficients are not premises.

## S6F / reflected rank-three geometry

- `[observed]` Actual physical rank-three determinant D1 stayed positive on the compact missing orbit interval with a large margin. Nearby seam scale alone does not force this: other initial scales fail later.
- `[proved/exact candidate]` Actual theta dynamics lie in a proved compact tube with `A>17`, controlled `−S`, and controlled `W`. Exact polynomial candidates are positive on the larger box `−1≤S≤0`, `A≥17`, `0≤W≤6/5`; finite-order closure does not imply an all-degree Xi producer.
- `[observed]` Direct D1 positivity is stronger and cleaner than projective-drift positivity on the physical cone. Scale variation is increasing/convex; clock-square variation is concave with positive third derivative. Alternating derivative hierarchy fails at fourth order.
- `[rejected]` Global wall monotonicity, upper-wall clock monotonicity, raw D1 monotonicity, simple factorization, and complete monotonicity are false or unavailable.
- `[observed]` After scale increase and clock concavity, D1 reduces to seam positivity plus one decreasing univariate outer face and its upper-corner value. This is the smallest surviving finite-gate architecture.
- `[observed]` Projective drift is inward at the seam and positive away from it on tested boxes, but raw D1 is unimodal rather than monotone. Local nonzero projective jets alternate `+,-,+`, so absolute monotonicity is false.
- `[proved]` Source dynamics contain an exact `sl₂` triple; physical scale differentiation is its Cartan derivative. This is the natural structure for a finite contravariant/Loewner proof.
- `[rejected]` Raw coefficientwise matrix-Bernstein positivity fails although the assembled derivative matrix appears positive definite; cancellation between scale layers is essential.
- `[observed]` On the refined cone, all tested principal minors of the scale-velocity Hankel matrix are positive, selecting strict Loewner increase as a candidate mechanism.
- `[rejected]` Full Bochner/positive-definite completion of the reflected theta fibre fails at six points. Positive definiteness survived all tested packets through five points. Thus use finite-order-5 or direct rank-three geometry, not an all-order measure representation.

## Weil forms, lag functions, compact locking, and HCF

- `[certified]` The pole-constrained restricted Weil form is positive through support length `S=1` (`λ≤√e`); certified ground lower bounds include about `0.518` at `S=log 2` and `0.0014` at `S=1`.
- `[observed]` At aperture `λ=√2`, constrained ground energy is about `0.547`, versus unconstrained `1.33·10⁻³`. Resolved positivity persists to about `λ=2.1`; no sign-changing aperture appears up to `λ≈5`, but later Galerkin values are only upper bounds and decay super-exponentially.
- `[observed]` Archimedean-only constrained form becomes indefinite near `λ=1.8145`; each omitted prime power becomes decisive shortly after entering. Prime contributions have no fixed sign and must conspire collectively.
- `[observed]` Both constrained and unconstrained ground-state Fourier zeros lock onto low zeta ordinates as aperture grows; pole directions accelerate locking but do not cause it. Extra interlacing zeros eventually appear from exponential-type counting.
- `[observed]` Compact-Weil ground states lock one transform root to each low ordinate, but close pairs eventually merge while scalar ground energy barely changes. Pre-collapse root error scales approximately as separation `δ⁻³`; multiplicity control needs a Hermite/divided-difference channel.
- `[proved]` Two point-sampling energies split exactly into average and antisymmetric channels; the antisymmetric channel vanishes quadratically at collision with limit controlled by the derivative norm.
- `[observed]` Ground autocorrelation monotonicity and post-first-atom cumulative prime–polar positivity survived finite Galerkin tests, while pointwise positivity of the completed error is false by known oscillation. Any proof must use ground-selected averaging of the sign-changing error.
- `[proved]` Published finite restricted-Weil matrices form an exact nested principal tower. Missing connector is convergence from those source matrices to the abstract Laurent/Galerkin compression.
- `[observed]` Fixed-pole parity energies stayed positive for `0<a≤8`; normalized margins oscillate around the sharp mass `2+γ−log(4π)≈0.04619`, with zero asymptotic margin. Any prime-side proof must reach that exact constant.
- `[observed]` Integer lags through `2·10⁷` remain far below the RH ceiling: maximum about 40% of it. Conditional recurrence to the ceiling is therefore extremely slow at accessible scales.
- `[observed/proved]` Prime-truncated lag positive-definiteness fails a few hundredths past the first omitted prime-power lag. Under RH, continuum positive-definiteness pins every prime-power position and weight exactly: any nonzero single-kink perturbation creates negative high-frequency directions.
- `[observed]` Arithmetic Gram least eigenvalues scale approximately `c/N`, `c≈0.09–0.10`; top eigenvalues scale as `N/(1/4+γ_j²)`. Finite PSD tests are insensitive to sufficiently high off-line zeros until matrix size is roughly square-root in zero height.
- `[observed]` Full infinite-lattice HCF receiver capacity improves the three-center threshold only from about `0.3437` to `0.3821`; receiver optimization is not the active bottleneck.
- `[rejected]` Scalar signed separator mixtures suppress off-diagonal response only outside a collision radius, with coefficient norm and negative lobe exploding as radius shrinks. Uniform HCF needs matrix/source cancellation or zero spacing.
- `[rejected]` Fixed-degree gamma-cell factors add only `O(T)` mobile off-line zeros versus zeta's `T log T`; they are finite-height falsifiers, not asymptotic density obstructions. Genuine adversaries need `N(T)`-scale mobility.
- `[rejected/observed]` Even positive strictly log-concave kernels can have negative rank-three packets; FE-symmetrized atoms can have off-axis zeros; finite causal/symmetric Volterra truncations were indefinite. Classical Laguerre wall jets `L₁,L₂` stayed positive, but close-pair failure is invisible to pointwise wall jets.
- `[observed]` Multi-band isolated-zero ladders did not hide energy materially better than one chirped band; this does not prove the full isolation law.
- `[proved/observed]` Uniform damping gives an `n`-uniform exponential floor; data suggest a sharper scale polynomial in `K/g` for `K≲g`. Gram/Ingham bounds alone do not resolve wide real-part spreads.
- `[rejected]` At actual Weil prime-power entries, many barrier jumps are negative and continuous convex growth alone cannot pay all losses. Positive jump credits are essential in the exact signed balance.

## C1, JAS, and T2 route triage

- `[rejected]` Current C1 global-mean scalar carrier misses the theta target by a stable margin of about 32%. An exact head/tail separation should retire this carrier; other possible C1 carriers are unaffected.
- `[rejected]` Flat prime-insertion cocycle integrates only to nonunitary diagonal similarity. Unequal apertures have no tested finite `*`-intertwiner; any surviving sewing needs a defect/environment, changed inner product, or non-diagonal coupling.
- `[observed]` Mixed prime-character/completed-theta packet Grams stayed independent through 10 primes (matrix size 1024). Scalar Gamma aperture weights cancel from normalized Grams, so they neither select critical wall nor improve conditioning.
- `[rejected]` Reciprocal bilateral scalar completion has primorial-scale growth; no fixed exponential gauge moderates it. A surviving bilateral construction needs different topology or a non-scalar defect channel.
- `[rejected]` Current T2 finite-shell interfaces miss required exponent even with prime-gap exponent `13/25`; generic `L²/L⁴`, buffered-gain, physical-slice, and reciprocal-tail repairs do not close it.
- T2 survivor requires both target-reciprocal localization `s+g≤1` and a genuinely arithmetic selected-cell/bad-set estimate across all paired low shells.

## Route J semilocal Jacobi response

- `[observed/proved]` One-prime deformation becomes order one near degree `n≈p`, far before the fixed first-jet scale `p²`. It collapses as `D_k(1/p)=p^{-1/2}Φ(n/p)+O(p^{-1})`.
- `[proved]` Universal profile is
  `Φ(x)=4√(2/π)[√x cos(4x)−8x^(3/2) sin(4x)]`, derived from Meixner–Pollaczek/Jacobi boost matrix elements and formalized as a scaling theorem.
- `[proved]` Fixed-frequency beat response has an explicit oscillatory `k^(3/2)` asymptotic; a uniform two-index law contains both beat and one-prime limits.
- `[rejected]` Two primes do not superpose. For comparable primes, pair cross terms dominate single-prime effects and equal the linear response to beat frequency `log(p₂/p₁)` to high accuracy.
- `[proved]` Two-mode determinant response is beat jet plus sum-mode jet minus truncation defect; explicit boost-entry bounds control the defect. One-prime quadratic response is `O(p⁻²)` and finite-set second order contains only one- and two-prime terms.
- `[proved]` True finite Euler-product log determinant has a second-order expansion with explicit cubic remainder. Current bound uses an entrywise norm that is too large; an `n`-uniform operator-norm refinement is missing.
- Finite-prime analysis must assemble Euler product first and organize around pairwise log-ratio beats; fixed Euler jets or independent one-prime boundary layers are not valid building blocks.

## CCM-FU signed divisor energy

- `[observed]` Diagonal dominance `S²≤Q` survived every cutoff through `2,097,152`; `[proved]` diagonal energy has exact update law and unconditional bound `Q(M)≤722M²`. The required nonpositive total off-diagonal sign remains open.
- `[rejected/proved]` Every-step energy contraction fails already at `M=5`; every-order nonincreasing paths fail at `M=7`. A local increase can still remain below the original diagonal, so contraction and ceiling are distinct.
- `[observed]` Original-diagonal ceiling survived finite exhaustive path searches through 32, greedy paths through 1024, fixed-late policies through 32768, and joint-prime policies through 8192. None gives all-cutoff control.
- `[observed]` Exact successor-envelope extension, least-energy successor selection, negative-support selection, and two-step repair after any prescribed prime all succeeded on complete subset cubes through 32; final-overlap states through 1024 also extended. These select concrete conjectural policies, not generic signed-field theorems.
- `[rejected]` Homogeneous descent of the geometric certificate, logarithmically averaged successor slack, uniform averaging of successor envelopes, and pointwise prime-2 envelope monotonicity all fail. Successful selection must retain prime-specific signed interactions.
- `[rejected/proved]` Simultaneously requiring nonempty-energy dissipation and envelope admission has a unique reachable trap at `M=25`; head-square release pays forced transverse growth. Generic sharp next-step bound is `V_next≤3V/2`.
- `[rejected/proved]` Keeping every nonempty fibre nonnegative fails from `M=21`; at least one moving defect is necessary. Exact defect-triangle and mixed-transverse compensation results capture the positive survivor.
- `[observed]` A fixed potential `V+αH²` admits complete monotone paths through 32 for `0≤α≲0.201`, but no fixed `α` gives a good next move from every state. Path existence is weaker than local extendability.
- `[rejected]` Binary gcd packets and individual exact-gcd groups need not be nonpositive. Compensation crosses distinct gcd classes.
- `[rejected]` Positive exact-gcd mass is not bounded by diagonal with constant one; complete signed cross sums nevertheless remained negative at all tested cutoffs. Preserve `S²=D+P−N` and bound `P−N`, not `P` alone.
- `[observed]` One-prime adjacency flow compensated positive gcd mass at tested cutoffs, but shared negative-neighbor capacity, not isolated vertices, controls the residual. Möbius parity-class balance alone is insufficient because graph neighborhoods restrict access.
- `[rejected]` Coarea mass-envelope greedy paths, coupled-sector steepest paths, and the proposed unit transverse budget fail at growing cutoffs. Local pair variance or average cancellation does not prevent coherent amplification.
- `[rejected/proved]` Advancing retained prime front can increase transverse energy even with small receiving coordinates. Child-inactive helper blocks commute exactly with later transverse costs, so head balancing cannot change the sign of those gains; a cumulative budget is required.
- `[rejected/proved]` Increasing middle-prime order exceeds original diagonal even after all fixed scalar reserves are removed. Analytic nested child-head amplification defeats every fixed quadratic ceiling uniformly over fixed scalar-reserve choices; adaptive orders remain open.
- `[observed]` Fixed small cores contain many asymptotically energy-increasing edges, including parents still far below original budget. This points to signed dilation correlation rather than local reserve.
- `[observed/proved]` Joint two-prime selection exposes a real middle/late amplitude window: both first moves may increase while their common endpoint compensates. Exact continuous optimum is classified; existence of an unused prime in the needed window at every stage is open.
- `[observed]` Coupled head/prime-2 source profiles admit positive zero-sum circuits; a `2,11,15` circuit also removes inherited prime-2 debt. Uniform capacity and complete exhaustion remain open.
- `[rejected]` Independent Bernoulli half-selection eventually has mean-head square above original diagonal; zeta-pole analysis gives the analytic obstruction.
- `[proved]` Literal unsigned channel orientation and square-root lower bound hold independently of the finite positive scans.
- `[rejected]` Ordinary decreasing weights, prefix-by-prefix positive pairings, and geometric/Laplace component positivity do not prove the source bound. Exact Abel representation as a mixture of prefix channels survives.
- `[rejected]` Blockwise feedback, uniform merge contraction, pointwise block contraction, and a fixed average decrement across scales fail. Literal source has aggregate cancellation plus locally coherent deficit clusters; no dependency-closed positive salvage was found.

## EDQ complete covariance

- `[observed]` Complete reciprocal flux was positive for every cutoff `2≤N≤512`, but positivity alone gives no subpower upper bound.
- `[rejected]` Absolute row variation is not always within four times flux, and the Bernoulli mean profile can miss nearly all row variation. Complete finite head, nonzero Fourier modes, and outer Möbius signs must remain.
- `[observed]` Exact-gcd total variation stayed below four diagonal units in tested raw/tapered sources. Individual groups have both signs; complete-gcd estimates remain plausible, not proved.
- `[rejected]` Separately charging head polynomial and corrected remainder can exceed the same budget even when the signed head/tail budget passes. Retain each head as one signed object.
- `[rejected]` Localization to divisor ratio `≤4`, reduced denominators `2,3`, or temporal radius `≤X` fails. Omitted long-range covariance can be larger than complete energy and restore its sign.
- `[proved]` Reduced-denominator head with denominator `≤B` is uniformly bounded by `B/2`; the missing estimate is the complete large-denominator tail.
- `[observed]` Logarithmic cutoff averaging suppresses measured post-support error but not at the preregistered strong rate; available omitted-tail bounds are too loose for a full comparison.
- `[rejected]` Choosing cutoffs by minimum harmonic head does not suppress complementary tail: roughly half or more lies in the first block. Exact first-tail source is `nH_N+M(n)−M(N)`.
- `[rejected]` Minimizing the all-gcd head polynomial does not consistently minimize full residue energy; the linear unit-source cross term changes finite rankings. Formal all-gcd subpower remainder remains valid but does not control complete tail.

## Chronological approximation and tensor capacity

- `[observed]` Bounded coefficient repair can reduce finite heat residuals by many orders. Rewriting nonsquarefree coefficients and coordinating head/tail help, but fixing the first quarter to Möbius still permits near-best finite errors. No tested construction proves asymptotic convergence.
- `[observed/proved]` Positive averages of raw Möbius cutoffs reach small finite errors while preserving Möbius signs. Successful near-identity power damping cannot have `ε_N log N→0`; mass must move cofinally away from terminal cutoff.
- `[observed]` Freezing a growing prefix has a visible cost under monotone positive averaging, largely removed by allowing a nonmonotone sign-preserving envelope. Remaining task is actual residual control as frozen prefix grows.
- `[observed]` Enforcing more exact boundary moments is not monotonically beneficial; error is concentrated outside Taylor-scale neighborhood. Local derivatives and harmonic charge do not settle global residual.
- `[rejected/observed]` Recovery-gap positive-moment model has a degree-17 square witness with negative numerical functional; finite Hausdorff differences can all pass while Hankel positivity fails. Global log-convexity remains open.
- `[proved]` Recovery multiplier has uniform block growth and exact closed spectral disc of radius `ρ≈0.0173600`, independent of moment positivity.
- `[rejected/proved]` Normalized chord-basis bound fails from three chords. Exact `27D+R` optimum is known; `27D−R` has signed capacity `28/27` versus monotone capacity `1`, proving genuine reversal advantage.
- `[proved]` Cubic reversal enclosure depth is exactly one. No finite search found a higher-degree counterexample to analogous shallow stabilization; this remains open outside proved cubic class.

## Arithmetic phases, minima, deletion, and Liouville recursion

- `[rejected/proved]` Real projected minimum balance admits off-line nonzeros of zeta and therefore is not a sufficient zero/location test. Retain the missing imaginary constraint or another independent equation.
- `[proved]` Every critical-line zero has a finite arithmetic value below the explicit tail boundary; observed minimizing moduli vary across primes/composites and Möbius signs. Finite minimum labels do not determine zero location.
- `[rejected]` Individual divisor terms are not monotone/dominant; large finite excursions coexist with proved power-decay envelopes.
- `[rejected]` Prime-sieve phase sign and monotone-insertion laws fail. A sufficiently late negative imaginary tail survives analytically, but supplies no sign for the full unit-head limit.
- `[observed]` Proposed successor cutoff `t<2πn` survived the finite ordinary-remainder scan. Cellwise negativity is false at special heights, so any proof must use cancellation across cells.
- `[rejected/proved]` Individual logarithmic phase turns may be positive while all tested cumulative prefixes are negative. Constant-speed prefix nonpositivity is proved; logarithmic clock transfer remains open.
- `[rejected]` Constant-speed signs do not persist under arbitrary exponential clock acceleration. Restricted layer formulations survived finite tests.
- `[rejected]` Growing-modulus remainder is not bounded after the naive main subtraction; it contains a universal `−(1/2)log p` term plus explicit real power and complex correction terms, not zero-specific cancellation.
- `[rejected]` Mixed refinement correction neither vanishes at zeros nor lies in tested scalar/two-coordinate repair spaces. Exact finite correction cocycle survives.
- `[rejected/proved]` Complete multiplicativity does not force finite endpoint-to-curvature sign: exact positive and negative tangent directions exist via paired primes.
- `[rejected]` Mixed chronological area is not rank at most two at tested zeros; endpoint area identities do not collapse contributions from many time pairs.
- `[observed]` Second-level quasi-shuffle identities hold, but self-area and cross-carry take both signs. Any depth-two producer needs compatibility of canonical continuation/refinement maps, not endpoint closure or universal sign.
- `[proved]` Signed-prime observable is exactly a weighted Liouville sum, not a second independent constraint. Prime dilation cancels divisible cofactors and leaves an explicit nondivisible remainder.
- `[rejected]` Two discarded log-recursion remainders reinforce rather than cancel on tested Liouville cutoffs; literal prime/cofactor alignment alternates between strong suppression and amplification. No fixed reversal law survives.

## Theta moment and Gram structure

- `[observed]` In the two-moment-preserving theta cosine family with signed direction (+,-), collision continuation stalls are regular interaction-coordinate folds at (t,lambda,kappa)≈(32.56568,.07879551,.35536084) and (40.67315,.06301241,.34758784): F=F_t=F_lambda≈0, F_tt≠0, lambda'(t)≠0. Both positive-multiplier bounds hold; 50/100/160-digit refinement and independent theta integration confirm local double-zero folds, not triple-zero events. No global branch or HB selection claim.
- `[observed]` For L1-normalized theta cosine deformations on frequencies (2,4,6)/(3,5,7), annihilating source mass and second moment, adding their moment-compensated product changes the continued gap-24 collision threshold by +1.42971% in direction (+,+) and -7.55148% in (-,+). Positive-multiplier bounds hold; endpoints survive 50/100/160-digit checks, branch-return checks and independent theta integration. Local interaction sensitivity is direction-dependent; no global first-collision, zero-ancestry or HB extinction claim.
- `[rejected]` Fixed theta-shell prefixes do not supply all-degree logarithmic Hankel positivity: first atom fails at degree 3; first two atoms fail at degree 12; third atom repairs the tested degree-12 block. Degree and shell cutoff must grow together.
- `[proved]` Every finite theta prefix has a negative high-frequency cosine-transform boundary canceled exactly by its omitted tail; truncation destroys a source-level cancellation.
- `[observed]` Cleared logarithmic Hankel kernel can be a positive contraction of raw odd Gram for sufficiently many shells at tested degree, but one/two-shell lower signs fail. Upper domination alone does not produce positivity; literal equality is proved false asymptotically.
- `[proved]` Signed exponential-polynomial Stein primitives yield rational global certificates for four first-atom integrals, sufficient for both Ward ratio inequalities and the full-source first minor. Method supplies finite-block, not all-rank, positivity.
- `[observed]` Tilted theta log-cumulants alternate through orders 2–8 for all tested tilts; low-tilt behavior follows pole-dominated factorial laws and high-tilt behavior follows saddle scaling. Complete monotonicity remains conjectural.

## Operator, cubic-current, and BM source lessons

- `[rejected/proved]` Bounded finite packet factors either retain nonzero defect or coherent zero defect; trace-norm limits of zero finite defects remain zero. ULF-INHD bounded landing is retired. A singular landing cannot inherit the old Hilbert–Schmidt/nuclear estimate.
- `[rejected/proved]` Exact Gamma subtraction leaves a positive tail and index zero; oversubtraction manufactures a negative direction but is not source-lawful. Wild-saddle relocation has trace zero and no horizontal sensitivity.
- `[proved]` Prime–polar–Gamma signed scalar completion is unconditionally subunit, but scalar cancellation is not a nuclear-norm estimate and cannot preserve index-one trace. Coefficient-faithful nuclear lift is missing.
- `[proved]` Relative theta metrics can have trace-one positive curvature with operator norm `1/3`, but positivity forces trace norm `1`; small operator norm cannot substitute for required subunit nuclear norm.
- `[observed]` Positive cyclic exponential-Hankel surrogate has ample cubic margin, dominated by mixed cyclic terms, but no identity lands it on the arithmetic Hardy seam. Only a direct same-boundary theta `S₃` kernel identity remains viable in that class.
- `[rejected/proved]` Flat cubic source does not force the two-channel spectral curve: three rational rank-one projections give an exact counterexample. Source cubic vanishes before Hardy compression; boundary charge is an infinite-dimensional compression effect.
- `[proved]` Three-column circulant source frames satisfy exact phase-area transgression and support faithful arithmetic Xi winding after Hardy compression. Missing ingredients are subunit nuclear budget and off-line-charge annihilation.
- `[rejected]` Constant-curvature HC94 proxy is not the physical AdS4 radial vertex. Its special cancellation cannot decide the BM route; physical vertex must retain radial derivatives and `1/z` structure.
- `[proved]` Actual quadratic BM angular source splits into scalar, mixed rotated-Hessian, and vector channels with distinct radial coefficients. Mixed source is an angular derivative and cannot be deleted or collapsed to one scalar amplitude.
- `[proved/observed]` Corrected mixed BM source has only time/radial–angular components; all third angular derivatives cancel, coefficients are horizon-regular but generally nonzero, and a conserved-current form is suggested. Complete vector-master curl is proved; all-height nonlinear source identity and causal pairing remain open.

## Other exact/numerical facts

- `[observed/rejected]` For A(rho)=Lambda(5rho/2-1)Lambda(rho/2)^2Lambda(1-3rho/2)/2, gamma-removed log-magnitude at zeta ordinates minus its two quarter-forward-gap controls has mean -0.13529 on zeros 1–64 but +0.03625 on held-out 65–128; 257–320 gives -0.01092. Stable at 50/100/160 digits with independent Euler–Maclaurin checks. Low-height average suppression is not a persistent sign selector; arithmetic sampling supplies no complete-action identification.

- `[observed]` No integer linear relation of height `≤10⁶` was found among `{1,γ₀,γ₁,γ₂,log2,log3,log5,ζ(2),ζ(3)}`; no degree-2 relation of height `≤2000` was found among the tested Stieltjes/log/MZV monomials. This is bounded PSLQ evidence only and RH-blind.
- `[proved]` Functional equation gives triangular Stieltjes dictionary `ζ^(k)(0)=(k/2)γ_(k−1)+R_k`; checked explicitly at `k=2,3`. It preserves rather than collapses the wild Stieltjes tower.
- `[proved/observed]` Mollified fourth-moment ratios recipe gives
  `c₄(θ)=1+8/(3θ)+2/θ²+2/(3θ³)` in its rigorous main-term range; Gaussian prediction is different. Numerical moments trend toward this formula.

- `[observed]` The unit-amplitude affine continuation of the full first-subtracted fundamental radial moment has numerically simple zeros at rho≈0.4197560634+6.3336824462i for (source,reader)=(false,false), and rho≈0.9225395686+6.8704538406i for (true,true), with s_false=-rho-1, s_true=rho-2, w_false=-2+rho/2, w_true=-1-rho/2. Fresh 50/100/160-digit solves, independent endpoint series, and direct fixed-source quadrature validate the blind spots. All three alternate channels remain nonzero at each point. These are spectral controls below the first cached zeta ordinate, not asserted Xi zeros: individual-channel strip-wide nonvanishing fails numerically; actual-Xi survival and common-zero exclusion remain open.

- `[observed]` For the first 64 zeta ordinates, a gamma-free 1:3:5 phase-curvature zero-versus-midpoint contrast has zeta mean +.274855, frequency-control mean +.161352, and conductor-4/5 means -.185584/-.214891. Only 5/8 zeta block signs agree; the frozen stability/control-dominance criterion fails. Selected precision and independent Euler-Maclaurin checks pass. This does not exclude other phase mechanisms or identify an HB action.
- `[observed]` In the two-moment theta cosine family, numerical backward continuation assigns the additive/product gap-24 collisions in directions (+,+) and (-,+) to the same original zeros24/25. Thus the +1.42971%/-7.55148% local threshold changes are not ancestor-label changes in these tracks. Selected100/160-digit roots and independent complex theta integrals agree; no interval branch certificate or global first-collision claim.

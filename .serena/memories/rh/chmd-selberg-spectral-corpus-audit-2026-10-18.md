# CHMD: existing Selberg spectral work and paid pole coefficient

Main task remains OPEN: unconditional rapidity-uniform one-sided bound on the complete folded Möbius wave. User requires the local research tool, no numerical experiments, no new axioms/unproved arithmetic premises, one owned foreground Lean audit, no full builds, no commits, clean owned scratch. Main card: docs/drafts/pipeline/1-in-progress/chmd-all-scale-folded-mobius-control-2026-10-18.md. Ledger: logs/chmd-all-scale-folded-mobius-1810.md. Do not edit current frontier map (concurrent owner).

## Verified applicability consequence

Existing RHTower.Sieve.abs_sum_moebius_log_div_le in formal/GaloisForLFunctions/RHTower/Sieve/LogMoebiusBounded.lean:18 bounds |sum_{m=1}^N μ(m) log(N/m)/m| by 5+|γ| for N≥1. Existing selbergMobiusCoeff_eq identifies the literal row μ(m) log(N/m)/log N. Therefore |sum selbergMobiusCoeff N m/m| ≤ (5+|γ|)/log N for N≥2. Direct scratch `lake --old env lean /tmp/chmd-selberg-pole-audit-1810c.lean` passed (exit0); axiom audit only propext, Classical.choice, Quot.sound. This is recovered existing work, no new repository wrapper. Proof: sum_div, sum_congr, selbergMobiusCoeff_eq, ring; rewrite abs_div and positivity of log N; apply div_le_div_of_nonneg_right to existing logarithmic bound. Also raw harmonic prefix bound ≤1 already exists in MoebiusFloorSummatory.lean:66. Do not treat pole amplitude as an unpaid arithmetic estimate for these rows.

## Prior source results read

- SelbergTruncatedVonMangoldtKreinCompletion: `LSeries_selbergWeightedVonMangoldt` (line179) is exact -M_w ζ' for Re(s)>1. Exact primes and low-aperture agreement; finite Weil multiplier representation on polar-constrained tests. Not the CHMD all-scale estimate.
- WeilFullConeSelbergCompletionFloorExclusion: finitely supported weights w with w(1)>0 cannot give full-cone Weil positivity. Positive survivor already formalized: on rough integers beyond support, Λ_w(n)=w(1)log n. Do not infer that any folded-wave density must be nonnegative or that this excludes all weighted negative-mass bounds.
- CCMPrimeDeficitResidualPairing:73 gives elementary source as exponential causal ramp dilation minus log-weighted linear causal ramp dilation.
- SupportRadiusCollarCutoffAndAllScaleObstacleBBridge:421,455 retains log d+R≤a for each prime in finite S, a≥3R+δ+L, continuum integrability premises, and supportArchBudget R δ L. Budget independent of S,a but not support radius; no comparison to fixed full-form archimedean coefficient proved. Header all-scale is scoped.
- CHMDKleinGordonEnergyPositivityAndOriginMaximum is local origin positivity, not a conserved spatial half-line energy bound. Native Doob localization and nodal identities refer to their own energy spaces.

## Unverified next candidate, recorded on main card

Let α=γ+1, β=log(2π)/2, R=bounded dilation remainder. Define B(q)=α−β+α/(q−1)+q²∫_0∞R(u)e^(−qu)du for Re q>0, q≠1. Finite real a_m: A_a(q)=Σa_m m^(−q), h_a=Σa_m/m. Paper derivation gives Σa_m Φ_y(v+logm)=αe^(−v)h_a P(y)+e^(−v/2)/π ∫ cos(y sqrt(r²+2))sech²(r/2) Re[e^(irv) B(1/2−ir)A_a(1/2−ir)]dr, v≥0. P=2cos(y sqrt7/4)/cos²(1/4). This precise combined formula is NOT Lean checked. Derive by full pole integral minus negative-half-line head and R Fourier Fubini; boundedR pays latter exchange. Causal ramps give paper B=ζ'+qζ/(q−1) on Re q>1; extension to critical line must not be assumed without analytic continuation.

For Selberg rows put d_N(r)=sech²(r/2)Re[B(q_r)A_N(q_r)]/π. Candidate arithmetic bound: sup_N ∫max(−d_N,0)<∞. Paid pole and fixed-y convergence bound signed mass via y=0; then integral|d_N|=integral d_N+2integral negative part yields uniform wave bound. Negative-mass estimate remains UNPROVED, not an arithmetic advance merely because it has this receiver. Do not replace real part by complex modulus, or presume positivity from finite completion.

## Search scope

Research queries included literal ccmPrimeDeficitDilationSource and selberg completion (lexical), and deep/hybrid dilation Laplace multiplier, finite mollifier density negative part, CHMD source energy, reciprocal harmonic heads. Deep/hybrid calls completed nonpartial with errors[], inventory complete ~74,193 files, source/compiler freshness mostly pending/stale/source-only; coverage snapshot older generation and semantic coverage unavailable warnings. All candidate/source arrays inspected; proposed ingredient sets were inapplicable (generic smooth mollification or hypothetical eigenvector consequences). Search metadata is not a kernel audit. Main all-scale bound still open. No repository Lean edits in this pass.
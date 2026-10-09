# Probe location and the sharp local exponential threshold

Status: [FORMALIZED AWAY FROM THE CRITICAL ENDPOINT]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Target and plan

Identify the local convergence threshold `r(y)=2*pi*exp(-|y|)`, hence `2*pi/m`
at an integer-log probe. Prove sufficient damping/growth below this rate,
necessary damping/growth above it, sharp divergence for exponential weights
above it, and the corresponding actual-probe implications.

1. Audit the new RiemannKernelTailDecayRate module and existing autocorrelation
   envelopes; reuse the latter because the former bounds Phi rather than K.
2. Prove local paired-kernel upper/lower envelopes for every rate strictly
   below/above r(y).
3. Transfer these to arbitrary signed-weight convergence and exponential growth;
   exhibit exponential-weight divergence above the boundary.
4. At log m, derive the inverse-location rate 2*pi/m. Subcritical deviation
   growth gives a finite probe limit without finite excess. With finite excess,
   a lower bound on a probe with log m>=4 gives growth bounds at all rates above
   2*pi/m.
5. Compile/export, audit all public declarations, wire/index/lint, promote,
   save memory and clean owned scratch. No critical-endpoint claim.

## Dependency-closed paper proof

The corpus proves K(z)<=C exp(-2c exp|z|) for every 0<c<pi, and eventually
K(z)>=D exp(-b exp z) for every b>2pi. Write P_y(n)=K(y+log n)+K(y-log n).

For 0<a<r(y), choose c=a*exp(|y|)/2<pi. Both exponentials exp|y±log n|
are at least n*exp(-|y|) for n>=1, so P_y(n)<=2C exp(-a*n).
For b>r(y), choose the kernel lower-envelope parameter B=b*exp(|y|)>2pi.
Apply its tail bound at log n-|y|. Evenness makes this a term of P_y(n),
and B exp(-|y|)=b, so eventually D exp(-b*n)<=P_y(n).

Thus summability of |v(n)|exp(-a*n) at any a<r(y) suffices for the potential
at y. If a<=0, increase a to max(a,r(y)/2), still below r(y), using monotonicity
of damping. Conversely, potential summability forces every damping b>r(y)
to be summable. Norm comparisons handle arbitrary signed v and finite heads.

If |v(n)|<=C exp(rho*n) with rho<r(y), choose a strictly between rho and r(y).
Geometric summability proves the damping at a, hence potential convergence.
If the potential converges, each damping b>r(y) bounds its individual terms,
giving |v(n)|<=C_b exp(b*n). For pure exponential weights exp(rho*n), rho>r(y),
choose b strictly between r(y) and rho: necessary damping would make the
positive exponential series exp((rho-b)*n) summable, a contradiction.

For m>=1, r(log m)=2*pi/m<=r(0). Therefore subcritical normalized-deviation
growth at this rate gives convergence at both the origin and the probe;
the existing exact probe-limit theorem then applies without finite excess.
With finite excess and log m>=4, an eventual probe lower bound already forces
origin and sampled convergence. Applying the local necessary growth theorem
gives every rate above 2*pi/m. The cutoff and multiplicative constants need
not be uniform over probes or rates.

## Audit evidence and limits

Local lexical search: 797 declarations, 285 modules, 437 eligible entries.
Read the entire 200-line RiemannKernelTailDecayRate module. Its derivative
decay, antitonicity, and edge-minimum theorems concern the theta kernel Phi,
so no theorem there duplicates the local paired-autocorrelation threshold.
The parameterized autocorrelation envelopes were inspected in the preceding
increment and checked against the current toolchain in a scratch import.

## Verification

- `WeilLogShiftLocalDecayThreshold.lean` compiled and exported with
  `lake --old env lean <leaf> -o <local olean>`; exit 0, no diagnostics.
- The umbrella imports the leaf. Index refresh succeeded; all 12 public
  declarations appear in `formal/LEAN_API.md`.
- `scripts/formal_tools.py lint` passed globally.
- The scratch axiom audit passed for all 12 public declarations; every result
  depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- All owned jobs exited. Owned scratch files were removed after recording
  these results.

All five plan steps are complete. The new insight is the inverse relation
between probe location and detectable coefficient growth: one fixed probe at
log m controls all exponential rates above 2*pi/m, while growth below 2*pi/m
already gives its finite limit. This is a local refinement of the earlier
whole-line/subexponential equivalence. Equality remains outside the result.

The estimates in this leaf leave equality undecided. The follow-up
`WeilLogShiftCriticalEndpoint.lean` now proves pure-exponential divergence at
rho=r(y), the exact criterion rho<r(y), and a necessary critical damping moment
with a factor 1/n. See `weil-logshift-critical-endpoint.md` for its separate
proof and verification. No RH, general mixed-sign rigidity, or external novelty
claim is made here. No numerical experiments, added analytic premises, axioms,
heartbeat increases, or full/umbrella builds.

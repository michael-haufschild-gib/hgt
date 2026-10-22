# Xi critical kernel: separated real-packet positivity at every rank

- **ID:** `xi-critical-kernel-separated-real-packet-positivity`
- **Stage:** 1-in-progress
- **Type:** OWN THEOREM (unconditional stratum of the live Bezoutian RH endpoint)
- **Sibling:** `theta-kernel-cp-deficit-domination` (CP-1 closed the auxiliary kernel's separated
  packets; this card closes separated packets of the *literal endpoint matrix family*).

## Exact frontier (Gate 1)

Internal. The live endpoint `riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`
(`RHTower/ThetaTailFirstMomentDoubleLaplace.lean:817`) states: RH ⟺ the matrices
`[thetaTailFirstMomentBezoutian W_j (conj W_k)]` are PSD for every finite node system in
`{Re W > 1/2}`. The corpus owns, unconditionally:

- `re_logDeriv_xiCent_pos` (`XiEulerSafeCauchyLoss`): `Re L(W) > 0` on `Re W > 1/2`,
  `L = logDeriv xiCent` — the n = 1 stratum at every complex node (with
  `criticalLogDerivKernel_self_re_nonneg_of_half_lt`).
- `xiSquaredEulerFullKernel_twoPoint_det_pos` + `twoMode_twoChannelKernel_realRay_energy_nonneg`
  (`XiSquaredEulerRayFullResponse`, `ThetaCuspTiltFluxWeilParityEulerRayWeld`): the n = 2 stratum
  at all real node pairs `1/2 < x < y` (all gaps), via the two response monotonicities.
- `ThetaCuspTiltFluxThreeRealDeterminant`: n = 3 real nodes *reduced* to the cubic determinant —
  OPEN. The corpus's own boundary marker: "an RH-detecting negative packet … must use either
  complex-node geometry or at least three real-ray modes."
- `XiSquaredEulerDiagonalCorrelationUniversalityLaw`: all-finite-central-minor nonnegativity is
  exactly RH — so the full real-node stratum carries RH content; any unconditional theorem must
  stay away from the tight regime.
- `xiCentBezoutian_eq_mul_criticalKernel`: B(W, conj V) = ξ(W)·conj ξ(V)·K₀(W,V) with
  `K₀ = criticalLogDerivKernel` — congruence transfer between the Bezoutian family and K₀.
- Theta representation: `thetaBilateralLaplace_eq_xiCent`, `thetaBilateralLaplaceMoment_eq_deriv_xiCent`:
  on the real ray, ξ(1/2+β) = ∫_ℝ Φ e^{βx} dx and ξ'(1/2+β) = ∫_ℝ xΦ e^{βx} dx with
  Φ = `thetaCuspFullSource` > 0, even, with the Hedenmalm envelopes
  `C_l E ≤ Φ ≤ C_u E`, `E(x) = e^{9x/2}e^{−πe^{2x}}` on the positive axis.

External. Literature on positivity of Re ξ'/ξ is single-point: classical Re ξ'/ξ > 0 for
Re s ≥ 1 (zero pairing), Hinkkanen/Lagarias-type criteria (RH ⟺ positivity down to the critical
line), and two recent notes on the near-critical strip (arXiv:2201.08599, arXiv:2509.18963).
The coincident-pair limit of the 2×2 minor is the Laguerre/Turán inequality lineage
(Csordas–Norfolk–Varga), proved by the same theta-moment method. No multi-node matrix stratum of
a ξ-Bezoutian/log-derivative kernel is stated anywhere we found. Residue: n ≥ 3 real nodes,
any unconditional regime.

## Structural frame (new, this card)

At real nodes x, y > 1/2 the critical kernel is
`K₀(x,y) = (r(x)+r(y))/(x+y)`, `r(β) = ξ'/ξ(1/2+β)`, with diagonal `K₀(x,x) = r(x)/x`. Hence

`K₀(x,y)/√(K₀(x,x)K₀(y,y)) = cosh(Δ_r/2)/cosh(Δ_β/2)`,
`Δ_r = log r(y) − log r(x)`, `Δ_β = log y − log x`.

So: **the 2×2 real-node minors are PSD exactly when log r is 1-Lipschitz in log β** — the corpus's
two monotonicities (response decreasing, radius-weighted response increasing) are exactly the
slope-in-[0,1] statement, and the corpus's own counterexample (the Herglotz function 1/(w−a),
log-slope < −1) is exactly a Lipschitz violation. Under RH, `r(β) ≈ (2+γ−log4π)·2β` near
β = 1/2: the Lipschitz bound saturates at the Euler edge — the real-node RH content lives at the
edge/close-ratio regime, so an unconditional theorem must take a base R₀ and ratio separation.
[CONJECTURE, recorded for later cycles — LOG-LIP: log r is 1-Lipschitz in log β on all of
(1/2,∞); it is RH-necessary (2×2 minors) and would close every real 2×2 minor. Not claimed.]

## The claim (Gate 2)

**BZ-1.** With `γ := C_u/C_l`, define the explicit constants
`R_u := πe⁴ + log γ + 12`, `R_l := (2π)²e^{2e+8} + 4·log(8γ) + 16`, `R₀ := R_u + R_l`.
(The `2e+8` exponent gives the slack `(b/4)(log b − 2log 2π − 2e) ≥ 2b`, which absorbs the
`(9/8)log b + log(log b) + log 8γ` bookkeeping in (B) with room.)
For every n, every real node sequence `x : ℕ → ℝ` with `x 0 ≥ R₀` and `x(m+1) ≥ R₀²·x(m)`:

1. the matrix `[criticalLogDerivKernel (x j) (x k)]_{j,k<n}` is PSD (complex PosSemidef), and
2. the matrix `[thetaTailFirstMomentBezoutian (x j) (conj (x k))]_{j,k<n}` is PSD —
   an arbitrary-rank unconditional stratum of the literal RH-equivalent endpoint family.

Unconditional, premise-free. New at every n ≥ 3 (corpus owns n ≤ 2; literature owns n = 1).

## Hostile audit (Gate 3)

- CIRCULAR? No: the proof consumes only the theta integral representation on the real ray plus
  envelope calculus; no zero information, no Hadamard product, no RH-adjacent input.
- REDISCOVERED? The method is Csordas–Varga-style theta-moment analysis (acknowledged); the
  statement (multi-node PSD stratum of this kernel family) is absent from corpus and literature.
  [NOVELTY UNVERIFIED] pending expert priority audit; no external priority claimed.
- FALSE? RH implies the full family is PSD, so no counterexample exists under RH; the proof
  below is direct and unconditional.
- INSIGNIFICANT? It moves the corpus's own boundary marker: an RH-detecting negative packet must
  now use complex nodes, or ≥ 3 real modes with base < R₀ or some consecutive ratio < R₀².
  Verdict: SURVIVES PRELIMINARY ATTACK.

## Paper proof (Gate 4) — complete

Φ > 0 on ℝ, Φ even, `C_l E ≤ Φ` (x>0), `Φ ≤ C_u E` (x≥0), E antitone on [1,∞),
`Z(β) := ∫_ℝ Φe^{βx}dx > 0`, `N(β) := ∫_ℝ xΦe^{βx}dx`, `r(β) := N/Z`; on the real ray
`logDeriv xiCent β = r(β)` (theta representation; Z > 0 so ξ(1/2+β) = Z(β) > 0).

**(A) Upper: r(β) ≤ log β + 1 for β ≥ R_u.** Split N at X := log β. On x ≤ X:
xΦe^{βx} ≤ XΦe^{βx}, so ∫_{x≤X} ≤ X·Z. Tail: Φ ≤ C_u E and
e^{2x} = β²e^{2(x−X)} ≥ β²(1+2(x−X)) give, with c := 2πβ² − β − 9/2 ≥ πβ² (β ≥ 2),
T ≤ C_u e^{−πβ²} β^{β+9/2} (X/c + 1/c²) ≤ C_u e^{−πβ²} β^{β+9/2}(log β + 1).
Floor: Z ≥ ∫_{[1,2]} Φe^{βx} ≥ C_l E(2) e^{β} (E antitone). Since
(β+9/2)logβ ≤ 2β² ≤ (π−1)β², one gets T/Z ≤ γ e^{πe⁴−9}(logβ+1)e^{−β²} ≤ 1 for β ≥ R_u
(crudely: logβ+1 ≤ β ≤ e^β and β² ≥ R_u ≥ πe⁴ + log γ + 12). Hence r ≤ log β + 1.

**(B) Lower: r(β) ≥ (1/8) log β for β ≥ R_l.** Evenness:
N = ∫_{x>0} xΦ(e^{βx} − e^{−βx}) ≥ ∫_{x>0} xΦe^{βx} − M₁ and
Z = ∫_{x>0} Φ(e^{βx} + e^{−βx}) ≤ Z₊ + M₀, with Z₊ := ∫_{x>0}Φe^{βx},
M₁ := ∫_{x>0} xΦ ≤ C_u, M₀ := ∫_{x>0} Φ ≤ C_u (envelope integrals, 2π − 11/2 > 0).
Let Y := (1/4)logβ. Then ∫_{x>0}xΦe^{βx} ≥ Y(Z₊ − S), S := ∫_{0<x<Y}Φe^{βx}.
Ceiling: S ≤ C_u e^{(β+9/2)Y}/β. Saddle slab: x₂ := (1/2)log(β/2π) (so πe^{2x₂} = β/2,
x₂ ≥ e/2 + 1 for β ≥ 2πe^{e+2}); on (x₂, x₂+1/2]: E ≥ e^{9x₂/2}e^{−eβ/2}, e^{βx} ≥ e^{βx₂}:
Z₊ ≥ (C_l/2) e^{βx₂ − eβ/2} ≥ (C_l/2)e^{β}.
Ratio: S/Z₊ ≤ (2γ/β)·exp(−(β/4)logβ + (β/2)log 2π + (e/2)β + (9/8)logβ) ≤ 2γe^{−β/4} ≤ 1/4
for β ≥ R_l (the exponent ≤ −β/4 once logβ ≥ 2log2π + 2e + 2, i.e. β ≥ (2π)²e^{2e+2};
2γe^{−β/4} ≤ 1/4 once β ≥ 4log(8γ)). Also C_u/Z₊ ≤ 2γe^{−β} ≤ 1/4, M₀/Z₊ ≤ 1/4. Hence
r ≥ (Y(3/4)Z₊ − C_u)/(Z₊ + M₀) ≥ (3Y/4 − 1/4)/(5/4) ≥ Y/2 = (1/8)logβ (using Y ≥ 2).

**(C) Correlation decay.** For R₀ ≤ x < y (both ≥ R_u and ≥ R_l):
K₀(x,y) ≤ (r(x)+r(y))/y ≤ 4·log y/y; K₀(x,x) = r(x)/x ≥ log x/(8x). So
ρ(x,y) := K₀(x,y)/√(K₀(x,x)K₀(y,y)) ≤ 32·√((x log y)/(y log x)).
Packet j < k, d := k−j: y := x_k ≥ R₀^{2d}·x_j =: b, and t ↦ log t/t is antitone on [e,∞)
(a log b ≤ b log a for e ≤ a ≤ b, from log(b/a) ≤ b/a − 1 ≤ (b−a) ≤ (b−a)log a). Hence
ρ ≤ 32·R₀^{−d}·√(1 + 2d·log R₀/log x_j) ≤ 32 R₀^{−d}√(1+2d) ≤ 32·(2/R₀)^d
(log x_j ≥ log R₀; 1+2d ≤ 4^d by induction).

**(D) Scaled Gershgorin** (CP-1 pattern). With q := 2/R₀ ≤ 1/2: for real a,
Σ a_i a_j K₀(x_i,x_j) ≥ Σ a_i² K₀(x_i,x_i)·(1 − 2·32·q/(1−q)) ≥ Σ a_i²K₀_ii(1 − 256/R₀) ≥ 0,
since R₀ ≥ (2π)²e^{2e+2} > 256. Entries K₀(x_i,x_j) > 0, diagonal > 0.

**(E) Complex and Bezoutian forms.** K₀ real symmetric at real nodes (realness of L on the ray
from the theta representation; conj_ofReal), so the complex Hermitian form decomposes into two
real forms: PosSemidef of matrix 1. Congruence: at real nodes
B(x_j, conj x_k) = ξ_j ξ_k K₀(x_j,x_k) with ξ_j = ξ(1/2+x_j) = Z(x_j) > 0
(`xiCentBezoutian_eq_mul_criticalKernel`), so x†Bx = y†K₀y with y_j = ξ_j x_j: PosSemidef of
matrix 2. ∎

Only numeric inputs: π > 3, 2 ≤ e ≤ 4-level facts; everything else symbolic in (π, C_l, C_u).

## Queued next

- LOG-LIP conjecture (above): would close all real 2×2 minors; RH-necessary.
- Shrink R₀, Q₀ (saddle sharpening; both-endpoint slabs).
- Complex separated nodes (imaginary displacement of a separated real packet — needs a bound on
  |L| off the ray; the theta representation still applies).
- Off-line quartet mass domination via Hardy-type on-line supply (zero-density input — heavy).

## Loop log

- 2026-08-29: card opened; Gates 1–3 recorded; paper proof complete (Gate 4). Lean next.

## Status: [LEAN-PROVED] (2026-08-29)

BZ-1 is formalized, unconditional and premise-free, in two umbrella-wired modules
(all listed theorems audited on axioms propext/Classical.choice/Quot.sound; built via
`lake build`, 10904 jobs; lint clean):

`formal/GaloisForLFunctions/RHTower/XiCriticalKernelSeparatedRealPacketPositivity.lean`
(the real-ray analytic layer):
- `xiRayLaplace`, `xiRayLaplaceMoment`, `xiRayLogDeriv` — the real bilateral Laplace data of
  the theta-cusp source, with integrability and the exponential floor `xiRayLaplace_ge`,
  positivity `xiRayLaplace_pos`.
- `xiCent_ofReal`, `deriv_xiCent_ofReal`, `logDeriv_xiCent_ofReal` — on the real ray the
  centered Xi function, its derivative, and its logarithmic derivative are the real Laplace
  transform, moment, and quotient (so ξ(1/2+b) > 0 on the whole real ray, for free).
- `xiRayEnvelopeRatio`, `one_le_xiRayEnvelopeRatio` (γ ≥ 1 extracted from the envelope
  sandwich at x = 1 — no structural constant needed), `xiRayUpperBase`, `xiRayLowerBase`,
  `xiRayPacketBase` (= R_u + R_l), `xiRayPacketBase_ge` (≥ 256).
- **`xiRayLogDeriv_le`** — r(b) ≤ log b + 1 for b ≥ R_u (split at X = log b; unit-rate
  pointwise tail majorant `(X+u)e^{−ru} ≤ (X+1)e^{−u}` avoids all shifted integrals).
- **`xiRayLogDeriv_ge`** — (log b)/8 ≤ r(b) for b ≥ R_l (even-splitting via
  `integral_comp_neg_Iic`; reflected mass/moment ≤ C_u; saddle slab at
  x₂ = (1/2)log(b/2π) of width 1/2; ceiling S ≤ C_u·Y·e^{cY} at Y = (log b)/4).

`formal/GaloisForLFunctions/RHTower/XiBezoutianSeparatedRealPacketPosSemidef.lean`
(correlation, Gershgorin, and the matrix strata):
- `log t/t` antitone device (a·log c ≤ c·log a), `1+2d ≤ 4^d`, and the private correlation
  bound: on nodes u ≤ v with v ≥ R₀^{2d}·u,
  K₀(u,v) ≤ 32·(2/R₀)^d·√(K₀(u,u))·√(K₀(v,v)).
- **`xiRayCriticalKernel_separatedPacket_quadraticForm_nonneg`** — the real quadratic form of
  `(L(x)+L(y))/(x+y)` is ≥ 0 on every packet with `x 0 ≥ R₀`, `x(m+1) ≥ R₀²·x m`
  (scaled Gershgorin, geometric row sums, threshold 64q ≤ 1−q at q = 2/R₀ ≤ 1/128).
- `criticalLogDerivKernel_ofReal_eq` — the corpus's RH-critical kernel at real nodes is the
  real Laplace-quotient kernel.
- **`posSemidef_criticalLogDerivKernel_separatedRealPacket`** — complex `Matrix.PosSemidef`
  of `[criticalLogDerivKernel (x j) (x k)]` on every separated packet (Hermitian + re/im
  decomposition into two real forms; imaginary part vanishes by kernel symmetry).
- **`posSemidef_thetaTailFirstMomentBezoutian_separatedRealPacket`** — PSD of the literal
  Bezoutian matrices `[thetaTailFirstMomentBezoutian (x j) (conj (x k))]` (congruence by the
  positive diagonal ξ(1/2+x_j) = xiRayLaplace (x j) via `xiCentBezoutian_eq_mul_criticalKernel`).
- **`posSemidef_thetaTailFirstMomentBezoutian_packet_nodes`** — the instantiation in the
  literal quantifier shape of `riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`.

Frontier consequence: the corpus's negative-packet no-go sharpens to — an RH-detecting
negative packet must use complex-node geometry, or at least three real-ray modes with base
below R₀ or some consecutive ratio below R₀².  Combined with the corpus's n ≤ 2 all-gap
theorems, the real-node RH content is now localized to the Euler-edge/close-ratio regime,
exactly parallel to CP-1's close-pair localization on the kernel side.

Labels: [LEAN-PROVED]; [NOVELTY UNVERIFIED] (new-to-corpus about corpus-native objects;
nearest literature is diagonal-only — Re ξ'/ξ positivity notes and the Csordas–Varga
Laguerre/Turán lineage; no external priority claim).  Next quantitative targets: shrink R₀
(both-endpoint slabs; sharper S-ceiling), the LOG-LIP conjecture (all real 2×2 minors),
n = 3 all-gap via the corpus's cubic-determinant reduction, and complex displaced packets.

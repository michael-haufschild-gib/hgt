# Xi Bezoutian: complex-tilted separated-packet positivity

- **ID:** `xi-bezoutian-complex-tilted-packet-positivity`
- **Stage:** 1-in-progress
- **Type:** OWN THEOREM (unconditional complex-node stratum of the live Bezoutian RH endpoint)
- **Siblings:** `xi-critical-kernel-separated-real-packet-positivity` (BZ-1, real nodes,
  closed 2026-08-29), `theta-kernel-cp-deficit-domination` (CP-1, kernel point-nodes).

## Exact frontier (Gate 1)

Internal. After BZ-1 the unconditional strata of
`riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian` are: n = 1 at every complex
node (`criticalLogDerivKernel_self_re_nonneg_of_half_lt`), n = 2 at all real pairs, and
arbitrary rank at separated real packets (BZ-1). At complex nodes with n ≥ 2 there is
NOTHING: the corpus's own boundary marker says an RH-detecting negative packet "must use
complex-node geometry or ≥ 3 real modes"; BZ-1 killed the separated-real branch, so the
complex-node branch is the named frontier. Assets: the theta representation and the BZ-1
real-ray bounds `(log b)/8 ≤ L(b) ≤ log b + 1` (`xiRayLogDeriv_ge/_le`), the general
Hermitian symmetry `criticalLogDerivKernel_conj_symm` (no hypotheses), the congruence
`xiCentBezoutian_eq_mul_criticalKernel`, and `Complex.add_conj` (diagonal entries at any
node are real: K₀(W,W) = Re L(W)/Re W).

External. Nothing multi-node exists even at real nodes (BZ-1 audit); a fortiori nothing at
complex nodes. n = 1 complex positivity is classical (Re ξ'/ξ > 0 for Re s > 1).

## The claim (Gate 2)

**BZ-2.** Define the tilt budget `τ(b) := 1/(32(log b + 3))` (frozen in Gate 4). For every n and every complex
node sequence `W : ℕ → ℂ` whose real parts `β_j := Re W_j` form a BZ-1 packet
(`β_0 ≥ R₀ := xiRayPacketBase`, `β_{m+1} ≥ R₀²·β_m`) and whose imaginary parts satisfy
`|Im W_j| ≤ τ(β_j)`:

1. `[criticalLogDerivKernel W_j W_k]_{j,k<n}` is PosSemidef, and
2. `[thetaTailFirstMomentBezoutian W_j (conj W_k)]_{j,k<n}` is PosSemidef —
   the first unconditional multi-node complex-node stratum of the literal RH-equivalent
   endpoint family, at every rank.

Unconditional, premise-free. Consequence: an RH-detecting negative packet at separated real
parts now requires an imaginary displacement exceeding the explicit budget `1/(32(log Re+3))`
at some node; combined with BZ-1 and the n ≤ 2 theorems, all remaining real-node RH content
sits at the Euler edge/close ratios, and all remaining complex content beyond the tilt strip.

## Hostile audit (Gate 3)

- CIRCULAR? No: perturbation theory of the theta transform around the real ray; no zeros,
  no RH-adjacent input.
- FALSE? RH implies the full family is PSD; the proof below is direct.
- REDISCOVERED? No complex multi-node statement exists in corpus or literature.
- INSIGNIFICANT? It is thin (budget ~ 1/log β — far below the zero heights), but it is the
  first foothold off the real ray for the criterion matrices, at arbitrary rank, and it
  upgrades the corpus's negative-packet no-go on its own named branch. Honest limitation
  recorded: the arithmetically deep complex geometry (|Im| comparable to zero ordinates) is
  untouched. Verdict: SURVIVES PRELIMINARY ATTACK.

## Paper proof (Gate 4) — complete

Notation: Φ = theta-cusp source, Z(β), N(β), r = N/Z, X := log β; BZ-1 gives, for
β ≥ R₀: X/8 ≤ r(β) ≤ X+1, Z(β) ≥ C_l E(2) e^β > 0, and e^β ≥ 32γ (γ = C_u/C_l).

**(F0) Oscillation bound.** ‖e^{iθ} − 1‖² = 2(1−cos θ) ≤ θ² (from cos θ ≥ 1 − θ²/2), so
‖e^{iθ} − 1‖ ≤ |θ|.

**(F1) Absolute first moment.** N_abs(β) := ∫|x|Φe^{βx} = N(β) + 2∫_{x<0}(−x)Φe^{βx}
≤ (X+1)Z + 2M₁⁰, M₁⁰ := ∫_{x>0}xΦ ≤ C_u ≤ Z (e^β ≥ γ e^{πe⁴−9} since β ≥ R_u − 21).
Hence **N_abs ≤ (X+3)Z**.

**(F2) Second moment.** M₂(β) := ∫x²Φe^{βx}. Split: |x| ≤ X gives ≤ X²Z; the x > X tail
uses the unit-rate majorant (X+u)² e^{−ru} ≤ (X+1)²e^{−u} (r ≥ 3; (X+u)² ≤ (X+1)²(1+u)²
≤ (X+1)²e^{2u} ≤ (X+1)²e^{(r−1)u}) and the BZ-1 floor comparison with (X+1)² ≤ e^{2X}
(the exponent slack πβ² − (c+2)X is enormous), giving tail ≤ Z; the x < −X piece is
≤ e^{−βX}·M₂⁰ with M₂⁰ = ∫x²Φ ≤ 8C_u (x² ≤ 4e^{|x|}), hence ≤ Z. **M₂ ≤ (X+2)²Z + ...
≤ (X+3)²Z** (crude absorption; only the square-of-linear shape matters).

**(F3) Tilt perturbation.** For W = β + it: Z(W) − Z(β) = ∫Φe^{βx}(e^{itx}−1), so
|Z(W) − Z(β)| ≤ |t|·N_abs ≤ |t|(X+3)Z, and |N(W) − N(β)| ≤ |t|·M₂ ≤ |t|(X+3)²Z; also
|N(W)| ≤ N_abs ≤ (X+3)Z outright.

**(F4) Budget consequences.** With |t| ≤ τ(β) = 1/(32(X+2)) ≤ 1/(32(X+3))·(33/32)... use
τ' := 1/(32(X+3)) ≤ τ (statement uses the cleaner (X+2); proof route re-derives with (X+3),
so freeze the budget as τ(b) := 1/(32(log b + 3)) — **adjust statement: τ(b) = 1/(32(log b+3))**):
|ΔZ| ≤ Z/32, |ΔN| ≤ (X+3)Z/32. Then Re Z(W) ≥ (31/32)Z, |Z(W)| ∈ [(31/32)Z, (33/32)Z],
|Im Z(W)| ≤ Z/32, Re N(W) ≥ (X/8)Z − (X+3)Z/32 = (3X−3)Z/32... = 3(X−1)Z/32,
|Im N(W)| ≤ (X+3)Z/32.

**(F5) Log-derivative bounds off the ray.** L(W) = N(W)/Z(W) (Z(W) ≠ 0 by (F4)):
Re L(W) = (Re N·Re Z + Im N·Im Z)/|Z|²
≥ [3(X−1)·31/1024 − (X+3)/1024]·Z²/((33/32)²Z²) = (93X − 93 − X − 3)/1089
= (92X − 96)/1089 ≥ X/16 (for X ≥ 96·16/(92·16−1089) = 1536/383 ≈ 4.0; X ≥ 9 holds).
**Re L(W) ≥ (log β)/16.** And |L(W)| ≤ N_abs/((31/32)Z) ≤ (32/31)(X+3) ≤ 2(X+3) ≤ 4X
(X ≥ 3). **|L(W)| ≤ 4 log β.**

**(F6) Kernel bounds.** Diagonal: K₀(W,W) = (L+conj L)/(W+conj W) = Re L(W)/β (real!),
so D_j := K₀(W_j,W_j) ≥ log β_j/(16 β_j) > 0. Off-diagonal (j < k):
|K₀(W_j,W_k)| ≤ (|L_j| + |L_k|)/|W_j + conj W_k| ≤ 8 log β_k/β_k
(|W_j+conj W_k| ≥ Re = β_j + β_k ≥ β_k; |L_j|+|L_k| ≤ 8 log β_k). By the BZ-1 log-ratio
contraction (log β_k/β_k ≤ (2/R₀)^{2d}(log β_j/β_j) for β_k ≥ R₀^{2d}β_j) and the same
square-root manipulation: |K₀(W_j,W_k)| ≤ 128·(2/R₀)^d·√(D_j D_k)
(8A ≤ 8q^d√(BA) = 128q^d·√(B/16)√(A/16); D_j ≥ B/16, D_k ≥ A/16).

**(F7) Hermitian Gershgorin.** The matrix is Hermitian (`criticalLogDerivKernel_conj_symm`).
For c : Fin n → ℂ, E := c*Mc satisfies Im E = 0 (Hermitian pairing) and
Re E ≥ Σ_j ‖c_j‖²D_j − Σ_{j≠k}‖c_j‖‖c_k‖|M_jk| (Re z ≥ −‖z‖). With b_j := ‖c_j‖√D_j and
|M_jk| ≤ 128 q^{dist} √(D_jD_k), q := 2/R₀: same AM–GM + Nat.dist geometric row sums as
BZ-1; closure 2·128·2q/(1−q) ≤ 1 ⟸ 513q ≤ 1 ⟸ R₀ ≥ 1026, true since
R₀ ≥ (2π)²e^{2e+8} ≥ 36·256 = 9216. Hence Re E ≥ 0, so 0 ≤ E in the complex order.

**(F8) Bezoutian congruence.** For Re W > 1/2:
B(W_j, conj W_k) = ξ(W_j)·conj ξ(W_k)·K₀(W_j,W_k); with y_j := conj(ξ(W_j))·c_j the form
c*Bc equals y*K₀y ≥ 0; Hermitianity from K₀'s. The endpoint-shape instantiation is a matrix
rewrite. ∎

Numeric inputs: π > 3, 2 ≤ e < 2.72, cos θ ≥ 1 − θ²/2 — all mathlib-owned.

## Queued next

- Widen the budget (second-order oscillation cancellation should give |t| ≲ 1/√log or
  const; the binding term is |ΔN| ≤ |t|M₂).
- Mixed packets: some nodes real-tight, some tilted.
- The genuine deep-complex regime (|Im| ~ zero heights) — needs |Z(W)| lower bounds through
  the Γ-decay envelope; separate programme.

## Loop log

- 2026-08-29: card opened; Gates 1–3 recorded; paper proof complete with budget
  τ(b) = 1/(32(log b + 3)). Lean next.

## Status: [LEAN-PROVED] (2026-08-29)

BZ-2 is formalized, unconditional and premise-free, in two umbrella-wired modules
(built via `lake build`, 10906 jobs; all listed theorems audited on axioms
propext/Classical.choice/Quot.sound; lint clean):

`formal/GaloisForLFunctions/RHTower/XiRayComplexTiltedTransforms.lean` (1027 lines):
- `xiRayLaplaceAbsMoment`, `xiRayLaplaceSecondMoment` with integrability and the comparisons
  **`xiRayLaplaceAbsMoment_le`** (≤ (log b + 3)·Z) and **`xiRayLaplaceSecondMoment_le`**
  (≤ (log b + 3)²·Z) — the second moment via the three-piece split (middle X², reflected far
  side ≤ 4C_u by the x² ≤ 4e^{|x|} device and `mass_reflected_le` at rate b−1, right tail by
  the (X+u)² ≤ (X+1)²e^{(r−1)u} unit-rate majorant).
- The oscillation bound ‖e^{iθ}−1‖ ≤ |θ| (from 2−2cos θ ≤ θ²), and the tilt perturbations
  **`norm_thetaBilateralLaplace_tilt_sub_le`** (‖Z(b+it) − Z(b)‖ ≤ |t|·N_abs),
  **`norm_thetaBilateralLaplaceMoment_tilt_sub_le`** (≤ |t|·M₂),
  `norm_thetaBilateralLaplaceMoment_tilt_le` (‖N(b+it)‖ ≤ N_abs).
- `xiRayTiltBudget b = 1/(32(log b + 3))` and the off-ray log-derivative bounds
  **`re_logDeriv_xiCent_tilted_ge`** ((log b)/16 ≤ Re L(b+it)) and
  **`norm_logDeriv_xiCent_tilted_le`** (‖L(b+it)‖ ≤ 4 log b) inside the budget, via
  `Complex.div_re` and the 31/32–33/32 component sandwich; the constants close at
  (92 log b − 96)/1090 ≥ (log b)/16 for log b ≥ 5.

`formal/GaloisForLFunctions/RHTower/XiBezoutianComplexTiltedPacketPosSemidef.lean` (~670
lines):
- `xiRayPacketBase_ge'` (R₀ ≥ 9216, from public inputs only), tilted diagonal identity
  K₀(W,W) = Re L(W)/Re W (real, via `Complex.add_conj`), diagonal floor
  log β/(16β) ≤ D, off-diagonal ‖K₀(W_j,W_k)‖ ≤ 8 log β_k/β_k and the correlation
  ‖K₀(W_j,W_k)‖ ≤ 128(2/R₀)^d √(D_j D_k) via the exposed `xiRayLog_div_self_contraction`.
- Hermitian Gershgorin at complex vectors: imaginary part vanishes by the conjugate pairing
  of `criticalLogDerivKernel_conj_symm`; real part dominated with b_j = ‖c_j‖√D_j, geometric
  row sums (`natDist_geom_row_sum_le`, threshold 256q ≤ 1−q at q = 2/R₀ ≤ 1/513).
- **`posSemidef_criticalLogDerivKernel_tiltedPacket`**,
  **`posSemidef_thetaTailFirstMomentBezoutian_tiltedPacket`**, and
  **`posSemidef_thetaTailFirstMomentBezoutian_tiltedPacket_nodes`** (the literal endpoint
  quantifier shape): for every packet Re W_0 ≥ R₀, Re W_{m+1} ≥ R₀²·Re W_m,
  |Im W_m| ≤ 1/(32(log Re W_m + 3)), every rank, the criterion matrices are PosSemidef.

Also refactored (same builds): `XiBezoutianSeparatedRealPacketPosSemidef.lean` now exposes
`xiRayLog_div_self_contraction` and `natDist_geom_row_sum_le` publicly; module 1 exposes
`moment_reflected_le`, `mass_reflected_le`, `moment_even_split`, `laplace_even_split`.

Frontier consequence: the corpus's negative-packet no-go now reads — an RH-detecting negative
packet needs edge/close-ratio real parts, or an imaginary displacement exceeding the explicit
budget 1/(32(log Re + 3)) at some node. First unconditional multi-node complex-node stratum
of the criterion family. Labels: [LEAN-PROVED]; [NOVELTY UNVERIFIED] (new-to-corpus about
corpus-native objects; nothing multi-node exists externally even at real nodes).

# Theta tail kernel: CP part versus short-range deficit

- **ID:** `theta-kernel-cp-deficit-domination`
- **Stage:** 1-in-progress
- **Parent programme:** `source-contraction-two-volterra-domination` (cycle-6 representation change)
- **Type:** OWN CONJECTURE FAMILY / PRODUCER SEARCH
- **RH status:** the full domination is RH-equivalent through the kernel-PSD receiver; the
  conjectures below are strictly stratified (one stronger than RH-sufficient, one partial).

## Lean-proved foundation (unconditional; axioms propext/Classical.choice/Quot.sound)

`RHTower/ThetaTailKernelGeometricDeficitSplit.lean`:

- `thetaTailFirstMomentKernel_eq_orbitShift`: `k(x,t) = ∫_{s>0} (x+t+2s)·Φ(x+s)Φ(t+s) ds`.
- `thetaTailFirstMomentKernel_eq_geometric_add_deficit` (nonneg nodes): `k = 2·M + D` with
  `M(x,t) = ∫ √((x+s)(t+s))·ΦΦ`, `D(x,t) = ∫ (√(x+s)−√(t+s))²·ΦΦ` — the exact AM–GM split.
- `thetaTailGeometricKernel_quadraticForm_nonneg`: **M is manifestly PSD** — the quadratic form
  on any finite nonnegative node system is `∫ (Σᵢ aᵢ·√(xᵢ+s)Φ(xᵢ+s))² ds ≥ 0`. No arithmetic
  input: the first structurally positive main term in this receiver family.
- `thetaTailDeficitKernel_self`, `_nonneg`, `_comm`: D is entrywise nonnegative, symmetric, with
  identically zero diagonal (hence indefinite unless zero: short-range perturbation shape).

## Frozen conjectures (per scientific-method: statements before provability)

- **CP-1 [CONJECTURE, weak/partial]:** quantitative domination on separation-restricted packets:
  for node systems with prescribed minimal separation/bandwidth, `2M + D ⪰ 0` with explicit
  margin, provable from Schur-type tests on `D` against the square-family of `M`. Falsifier: a
  restricted packet class where margins degenerate faster than any Schur bound.
- **CP-2 [CONJECTURE, RH-sufficient, possibly false]:** the full kernel `k` is completely
  positive: `k(x,t) = ∫ m(x,u)m(t,u)dν(u)` with `m ≥ 0`. CP ⟹ PSD ⟹ RH. Could fail even under
  RH (doubly-nonnegative ≠ CP from order 5); a numerically non-CP section kills it cleanly.
- **CP-3 [LEAN-FALSIFIED, 2026-10-02; original sufficiency claim withdrawn]:** the double-commutator comparison
  `2C₁(x,t) ⪰ (√x−√t)²·C₀(x,t)` as forms, `C₀ = ∫ΦΦ`, `C₁ = ∫ s·ΦΦ` (from
  `{X,P} = 2√X P√X + [√X,[√X,P]]`). This is not the sufficient comparison supplied by
  that identity: writing `D₀=[√X,[√X,C₀]]`, the full kernel is
  `2√X C₀√X + D₀ + 2C₁`, so the required sufficient comparison has the opposite sign,
  `2C₁ ⪰ -D₀`. The original comparison remains a separate unproved conjecture about the
  literal theta kernel; no RH implication is claimed for it without another argument.
- **CP-3′ [LEAN-FALSIFIED, 2026-10-02; sufficient-only]:**
  `2C₁ ⪰ -[√X,[√X,C₀]]`. Together with `C₀ ⪰ 0`, this would make the full kernel PSD.
  This corrects the algebraic implication, not the missing theta inequality. The endpoint
  kernel `√X C₀√X` is distinct from the orbit-weighted geometric kernel `M` above.

## Corpus/no-go compliance

The corpus HCF no-go ("continuous scalar displacement kernels overcount close pairs; need signed
matrix covariance or genuine pair repulsion") marks exactly where naive domination of `D` must
fail: `D` is a displacement kernel. The frame turns that warning into a quantitative battlefield:
the required "pair repulsion" is now a concrete inequality between two explicit integrals of the
same positive family. Prior falsifications inherited from the parent card: no shape-class,
truncation, single-place, transport/jet, or Mourre-type mechanism can substitute.

## Queued probes

1. Numerics (pod): PSD/CP analysis of pointwise sections of `k`; cp-rank behaviour; CP-3 sign
   test; margin maps for CP-1 separation classes.
2. Paper: Schur-test bound for `D` against `M`'s square family on separation-restricted packets
   (CP-1 first theorem candidate).

## Loop log

- 2026-08-28: card opened with the Lean foundation already in place (split + manifest PSD of M).

## CP-1 first theorem: separated-packet positivity [PAPER-PROVED 2026-08-28, Lean build in progress]

**Statement.** Let `E(y) = e^{9y/2}e^{−πe^{2y}}`, `C_l = 2π(2π−3)`, `C_u = (1+W)·4π²` (the corpus
envelope constants of `HedenmalmThetaKernelEnergy`), `K* = 3C_u²e^{8π}/(2πC_l²)`,
`σ₀ = 2·log(1+2K*)`. For every σ ≥ σ₀, every base point x₀ ≥ 1, every packet
`x : ℕ → ℝ` with `x 0 = x₀` and `x_{m+1} ≥ x_m + σ`, every n and every real vector a:
`Σ_{i,j<n} a_i a_j k(x_i, x_j) ≥ 0`, where `k = thetaTailFirstMomentKernel` — the kernel whose
PSD at ALL finite node systems produces (through the double-Laplace identity and
`riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`) the Riemann hypothesis.
Unconditional; first PSD stratum of the live Bezoutian endpoint beyond the diagonal.

**Proof.** (1) *Diagonal floor.* For y ≥ 1 and δ := e^{−2y}: k(y,y) = ∫_{s>0}(2y+2s)Φ(y+s)²ds
≥ ∫_{(0,δ]} ≥ 2y·δ·(C_l E(y+δ))², using Φ ≥ C_l E (positive half-line) and E antitone (shift
law). Since e^{2δ}−1 ≤ 2δe^{2δ} ≤ 4δ (δ ≤ e^{−2} ≤ 1/4, e^{1/2} ≤ 2), E(y+δ) ≥ E(y)e^{−4π}.
Hence k(y,y) ≥ L(y) := 2C_l²e^{−8π}·y·e^{−2y}·E(y)².
(2) *Off-diagonal ceiling.* For 1 ≤ x ≤ t: Φ(x+s)Φ(t+s) ≤ C_u²E(x)E(t)e^{−ρs} with
ρ = π(e^{2x}+e^{2t}) ≥ πe^{2t} (shift law twice); ∫_{s>0}(x+t+2s)e^{−ρs} = (x+t)/ρ + 2/ρ²
≤ (x+t+1)/ρ (ρ ≥ 2). Hence k(x,t) ≤ U(x,t) := (C_u²/π)(x+t+1)E(x)E(t)e^{−2t}.
(3) *Correlation ratio.* U/√(L(x)L(t)) = [C_u²e^{8π}/(2πC_l²)]·(x+t+1)/√(xt)·e^{−(t−x)};
x+t+1 ≤ 3t and 3√(t/x) ≤ 3e^{(t−x)/2} (log t − log x ≤ t − x for x ≥ 1), so
k(x,t) ≤ K*e^{−(t−x)/2}√(L(x))√(L(t)) ≤ K*e^{−(t−x)/2}√(k(x,x))√(k(t,t)).
(4) *Scaled Gershgorin.* Gaps ≥ σ give x_j − x_i ≥ (j−i)σ, so with q = e^{−σ/2}:
k(x_i,x_j) ≤ K*q^{|i−j|}√(k_ii k_jj); |a_i a_j|k_ij ≤ K*q^{|i−j|}(a_i²k_ii + a_j²k_jj)/2;
row sums Σ_{j≠i}K*q^{|i−j|} ≤ 2K*q/(1−q) ≤ 1 exactly when σ ≥ σ₀. The form is
≥ Σ_i a_i²k_ii(1 − rowsum) ≥ 0. ∎

Everything is symbolic in (π, C_l, C_u, W): the only numeric facts used are 2π > 3
(π > 3), e ≥ 2, e ≤ 4, all mathlib-owned. Where the RH-difficulty survives: pairs with
separation < σ₀ — the close-pair displacement regime the HCF no-go named. Next quantitative
targets: shrink σ₀ (sharper diagonal slab, both-endpoint ρ), and the coincident-limit jet
strata (razor-thin near x = 0; encodes central-value margins; needs certified numerics —
queued, not claimed).

## CP-1 status update: [LEAN-PROVED] (2026-08-29)

The separated-packet theorem is formalized, unconditional and premise-free, in
`formal/GaloisForLFunctions/RHTower/ThetaTailSeparatedPacketPositivity.lean`
(umbrella-wired; all theorems on axioms propext/Classical.choice/Quot.sound; module built,
9651 jobs). The Lean surface:

- `thetaEnvelope_le_of_le` — the envelope is antitone on `[1,∞)` (from the corpus shift law).
- `integral_Ioi_id_mul_exp_neg_mul`, `integrableOn_Ioi_id_mul_exp_neg_mul` — half-line first
  Laplace moment `∫ s·e^{−cs} = 1/c²` (mathlib gap at this phrasing; via `Γ(2) = 1`).
- `integrableOn_thetaTailOrbit` — the orbit integrand is integrable on the half line
  (public replacement for the split module's private lemma; envelope majorant).
- `thetaTailKernel_nonneg_of_one_le` — entrywise nonnegativity on `[1,∞)²`.
- `thetaTailFirstMomentKernel_le_ceiling` — the off-diagonal Laplace ceiling
  `k(x,t) ≤ (C_u²/π)(x+t+1)E(x)E(t)e^{−2t}`.
- `thetaTailDiagonalFloor`, `thetaTailDiagonalFloor_pos`, `thetaTailDiagonalFloor_le` — the
  one-slab diagonal floor `k(y,y) ≥ 2C_l²e^{−8π}·y·e^{−2y}·E(y)²`.
- `ratio_identity_abstract` (private) — the division-free core of the correlation-constant
  identity, with the two exponential relations abstracted; kills the exp-bookkeeping cleanly.
- `poly_vs_exp` (private) — `(x+t+1)² ≤ 9xt·e^{t−x}` on `1 ≤ x ≤ t` (the log-vs-linear step).
- `thetaTailFirstMomentKernel_sq_le` — the squared correlation master
  `k(x,t)² ≤ (K·e^{−(t−x)/2})²·k(x,x)k(t,t)`, `K = thetaTailPacketRatioConstant`.
- `thetaTailFirstMomentKernel_le_corr` — the unsquared correlation bound.
- `thetaTailPacketRatioConstant`, `thetaTailPacketSeparation` (`= 2·log(1+2K)`), positivity.
- `geom_row_sum_le` (private) — off-diagonal geometric row sums `≤ 2q/(1−q)`.
- **`thetaTailFirstMomentKernel_separatedPacket_quadraticForm_nonneg`** — the main theorem:
  for every `σ ≥ thetaTailPacketSeparation`, every packet `x : ℕ → ℝ` with `x 0 ≥ 1` and
  `x (m+1) ≥ x m + σ`, every `n` and every real vector `a`,
  `0 ≤ Σ_{i,j<n} a i·a j·k(x i, x j)`.

Relation to the endpoint catalogue: `riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`
(`ThetaTailFirstMomentDoubleLaplace`) makes PSD of this kernel's Bezoutian transform on all
finite node systems exactly RH; this theorem is the first unconditional off-diagonal stratum of
that source-side condition — the burden now lives entirely in the sub-threshold (close-pair)
regime, exactly where the HCF displacement warning predicted. Labels: [LEAN-PROVED];
[NOVELTY UNVERIFIED] as new-to-corpus mathematics about a corpus-native object (the kernel has
no literature presence; no external priority claim made).

Next quantitative targets (unchanged): shrink the threshold (sharper slab, both-endpoint decay
rate, non-lossy `x+t+1 ≤ 3t`), extend the node domain below 1 via the reflection seam, and the
close-pair regime itself (CP-1's genuine frontier); the coincident-jet strata remain parked
(razor-thin margins near x = 0, need certified numerics).

## CP-3 and CP-3′ resolution: [LEAN-FALSIFIED] (2026-10-02)

`ThetaTailEndpointCommutatorObstruction` proves strictly negative quadratic
forms for both `2 C_1 - D_0` and `2 C_1 + D_0` on the literal complete theta
source, on nodes `(r,r+1)` for every sufficiently large `r`. The normalized
coefficient signs are respectively equal and opposite. On exactly those
nodes the full `H` matrix is positive definite eventually.

The new analytic ingredient is the first correction for `C_0`, proved from
the complete-source score limit. It shows that the first moment is negligible
at the endpoint-commutator scale. This excludes the auxiliary comparisons;
it does not refute full-kernel positivity or RH. The leading endpoint Gram
term cannot be discarded in this argument.

Exact statements, paper proof, positive survivor, and audit record:
[failed-comparison card](../5-failed/theta-endpoint-commutator-comparisons.md).

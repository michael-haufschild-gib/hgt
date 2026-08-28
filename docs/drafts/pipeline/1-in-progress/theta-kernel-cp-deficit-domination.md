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
- **CP-3 [CONJECTURE, sufficient-only]:** the double-commutator comparison
  `2C₁(x,t) ⪰ (√x−√t)²·C₀(x,t)` as forms, `C₀ = ∫ΦΦ`, `C₁ = ∫ s·ΦΦ` (from
  `{X,P} = 2√X P√X + [√X,[√X,P]]`). Sufficient for RH; expected false or tight — its failure
  pattern calibrates the next splitting of the affine weight.

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

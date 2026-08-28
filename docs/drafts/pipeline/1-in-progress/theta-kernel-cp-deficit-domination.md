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

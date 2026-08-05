# Cycle 7: recursive stability, threshold 1/σ(m) (2026-08-05)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-7 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsRecursiveStability.lean` (RHTower.GibbsGas),
wired, built, no sorry, axioms clean, one-iteration compile.

## The theorem
Let E_S(z,x) := P_S(z,x) − (1+z)^{|S|}. T0 gives EXACTLY
  E_{S∪p}(z,x) = E_S(z,x) + z·E_S(z,px),  E_∅ = e^{−x} − 1.
Induction + the elementary geometry `1 + p‖z‖ ≤ (1+p)‖1+z‖` (valid when 1 ≤ ‖1+z‖ and
‖z‖ ≤ ‖1+z‖) gives the RELATIVE estimate
  ‖P_S(z,x) − (1+z)^k‖ ≤ x·σ(m)·‖1+z‖^k,  σ(m) = ∏(1+p).
Hence (V3) `x·σ(m) < 1 ⟹ no zero with Re z ≥ 0` — Hurwitz stability, ALL k;
and (V4) every zero has ‖z+1‖ < 1 OR Re z < −1/2 (the strip between is zero-free).

## Why it beats W3 (cycle 6)
W3 needed x·m < 3^{−k}. The exponential came from taking moduli INSIDE the product
(∏(1+(1+‖w‖)p) ≤ m(2+‖w‖)^k). Keeping the relative form ‖·‖/‖1+z‖^k and absorbing the
dilation factor p by 1+p‖z‖ ≤ (1+p)‖1+z‖ creates no 2^k/3^k at all.
σ(m)/φ(m) = ∏(p+1)/(p−1) ≍ (log p_k)² ⟹ the threshold is within a POLYLOG factor of the
natural barrier 1/φ(m) (where T4's parity star reaches the unit circle).

## Open
Window x ∈ (1/φ(m), ~0.5) for general k (k ≤ 4 is stable at EVERY coupling, cycles 3–5).
Strong-coupling end: Kurtz anchor (O3) at x ≳ absolute constant (binding constraint is
j=1, essentially k-independent).

## Lean notes
- Quantify x INSIDE the statement (`∀ x, 0 ≤ x → ∀ z, … → …`) before
  `Finset.induction_on`, so the IH can be applied at both x and p·x. This is the formal
  shape of any two-scale recursion argument — reusable.
- No hypothesis `1 ≤ p` needed anywhere (only p ≥ 0 via Nat.cast_nonneg).
- `Complex.normSq_eq_norm_sq` + `Complex.normSq_apply` + nlinarith for both geometric
  lemmas (Re z ≥ 0 ⟹ 1 ≤ ‖1+z‖; Re z ≥ −1/2 ⟹ ‖z‖ ≤ ‖1+z‖).

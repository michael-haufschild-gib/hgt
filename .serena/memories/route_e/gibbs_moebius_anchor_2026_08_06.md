# Cycle 15: the arithmetic anchor — the gas IS Möbius (2026-08-06)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-15).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsMoebiusAnchor.lean`, wired, built, no sorry,
axioms clean.

## THE ANCHOR (closes an integrity gap from cycles 1–14)
For a finite set S of distinct PRIMES with m = ∏S:
  `gibbs_parity_eq_moebius_divisors` : gibbsDiag S x (−1) = ∑_{d ∣ m} μ(d)·e^{−dx}
  `gibbs_parity_eq_moebius_powerset` : the same as a powerset sum with μ(∏T) weights
  `moebius_prod_primes` : μ(∏_{p∈T} p) = (−1)^{|T|}  ← the gas's alternating sign IS μ
  `squarefree_prod_primes`, `cardFactors_prod_primes` (both by Finset.induction_on)
Re-indexing: `Finset.sum_nbij'` with T ↦ ∏T and d ↦ d.primeFactors, using
`Nat.primeFactors_prod` and `Nat.prod_primeFactors_of_squarefree`.

Until this cycle, "the parity point is Möbius" was an interpretive claim on the card, NOT a
Lean theorem. Now every cycle-1..14 theorem about the parity point is literally a theorem
about finite Möbius–Laplace sums. In particular:
  |∑_{d∣m} μ(d)e^{−dx}| = e^{−xm}·∏_ζ‖1+ζ‖
so a Möbius–Laplace sum is anomalously small IFF a gas zero condenses onto −1 (rate: T1/T2
of cycle 13).

## Lean traps
- `μ` notation requires `open scoped ArithmeticFunction.Moebius`. With plain
  `open ArithmeticFunction`, write `moebius` — otherwise autoImplicit binds μ as a variable
  and the error message is misleading ("Function expected at μ ... type ?m.1").
- `Finset.sum_nbij'` argument order: map, inverse map, mem, mem', left_inv, right_inv, value.
- α-equivalent goals after push_cast (`∏ p ∈ T, ↑p` vs `∏ i ∈ T, ↑i`) close with `rfl`.

## Repo integrity
Other sessions concurrently edit this tree; after their edits the full
`GaloisForLFunctions.RHTower` umbrella was re-verified: builds clean (17094 jobs).

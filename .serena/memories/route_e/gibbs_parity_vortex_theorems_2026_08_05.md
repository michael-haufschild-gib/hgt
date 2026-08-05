# The parity vortex of the squarefree Gibbs gas (2026-08-05)

Card: `docs/drafts/pipeline/1-in-progress/squarefree-gibbs-parity-vortex.md`.
Lean: `formal/GaloisForLFunctions/RHTower/GibbsParityVortex.lean` (namespace
`RHTower.GibbsGas`), wired, built, axioms clean.

New structural law for the (G2)/Route E coherent-mode frontier. Object:
P_S(z,x) = ∑_{T⊆S} z^{|T|}e^{−x∏T} (multiplicative-energy gas diagonal); parity point
z = −1 carries the Möbius–Laplace current ∑_{n|∏S} μ(n)e^{−nx}.

Proved (all unconditional, finite):
- T0 cutoff recursion: P_{S∪p}(z,x) = P_S(z,x) + z·P_S(z,px) — the exact "multiplicative
  cutoff boundary" of the (G2) card.
- T1: 2-element gas is Lee–Yang for ALL x (AM–GM + p+q < pq+1).
- T2 parity-jet law: P_S(−1+w,x) = w^k − x·∏(pw−(p−1)) + O(x²); current derivative at 0
  is (−1)^{k+1}φ(∏S) — Euler's totient is the vortex intensity.
- T3 parity-vortex (k=3): Δ(x) = −27φ²x² + O(x³) < 0 for small x > 0 ⟹ NO real
  factorization: the parity current itself drives the cluster complex. Lee–Yang fails
  maximally (k-star of radius (φx)^{1/k}, paper-level T4).
- T3′ current–discriminant inequality: 27a₃²e₀² ≤ 18a₃e₂e₁e₀ − 4e₂³e₀ + e₂²e₁² − 4a₃e₁³
  whenever the jet factors real: real-rootedness IS a current bound; lower bounds on the
  cluster discriminant are upper bounds on the parity current — the seam-flux observable
  in exact algebraic form (outside the mean-square σ-algebra per
  `mr-bilinear-scope-boundary`).

Consequence: every strong-Rayleigh/negative-dependence route to (G2) is structurally dead
(parity point = vortex center at k ≥ 3), upgrading the (G2) card's assertion to theorem.
OPEN CORE: infinite-volume discriminant/zero-repulsion lower bounds at scale x (full
strength = (G2) = RH); partial repulsion ⟹ partial current bounds — a graded route whose
rungs are cluster geometry, not zero-free regions.

SOTA check (2026-08): Lee–Yang literature has no multiplicative-energy gas (primon/Riemann
gas = Dirichlet weights, factorizes, trivial zeros); de Bruijn–Newman is the ξ-side.

## Lean traps
- set-bound reals opaque to ring — rw the defining eq first; HasDerivAt combinator chains:
  match value trees with `show ... from by ring` rewrite, NOT convert (convert using 1 on
  HasDerivAt can emit a function-eq goal ring can't touch).
- HasDerivAt.sum yields ∑-of-functions; convert with congr_of_eventuallyEq +
  Finset.sum_apply.
- hasDerivAt_mul_const avoids the RCLike instance diamond that (hasDerivAt_id).mul_const
  hits on ℝ.
- simp leaves −1−1+3−1 unevaluated (finish norm_num); {q} is not insert q ∅ syntactically.
- cubic Vieta from ∀w factorization: linear_combination at w = 0, ±1 (h1/2 ± hm/2 − h0).

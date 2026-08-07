# The restarted Euler sieve is a bounded cofinal unit profile (2026-08-07)

Module `RHTower/RouteRCofinalSieveIsUnitProfile.lean`, `lake build` green (11303 jobs), axioms
`[propext, Classical.choice, Quot.sound]`, in the umbrella. Closes the subsumption claim made — but
not proved — in `mem:route_r/harmonic_quantum_gap_criterion_2026_08_06`.

## What is proved

- `routeRCofinalSieveProfile e N p := if N ≤ e.symm p then routeRCofinalSieveDensity e N (e.symm p - N) else 0`
  — the sieve density transported from the tail index to the primes.
- `isCofinalUnitProfile_routeRCofinalSieveProfile` — it satisfies
  `IsCofinalUnitProfile primeHarmonicWeight`. Unit mass transports along the injective tail
  enumeration `n ↦ e (N + n)` by `Function.Injective.hasSum_iff`, consuming the sieve's own
  `hasSum_routeRCofinalSieveWeight`; escape holds because primes before the restart carry zero.
- `profileAverage_routeRCofinalSieveProfile` — the sieve reporter IS the profile average
  (`Function.Injective.tsum_eq`, support inside the range).
- `tendsto_routeRCofinalSieveHarmonicReporter_of_residue` / `_of_residueMod` — the sieve's
  coefficient recovery as a corollary of the universal law, and on the ENLARGED domain
  `ℓ¹ + o(1/p)` which its own development never covered.

Nothing about the Euler product survives in the proof: only boundedness, unit prime-harmonic mass and
cofinal escape. That is what makes this a subsumption rather than a renaming — and the reporter gains
a strictly larger domain than it was built with.

## Lean notes

- `Function.Injective.hasSum_iff (hi) (hf : ∀ x ∉ Set.range g, f x = 0) : HasSum (f ∘ g) a ↔ HasSum f a`;
  `Function.Injective.tsum_eq (hi) (hsupp : Function.support f ⊆ Set.range g) : ∑' c, f (g c) = ∑' b, f b`.
  Both live in the root `Function.Injective` namespace, not in the `InfiniteSum` files one greps first.
- A `Function.support` membership goal needs a `show` to beta-reduce before `rw` will fire.
- `rw` closes goals by `rfl` only at reducible transparency, so after rewriting, a residual
  `f (index n)` vs `f (e (N+n))` mismatch — defeq but through a plain `def` — needs an explicit `rfl`.

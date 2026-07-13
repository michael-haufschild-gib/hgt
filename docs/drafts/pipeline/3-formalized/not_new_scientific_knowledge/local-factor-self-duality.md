# Local factor self-duality

- **ID:** local-factor-self-duality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/orthogonality-meta-theorem.md` §5 and its `LocalFactorDuality` function-field polarization check; Lean file `formal/GaloisForLFunctions/RHTower/LocalFactorDuality.lean`
- **Statement:** If a finite Satake multiset is closed under inversion, then the local factor product `prod (1 - a*x)` is unchanged when every Satake parameter `a` is replaced by `a^{-1}`.

## Goal
This banks the exact finite Euler-factor self-duality floor used in the `F_q` side of the orthogonality meta-theorem: after weight normalization, the functional-equation pairing becomes inversion on the unitary parameter. It does not formalize global functional equations, archimedean factors, sheaf polarizations, Weil positivity, or Rankin-Selberg theory.

## Paper Proof
Let `s` be a finite multiset of complex Satake parameters and assume it is inversion-closed:
`map (a -> a^{-1}) s = s`. Then
```
prod_{a in s} (1 - a*x)
  = prod_{a in map(inv) s} (1 - a*x)
  = prod_{a in s} (1 - a^{-1}*x),
```
where the first equality uses inversion-closedness and the second is the functoriality of multiset map. This is just a relabelling of the finite product.

## Gates
- [x] 0 -> 1  in-progress: exact finite local-factor self-duality lemma extracted from the `F_q` polarization check.
- [x] 1 -> 2  fully-proven: paper proof above, by multiset relabelling under inversion.
- [x] 2 -> 3  formalized: Lean theorem `selfDual_localFactor_eq`; name checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: cite as the local Euler-factor self-duality certificate for the function-field polarization floor.

## Log
- 2026-06-19 — Leaner split this exact local-factor self-duality lemma from `orthogonality-meta-theorem` §5. The parent card remains outside `3-formalized` because the polarization lemma, Weil positivity import, realization-family scope, and universal orthogonality residual are not fully Lean-formalized.

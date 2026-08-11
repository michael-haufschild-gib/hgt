# Label-faithful multi-place assembly of the Gauss channel system

- **ID:** gauss-multiplace-label-faithful-assembly
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper + Lean; assembly layer)
- **Source:** rh-current-frontier-map.md §"Gauss quasi-inner multi-place assembly"; successor of
  card `gauss-propagated-iterate-log-mean`
- **Statement:** The Gauss channel system over any finite prime family assembles into one
  block-diagonal operator on the `ℓ²`-direct sum of the per-place circle spaces which (i) is
  exactly label-faithful — cross-place matrix elements vanish identically and each place's
  diagonal is the actual single-place diagonal; (ii) realizes the localized channel residue
  *per label* by the actual operators (`m = 1` at power one, `m = 2` at power two); (iii) has the
  existing scalar `gaussPairedChannelResidue` as its exact codiagonal collapse; (iv) retains the
  reflection data per place (sample-value conjugation, phase evenness, both frequency
  orientations as separate summands); (v) admits the canonical cofinal prime aperture
  `N ↦ (nth-prime : Fin π(N) → Primes)` with injective labels; and (vi) reads the source-zero
  horizontal carrier's prime-labelled orientation without erasing it: the assembled residue
  current is a strictly positive section of the same `(Nat.Primes → ℝ)` label bundle, its
  `log p`-normalization is the rational Weil-type local factor
  `(2/m²)·((p−1)/p)^{2m}·(p^m−1)²`, and its pointwise product with the carrier has the carrier's
  exact sign and critical radical at every label.

## Goal

This is step 2 of the intersection-form programme: turn the per-place laws (closed on the
predecessor card) into the multi-place object that the future Connes–Consani identification and
positivity law must consume, under the corpus's carrier design guardrails — prime labels never
summed before the final comparison, both reflection orientations retained, coefficient-faithful
landing.  The existing paired Schatten layer (`gaussPairedChannelResidue`, diagonal-model
realizations) is proved to be precisely the label-blind shadow of this object.  What this card
does **not** claim: identification with the literal CC intersection pairing and any positivity —
these remain the named continuations.

## Gates
- [x] 0 → 1  well-posed; frontier audited (paired layer is scalar-only; carrier fixes the label
      vocabulary; `PiLp 2` interface verified against the toolchain)
- [x] 1 → 2  paper content: block-diagonal assembly + exactness + per-label transport of the
      m ∈ {1,2} residue laws + collapse + aperture + carrier bridge (proofs are short given the
      predecessor card; recorded in module docstrings)
- [x] 2 → 3  formalized: `RHTower/GaussMultiPlaceAssembly.lean`; umbrella-wired; axiom-clean
- [ ] continuation: identification with the literal CC intersection/Weil pairing on the
      rational Bruhat–Schwartz core; the positivity/orientation law

## Design constraints honored (from the carrier)

1. Label space `(Nat.Primes → ℝ)` / `(J → ℂ)`: the assembled diagonal current and the residue
   current are label-indexed functions; the only summed statement is the explicitly named
   codiagonal-collapse theorem.
2. Reflection: per place, `d_{-i} = conj d_i` and `δ_{-i} = δ_i` are carried to the assembly;
   the two frequency orientations enter the current as separate summands.
3. Coefficient-faithfulness: the carrier bridge multiplies the carrier by the strictly positive
   residue current and proves sign and radical are exactly preserved at every label — no
   codiagonalization, no erasure.
4. Cofinality: the canonical aperture family has injective prime labels and its critical depth
   `2π(N)` is cofinal (existing `tendsto_gaussPairedCriticalDepth`).

## Log
- 2026-08-11 — created; frozen statement (i)–(vi); Lean module written and wired.

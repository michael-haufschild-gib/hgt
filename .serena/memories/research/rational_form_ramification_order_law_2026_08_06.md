# The local order law for rational forms (poles) — closed (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(still stage 2).

## Added to `GaloisForLFunctions/HTGeometry/LocalRamificationOrderLaw.lean`

The earlier version of the law only covered **ring elements**, i.e. non-negative orders.  The card
needs **poles** (`div Ω = −D`), so `c` must range over all of `ℤ`.

| statement | declaration |
|---|---|
| integer order of a ring element | `natOrd`, `natOrd_spec`, `natOrd_mul` |
| ramification scales it | `natOrd_map_eq_mul_ramification` |
| order of a quotient `a/b` scales | `ramificationOrder_frac` |
| **(8) for a form with poles** | `ramificationOrderLaw_frac` |
| **(9) for a form with poles** | `ramificationShiftLaw_frac` |

`ramificationShiftLaw_frac` is *literally* the `hlaw` hypothesis shape consumed by
`EigenvolumeRamificationSystem.lean`, so the chain local law → reduced horizon is now formal
end-to-end in the local model.  All axiom-clean.

Design choice worth reusing: rather than constructing a `ℤ`-valued valuation on the fraction
field (which needs `IsFractionRing` well-definedness plumbing or `HeightOneSpectrum.valuation`'s
`ℤᵐ⁰` encoding), state the law in **numerator/denominator form** — `natOrd a − natOrd b : ℤ` for
the rational form `a/b`.  That is honest, avoids all the localization glue, and is directly what
the card's `c_E` means.  `natOrd A a := (addVal A a).toNat`, with
`ENat.coe_toNat` + `addVal_eq_top_iff` for the round trip and `ENat.coe_inj` to descend
identities from `ℕ∞` to `ℕ`.

## Card status

Formal: (7) `TopExteriorPowerDeterminant`; (8)+(9) for regular *and* rational forms, both the `e`
(`addVal_map_eq_mul_ramification`) and the `e−1` (`TameEisensteinDifferentExponent`); steps 3,4,5
and conclusions (2)–(6) (`EigenvolumeRamificationSystem`, with the sharpened step 4 from
`research/eigenvolume_step4_sharpened_and_globalisation_recon_2026_08_06`).

Remaining: globalisation only.  The two concrete targets, both confirmed missing from mathlib:
1. divisor of a rational function as a cycle with **finite support**
   (`AlgebraicGeometry/AlgebraicCycle/Basic.lean` is a stub);
2. **pullback law for `AlgebraicGeometry.ord` along a morphism** — the scheme-level form of
   `natOrd_map_eq_mul_ramification`, with `Ring.ord_eq_addVal` as the intended glue.
Then identification of a rational top form with a coframe top wedge.  `N^1`/int-amplification is
now needed much less, because the sharpened step 4 only wants one ramified place per cycle.

## Repo hazard

`lake build GaloisForLFunctions.HTGeometry` was red earlier today on two other agents' broken
modules; they have since been fixed and it is green again (14908 jobs).  The lint gate still
reports one *other* agent's unwired untracked module (`HTGeometry.SubsystemComponentGenericity`).
Always `git status` before attributing a gate failure.

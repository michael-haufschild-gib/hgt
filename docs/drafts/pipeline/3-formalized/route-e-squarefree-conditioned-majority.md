# Route E: squarefree majority sign after conditioning

- **ID:** E-SQUAREFREE-CONDITIONED-MAJORITY-001
- **Stage:** 3-formalized
- **Target:** turn the proved within-history support bound into a signed source bound for the literal window-conditioned cell.
- **Status:** finite rigidity, invariant-weight anchor transport, and uniform literal-cell Möbius majority are closed in Lean; targeted build and axiom audit pass.
- **Parent:** [conditioned-slot divisor theorem](route-e-conditioned-slot-divisors.md).

## Scope correction that creates this target

The proved four-value theorem bounds receiver values inside each history.
It does not bound their union across different histories. No cell-wide
sign or load conclusion follows without an additional source law.
Squarefreeness of every physical receiver may supply that law.

## Theorem and proof

Fix positive integer factor arrays `a_c,b_c`, a singleton histogram with
`M>=30` slots, and a nonempty family of histories whose every receiver is
squarefree and lies in `[L,L+W]`. Keep `A=prod_c a_c`. Assume the proved
source inequalities give `W<A` and at most four distinct receiver values
inside every history. The intended family is the literal full histogram
restricted by these physical conditions; it is invariant under common
slot permutations. Arbitrary further conditioning need not have that
invariance and is outside the parity claim below.

1. Distinct inactive factors are pairwise coprime. Given components `c,d`,
   at most two slots activate one of them. Since `M>=3`, another slot
   contains both `a_c,a_d`. Their product divides its squarefree receiver,
   so `a_c` and `a_d` are coprime.
2. If two different slots have the same receiver `n`, then `A` divides
   `n`. For each component, at least one of the two slots is inactive,
   hence `a_c` divides `n`. Pairwise coprimality combines these divisibilities.
3. Distinct multiples of positive `A` differ by at least `A`, so at most
   one multiple of `A` fits the common interval because `W<A`. This is a
   statement about the fixed interval and factor arrays, independent of
   history.
4. Every history has a repeated value since `M>4`. By steps 2–3 it is the
   same integer `n_star` throughout the nonempty family. Every other value
   occurs at most once; the four-value bound leaves at most three such
   slots. Thus at least `M-3` slots equal `n_star` in every history.
5. Since `n_star` is squarefree, `mu(n_star)` is `+1` or `-1`. The signed
   slot sum therefore obeys
   `mu(n_star) * sum_r mu(n_r) >= M-6` in every history.
6. For the uniform law on a family invariant under common slot
   permutations, every anchor has the same distribution. Double-counting
   first gives the stronger positive statement
   `P(n_anchor=n_star)>=1-3/M`. It also gives anchored signed mean of magnitude at least
   `1-6/M`, with orientation `mu(n_star)`. The same argument should hold
   for any nonnegative weight invariant under those permutations. This weighted statement is
   now formalized without dividing by total mass: `(M-6)*sum_x w_x` is at most `M` times the
   oriented weighted sum at every fixed anchor.

This would obstruct small anchored Möbius bias for the literal conditioned
squarefree singleton source with fixed activation powers. It would not
bound the Gamma--Hankel covariance of arbitrary prefixes, and it would not
exclude different occupancy laws or source families failing the power bound.

## Deriving the remaining geometric inequality

The closed bounded-activation theorem gives `L^10<=A^11` and the actual
window gives `W^55<L^30`. Hence `W^55<A^33<=A^55` because `A>=1`, so
`W<A`. No logarithmic baseline hypothesis needs to be added.

## Lean formalization

`RouteESquarefreeConditionedMajority.lean` closes:

- `inactive_factors_pairwise_coprime` and `baseline_dvd_of_repeated_receiver`;
- `image_card_le_four_of_no_five_distinct`, converting the prior selected no-five theorem into
  the exact support-cardinality premise;
- `width_lt_baseline_of_power_separation`, deriving `W<A` from `L^10<=A^11`,
  `W^55<L^30`, and `A>=1`;
- `squarefree_singleton_family_mobius_majority`, giving one common squarefree `n_star`, at most
  three exceptions per history, and the oriented lower bound `M-6`;
- `routeE_invariant_weighted_anchor_sum_eq`, transporting any nonnegative swap-invariant source
  weight to a fixed anchor;
- `routeESquarefreeWindowFamily_anchorSwap_mem_iff`, proving that the literal histogram cell
  filtered only by squarefreeness and the physical window is closed under common slot swaps;
- `squarefree_power_bounded_uniform_conditioned_anchor_majority`, which combines the existing
  source-derived power bounds with uniform source weights and has no added anchor-invariance,
  support-cardinality, or baseline-width premise.

The first deep search is complete but partial; it returned no checked
ingredient sets. Source inspection found
`RHTower.finset_prod_dvd_iff_of_pairwise_coprime` in
`EulerDeletionQuasiShuffleCylinderClosure.lean`,
`Nat.coprime_of_squarefree_mul`, `Squarefree.squarefree_of_dvd`, and
`routeEComponentHistoryAnchorSwap_mem_cell_iff`. These are candidate
ingredients used by the verified proof. A September 2026 broad arXiv search also found the
odd-dependence/coboundary criterion for signed cycle systems; it reinforces that bounded local
sign rules do not certify global pairing consistency, but supplies no arithmetic source bound.

## Remaining frontier

This route is obstructed, not closed toward RH. Under any fixed activation-power bound and the
actual aperture, squarefree singleton cells have overwhelming same-sign anchored bias. A surviving
prime-factor relation must therefore use receiver support growing with slot count, a different
occupancy law, or cancellation between products, while retaining literal source weights. It must
still prove unsigned incidence/load dispersion, co-degree/Hall expansion, moving-cutoff flux, and
the strict-half all-scale source estimate. The theorem gives none of those estimates and does not
imply RH.

## Final audit

`lake env lean GaloisForLFunctions/RHTower/RouteESquarefreeConditionedMajority.lean` and
`lake build GaloisForLFunctions.RHTower.RouteESquarefreeConditionedMajority` pass. The module is
wired into `RHTower.lean`; no umbrella build was run. `#print axioms` for the family, invariant-weight,
and uniform literal-cell capstones reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` token occurs in the module. Repository-wide
`scripts/formal_tools.py lint` currently stops on unrelated untracked
`RHTower.ZetaBinomialHalfKaramataLaw`, which another dirty-worktree task has not yet wired into the
umbrella; this route module itself is wired and built.

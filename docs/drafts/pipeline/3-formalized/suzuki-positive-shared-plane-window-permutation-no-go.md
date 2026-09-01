# Suzuki positive shared-plane window-permutation no-go

- **Stage:** 3-formalized
- **Claim:** `[LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Route:** CCM-FU
- **Proof-chain target:** eliminate cutoff-dependent reordering confined to one macroscopic source window as the missing nonlocal pre-scalar producer.

## Frontier

- `[CORPUS]` `SuzukiPositiveSharedPlaneOrderedProductNoGo` proves divergence for the canonical increasing word. Its pair-surplus lemma is order-free for any list whose cells share the same positive plane.
- `[LOCAL-RESEARCH]` fixed local Cartan germs, fixed shared-reservoir quadratic scalarizations, and bounded Robin observers are terminal. Any survivor must cancel center trace before scalar passage.
- `[LITERATURE]` Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v2, leaves the nonlocal finite-interval operator limit conjectural. Suzuki's canonical-system and screw-line papers give RH receivers, not a permutation-dependent positive `SL₂` source product. Matrix-product literature supplies general positive-matrix inequalities but no arithmetic Suzuki window-permutation result.
- `[NOVELTY AUDIT]` No internal or external theorem found for arbitrary cutoff-dependent permutations of the literal `(2n,5n]` Suzuki cells.

## Exact claim

Let `order n` be any list permutation of the canonical labels in `(2n,5n]`. Keep the canonical prefix `[2,2n]` and suffix `(5n,20n]`, replace only the middle list by `order n`, map every label `k` to the literal nonnegative cell `suzukiCenterStokesCartanCell (20n) k`, and form the same shared positive `SL₂` word. Add the forced quadratic counterterm and subtract the literal regular Ward mass. Then this completed observable tends to `+∞` as `n→∞`, uniformly in the choice of `order`.

## Dependency-closed paper proof

Write `X(xs)=log((positiveSharedPlaneWord xs)₀₀)-Σ_{x∈xs}log(1+x)`.

1. Every literal cell in `[2,20n]` is nonnegative. Superadditivity of `X` under concatenation therefore gives
   `X(prefix ++ middle ++ suffix) ≥ X(middle)`.
2. Filter `middle` by primality. The corpus filter inequality gives
   `X(middle) ≥ X(primeSublist)-L(nonprimeSublist)`,
   where `L` is the sum of `log(1+x)` over the complementary proper-prime-power cells.
3. List permutation commutes with filtering and mapping. Hence `primeSublist` is a permutation of the canonical prime-cell list, and `nonprimeSublist` is a permutation of the canonical nonprime-cell list. In particular, the latter has exactly the same `L`, bounded by the existing proper-prime-power loss `o(sqrt n)`.
4. For `n≥exp(20)`, every prime cell in `(2n,5n]` lies in `[delta_n,1]`, with `delta_n=log(2n)/(4sqrt(20n))`. These membership bounds and list length are permutation-invariant. The order-free pair lemma therefore yields
   `X(primeSublist) ≥ floor(card/2) log(1+delta_n/4)`.
   The existing Chebyshev prime-block cardinality argument, which uses only that length and those cell bounds, gives
   `X(primeSublist) ≥ sqrt(n)/(1024 sqrt(20))`.
5. Thus every permitted order satisfies
   `X(fullOrderedList) ≥ sqrt(n)/(1024 sqrt(20)) - primePowerLoss(n)`.
6. Permutation preserves the full logarithmic cell mass. Expanding the completed observable therefore gives exactly
   `2 log((word fullOrderedList)₀₀)+quadraticCounterterm-regularWardMass`,
   with no redefinition of the source quantity.
7. The existing unconditional limits say `primePowerLoss(n)/sqrt(n)→0` and `Green(log(20n))/sqrt(n)→0`; the cubic remainder is nonnegative. Dividing the lower bound by `sqrt n` leaves positive limit inferior `1/(512sqrt(20))`. Hence the completed observable tends to `+∞`.

All quantifiers are unconditional. No RH premise, zero input, computation, or fitted order is used.

## Hostile attack and positive survivor

- Moving only zero/nonprime labels cannot defeat the proof; filtering records their exact total logarithmic loss.
- Adversarial dependence of `order n` on the cutoff does not enter any estimate.
- Claim does **not** cover phase-twisted/indefinite cells or permutations moving a macroscopic portion of prime mass across prefix/window/suffix boundaries.

`[LEAN-PROVED]` The conjecture survives hostile attack. Exact positive boundary: a permutation-based CCM-FU survivor must perform macroscopic cross-scale transport; within-window adaptive rearrangement is rigidly divergent.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.SuzukiPositiveSharedPlaneWindowPermutationNoGo`
- Exact semantic guard: `suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable_eq`
- Uniform divergence: `tendsto_suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable_atTop`
- Route-class certificate: `no_bounded_suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable`
- Source check: `lake env lean GaloisForLFunctions/RHTower/SuzukiPositiveSharedPlaneWindowPermutationNoGo.lean` passed.
- Final audit: `lake build GaloisForLFunctions.RHTower.SuzukiPositiveSharedPlaneWindowPermutationNoGo` passed.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint reports only pre-existing unrelated umbrella-reachability debt; this module is wired into `GaloisForLFunctions.RHTower` and contains no forbidden declaration.

# PW closed-relation endpoint tomography

- **ID:** PW-CRET
- **Stage:** 3-formalized
- **Type:** ROUTE-CLASS KILL
- **Source:** `ThetaCuspHawkingParikhWilczekBoundedPacketCountableTomography` + `SourceLinearClosedRelationSplitting`
- **Statement:** Physical PW endpoint packets `v_j(n)=exp(-(j+1)(n+1))` are total in `ℓ²`; every closed relation dark on all `(v_j,0)` is source-nonselective, and every single-valued one is the zero everywhere-defined relation.

## Goal
Kill every closed possibly unbounded/multivalued/singular linear Hilbert/Gram positive PW-B endpoint mechanism. Chain: PW endpoint winding → closed positive quadratic response → all-scale partner darkness → source-nonselectivity; single-valued response → trivial response. This does not assume Xi data or RH.

## Gates
- [x] 0 → 1 in-progress: source-pure statement, exact chain, hostile tests
- [x] 1 → 2 fully-proven: totality + closed-relation rigidity
- [x] 2 → 3 formalized: target module, target build, axiom audit
- [ ] 3 → 4 publication-ready

## Approach
1. Construct `v_j : ℓ²(ℕ,ℂ)` from corpus nodes `q_j`.
2. If `x ⟂ v_j` for all `j`, `lp.inner_eq_tsum` gives a bounded complex power series vanishing at every `q_j`; apply corpus zero-sequence uniqueness to real and imaginary parts, hence `x=0`.
3. The zero-output fibre of a closed relation is closed. It contains `span {v_j}`, hence all `ℓ²`. Thus membership depends only on vertical fibre; single-valuedness kills that fibre.

Hostile falsifiers: failure of `ℓ²` totality; graph-closed relation with nonclosed zero fibre; energy zero without zero output. The singular-flat scalar carrier is not a counterexample unless it supplies a closed linear positive response containing all endpoint packets.

Literature audit: standard Hardy-kernel totality and closed-operator facts are known; no source found connecting the prescribed PW scales to closed unbounded quadratic-response tomography. Novel claim is the exact PW-B route-class closure.

## No-go closure
- **Exact theorems:** `schwarzschildParikhWilczekClosedRelationEndpointDarkNonselective`; `schwarzschildParikhWilczekClosedRelationEndpointDarkRouteKilled`.
- **Mechanism:** physical endpoint packets have dense complex span in `ℓ²`; closed zero fibre is full, making every relation source-nonselective; single-valuedness then kills output.
- **Strongest positive survivor:** nonclosed/domain-excluding, indefinite, nonlinear/nonpointwise response.
- **New insight:** closed unboundedness, multivaluedness, and singular partial domains cannot retain source information under physical all-scale endpoint darkness.
- **Lean:** direct check and target build pass; axioms only `propext`, `Classical.choice`, `Quot.sound`; wired into `RHTower.lean`.

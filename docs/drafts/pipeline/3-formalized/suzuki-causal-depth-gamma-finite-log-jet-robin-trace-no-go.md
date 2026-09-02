# Suzuki causal-depth Gamma finite-log-jet Robin-trace no-go

- **ID:** CCM-FU-C29
- **Stage:** 3-formalized
- **Type:** THEOREM / producer-class no-go
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Source:** `irregular-stokes-robin-gamma-holonomy-coercivity.md` C1--C28
- **Module:** `GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaFiniteLogJetRobinTraceNoGo`
- **Terminal theorem:** `no_suzukiCausalDepthGammaFixedLogJetWardProducer`
- **Statement:** Every fixed logarithmic Wigner--Smith/Robin jet of the actual causal-depth Gamma
  feature is nuclear and cannot yield a lower-semibounded rectangular Ward defect through a
  uniformly bounded response.

## Exact claim and proof

For `q_(p,e)=p^(e+1)` and fixed `k≥0`, scale the `(p,e)` source column of the actual feature `F`
by `(log q_(p,e))^k`; call the resulting operator `F_k`.

The corpus gives

`weight(p,e)=A_p r_p^e`, `A_p ≤ C(1+log p)p^(-5/4)`, and `0<r_p≤r<1`.

Moreover `log q_(p,e)=(e+1)log p`. Hence

`(log q_(p,e))^k weight(p,e)`

is dominated by the product of

`C (log p)^k(1+log p)p^(-5/4)` and `(e+1)^k r^e`.

The prime factor is summable because every fixed logarithmic power is absorbed by exponent
`5/4>1`; the depth factor is a polynomial times a geometric series. Tonelli gives joint `ℓ¹`.
The unscaled feature-column norm is at most `weight(p,e)`, so the scaled column norms are jointly
summable. Their canonical rank-one expansion is therefore nuclear, proving `F_k∈S¹`.

For any response family `R_N` with one operator-norm ceiling,

`|Re Tr(F_k R_N†)| ≤ ‖F_k‖₁ sup_N ‖R_N‖ = O(1)`.

Thus this correction is `o(N)`. The corpus theorem
`no_sublinear_transitionCore_rectangularWardProducer` excludes eventual lower semiboundedness of
the rectangular Ward defect.

## Source fidelity and hostile audit

The multiplier is the exact source charge: the corpus Weyl relation gives Wigner--Smith value
`log(p^(e+1))`. C28 alone does not imply the theorem because trace ideals are not stable under an
arbitrary unbounded multiplier; the new input is the all-log-moment source decay above.

Fixed `k` is essential. The theorem does not cover cutoff-growing jet order, super-polynomial or
singular functional calculus, norm-growing response, or a non-nuclear moving source. Suzuki's 2026
screw-function operator framework and standard Wigner--Smith literature do not state this
source-specific nuclearity/no-go. Abstract polynomial-geometric summability and trace duality are
classical; novelty claim is only exact CCM-FU producer-class kill.

## RH-chain consequence and positive survivor

`finite-order source Weyl/Robin jet → F_k∈S¹ → bounded response correction O(1) → sublinear →`
`no_sublinear_transitionCore_rectangularWardProducer`.

- **Killed class:** every fixed jet order paired with a uniformly operator-bounded response.
- **Exact obstruction:** all fixed logarithmic source moments remain trace class, so trace duality
  caps every correction at `O(1)`.
- **Strongest positive survivor:** cutoff-growing order, genuinely singular functional calculus,
  norm/graph-weak blow-up, singular trace, or a moving source that loses `S¹` after weighting.

## Lean certificate

Lean proves the full chain, not a wrapper:

- exact fixed-log source factor and joint prime-depth summability;
- Hilbert--Schmidt kernel and nuclear/Schatten-class-one operator;
- exact source-column scaling and Wigner--Smith charge identification;
- bounded-response correction sublinearity;
- closed capstone
  `no_suzukiCausalDepthGammaFixedLogJetWardProducer :
  ¬ Nonempty SuzukiCausalDepthGammaFixedLogJetWardProducer`.

The producer structure internalizes fixed order, uniform operator-norm ceiling, and eventual Ward
semiboundedness. Terminal theorem therefore has no premise and adds no route hypothesis.

## Audit

- Corpus search found exact existing module and declarations before any Lean construction.
- `lake env lean GaloisForLFunctions/RHTower/SuzukiCausalDepthGammaFiniteLogJetRobinTraceNoGo.lean`:
  passed on 2026-09-02.
- `lake build GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaFiniteLogJetRobinTraceNoGo`:
  passed on 2026-09-02 (`Build completed successfully (12327 jobs)`).
- Existing declaration audit reports only `propext`, `Classical.choice`, `Quot.sound`; not rerun
  because no Lean declaration changed.
- Formal lint confirms module is umbrella-reachable and clean. Repository-wide lint remains red
  only on unrelated existing unwired modules.
- No full or umbrella build was run. No computation was used.

## Gates

- [x] exact source-pure claim and RH chain fixed
- [x] dependency-closed paper proof and hostile audit
- [x] exact unconditional Lean theorem
- [x] direct file check, targeted module build, axiom and umbrella-reachability audits
- [ ] publication-ready

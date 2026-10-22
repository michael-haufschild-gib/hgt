# Suzuki wall-light prime-power finite-linear-carrier no-go

- **ID:** RH-SUZUKI-LIGHT-FINITE-LINEAR-CARRIER-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every finite packet of distinct literal Suzuki prime-power positive-light amplitudes is complex-linearly independent as a function of real height; likewise for the negative-light amplitudes. Consequently neither complete light family factors through any fixed finite-dimensional complex-linear carrier.

## RH proof chain

Literal prime-power wall field → exact FE-reflected positive/negative light completion → actual Robin/Gamma/holonomy Ward assembly → shared Ward endpoint → HB / FZZ-P / PW-B / RBH endpoint → RH.

This theorem kills the fixed finite-dimensional linear-carrier producer at the first arrow. It does not assume or prove the remaining global Ward assembly. Any survivor must retain unboundedly many prime-power frequency directions, or use a genuinely nonlinear/singular source stage before global compensation.

## Exact theorem

For `pe = (p,e)`, set

`λ(pe) = log(p^(e+1))/2 > 0`

and let `A(pe)` be the Suzuki critical entry-wall bare amplitude. For any finite type `ι` and injective `source : ι → Nat.Primes × ℕ`, both families

`k ↦ (t ↦ suzukiCriticalWallPositiveLightAmplitude t (source k).1 (source k).2)`

and

`k ↦ (t ↦ suzukiCriticalWallNegativeLightAmplitude t (source k).1 (source k).2)`

are `ℂ`-linearly independent.

Equivalently, every `M`-source packet spans exactly `M` source directions. Therefore, for every finite-dimensional complex vector space `V` and every complex-linear decoder `D : V → (ℝ → ℂ)`, at least one prime-power positive-light amplitude and at least one negative-light amplitude lie outside `range D`.

## Complete paper proof

Write `χ_r(t)=exp(i r t)`. Distinct characters of the additive real group are complex-linearly independent (Dedekind independence of characters).

The corpus square-root weld gives

`ω_pe(t) = A(pe) χ_{λ(pe)}(t)`.

The bare-amplitude square is the strictly positive von-Mangoldt far-hinge weight, so `A(pe) ≠ 0`. Unique factorization makes `pe ↦ λ(pe)` injective, and every `λ(pe)` is positive.

For an injective finite packet, the `2|ι|` frequencies

`{ λ(source k), -λ(source k) | k ∈ ι }`

are pairwise distinct: equality within either sign follows from frequency injectivity; equality across signs contradicts positivity. Hence all corresponding characters are linearly independent.

The light definitions and height reflection give

`L⁺_k(t) = A_k/2 · χ_{λ_k}(t) + i A_k/2 · χ_{-λ_k}(t)`,

`L⁻_k(t) = A_k/2 · χ_{λ_k}(t) - i A_k/2 · χ_{-λ_k}(t)`.

If `Σ c_k L⁺_k=0`, character independence forces the coefficient of `χ_{λ_k}` to vanish for every `k`, so `c_k A_k/2=0`; because `A_k≠0`, every `c_k=0`. The identical positive-frequency coefficient proves the negative-light case.

For the carrier conclusion, let `r=dimℂ V` and choose `r+1` distinct sources, for example `(2,k)` for `k=0,…,r`. If all their light amplitudes were in `range D`, choose preimages `v_k`. A relation among the `v_k` maps under `D` to a relation among the independent light amplitudes, so the `v_k` are independent. This gives `r+1≤r`, contradiction. The proof uses no injectivity, continuity, boundedness, positivity, or sign condition on `D`.

## Hostile audit

- **Internal:** corpus already proves exact local light completion and a weaker fixed-finite-positive-rank escape under a uniform per-channel ceiling. Corpus search found no independence theorem or arbitrary finite-linear-carrier obstruction for these literal light amplitudes.
- **External (checked 2026-08-31):** Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function* (arXiv:2206.03682v4), *The screw line of the Riemann zeta-function and its applications* (arXiv:2209.04658v3), *On the Hilbert space derived from the Weil distribution* (arXiv:2301.00421v3), and *Weil's quadratic form via the screw function* (arXiv:2606.09096v2) study Weil forms, localized operators, finite-dimensional restrictions, and conjectural nonlocal limits; they do not state this prime-power light-family independence or carrier obstruction. General character independence is classical and not novel.
- **Verdict:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` as a new exact application and route-class obstruction; scientific priority remains subject to independent expert review.

## Positive survivor

The literal positive and negative Suzuki light-source spans are algebraically infinite-dimensional, with exact finite-packet dimension equal to source count. Thus a faithful FE-reflected wall assembly cannot compress source before compensation into any fixed finite complex-linear state space.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.Suzuki.SuzukiWallLightPrimePowerFiniteLinearCarrierNoGo`
- Packet theorems: `suzukiCriticalWallPositiveLightAmplitude_linearIndependent`, `suzukiCriticalWallNegativeLightAmplitude_linearIndependent`
- Capstone: `suzukiCriticalWallLightFixedFiniteLinearCarrierRouteKilled`
- Target build: PASS
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`

## Gates

- [x] 0 → 1: source-pure, exact route class, falsifiable
- [x] 1 → 2: dependency-closed proof above; no RH premise
- [x] 2 → 3: exact Lean theorem, targeted build, axiom audit; global lint sees module wired and fails only on unrelated unwired concurrent modules

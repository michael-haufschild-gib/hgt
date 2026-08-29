# Xi Gamma-six literal collision-current residue

- **Route:** HC
- **Stage:** 3 — formalized in Lean 4
- **Active claim:** one
- **Frontier map:** read-only; no edit planned

## Frontier

- `[CORPUS]` `XiGammaSixFilteredBoundaryConfluentFlux.lean` constructs the unique natural
  coefficientwise-continuous harmonic boundary layer and proves its derivative flux has scaled
  wall residue `log 2 / m²`.
- `[CORPUS]` `XiGammaSixFilteredBoundaryControl.lean` factorizes the literal filtered Gamma-six
  second jet by three additional positive radial local factors and classifies its prime
  summability wall.
- `[CORPUS]` `XiHorizontalCollisionGaussHodgePrimeCurrent.lean` proves that summability of the
  multiplicity-faithful Gauss--Hodge current is exactly the zero-collision/RH receiver. It does
  not identify that endpoint current with the differentiated filtered boundary jet.
- `[LITERATURE]` Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494,
  supplies a theta differential-pair boundary problem but no primewise Gamma-six collision-current
  residue.
- `[LITERATURE]` Kawalec, *On the series expansion of the prime zeta function about s=1 and its
  coefficients*, arXiv:2603.21535, analyzes the prime-zeta singularity at one but does not track
  the HC Gauss/Gamma/Fisher radial factors or the dyadic differentiated boundary layer.

## Conjecture

`[CONJECTURE]` Let

`A_m(p)=(1-p⁻¹)^(2m)(1-p⁻ᵐ)²(1+p⁻¹)⁻²`

and let `J~_{m,p}(t)=K_{m,p}(t)A_m(p)` be the literal Gamma-six jet interpolated in horizontal
depth. For every `m≥1`:

1. `J~` specializes coefficientwise to the literal filtered Gamma-six second jet at every Xi copy.
2. For every `t>0`, the literal collision-current `∂ₜJ~_{m,p}(t)` is absolutely summable over
   primes.
3. The radial factors do not change the wall residue:
   `t∑ₚ ∂ₜJ~_{m,p}(t) → log 2/m²` as `t→0+`.

Thus the literal filtered source has a universal nonzero collision anomaly. Absolute summability
at each positive depth is true, but it does not provide the zero-collision Gauss--Hodge endpoint;
any claimed weld must account for the surviving wall residue.

## Hostile audit

- The conjecture is false if `A_m(p)` has a nonunit limit at the prime end. Exact local factors
  instead satisfy `A_m(p)=1+O_m(p⁻¹)`.
- Pointwise convergence `A_m(p)→1` is insufficient because flux mass escapes to large primes as
  `t→0+`. A uniform summable loss majorant is required.
- The loss current should satisfy
  `0≤K'_{m,p}(t)(1-A_m(p))≤2(log 2/m²)(2m+5)log(p)/p²`, uniformly for `t>0`.
  This would make its total uniformly bounded and force its depth-scaled contribution to zero.
- Even if proved, this does not prove RH: the established Gauss--Hodge endpoint current is a
  different multiplicity-faithful source object. The result is a compatibility/no-go constraint
  on any proposed identification, not permission to identify the two currents.

## Paper proof

`[PAPER-PROVED]` Put `C=log 2/m²`, `B=2m+5`, and

`A=A_m(p)=(1-p⁻¹)^(2m)(1-p⁻ᵐ)²(1+p⁻¹)⁻²`.

The exact filtered-jet factorization already proved in the corpus gives `J~=KA`, and therefore
specialization at `t=primeDepthBVWoldXiCenteredRate(q)` gives the literal second jet. The local
factor estimates used in the confluent-defect theorem give

`0≤A≤1`, `0≤1-A≤B/p`.

For `t>0`, the proved counterterm derivative formula is

`K'_{m,p}(t)=2C(W_{t/2}(p)-W_t(p))`,

where `W_d(p)=log(p)p^(-1-2d)`. Since `0≤W_t≤W_{t/2}`, the derivative is nonnegative; multiplying
by `0≤A≤1` preserves absolute summability. This proves absolute prime summability of the literal
collision-current `J'=K'A` at every positive depth.

For the loss current `L_p(t)=K'_p(t)(1-A_p)`, monotonicity also gives

`0≤W_t≤W_{t/2}≤W_0=log(p)/p`.

Hence, uniformly for `t>0`,

`0≤L_p(t)≤2CB log(p)/p² = 2CB W_{1/2}(p)`.

The right side is summable by the existing positive-depth prime-log Dirichlet theorem. Therefore
`0≤∑L_p(t)≤M_m` for one constant independent of `t`, and
`t∑L_p(t)→0` as `t→0+` by squeezing. Coefficientwise and after absolutely convergent summation,

`K'=J'+L`.

The already-proved limit `t∑K'_p(t)→C` now yields

`t∑J'_p(t)=t∑K'_p(t)-t∑L_p(t)→C=log 2/m²`.

Every premise is unconditional. The proof establishes positive-depth summability while proving
that the literal filtered current retains, rather than cancels, the canonical wall anomaly.

## Lean status

`[LEAN-PROVED]` `XiGammaSixFilteredBoundaryCollisionCurrent.lean` formalizes the radial-factor
bounds, specialization to the literal filtered second jet, its derivative, absolute prime
summability at positive depth, the uniformly summable `log p/p²` loss, exact flux splitting, loss
vanishing after depth scaling, and the universal residue `log 2/m²`. Source check and target-only
`lake build` pass. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Status

`FORMALIZED; SURVIVES HOSTILE ATTACK`. The theorem proves the filtered-current route has a
nonzero anomaly; a valid HC-to-Gauss--Hodge weld must cancel or transport it by genuinely new
source structure.

## Subsequent diagonal-landing audit

`[LEAN-PROVED, 2026-08-29]` The positive bounded coefficientwise weld is now ruled out. Filtered
flux is strictly positive and prime-summable at positive depth, whereas Gauss--Hodge mass is zero
on a critical Xi copy and nonsummable off line. Bounded diagonal landing is exactly RH-strength,
and literal equality is impossible copywise. See
`formal/GaloisForLFunctions/RHTower/XiGammaSixFilteredBoundaryDiagonalLandingNoGo.lean` and the
stage-5 card `hc-filtered-gamma-six-diagonal-landing-no-go.md`.

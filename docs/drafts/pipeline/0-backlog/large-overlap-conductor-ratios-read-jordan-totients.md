# Large-overlap conductor ratios read Jordan totients

- **ID:** large-overlap-conductor-ratios-read-jordan-totients
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** completed coprime Fourier-tail series; boosted cubic-spline transform.
- **Statement:** For the tilted unit spline, `E_m(c)/E_1(c) → J₈(m)/ϕ(m)` as `c→∞`, for every positive conductor `m`.

Here `J₈(m)=Σ_(d|m) μ(m/d)d⁸`.

## Goal

Identify the arithmetic operator surviving after the completed energies
shrink to zero. A positive rescaled limit would distinguish conductor
weights by an exact multiplicative invariant, beyond a common tail floor.
The intended capstone is the actual finite-packet limit at
`c_N=log log N`: for one explicit `K>0`,

`c_N⁷ completeWeilEnergy(Σ a_m v_(m,N)) → K Σ (J₈(m)/ϕ(m)) a_m²`.

This identifies the positive arithmetic form surviving growing overlap,
including mixed entries. Transfer depends on the packet quasimode estimate
currently under formalization. No contribution counted.

## Approach

The existing definition is the exact finite identity
`E_m(c)=ϕ(m)⁻¹ Σ_(d|m) μ(m/d) d E_1(c/d)`.
Thus the scalar asymptotic `c⁷E_1(c)→K>0` would give
`c⁷E_m(c)→K Σ_(d|m) μ(m/d)d⁸/ϕ(m)=K J₈(m)/ϕ(m)`.
No interchange with an infinite conductor sum is needed.

The positive repayment series for conductor one reduces that scalar
asymptotic to `c⁷T(c)→K_tail>0`, where `T` is the Fourier tail.
Its upper Fourier bound gives a summable eighth-power majorant.
`TheShellsRepayEveryConductor.completedConductorEnergy` already supplies
the finite Möbius identity, and `MobiusDivisorSectionSignLaw` supplies the
prime-factor product for Möbius inverse-power sums.

The boosted cubic-spline Fourier formula has a positive periodic
numerator over `(1+r²)^4`. Its tail asymptotic should follow by separating
the periodic mean and integrating its bounded-primitive remainder.
`PeriodicMeanZeroAveraging` and `PaperDirichletPeriodicPrimitive` supply
the averaging mechanism and periodic-primitive construction. The exact
Fourier input is `WeilDeletionTestKit.paperFT_unif` and `paperFT_upow`,
combined with `paperFT_tiltedSource`.

## Gates

- Novelty search found completed-energy positivity, conductor comparison,
  vanishing energies and polynomial bounds; no Jordan-totient limit.
- Exact periodic numerator, tail asymptotic and Jordan divisor identity
  remain to be checked and proved in Lean.
- Keep separate from the growing-overlap packet theorem; no new claim
  follows from its polynomial lower bound alone.

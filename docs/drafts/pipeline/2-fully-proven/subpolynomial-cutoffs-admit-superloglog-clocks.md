# Every subpolynomial cutoff admits a super-log-log clock

- **Stage:** 2-fully-proven; Lean written, checks pending.
- **Type:** THEOREM (paper).
- **Wall:** Σ1d.
- **Statement:** For every nonzero compact real `C²` profile and every conductor cutoff `R(N)` with `log(max(1,R(N)))/log N→0`, there is an explicit clock `Cφ,R(N)/log log N→∞` retaining margin `(log N)^(-η)/4` on `V_R(N)` for every `0<η<1/2`, uniformly for `1≤c≤Cφ,R(N)`.

## Mechanism

Put `L=log N`, `t=log L`, `R'=max(R,floor L+2)`, and `ρ=(1+log R')/L→0`.
Cap the existing spectral clock by `t/sqrt ρ`. Its ratio to `t` still tends
to infinity; it remains at most `t²`.

Polarization and balanced rescaling of the linear quadratic overlap bound give
the bilinear bound `|⟨overlap u,v⟩|≤Cφ c‖u‖‖v‖`.
It makes the coefficient-low/high
comparison cost `Oφ(cρ)`, whose ratio to `t` is at most `Oφ(sqrt ρ)→0`.
Terminal weighted payment absorbs the near error into prime adjunction.
For `Q=floor(L^q)`, `q=(1−2η)/4`, the high gap is proportional to `qt`.
All remaining horizon errors vanish: `R'=N^o(1)`, `c≤t²`, and the terminal
coefficient has a factor `1/L`. The logarithmic low floor and mixed residual
budget are already proved throughout the original spectral clock.

The clock is independent of `η`; the eventual horizon may depend on `η`.
This subsumes every fixed iterated-log cutoff and gives every subpolynomial
conductor cutoff a super-log-log positivity interval.

## Uniform horizon bounds

For `L≥2`, put `A=max(1,R)`. Then `R'≤2AL`, so
`0≤ρ≤log A/L+(1+log 2)/L+t/L→0`.
Consequently `R'≤N^(1/16)` eventually, and the frame condition follows.
For `c≤t²`, `1+log c≤2t` and `Q≥L^q/2`, the retained overlap rate is at most

`t sqrt ρ + 2t^5/L + 2t^6/L^(q/2) + 2L^6/N^(1/4)`.

The terminal coefficient is at most `4t^10/L+2L^10/N^(7/8)→0`.
Thus its budget is discharged, the overlap cost divided by `t` tends to zero,
and `D+log c+1=o(t)` uniformly. Since `log Q≥qt−log 2`, the high gap exceeds
one eventually. All polynomial-size geometry follows from `R'≤N^(1/16)`.

## Low block and mixed pairing

Take `q=(1−2η)/4>0`. The spectral clock supplies `E_m(c)≥L^(−η)` for all
conductors. Since `2q+2η<1`, the summed raw squared residual on `m≤Q` is at most
`L^(−2η)/128`. The frame inequality gives low-block coercivity `L^(−η)/2`.
The mixed pairing is at most `L^(−η)‖p‖‖z‖/8`; the orthogonal high block has
margin one. Their sum retains `L^(−η)/4` on `V_R'`, hence on `V_R`.

## Lean boundary

- The quadratic bound in `TheLinearMomentRemovesTheOverlapLogarithm.lean` is checked
  with a clean axiom audit. Its bilinear consequence
  `exists_overlapMatrix_inner_le_linear` in
  `LinearOverlapBoundsControlBothPacketArguments.lean` is also directly checked,
  with only `propext`, `Classical.choice`, `Quot.sound` in its transitive audit.
- `LinearOverlapComparisonRetainsItsCutoffRatio.lean` retains the explicit `cρ`
  cost in the coefficient split; directly checked with only the three standard
  axioms in its transitive audit.
- `TerminalPaymentRetainsTheGrowingHighConductorGap.lean`: terminal payment with
  the explicit linear cutoff ratio and cubic lag remainder; directly checked,
  with only the three standard axioms in its transitive audit.
- `SubpolynomialConductorRatiosSetExplicitOverlapClocks.lean`: augmented-cutoff
  ratio and divergent clock ratio; directly checked, with only the three
  standard axioms in both transitive audits.
- `SubpolynomialCutoffsRetainGrowingHighConductorGaps.lean`: uniform terminal,
  lag and geometric horizon; directly checked, with only the three standard
  axioms in its transitive audit.
- `EverySubpolynomialSpanHasASuperLogLogPositivityClock.lean`:
  `eventually_subpolynomial_span_coercivity`; written, unchecked.

The cutoff condition defines the claimed class; no additional spectral or prime-distribution hypothesis is assumed.

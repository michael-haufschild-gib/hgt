# Polynomial conductor spans at growing overlap

- **Stage:** 3-formalized.
- **Wall:** Σ1d.
- **Statement:** A universal `B>0` gives, for every nonzero compact real `C²` profile on `[0,1]`, a prefactor `aφ>0` such that, for every `0<θ<1/1080` and `0<β<1/4`, eventually
  `Wφ,c,N(x)≥aφ exp(-Bc)‖x‖²`
  on `V_floor(N^θ)`, uniformly for `1≤c≤(log log N)^β`.

## Proof

For a unit packet on `V_R∩V_Q^⊥`, put `E=Σ_m(log m+tameDifferent(m))a_m²`.
The harmonic lower frame gives `Σa_m²≤2` and weighted coefficient mass
`G≤2+E`. The center pairing squared is bounded by
`Cφ c²(2+E)`; the merged overlap/downward pairing squared is bounded by
`Cφ c⁴(2+log c)(2+E)`, under the existing polynomial-span horizon
conditions. If `z²≤D(2+E)`, then
`|z|≤E/32+8D+1/16`. The separated remainder costs `Oφ(c²)`;
the upward term costs `Oφ(c sqrt(1+log c))`; the self term costs
`Oφ(1+log c)`; the two-pole term vanishes.
Prime adjunction therefore leaves

`W(u)≥E/16+(log Q)/4−Cφc⁴(1+log c)`.

Take `L=log N`, `t=log L`, `Q=floor(L^(1/8))`, and `R=floor(N^θ)`.
All horizon conditions hold because `1080θ<1` and `2θ,6θ<1`.
The high gap tends to infinity: `log Q=t/8+O(1)`, whereas
`c⁴(1+log c)=O(t^(4β)(1+log t))=o(t)`.

The existing universal log-log low-block theorem applies since
`t^β=o(t)`. Shrink its positive prefactor to at most one and write
`e=aφ exp(-Bc)`. The summed low-block raw residual is at most `e²/128`
eventually; choose a fixed overlap multiple `γ>0` with `2Bγ≤1/4`.
The lower frame and Cauchy–Schwarz bound the mixed pairing by
`e‖p‖‖z‖/8`. Orthogonal splitting retains at least `e/2` times the
full squared norm. All constants in this margin are independent of
`θ,β`; only the horizon changes.

## Lean

- `EveryProfileHasAPolynomialHighConductorLoss.lean`: direct check passed; transitive audit contains only `propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.
- `EveryProfileIsPositiveOnPolynomialSpansAtGrowingOverlap.lean`: `exists_universal_growing_overlap_polynomial_span_coercivity` directly checked; transitive audit contains only `propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.
- The raw residual and mixed-pairing inputs are checked in `EveryPolylogConductorSpanIsPositiveAtLogLogOverlap.lean`.

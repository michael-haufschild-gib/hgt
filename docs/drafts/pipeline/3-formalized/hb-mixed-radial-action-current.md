# HB: Einstein radial current of the mixed metric

Status: the metric-jet current identity is formalized. The source-specific horizon calculation below is analytical, with its two polynomial reductions scratch-checked. The complete causal pairing, its extinction and RH remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Proved tensor identity

For the original BM background

`g=diag(-f,1/f,r²/y²,r²/y²)`, `f=r²-1`,

let h and k have arbitrary symmetric mixed time/radial-angular metric entries and arbitrary first jets of those entries. Define the current by differentiating the existing Einstein action boundary current, including its volume ratio, in the two metric directions:

`omega^r = (r²/y²) [d_h(theta_g(k)^r)-d_k(theta_g(h)^r)]`.

The exact result is

```
omega^r = sum_A [h_tA*(partial_t k_rA-partial_r k_tA)
                 -k_tA*(partial_t h_rA-partial_r h_tA)].
```

The proof differentiates the inverse matrix, connection variation and relative volume. The two mixed connection variations agree and cancel in the antisymmetrization. Evaluation of the remaining full contraction gives the displayed formula; all angular first jets were retained during evaluation. The current uses only first metric jets, so the choice of second jets is immaterial. The final theorem takes an actual exterior point and discharges every nondegeneracy condition internally. It assumes no field equation, inverse, zero pairing, or extinction law.

This is the radial current density in the increasing-r direction. The outward orientation at the horizon has the opposite sign. It is not an assertion about an integrated, renormalized Peierls form.

Lean: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedRadialActionCurrent`, theorem `RHTower.D4BMMixedActionCurrent.mixed_radial_action_current`.

## Source-specific horizon calculation — analytical

Use the actual global mixed-stream response covectors `A_s=fullAngularCovector q branch`, `J=fullSquareCovector q`, and `k_s=s(s-1)/4`. For the existing particular stream, write

```
F_s(r) = a²*(1+1/r)^(2s)*(A_s-k_s*J/r²),
Psi_s(v,r) = chi(v)*exp(2s*v)*F_s(r),
chi = Real.smoothTransition.
```

This is switching the stream and reconstructing its metric. It is not yet identification with the retarded solution. The previous `timeOriginalForcing` is a switched current source; the corpus already retains its extra differentiated-onset tensor in `switchedCurrentSource_eq`. That source identity alone does not identify the reconstructed stream with the causal response.

Since `v=t+tortoise(r)`, actual reconstruction gives, in ingoing coordinates,

```
h_vA = exp(w*v)*[(chi'+w*chi)*F_A+f*chi*F'_A],
h_rA = -exp(w*v)*chi*F'_A,                         w=2s.
```

The time/radial curl is unchanged by this coordinate substitution:

```
partial_t h_rA - partial_r h_tA
  = -exp(w*v)*[2*(chi'+w*chi)*F'_A
               +2*r*chi*F'_A+f*chi*F''_A].
```

At the horizon put `X_s=A_s-k_s*J`, `Y_s=-s*X_s+2*k_s*J`. Then

`F_s(1)=a²*2^(2s)*X_s`, `F'_s(1)=a²*2^(2s)*Y_s`.

For opposite source rates `t=-s-3`, with amplitude b for the second stream, the radial current therefore has horizon value

```
omega_hor(v) = -a²*b²/32 * exp(-6*v) *
  [(chi'+2s*chi)*(chi'+(2t+1)*chi) * dot(X_s,Y_t)
   -(chi'+2t*chi)*(chi'+(2s+1)*chi) * dot(X_t,Y_s)].
```

Here dot is the sum of the two covector component products. No angular integral, adjoint identification or cusp boundary term has been suppressed by this notation.

Let

```
B_s = (2s+3)*dot(X_s,X_t)
      +2*k_t*dot(X_s,J)-2*k_s*dot(X_t,J),
e = (s+1)*(s+2),
C_chi = integral_0^infty exp(-6v)*chi(v)^2 dv,
D_chi = integral_0^infty exp(-6v)*chi'(v)^2 dv.
```

Both integrals converge. Integration by parts gives `integral exp(-6v)*chi*chi'=3*C_chi`: the lower endpoint is zero and the upper endpoint decays. Expanding the current yields

```
integral_0^infty omega_hor(v) dv = -a²*b²/32 *
  [(D_chi-(4e+7)*C_chi)*B_s
   +4*C_chi*(s*k_t*dot(X_s,J)-t*k_s*dot(X_t,J))].
```

The polynomial identity giving this expansion passed a scratch Lean check. The actual reconstructed-field derivative and horizon-limit identification, and the improper-integral theorem, are not yet formalized. In particular, the formula includes a squared onset-derivative contribution. Replacing this tensor current by a scalar master Wronskian would lose that term. No counterexample to full extinction is asserted.

## Exact spectral coefficient to test — no domain claim

Set `alpha=(2s+1)*(2s+2)`, `beta=(2t+1)*(2t+2)`. In a formal angular spectral coordinate lambda, the response equation gives the candidate multipliers

`X_s=[alpha/(lambda-alpha)-k_s]*J`,
`X_t=[beta/(lambda-beta)-k_t]*J`.

The denominator-cleared numerator of B_s is exactly

```
B_s multiplier = (2s+3)*P_e(lambda)/[16*(lambda-alpha)*(lambda-beta)],

P_e(lambda) = (e-2)*(e-6)*lambda²
             -2*(4e³-13e²-36e+108)*lambda
             +4e*(4e-3)*(e²+28).
```

This identity also passed a scratch Lean check. It is a coefficient target, not an admitted spectral expansion: the full theta square and global response have cusp tails. Using this multiplier in an actual angular pairing requires the original domain, cutoff and cusp boundary contributions. Those obligations remain present.

## Continuing cancellation test

The active conjecture is that the complete causal pulse response cancels the displayed mixed-sector horizon contribution at the fixed clock, and that the complete physical tensor pairing vanishes. Keep the source amplitudes independent when testing this: for branch polarizations `(aS,aV)` and `(bS,bV)`, SV–SV carries `aS*aV*bS*bV`, SS–VV carries `aS²*bV²`, and VV–SS carries `aV²*bS²`. These are different monomials. Their coefficients cannot be combined unless the actual source construction proves the required polarization relation. No such relation is imposed to fit the result. Every other sector pairing and its physical orientation remains required for full extinction. The immediate source calculation is the causal pulse contribution to the same SV–SV coefficient; a generic scalar normalization or another no-go certificate does not answer that test.

The formalized current is a needed input to this specific cancellation attempt. It does not construct the SS/VV responses or prove the conjecture.

## Validation

The final source passed `lake env lean` in scratch. One isolated `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedRadialActionCurrent` compiled the requested leaf in 28 seconds, reading 2630 required old corpus modules from frozen caches. No dependency, full or umbrella build ran. Lake emitted only bootstrap warnings about the temporary dependency manifests; the Lean leaf emitted no warnings. The audited source and installed source are byte-identical, as are its installed olean/ilean files. The new import is wired into RHTower.

The one new public theorem's axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The two analytical coefficient identities were checked separately in scratch with the same axiom set; they are not installed as standalone corpus theorems. Index refresh, static lint with generated-file checks, and scoped whitespace checks passed. No numerical computation was used. Owned Lean/Lake processes completed; the owned scratch and isolated audit package were removed.

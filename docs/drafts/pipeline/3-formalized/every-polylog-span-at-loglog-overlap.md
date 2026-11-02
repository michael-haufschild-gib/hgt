# Every polylogarithmic conductor span at log-log overlap

- **ID:** every-polylog-span-at-loglog-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Σ1d; exponential low floors and logarithmic high-conductor gap.
- **Statement:** There exist universal `B,α>0` such that every nonzero real compact `C²` profile supported on `[0,1]` admits `a>0` with
  `Wφ,c,N(x)≥a exp(-Bc)‖x‖²`
  eventually on every `V_{⌊(log N)^A⌋}`, `A>0`, uniformly for `1≤c≤α log log N`.

## Proof

Take the universal `B>0` of `exists_universal_loglog_overlap_coercivity`
and put `α=1/(128(B+1))`. Write `L=log N`, `t=log L`,
`q=1/8`, `Q=⌊L^q⌋`, and `R=⌊L^max(A,q)⌋`.
The low-block theorem gives a constant `a₀>0`, independent of `A`, with
`W(p)≥e‖p‖²` on `V_Q`, where `e=min(a₀,1)exp(-Bc)≤1`.

At `k=4`, the generic individual quasimode estimate sums to
`Σ_(m≤Q)‖r_m‖² ≤ Cφ[t⁷L^(-1/2)+t¹²L^(9/4)/N²]`.
Since `2Bα<1/4`, multiplication by `exp(2Bc)` bounds this by
`Cφ[t⁷L^(-1/4)+L¹⁵/N²]→0`, uniformly in the stated overlap interval.
Consequently the raw residual sum is eventually at most `e²/128`.
The lower Riesz bound gives coefficient mass at most twice packet norm
squared, hence residual synthesis norm at most `e‖p‖/8`.
For `z⊥V_Q`, all diagonal quasimodes pair to zero, so
`|⟨Wp,z⟩|≤e‖p‖‖z‖/8`.

The general-profile high-conductor theorem gives, on unit vectors in
`V_R∩V_Q^⊥`,
`W≥(log Q)/4−log c−Cφ`.
All nine error terms vanish: each is a fixed power of `t` divided by a
positive power of `L`, or a fixed power of `L` divided by a positive
power of `N`. The same comparison discharges the geometric horizon bounds.
Since `Q≥L^q/2`, `log Q≥qt−log 2`, whereas
`log c≤c≤αt≤t/128`, the high-block lower bound tends to infinity.
It is eventually at least one.

For `x=p+z`, the orthogonal projection onto `V_Q` preserves membership
in `V_R`. The mixed term costs at most
`e(‖p‖²+‖z‖²)/8`. Thus `W(x)≥e‖x‖²/2`.
Monotonicity of conductor spans includes the requested span in `V_R`.
Set `a=min(a₀,1)/2`; it is independent of `A`.

## Lean

`CriticalArithmeticCorrelationTheory/EveryPolylogConductorSpanIsPositiveAtLogLogOverlap.lean`:
`exists_universal_loglog_overlap_all_polylog_coercivity` passed its direct
Lean check and transitive axiom audit: only `propext`, `Classical.choice`,
`Quot.sound`. The module is wired into the umbrella. All residual,
geometric and high-band horizon bounds are discharged in the theorem.

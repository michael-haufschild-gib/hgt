# The Gamma scale after radial integration

- **Stage:** 1-in-progress.
- **Question:** Can radial integration retain a fixed positive fraction of the local Gaussian model at every rank?
- **Sources:** `BesselTailCoshMoment`, `FirstAtomGaussianHorizon`, `NativeTailReserve`.

Let `B_q(b)=besselFirstAtomTailDensity (b/2) q`, `q≥3`, and `M_k(q)=∫b^(2k)B_q(b)db`. The corpus gives `B_q>0` and a finite cosh moment at every `0≤η<π/2`.

Candidate quantitative boundary:

`0≤[2^k/(2k)!] M_k(q)≤C(q)(8/9)^k`,

where `C(q)=2π besselFirstAtomExponentialTail (cos(3/2)) q`. The proposed proof uses `t^(2k)/(2k)!≤exp(|t|)≤2cosh(t)` at `t=3b/2`, followed by the exact cosh integral. Thus the normalized moments tend to zero. No fixed positive multiple of `(2k)!/2^k` can be retained by every actual first-atom moment.

The local Gaussian mass model has candidate moments `π(2k)!/k! · ∫_q^∞u^(k+3/2)(2u−3)²exp(−2u)du`. For `q≥3`, dropping the square leaves a weaker comparison model. The corpus's exact incomplete-Gamma recurrence gives `powerTail(k+3/2,q)≥k!/2^k · powerTail(3/2,q)>0`. Thus even the weaker model retains a positive fixed fraction of `(2k)!/2^k`. The moment normalization and its exact relation to the physical Gaussian model must be checked in Lean before claiming a model obstruction.

Positive survivor sought: an explicit all-degree source moment bound in the actual analytic-strip scale. Subsequent aggregate payment should retain the exact integrated source norm or a suitably rescaled Gamma norm. The complete unequal-pair and infinite-remainder payment remains open.

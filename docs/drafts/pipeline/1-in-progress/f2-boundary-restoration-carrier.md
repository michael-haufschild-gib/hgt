# F2 — retain the boundary coordinate in source-operator transport

- **Stage:** 1-in-progress
- **Target:** Upgrade corrected core eigenlaws to a source-operator intertwining on an explicit period carrier.
- **Dependency:** [Audited global identity and evaluation-coordinate recovery](../3-formalized/f2-global-core-hecke-correction.md).

## Candidate exact restoration

Assume `0<Re s<1/2`. Write `w=2s`, `A(a)=1+a^(−w)`, `P(a)=a⁻¹+a^(1−w)`, and let `α,β` be the two evaluation coordinates. Put `R f=f+α(f)A+β(f)P`.

Direct evaluation predicts `2(Rf)(2)=(Rf)(1)` and `ker R=span{A}`. Thus restoring the completed period alone loses one coordinate. Retaining `α(f)` should give a bijection onto

`{g : 2g(2)=g(1)} × ℂ`,

with inverse

`(g,c) ↦ g−cA−g(1)/(w−1) P`.

For the actual core, this pair is `(E_s,ζ(w))`. At resonances the second coordinate vanishes.

On the resonant channel, the simpler maps

`C g=g−g(1)/(w−1)P`, `R₀ f=f+f(1)/(w−3)P`

are inverse on all physical functions when `w≠1,3`. Conjugation `C T_p R₀` therefore gives an actual transported source action. To identify it with the explicit corrected Hecke formula on a full period carrier, prove the boundary evaluation law `(T_p g)(1)=(1+p^(1−w))g(1)` there. For `p=2`, inversion and the Lewis equation give `g(2)=g(1)/2`, which supplies this law.

## Open work

Audit the exact restoration and carrier statements; prove the source evaluation law and carrier invariance without importing an eigenfunction assumption. Tie the carrier to actual PM cores. Any full-prime algebra or topology claim requires its own proof. None of these identities supplies Krein positivity.

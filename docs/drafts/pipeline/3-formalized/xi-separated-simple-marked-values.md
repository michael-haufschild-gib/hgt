# Separated inverse disks and simple marked Xi values

- **ID:** RH-XISS-20261007
- **Stage:** 3-formalized
- **Parent:** `../1-in-progress/xi-logarithmic-islands-monodromy.md`
- **Verdict:** BRIDGE; novelty uncertified; no RH conclusion

## Exact endpoints

For any finite real slope set A, selected real slope a, M>0 and real R,
there is a holomorphic logarithmic inverse h on ball(0,M), with Re(h)>R,
d_a(h(w))=exp(w), and |d_b(h(w))|!=1 for every b in A different from a.
Here d_a(s)=xi(s)*exp(-a*s). The selected slope need not belong to A.

For every real a,R there is s with Re(s)>R, d_a(s)=-1, and analytic order
of1+d_a at s exactly1. At that point d_b(s)!=-1 for every real b!=a.
There is no zero-location, critical-value, RH, or regular-value premise.

## Dependency-closed proof

On an a-island, |d_b(h(w))|=exp(Re(w)+(a-b)*Re(h(w))). Put
Q=sum_(b in A)(M+1)/|a-b|, with the b=a summand zero. Use an island beyond
max(R,Q+1). Each nonzero |a-b| then satisfies M<|a-b|*Re(h(w)), whereas
|Re(w)|<M. The displayed exponent cannot vanish, proving separation.

For the simple value, the established far-right estimate supplies B>=2 with
Re(xi'/xi)>=a+1 on Re(s)>=B. Nonzero-value occurrence gives d_a(s)=-1 beyond
max(B,R). Its derivative d_a*(xi'/xi-a) is nonzero, so1+d_a has order1.
Another mark equal to-1 would give exp((a-b)*Re(s))=1 and hence b=a.

## Prior work and scope

The corpus already proves global disjointness of equal-radius exponential
translates in `XiSignedFactorZeroSeparation`. All-real-label disjointness
is not a new claim. The additional formal content is far-right simplicity
and separation over the entire inverse disk. Classical logarithmic-derivative
and univalence inputs were audited in the parent. These are analytic inputs
to its finite-packet monodromy proof, not a proof of joint monodromy.

## Formal audit

- `RHTower/XiMarkedIslandSeparation.lean`: two public theorems.
- `RHTower/XiSimpleMarkedValues.lean`: one public theorem.

Two targeted builds pass. Both actual-source `lake env lean` checks pass.
All three public axiom closures are exactly propext, Classical.choice,
Quot.sound. Both imports occur once in RHTower. No admission or heartbeat
change. Matching proof scratches removed after final audits.

Evidence: `/tmp/rh-XiMarkedIslandSeparation-build.log`,
`/tmp/rh-XiSimpleMarkedValues-build.log`,
`/tmp/rh-final-XiMarkedIslandSeparation.log`,
`/tmp/rh-final-XiSimpleMarkedValues.log`,
`/tmp/rh-xi-marked-analytic-axioms.log`.
Global lint status belongs to the ongoing topology assembly; no claim that
unrelated concurrent leaves pass lint.

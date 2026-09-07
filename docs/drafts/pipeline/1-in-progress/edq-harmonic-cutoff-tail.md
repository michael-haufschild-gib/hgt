# EDQ harmonic cutoff selection and complementary divisor tail

Stage: 1-in-progress. Diagnostic experiment and exact arithmetic bridge; RH remains the primary objective.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.

## Question

Does selecting a cutoff with exceptionally small harmonic Möbius defect also
suppress the actual complementary weighted tail, or only the already controlled
initial segment? The answer is not supplied by the existing full-source estimates.
The experiment discriminates these mechanisms; it cannot certify an asymptotic
ceiling or prove/falsify RH.

## Exact source and visible bridge

Write H_N=sum_(d<=N)mu(d)/d and M(n)=sum_(d<=n)mu(d). The corpus gives
1-F_N(n)=n*H_N+sum_(N<d<=n)mu(d)*floor(n/d), n>=N.
On N<n<=2N every retained floor in this omitted sum equals one. Thus
1-F_N(n)=n*H_N+M(n)-M(N) exactly on the first complementary block.
The initial error energy is H_N^2*sum_(1<=n<=N)n/(n+1).
The next block therefore measures actual Mertens increments coupled to that
same scalar defect. This identity is a [BRIDGE], already predicted by the
visible paper derivation; no computation is needed to establish it.

## Diagnostic protocol

The preregistered finite comparison is in
../2-fully-proven/computations/edq-harmonic-cutoff-tail-2026-09-07/PROTOCOL.md.
Only its uncertain coupling and cutoff-selection outcomes justify computation.
All numerical work runs on the prescribed RunPod host, with bounded runtime and
parallel independent cutoff jobs. Full scripts and downloaded results stay in
that computations directory. Numerical results never enter Lean proofs.

## Status

Protocol frozen before results. Experiment and exact first-tail bridge pending.

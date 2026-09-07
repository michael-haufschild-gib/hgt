# EDQ harmonic cutoff selection and complementary divisor tail

Stage: 3-formalized. Exact arithmetic [BRIDGE] proved independently of the finite diagnostic; RH remains the primary objective.
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

Put I_N=sum_(N<n<=2N)(M(n)-M(N))^2/(n(n+1)),
B_N=sum_(N<n<=2N)(M(n)-M(N))/(n+1), and let E_N^(1) denote
first-block target-error energy. Squaring the exact source identity gives
E_N^(1)=I_N+2*H_N*B_N+H_N^2*sum_(N<n<=2N)n/(n+1).
The signed cross term is retained. Since the last sum is at most N, the
inequality (a+b)^2<=2a^2+2b^2, in both directions, gives
E_N^(1)<=2*I_N+2*N*H_N^2 and I_N<=2*E_N^(1)+2*N*H_N^2.
The corpus's exact prefix/complement splitting puts E_N^(1) inside the genuine
infinite complementary tail. Its initial-error lower bound N*H_N^2/2<=E_full
therefore also gives I_N<=6*E_full. All statements are unconditional and
independent of the experiment. Small scalar defect still requires control
of the actual increment field and all subsequent blocks.


## Diagnostic protocol

The preregistered finite comparison is in
[protocol](../2-fully-proven/computations/edq-harmonic-cutoff-tail-2026-09-07/PROTOCOL.md).
Only its uncertain coupling and cutoff-selection outcomes justify computation.
All numerical work runs on the prescribed RunPod host, with bounded runtime and
parallel independent cutoff jobs. Full scripts and downloaded results stay in
that computations directory. Numerical results never enter Lean proofs.

## Status

The frozen RunPod diagnostic reports persistent complementary tail in all seven
tested dyadic ranges: the minimum-defect cutoffs retain tail error 0.035...0.041
on N<n<=128N, including N=56359 with N*H_N^2 approximately 1.154e-12.
The first block carries about half to two-thirds of that measured tail. This is
finite numerical evidence, not a positive asymptotic floor or a refutation of
a cofinal logarithmic ceiling. The corrected run took 2.2267 seconds; a sieve
implementation failure was caught and retained before any energy rows were
emitted. See the computation report for validation and omitted-tail limits.

## Lean validation

`EulerDeletionFirstTailMertens.lean`, namespace `RHTower.DeletionFirstTail`, has
three definitions and eight public theorems. The two pointwise identities cover
the entire first block. `firstTailErrorEnergy_eq` retains the exact signed cross
term; `firstTailErrorEnergy_le` and `incrementEnergy_le` give both quantitative
directions. `firstTailErrorEnergy_le_complementaryTail` and
`incrementEnergy_le_full_tail` retain the genuine infinite complement.
`incrementEnergy_le_six_fullErrorEnergy` supplies the unconditional full-error bound.

The complete scratch file passed `lake env lean` without diagnostics. The final
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionFirstTailMertens` built
only this new leaf (122 seconds). All eleven new public declarations were audited
once through a temporary `lake env lean` file: exactly `propext`, `Classical.choice`,
and `Quot.sound`, with no admission, added axiom, or numerical certificate.
The leaf is wired into `RHTower.lean`; no full or umbrella build was run.
Repository-wide formal lint reported one unrelated unwired concurrent module,
`RetainedPrimeMobiusEulerIdentity`. The EDQ leaf is wired and has no lint error;
the repository-wide gate is not claimed to pass. The search index was refreshed.
Scoped whitespace, declaration coverage, umbrella, and documentation-link checks
passed. All owned Lean processes exited and temporary proof/API/audit sources
were removed. Owned RunPod processes and temporary
files were already cleaned after downloading the successful and failed-run records.


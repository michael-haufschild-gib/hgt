# SZ: actual amplified source defect in the singular metric regime

- **ID:** SZ-ACTUAL-DEFECT-QUASIMODE
- **Stage:** 3-formalized
- **Type:** PROVED actual source constraint; not an RH proof
- **Source:** SZ-SHIFT-EDGE; actual interval covariance and prescribed source profile.

## Exact formalized statement

Use the actual interval covariance C, prescribed shift c, mu=norm(C),
strictly admissible shift d=c+(m-1)/mu, physical source p(u)=exp(u), and the
constructed response x=C*(I+(m-1)C/mu)^(-1)*p. Put y=d*x-p.
For a cofinal aperture sequence whose literal fixed-source carrier has a
nonzero limit at one imaginary test with 1/2<s<1, Lean proves:

1. y is eventually nonzero;
2. norm((I-C/mu)y)/norm(y) tends to zero.

This is a statement about the actual source defect, not an arbitrary
chosen approximate eigenvector. It is only relative covariance-scale
concentration. It does NOT assert concentration in a single ground
eigenspace, a uniform spectral gap, an absolute energy-gap limit, a parity
sign, or RH.

## Paper mechanism

Write r=exp(-(1+s)a), Gplus=r*<p_s,p>, Gminus=r*<p_-s,p>,
P=r*d*<p_s,x>, M=r*d*<p_-s,x>, and k=(is-i)/(is+i).
The actual source equation gives T*y=c*C*p-p. The literal quotient gives
B*P=k*M whenever its unscaled denominator is nonzero; a nonzero limit
ensures this eventually, without requiring d nonzero. The audited source
Gram limits are Gplus->g=1/(1+s), Gminus->0. Cauchy--Schwarz gives

    norm(P-Gplus), norm(M-Gminus) <= exp(-a)*norm(y).

Consequently

    norm(B*Gplus-k*Gminus)
      <= (norm(B)+norm(k))*exp(-a)*norm(y).

The left side has a strictly positive limit when B->L!=0. Thus
exp(-a)*norm(y) is eventually bounded below by some positive constant.
The prescribed profile error tends to zero and c<=K*exp(a), giving
norm(c*C*p-p)/norm(y)->0. The exact decomposition

    (I-C/mu)y = T*y - m*(C/mu)y

and norm(C/mu)=1 then bound the proposed residual ratio by
norm(c*C*p-p)/norm(y)+m. The spectral-margin necessity supplies m->0.
No numerical constants need optimization.

## Corpus checks and remaining hard problem

Search1190984 was partial with older coverage1190971 and a semantic
timeout. Its proposed ingredient set concerned moving-wall alignment,
not this spectral source assertion. The subsequent lexical search and
source scans did not supply this theorem; absence is not a novelty proof.
`SuzukiGroundProjectionReflectionCone` calibrates an assumed projected
pair to Xi, but does not establish the actual source projection's cone.
`SuzukiLimitingLogGroundSimplicity` proves simplicity for the represented
limiting logarithmic operator on aperture1, not the actual interval Weil
operator used here. Its conclusion cannot be substituted.

After the source-defect statement, the hard mathematical target remains
the actual signed parity/residue behaviour of this moving-aperture
family and the Gamma--prime--polar sign on canonical heads. A relative
quasimode alone does not settle either. Do not turn it into a generic
ground-simplicity or nonzero-overlap receiver.

## Log

- 2026-10-02: precise source-derived conjecture and paper argument recorded
  during final checks of SZ-SHIFT-EDGE. No Lean theorem or RH conclusion
  claimed for this card.
- Continuation: revalidated current source/necessity leaves. Search1191242
  had partial coverage (older snapshot1191238), source-only candidates and
  no proof ideas. Its proposed ingredient set mixed the limiting logarithmic
  covariance with actual covariance sources; rejected that identification.
  The proof is built directly from the actual interval transfer identity.
  The base-defect, mixed-pairing and normalized residual statements are
  being checked in Lean; no assumed ground projection is introduced.

## Final audit ledger

- `SuzukiSpectralSourceDefect.lean`: source scratch67821 and final5344
  exited0, warning-free. Five public theorems: physical identity, exact
  transfer identity, normalized covariance contraction, source residual
  inequality, and vanishing scaled actual base defect.
- `SuzukiSpectralSourceDefectQuasimode.lean`: scratch13322 and final76442
  exited0, warning-free. Four public theorems: two complex mixed-error
  bounds, carrier-derived source amplification, nonzero-limit quasimode,
  and the Xi-identification consequence.
- Both imports wired once in `GaloisForLFunctions.RHTower`; no umbrella
  build. Final commands from `formal/`:

      lake --old env lean GaloisForLFunctions/RHTower/<Leaf>.lean \
        -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Leaf>.olean

- Axiom52632: all nine public theorems checked, exit0; only propext,
  Classical.choice and Quot.sound.
- Lint28194 exited1 on11 unrelated unreachable modules:
  CCMApertureChainProfile, CCMApertureTranslationChains,
  CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
  CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
  MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
  ThetaMovingShellFirstOrderPhase, ThetaTailSchurAxisExtension,
  ZetaZeroDensityPowerSaving. Neither current leaf is listed. Global lint
  is not green. No numerical experiments, heartbeat increase, subagents,
  full builds, commits or pushes. Lean checks strictly serial.

## Frontier assessment

This adds an actual amplified vector and its limiting equation to the
previous scalar margin constraint. It does not establish an actual signed
residue, a distance to a ground eigenspace, or canonical-head positivity.
No theorem identifies this varying-aperture vector with a fixed-aperture
canonical head. Next target is the literal joint Gamma--prime--polar phase
gap on canonical heads, with the complete signed current retained:
P1:sz-canonical-head-joint-phase-credit. That sign is not proved here.

Cleanup verified: all eight owned scratch/search/audit files removed; all
owned processes terminal. Audited oleans retained. New imports occur once;
targeted tracked diff and new-file whitespace checks passed. Unrelated
working-tree changes preserved. Goal remains active and unachieved.

# Unit-coefficient law, sawtooth non-identifiability, and sharp rough-checkpoint sign classification

2026-10-18. Third connected contribution to ACTIVE open-ended THIM research. Do not mark the whole goal complete. User forbids hgtl7, RH focus, numerical experiments, proof holes/new axioms, heartbeat hacks, README edits, full/umbrella builds. One foreground Lean process per agent.

Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/RadicalCheckpointSignRigidityAndGaugeLaw.lean`.

Core facts:
- `sieveUnitShiftWeight c a d = c d + if d=1 then a else 0`.
- ALL active sawtooth observables, for every horizon H and positions m,j, are invariant under this shift. Unit-divisor centered sawtooth is identically zero. Actual supporting theorem is `GaloisForLFunctions.BiScaleUncertainty.centeredDiscreteSawtooth_one` (fully qualify it).
- Every additive sieve difference is invariant. For all N,M, including zero:
  `D_N(M;U_a c)=D_N(M;c)+a*(s_N(c,M+1)-s_N(c,1))`.
- The shift orbit has full real defect range iff endpoint responses differ. Nonpositivity under ALL unit shifts iff responses agree; on that hyperplane `2D=-sum(delta s)^2`.
- Prefix defect is quadratic under scaling of the coefficient weight.
- For k>=1, `horizonRadicalState N k=1` iff `IsTransHorizonRough N k`.
- Rough endpoints are exactly checkpoints nonpositive for ALL weights, or all squarefree-supported weights, or all nonnegative squarefree-supported weights.
- At every nonrough endpoint choose visible prime p|k. The family U_a(delta_p), supported on {1,p}, realizes every real defect while preserving the ENTIRE active sawtooth profile across all horizons/positions. Formal witness theorem: `exists_squarefree_same_active_sawtooth_defect_eq`.
- Nonnegative squarefree weights have unbounded positive defects there. Exact universal finite bound classification: `(forall nonnegative squarefree c, D_N(k-1;c)<=B) iff (rough_N(k) and 0<=B)`.
- STRONGER NORMALIZED SIGN OBSTRUCTION: let D=D_N(k-1;delta_p), t=1/(|D|+1). Then c=delta_1+t delta_p has c1=1, every coefficient in [0,1], squarefree support, and D_N(k-1;c)=t^2*(D+|D|+1)>0. Thus even this normalized bounded class detects precisely rough checkpoints. Formal theorem `isTransHorizonRough_iff_forall_normalized_bounded_squarefree_defect_nonpos`.

Boundary: these weights are NOT counterexamples for specific Mobius/power-damped weights. Those impose extra sign and multiplicative relations. Full-profile non-identifiability uses free unit coefficient; normalized witnesses prove sign obstruction, not non-identifiability at fixed unit. Remaining question: exploit specific coefficient relations at canonical radical representatives beyond current band envelopes; squarefree support, unit normalization, coefficientwise bounds alone cannot suffice. Other agents now prove endpoint envelopes through3N and portions through4N; avoid duplicating their band/period tracks.

Verification: actual source `lake --old env lean -o <leaf.olean> <leaf.lean>` exit0, no warnings. All21 public theorems +1definition +1private helper #print axioms audit exit0, every closure exactly propext/Classical.choice/Quot.sound. Source SHA256 794f867becd1c93d3158cdd8259efd4c5c9463e73d77e1de316c917224254619. Needed existing RoughAbsorption leaf .olean absent; individually compiled its unchanged source exit0. Field umbrella imports new leaf once; MainTheorems reaches it; all22 public exports indexed. Index exit0. Global lint --check-generated exit1: five unrelated BiScaleUncertainty leaves unwired plus existing THIM umbrella registration; no own-leaf finding or stale generated file. Do not claim globally clean lint.

Artifacts: card `docs/drafts/pipeline/3-formalized/thim-radical-checkpoint-sign-rigidity.md`; ledger `logs/thim-radical-sawtooth-knowledge.md`; `logs/thim-gauge-{lean,axioms,index,lint}.txt`; `logs/thim-gauge-rough-dependency-lean.txt`; `logs/thim-gauge-audit.json`. All nine owned scratch files removed after jobs terminal. No README edits or commits. Previous facts: `mem:trans-horizon/radical-state-defect-normal-form`, `mem:trans-horizon/all-horizon-radical-sawtooth-defect`.

Private axiom audit: construct Lean.Name starting `_private.<module>`, add `.num n 0`, append namespace and `prime_indicator_support` with `.str`, then `Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent n):ident))`. This audits the private helper without guessing a parsable numeric identifier.

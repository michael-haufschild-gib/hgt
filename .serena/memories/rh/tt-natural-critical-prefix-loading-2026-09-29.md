# TT natural critical prefix-energy loading

Validated modules: `XiHeatCassiniWoldNaturalPrefixEnergyAbelBounds.lean` and `XiHeatCassiniWoldNaturalCriticalPrefixLoading.lean`, wired into RHTower. Named `lake build --old` passed, both required exact `lake env lean <module>` audits passed. Scratch axiom audit of capstone `RHTower.exists_woldNatResidualCriticalPrefixLoading` and generic bounds reports only propext, Classical.choice, Quot.sound.

Unconditional actual-source theorem: there exist s0 with Re=-1/2, Im>0 and multiplicity m>=1 such that for every 0<c<m^2/(4*norm(s0)^2), arbitrarily large natural cutoffs K satisfy c*log K < sum_(n<K) R(n+1)^2. No RH or analytic source premise. Proof assumes an eventual contrary prefix upper bound, establishes discounted square energy and Abel holomorphy, then contradicts the forced residue -m.

STRONGER PAPER-CLOSED C4c pending Lean: compare log N to harmonic prefix H_N; finite Abel majorization should give D(x)<=c*(1+1/x)+C, improving charge to m^2<=c*norm(s0)^2 and threshold m^2/norm(s0)^2. Do not close the failed critical energy no-go at weaker coefficient before formalizing strongest paper survivor.

External novelty unresolved; searches provide limited negative evidence, no global absence certificate. Global lint fails on unrelated unreachable modules, own leaves absent from errors. Goal remains ACTIVE until unconditional RH proof/falsification fully formalized. Working log `docs/drafts/pipeline/1-in-progress/tt-source-frontier-conjecture-loop-2026-09-29.md` records exact status, C2/C3 and C9 subhalf-energy criterion candidate.

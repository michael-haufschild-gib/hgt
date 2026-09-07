# EDQ actual coprime head — 2026-09-07

Persistent full RH/EDQ goal ACTIVE, unbudgeted, not achieved. Baseline at start9674589 tokens. Full chain Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH. This turn is PROGRESS: novel full-source RunPod discriminator, rational failed-sign diagnosis, and an unconditional subpower bound for the actual signed coprime initial remainder. No RH proof/falsification.

## Critical constraints
Frontier `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is READ ONLY by latest explicit user instruction. No frontier write this turn. Preserve this across continuations. Read before relying on current state. No subagents, commits, full/umbrella builds. One foreground owned Lean at a time. Only RunPod computations; no computed result enters Lean. Audit only newly created declarations once; do not repeat the unchanged audits documented here or in mem:rh/edq-coprime-column-cancellation-2026-09-07.

## New CLOSED Lean
Leaf `formal/GaloisForLFunctions/RHTower/EulerDeletionCoprimeHeadSubpower.lean`, namespace `RHTower.DeletionCoprimeHead`. Five public definitions, two public theorems, seven private helpers. Imports prior complete-column leaf.
- `harmonicQuadratic N` = W_N = Σ_(d,e≤N,coprime d e) μd μe/(de).
- `residueQuadratic N t` = B_N(t) = Σ_(d,e≤N,coprime d e) μd μe ((t mod d)/d)((t mod e)/e). This is an actual SIGNED coprime portion of the discrete modular Gram, not independently positive.
- `mixedColumn N t` = L_N(t) = Σ_(d≤N) μd S(d,t)/d, support-count S from prior leaf.
- `residueQuadratic_eq` for t≤N: B_N(t)=t² W_N−2t L_N(t)+floorCorrelation (Icc1N) t. Higher floor columns vanish; exact finite polarization and complete-column inversion.
- `initialEnergy N` = Σ_(1≤t≤N) B_N(t)/[t(t+1)].
- `headMass N` = Σ_(1≤t≤N)t/(t+1).
- `exists_initialEnergy_remainder_subpower`: ∀epsilon>0, ∃C>0, ∀N, |initialEnergy N−W_N*headMass N|≤C N^epsilon. Includes N=0. No RH/sign/numerical premise.
Proof uses support bound with delta=epsilon/4, |L|≤A N^(2delta)(1+logN), complete floor bound |F(t)|≤B t^(1+delta), then actual reciprocal-square weights and harmonic factors. This is a proved estimate for actual initial arithmetic cancellation, not a new conditional norm receiver.

## Remaining actual hard target
The explicit W_N*headMass N survives. Define complete later coprime tail as Σ_(t>N)B_N(t)/[t(t+1)]; need a subpower bound on its joint sum with the explicit head term, retaining cancellation before integration. Expanding every later floor separately introduces divergent polynomial pieces; keep the compensated sum intact. For general gcd r the coefficient also has coprimality with r, and coordinates k=rt+i retain affine offsets i/r. No bound for these full grouped tails, preserved inner cutoff X, or complete EDQ energy is proved. Do NOT replace that with another receiver or re-prove the column/head estimates. The actual averaged source and existing RH current receivers are in the prior memories/cards.

## Failed sign shortcut, PAPER only
A direct rational derivation shows W(22)>3/800. Divisor inversion: W22=H22²−P+Q. P contains the 8 prime terms p2,3,5,7,11,13,17,19. Inner coprime harmonic sums are 269/1155<1/4, 11/70<1/6, 1/6,1/6,1/2,1,1,1. Hence P < 1/64+1/324+1/900+1/1764+1/484+1/169+1/289+1/361 <29/800 using paired bounds 1/50,1/500,1/125,1/160. Q =Σ_(r=6,10,14,15,21,22)1/r² >1/36+1/100+1/196 >1/25. Thus W22>3/800. No numerical sign scan was run because reasoning already determines this. Counterexample is not Lean-audited; never imply otherwise. Positive survivor (exact head with subpower remainder) IS now formalized above. No whole route retired.

## Novel RunPod experiment COMPLETE
Directory `docs/drafts/pipeline/2-fully-proven/computations/edq-gcd-gram-variation-2026-09-07/`; 9 files including REPORT and SHA256SUMS.
Question: does grouping ACTUAL weighted normalized residues by exact gcd retain cancellation enough that total variation V≤4D on frozen test scales? Threshold four predeclared finite discriminator, not universal theorem/fitted constant.
Cases M64,128,256,512, each raw and exact logarithmic taper X=M/4. E_q=full weighted norm² of coefficient terms with q|d. C_r=Σ_l μl E_rl. V=Σr|C_r|, D=full Gram diagonal. Finite arithmetic inversion reconstructs E1. This is modular-source norm, NOT target-error norm.
Compression: k=qt+i, multiples channel=A_q(t)+(i/q)H_q. Divisor sieve for A. Direct moments t<16; 20-term convergent reciprocal-weight expansion for t≥16. Tail per E_q≤mass_q²/(qBq); allocation ensures Σtau(q)*tail_q≤0.05. Different prefix endpoints refer via bounds to common complete infinite E_q. Analytic series remainder separately bounded below1.64e-20 on V; diagonals below8.76e-25. Floating rounding has independent controls and a1e-7 sensitivity margin, NOT an interval arithmetic certificate. No data enters Lean.
All8 classified GROUPWISE_CANDIDATE. Raw V/D intervals atM64 [2.319329,2.343689], M128[1.913478,1.933024], M256[1.669379,1.685595], M512[1.452045,1.465901]. Averaged intervals [1.022580,1.057715], [1.705284,1.731602], [1.877595,1.898442], [1.545051,1.562245]. Both positive and negative gcd groups in every case; max r|Cr| moves r2→r6, rawM512upper7.661071. Rawtotalvariation~4.74..5.29, signednorm~.92..1.12; finite evidence only.
8 Python workers, native pools1, wall4.048205s under180s. Python3.8.10 NumPy1.24.4 SciPy1.10.1 LD63bits. Controls: moments relative≤1.21e-19, direct finite energy diff≤1.09e-19, modulus2diag log2/4 diff≤3.12e-19, accumulated channel spots≤8.38e-13, inversionrecon≤6.51e-19. REPORT has full table and limits. All7 remote data/source hashes verified; REPORT localhash appended. Remote exact jobdir `/tmp/edq-gcd-gram-variation-20260907-root` and its8files+generatedpycache removed after /proc cwd audit found no activejob. All remote handles terminal. No other sweep.

## Validation / cleanup
Complete scratch /tmp/edq_head.lean passed lake env lean with NO diagnostics. Final `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionCoprimeHeadSubpower` exit0: only this leaf Built7.1s,10901cached graph jobs. Umbrella import wired; never built umbrella. One separate import-only /tmp #print axioms audit of7new publicdecls exit0: exactly propext,Classical.choice,Quot.sound. Index refreshed once (3changed0removed); current full repo lint PASSED exit0 (prior foreign ChiIncrementDifferenceJets debt had been resolved externally). Scoped diffcheck no diagnostics. All owned Lean handles terminal (lastscratch66010, build94546,audit16140,index86981,lint19610). ps found no ownedLean. Seven exact /tmp/edq_head*scratch/part/audit/log files removed. No old audits repeated, no commits, no subagents.

## Docs updated
Workingcard `docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md`: frozen gcd experiment, full outcome/reportlink, rational W22 diagnosis, and formalized head survivor. New `docs/drafts/pipeline/3-formalized/edq-coprime-head-subpower.md`. STATUS existing MUST-RETAIN-COMPLETION-POLYNOMIALS expanded by route-independent corrected-head/full-source distinction. Frontier untouched. Experiment is isolated under computations with original protocol, source, outputs, controls, report, and hashes.

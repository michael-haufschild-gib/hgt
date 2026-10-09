# Every positive shift detects divergent origin mass

Status: [FORMALIZED; GLOBAL LINT HAS THREE UNRELATED UMBRELLA ERRORS]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Objective and plan

Remove the artificial shift restriction c>=4 from uniform truncated-tail gain
and its single-probe consequences. Establish the exact convergence/divergence
alternative at every integer probe m>=2 under the existing finite-excess class.

1. Audit cutoff transition positivity, kernel envelopes, and existing probe
   divergence proofs. Done: the old proof uses a fixed plateau interval.
2. Prove a central lower envelope with arbitrary positive radius and margin,
   then uniform inward tail gain for every c>0. Done: PositiveTailGain leaf
   compiled/exported without diagnostics.
3. Transfer gain to divergent origin mass and every integer probe m>=2.
4. Use the already proved local exponential rates to transfer convergence
   strictly inward. Obtain single-probe convergence iff eventual lower bounds,
   divergence to minus infinity otherwise, and the improved growth bound.
5. Compile/export leaf modules individually, audit every public declaration,
   wire/index/lint, promote card, save memory, clean owned scratch.

## Dependency-closed paper argument

Write S=Real.smoothTransition, Phi=riemannKernelReal, and K_L for truncated
autocorrelation. If |t|<=L-d, monotonicity gives bulkCutoff(L,t)>=S(d)^2.
For d>0 this constant is positive. On the interval (z/2-d,z/2+d], z>=0,
both |t| and |t-z| are <=z/2+d. If z/2+2d<=L, both cutoffs therefore have
this lower bound. The corpus lower bound for Phi gives

  K_L(z) >= D_d exp(-2*pi*exp(z+2d)),
  D_d = 2d*(2*pi^2)^2*S(d)^4 > 0.

Fix c>0 and take d=c/4, z=y-c. Whenever the original kernel is visible,
y<2L, the margin condition holds. Otherwise K_L(y)=0 and the desired gain
is automatic. The lower envelope has exponential coefficient
B=2*pi*exp(-c/2)<2*pi. Pick q strictly between B and 2*pi. The corpus full
upper envelope gives K_L(y)<=K(y)<=C exp(-q*exp y). The ratio is bounded by
(C/D_d)exp(-(q-B)exp y), which tends to zero. Thus every A has a tail on
which A*K_L(y)<=K_L(y-c), uniformly over ALL real L.

Split an arbitrary nonnegative coefficient sequence at that fixed tail.
The finite head is bounded by full K, independently of L; the tail gain with
A=4 gives 4*D_L<=T_L(c)+4H. With finite positive excess the existing actual
probe estimate is Q_L(c)<=W_L(c)+4*K(0)*sum(excess)+4*D_L-2*T_L(c).
Consequently divergent origin deficit mass sends Q_L(log m) to minus infinity
for every m>=2, since log m>0 and W_L(log m)->0.

The local rate r(y)=2*pi*exp(-|y|) strictly decreases with |y|. If the signed
potential converges at c and |y|<|c|, choose b between r(c) and r(y): the local
necessary growth bound at c and sufficient growth bound at y imply convergence
at y. In particular convergence at log m implies convergence at 0 for m>=2.
Finite excess then also gives the origin deficit moment. Conversely an eventual
lower bound on Q_m excludes divergent origin mass; the existing sampled
divergence theorem excludes divergent potential at log m. Therefore, for each
m>=2, eventual integer-cutoff lower bounds are equivalent to signed potential
summability at log m. Summability gives the exact finite real-cutoff limit.
Nonsummability sends the real-cutoff probe to minus infinity, by splitting on
origin deficit summability. The local necessary growth bound now applies to
lower-bounded probes at every m>=2, removing the old log m>=4 restriction.

No critical-growth endpoint, RH, arbitrary signed rigidity, or external novelty
claim is made. No new analytic assumption is introduced: finite excess only
specifies the already established coefficient class for the probe corollaries.

## Corpus audit

Direct lexical corpus search found the existing c>=4 truncated/full shift gains,
origin gain bound, exact strict cutoff support, and transition monotonicity.
The source definition is S(L-t)*S(L+t); the needed positivity and monotonicity
are already used in the corpus. New toolchain names will be checked in scratch.
The core cutoff-tail theorem has no unproved analytic hypotheses.
Search reported 3425 declarations, 753 modules, 1266 eligible entries. Cached
lexical output has no partial/coverage/candidate_lemmas/source_arguments fields;
all used dependencies were inspected in source and checked in Lean scratch.

## Verification

- `WeilLogShiftPositiveTailGain.lean`: direct leaf compile/export exit 0, no
  diagnostics; three public theorems.
- `WeilLogShiftSingleProbeDomain.lean`: direct leaf compile/export exit 0,
  no diagnostics; eight public theorems implement the probe and strictly
  inward convergence results.
- All 11 public theorems passed scratch `#print axioms`; only `propext`,
  `Classical.choice`, and `Quot.sound` occur.
- Both modules are imported by the RHTower umbrella. Index refresh succeeded;
  all 11 API rows were inspected. Scoped `git diff --check` passed.
- Global formal lint exited 1 with three unrelated modules unreachable from
  the RHTower umbrella: `CCMRestrictedWeilCrossFormBound`,
  `PaperCirclePosteriorFourierMetric`, and `PaperCirclePosteriorPortraitStability`.
  These modules/imports were not modified. No full/umbrella build was run.
- All owned jobs exited; owned `/tmp/hgt-weil-small-shift-*` scratch files
  were removed after recording the evidence. No heartbeat increases, numerical
  experiments, new axioms, unproved analytic inputs, commits, or subagents.

All scoped proof steps are formalized. The stronger insight is a local
alternative at EVERY nontrivial integer probe: under finite excess, sampled
potential summability gives the exact finite probe limit; failure of summability
forces the probe to minus infinity. A single eventual lower bound is therefore
equivalent to local summability. The finite-limit direction needs neither finite
excess nor a separate origin premise, because convergence transfers strictly
inward without a separation threshold.

## Next conjecture, not formalized here

The global unweighted finite-excess assumption may be replaced by convergence
of the positive-excess potential at the individual probe. That local moment
bounds the positive contribution to the probe identity, and strict inward
transfer also supplies its origin moment. A fresh audit must check the full
signed/deficit decomposition and all divergence cases before implementation.

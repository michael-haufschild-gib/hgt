# Unbounded spatial support forces cofinally unbounded positive response

- **ID:** LI-CLOCK-UNBOUNDED-SUPPORT-GROWTH
- **Stage:** 3-formalized; unconditional complete-source capstone verified
- **Type:** THEOREM, paper audited independently twice and Lean-closed
- **Parent:** [literal clock growth boundary](../2-fully-proven/li-actual-clock-sine-growth-boundary.md)
- **Prior work:** [formal complete-source Volterra law](../3-formalized/li-actual-clock-volterra-positive-mass.md)

## Audited statement

The literal response `F(t)=tS(t²/16)` satisfies `∀M,T₀ ∃t>T₀, F(t)>M` unconditionally. Proof uses unbounded spatial support and the exact Volterra law, without RH case split, reciprocal top-packet asymptotics or RVM counting. Stronger source-growth survivor is `B(t)exp(−R√t)→∞` for every real R.

## Paper proof proposed before hard work

Let `B(t)=Σ_j C_j t^(2j)/[(2j)!]²`, `C_j=R_j/R_0`, and `H(t)=∫₀ᵗB(s)ds`. Already formalized: `B≥1`, continuous differentiability, monotonicity for `t≥0`, and `F⋆B=tB'`.

Suppose F is bounded above by M eventually. Increase M to be positive. Continuity on the initial compact interval yields finite `C≥0` such that, for every `t≥0`,

`tB'(t)≤C B(t)+M H(t)`.

Indeed subtract M from the convolution integrand; its positive part is supported on one fixed compact interval, and `B(t−s)≤B(t)`. One may take `C=∫₀ᵀ(F(s)−M)_+ds` after the eventual bound begins.

For `u≥1`, set `Y(u)=H(u²)`, `Z(u)=2uB(u²)=Y'(u)`. Both are nonnegative and

`Z'(u)=2B(u²)+4u²B'(u²)≤[(2C+1)/u]Z(u)+4M Y(u)`.

Thus `V=Y+Z` satisfies `V'≤R V`, with `R=max(2C+2,4M)`. First-order differential comparison gives `V(u)≤V(1)e^(R(u−1))`, hence `B(t)≤K e^(R√t)` for every `t≥1`, with finite positive K. Only C¹ regularity of B is used; no differentiation of the original inequality occurs.

The literal source k is strictly positive everywhere. For each `X>0`, the normalized source mass `d_X=R_0⁻¹∫_[X,X+1]k` is positive and gives `C_j≥d_X X^(2j)` for all j. For each integer `j≥1`, choose `t_j=16j²/X`. The elementary bound `(2j)!≤(2j)^(2j)` yields

`B(t_j)≥C_j t_j^(2j)/[(2j)!]²≥d_X16^j`.

The claimed upper growth bound instead gives `B(t_j)≤K exp(4Rj/√X)` eventually. Choose X so `4R/√X<log16`; geometric growth contradicts the two bounds. Therefore F has no eventual finite upper bound, exactly the candidate cofinal conclusion.

## Audit obligations

1. Check compact convolution remainder, including all `t≥0`, normalization of `d_X`, and support interval.
2. Check C¹ chain-rule comparison and the exact factorial/clock constants.
3. Check installed corpus collisions; structural result is not an arithmetic RH producer or a novelty claim.
4. Only after dependency-closed paper audit, formalize generic differential comparison and actual moment lower envelope in disjoint leaves.

## Independent audit and stronger survivor

Both independent audits pass. Canonical window mass is `δ_X=(2/R_0)∫_[X,X+1]k>0`, giving exact `C_j≥δ_X X^(2j)`. Original `d_X=δ_X/2` is conservative. With `n=floor(√(Xt)/4)`, monotonicity and grid bound give, for `t≥16/X`,

`B(t)≥(δ_X/16)exp[(log16·√X/4)√t]`.

Choose X so this exponential rate exceeds any fixed real R. This proves `B(t)exp(−R√t)→∞`; the stronger statement returned through both paper and corpus audits before formalization.

Prefer simpler comparison: continuity plus eventual upper boundedness of F gives a global positive bound M on `[0,∞)` by compactness. Then C=0, `tB'≤MH`, `Z'≤Z/u+4MY`, and `V'≤max(2,4M)V`. Signed differential comparison is sufficient; norm-Grönwall must not be substituted without its stronger hypotheses. Actual B source exports continuous B and `HasDerivAt` everywhere; continuity of B' is unnecessary.

Source/API obligations audited: raw `R_j` definition and integrability in `PrimeArchThetaCumulantMinor`; positive k in `PrimeArchThetaFirstMoment`; complete Volterra derivative identity in `LiEvenCrossActualClockVolterra`; term lower bound and monotonicity in `LiEvenCrossActualClockBorelGrowth`/`BorelSource`; installed `IsCompact.bddAbove_image`, `Nat.factorial_le_pow`, interval positive-integral and comparison APIs. No paper gap remains.

Corpus audits completed at generations 1144805/current 1144806 and 1144857, with complete source inventories, semantic coverage unavailable and compiler evidence mostly pending/stale. Existing weighted-degree escape is weaker; mechanism is generic positive unbounded-support moment growth. No world-priority or independently proved arithmetic RH producer claim.

## Formal plan

1. `LiClockVolterraBoundedResponseGrowth.lean` is final: global upper bound, exact convolution ceiling and signed square-root-clock comparison; four public declarations foundational. No monotonicity or continuity of B′ premise.
2. `LiEvenCrossActualClockBorelSpatialGrowth.lean` is final: literal factor-two positive window mass, all-order coefficient envelope, grid and continuum lower bounds, strongest all-R fast growth; seven public declarations foundational.
3. `LiEvenCrossActualClockUnboundedResponse.lean` is final: `liEvenCrossActualClockResponse_unboundedAbove_cofinally` combines these leaves with literal Volterra identity and actual differentiability. No RH premise; capstone axiom audit foundational.
4. Named builds, final exact source checks and all 12 public axiom audits passed. Root independently checked complete source and evidence; all three imports wired into `RHTower.lean`.

## Limits

The theorem gives cofinal positive amplitudes, not all-clock positivity or a negative source witness. `S(w)=F(4√w)/(4√w)` need not be unbounded positive; no RH conclusion follows. Existing paper RH/non-RH classification remains separate.

## Log

- 2026-09-30 — Candidate recorded before new Lean work. Root checked coefficient lower bound at `t_j=16j²/X`, first-order comparison and absence of differentiated-inequality step. Independent hostile audit pending.
- 2026-09-30 — Two independent hostile audits passed; stronger all-clock fast-growth limit audited and recorded. Global-bound simplification removes compact remainder from the formal interface. Moved to stage two; disjoint generic and actual-source leaves assigned next.

- 2026-09-30 — Three exact leaves passed named builds and final direct checks with empty logs. Generic own leaf 30s, actual spatial source 14s, actual joint capstone 11s; all 12 public axiom audits use only `propext`, `Classical.choice`, `Quot.sound`. Promoted to stage three. Source sign burden and RH remain open.

## Verification evidence

- `/tmp/hgt-volterra-response-growth-{build,direct,axioms}.log`
- `/tmp/li_pole_audit_spatial_{named_build,axioms,final_direct}.log`
- `/tmp/hgt-li-actual-clock-unbounded-{build,direct,axioms}.log`

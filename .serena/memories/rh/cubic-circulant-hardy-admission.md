# Faithful circulant source winding: Lean-closed

2026-09-05. RH goal active; no RH endpoint or independent arithmetic conservation law proved. Parent algebra/computation: `mem:rh/cubic-circulant-source-normalization`.

Verified/wired leaves (declaration namespace RHTower):
- CubicFiniteChannelHardySource: PiLp finite blocks preserve multiplication, adjoints, S1 admission and ordinary diagonal-sum trace. Constant-plus-Schwartz CCM formula i/(2*pi)*integral tr(M N').
- CubicCirculantHardyAdmission: explicit E(norm z) tensor three-column circulant source. Smooth/compact input gives Schwartz admission, orthogonal source projections, flat source aggregate/current, exact pointwise recovery. Rounded cubic trace i/(4*pi)*integral tr(S K').
- CubicCirculantWindingIntegral: actual graph and tensor-current derivatives; phase logarithmic derivative f'/f-(log norm f)'; both exact primitives integrate to zero; integral_cyclicFaithfulSourceSymbol_current proves integral tr(S K')=integral f'/f for the literal admitted matrices.

Main theorem `exists_faithful_circulant_winding_cubic` (winding module, line 381):
∃ real t,b with t²+b²=1, 6(tb)²=1, tb≠0, chosen BEFORE ∀f,c; for every smooth nowhere-zero f:R→C with f-c compactly supported: exact precompression recovery of f AND genuine 12-channel orthogonal P,Q,R, nuclear corrections to doubled Hardy source compressions with labels 0,2,1, nuclear combined cubic, Tr((R-P)^3-(R-Q)^3-(Q-P)^3)=(2*pi*i)^-1 integral f'/f. No index, zero count, trace value, RH, budget or moderation premise. Recovery is pointwise nonlinear, not bounded inverse or linear coefficient transport.

All leaves/scratch checks passed; winding leaf five principal axiom audits only propext/Classical.choice/Quot.sound; lint passed. No umbrella/full build; all own jobs completed. Module is a standard analytic BRIDGE, not claimed beyond-literature arithmetic knowledge.

NEXT formal edge: smooth orientation-preserving parametrization of literal arithmetic rectangle, f=completed Xi on that path; integral f'/f=rectIntegral continuedPrimeArchSourceRelativeTrace. FormationAnchoredCubicContourCharge already proves the latter /(2*pi*i)=Xi multiplicity copies. No smooth rectangle reparametrization found by targeted corpus search. Natural construction: four translated smoothTransition ramps, each moving one edge, constant before 0/after 4; scalar substitution on each edge. Do not insert the count into the loop.

OPEN MATHEMATICS after specialization: independent arithmetic zero-charge control on strict-right contours. Universality over all smooth sources means admission/recovery/normalization cannot supply that selection by themselves.

Pitfalls: explicitly type matrix value/jet before multiplication (bare function literals can select Pi pointwise multiplication). ContDiff.norm takes ℂ explicitly. Real derivative casts require ((deriv realFunction x : R):C), or elaboration may move coercion inside deriv. Complex group-instance diamonds: convert ... using 1; congr handles proof-field variants. `HasCompactSupport.div` is misnamed multiplicative-support theorem: for zero-support quotient use mul_right of reciprocal. When Kronecker simp uses local E, unfold E in rewrite hypotheses to match source expressions. Constants t*b and Hardy sign checked exactly, not numerically.

RunPod CFC-1 experiment is complete/report downloaded. No further numerical discriminator needed for these analytic steps.
# TG-C9.6: neutral projection in the source graph norm

- **ID:** TG-C9.6-20261002-01a0
- **Stage:** 5-failed
- **Type:** RETIRED bounded-neutral candidate / exact positive survivor formalized
- **Parents:** `../3-formalized/tg-fourier-jet-prime-graph-core.md`,
  `../5-failed/tg-fourier-jet-even-bounded-recovery.md`

## Exact hard source question

Let G be the closed even source graph of E(f,g)=(f+Fg,Mf+FMg), with its inherited norm
retaining BOTH input and output coordinates. Does the original neutral operation
N(f,g)=(f,0) extend continuously to G? Output-only recovery has been excluded, but that
does not answer this stronger-topology question. A bounded neutral projection is required
before treating this completion as the original bounded projection algebra for TG's cubic
transgression. Do not infer its failure from C9.5.

## Corpus-grounded obstruction attempt

Current audited source gives `W=8π²Q²+2D²` and the exact admitted cancelling pair
`E(Fφ,-φ)=(0,-(8π²)^(-1)F(Wφ))`. It also gives the actual Gaussian, normalized physical
dilation, and exact position-square dilation covariance.

Search `Schwartz quadratic chirp dilation` returned partial results (malformed local
filter response and reranking deadline); it did return the actual normalized Schwartz
dilation in `CCMArchimedeanGeometricScaledKernel` and Fourier dilation covariance in
`SoninEulerCalkinPartialIsometry`. Source inspection also located mathlib's
`SchwartzMap.smulLeftCLM` for temperate multipliers. These are ingredients, not proof
of quadratic-phase admission. Build the missing phase multiplier/domain proof if needed.

Use the actual even family
`φ_r(x)=sqrt(r) exp(iπx²) exp(-πr²x²)`, for 0<r≤1.
Algebraic differentiation predicts

`Wφ_r = 4π(i-r²)φ_r + 8π²(r⁴-2ir²)x²φ_r`.

The unimodular phase and normalized dilation give constant ||φ_r|| and
`||x²φ_r||=r^(-2)||x²h_0||`. Thus Wφ_r remains bounded as r tends to zero, while
||x²φ_r|| diverges. The exact Fourier–jet identity forces ||M Fφ_r|| to diverge too.
The source graph vectors of `(Fφ_r,-φ_r)` stay bounded, but their neutral images do not.
This would exclude bounded neutral extension even in the source graph norm. It is a
qualitative domain/projection obstruction, not an optimization of a constant or a
numerical experiment. Every admission, derivative and norm statement still needs Lean.

C9.4 supplies approximation of each coordinate together with its M-image, so any bound
assumed only on a fixed prime's finite graph core can be passed to these actual source
pairs. Ordinary L2 density alone would not justify that transfer.

## Required positive survivor

Before retiring bounded neutral extension, prove and audit the exact closed unbounded
neutral operator. Its domain should be the original separately admitted even D(M)×D(M)
source inside G. If z_j and N z_j converge in G, their first inputs and separate first
jets converge. Closedness of M recovers f∈D(M). Subtract that jet from the total output
and apply F inverse; closedness of M then recovers g∈D(M). The limit is the neutral
image of the limiting source. This proves closedness of N on that domain.

Its range and kernel are the two closed individual source-channel graphs; their direct
sum is dense. Unboundedness would force a proper domain and show the sum is not closed.
This exact decomposition, rather than only a negative estimate, is the required survivor.
Both obstruction and exact positive survivor are now Lean-certified; see the final audit below.

## Working audit, 2026-10-02

The closed-relation construction, exact original domain, idempotence, channel range,
kernel and original-source action passed the scratch Lean check. Production audit is
pending. The quadratic-phase proof is reduced to two elaboration repairs; its final
inequality and limit argument already elaborated. No obstruction is certified yet.

The paper proof now avoids any uniform-constant optimization: multiply the hypothetical
position graph estimate by r². With a=||h₀||, b=||x²h₀||>0 and a_r=π(i-r²), this gives
`b ≤ C(r²a+r²||4a_r||a+||8π²+8a_r²||b)`.
The right side is continuous at zero and vanishes there, contradicting b>0.
The actual cancelling source then converts any neutral graph estimate to this forbidden
position estimate. Closed-graph reasoning forces a proper neutral domain and nonclosed
sum of the two individually closed source channels.

Search `closed unbounded projection disjoint closed submodules sum` completed with
no retrieval-stage error; compiler coverage is mostly source-only/pending/stale.
Its finite-dimensional complement candidates do not apply here. The exact current
mathlib closed graph theorem supplies the Banach-space step; applicability remains
subject to the leaf audit. No absence claim follows from the search ranking.

## Remaining RH gap

This question decides whether the retained-jet repair supplies the bounded neutral
projection needed by the proposed source algebra. Gamma–Xi identification, Hardy-index
transfer and the arithmetic sub-unit producer remain open. Do not replace them with a
completed Mellin symmetry or a generic closed-operator theorem.

## Final result and positive salvage

**Conjecture failed:** no uniform neutral graph bound exists on the full even admitted
source, nor on any individual prime's literal finite depth core. Thus no bounded extension
of the original neutral operation can act on this graph completion while retaining its
source action.

**Positive survivor, paper and Lean complete:** the original operation is a closed
idempotent partial linear operator. Its exact domain is the original even separately
admitted D(M)² source graph; its range and zero fibre are exactly the two closed source
channel graphs. These channels are disjoint, their algebraic sum is that domain, and
the sum is nonclosed. The domain is proper dense in the completed even source graph.
Canonical positive record: `../3-formalized/tg-fourier-jet-closed-neutral-domain.md`.

The phase obstruction uses a symbolic limit, not a numerical experiment. Each prime-core
transfer uses closure in both separate multiplication graphs, so it controls the neutral
image as well as the total source output.

All three changed/new production leaves pass foreground `lake --old env lean` with matching
olean output. Both new leaves are wired into RHTower; no umbrella/full build was run.
All 21 added public theorems pass a separate /tmp axiom audit, depending only on
propext, Classical.choice and Quot.sound. No added axiom, hole, computation certificate,
heartbeat increase, subagent, commit or push. Source index refresh exits zero; scoped
whitespace checks are clean. Global lint exits one on sixteen unrelated unwired leaves,
with no TG leaf error; exact list is on the positive card.

This retires bounded-neutral completion, not route TG and not the complete cubic
transgression. Next attack: `../1-in-progress/tg-fourier-jet-theta-cubic-domain.md`.

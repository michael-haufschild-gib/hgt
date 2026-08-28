HC59 formalized in `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFELinearAntilinearClockReflectionCoherence`.

Let literal source cocycle be kappa and define complex-linear transport `L(x)(r)=kappa(Rr)x(Rr)`, versus literal anti-linear `T(x)(r)=kappa(Rr)conj(x(Rr))`.

Lean proves:
- L is complex-linear; exact apply and basis formulas.
- L anticommutes with centered BM QNM generator on every packet unconditionally.
- L²(x)(q)=kappa(Rq)kappa(q)x(q).
- kappa(Rq)kappa(q)=1 iff cocycle is real iff Re(q)=1/2.
- L² fixes unit basis q iff q is on critical line.
- global L involutivity iff RH.
- L(i e_q) != T(i e_q) for every Xi copy.
- full involutive/clock-odd coherence of either L or T iff RH; the coherence predicates are equivalent although maps differ.

Interpretation: complex-linear Kerr t-phi reflection conservation cannot be transferred to literal source-FE transport. Linear reflection gets clock oddness unconditionally but involution only under RH; anti-linear literal transport gets involution unconditionally but clock oddness only under RH. Missing producer is semilinear reflection coherence, not ordinary conservation.

Files:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceFELinearAntilinearClockReflectionCoherence.lean`
- `docs/drafts/pipeline/3-formalized/hb-source-fe-linear-antilinear-reflection-coherence.md`
- umbrella wired.

Audit: direct Lean passed; target build 12024/12024; 11 theorem axioms standard only; no HC59 lint issue.

Next: seek a source-derived real structure/phase trivialization that could make linear and anti-linear realizations coherent without assuming RH; classify all diagonal phase gauges and determine whether causal/analytic source constraints forbid the required divisorwise gauge. Frontier map remains read-only.
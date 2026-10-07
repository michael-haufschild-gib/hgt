# Discrete fiber differences force affine deck germs under dilation

- **ID:** discrete-fiber-difference-dilation-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); BRIDGE; significant novelty unverified
- **Source:** ../1-in-progress/labeled-lattice-section-periodicity.md, C2-P
- **Statement:** A dilation-compatible holomorphic map to the sphere with a regular nonzero return to its origin and closed discrete fiber differences has a nonzero period; regularity at the origin follows.

## Goal and limits

Test the Poincaré-function subclass of C2-P by an exact topological mechanism. No dilation law has been proved for arbitrary admissible sections or for Xi. This result alone does not establish C2-P, differential algebraicity, or RH. Reflection and the three separate residue labels are unnecessary for this subclass.

## Exact theorem [PROVED HERE]

Let F: C -> P1 be holomorphic, let lambda != 0 satisfy lambda^(-n) -> 0, and suppose

    F(z) = F(w) implies F(lambda*z) = F(lambda*w)     for all z,w.

Write S = F^(-1)(F(0)). Assume S-S is closed and discrete in C, and there is tau != 0 in S such that F is unramified at tau. Then F is also unramified at 0, and

    F(z + (lambda-1)*tau) = F(z)                    for every z.

The displayed period is nonzero. More precisely, every local deck germ g at 0 with g(0)=tau and F o g=F is affine.

A semiconjugacy F(lambda*z)=R(F(z)) implies the fiber-compatibility assumption. Neither rationality nor even continuity of R enters the proof. A fiber contained in an additive lattice has closed discrete differences; the lattice need not be assumed stable under lambda. The theorem also applies when S-S is closed discrete without an ambient lattice.

## Dependency-closed paper proof

1. Choose a holomorphic coordinate at F(0). Unramifiedness at tau gives a local analytic inverse there. Composing with F near 0 gives g, with g(0)=tau, F(g(z))=F(z), and b=g'(0). At this stage b is allowed to vanish.
2. Set a_n=lambda^(-n)*tau. Then a_n!=0 and a_n -> 0. For all sufficiently large n the germ identity applies at a_n. Iterate fiber compatibility n times to obtain F(lambda^n*g(a_n))=F(tau)=F(0). The same compatibility applied to F(tau)=F(0) gives lambda^n*tau in S.
3. Hence r_n=lambda^n*(g(a_n)-tau) belongs to S-S eventually. The derivative definition gives

       r_n = tau * (g(a_n)-g(0))/a_n -> tau*b.

   Closedness places tau*b in S-S. Discreteness gives r_n=tau*b eventually. This uses no numerical estimate, growth theorem, counting theorem, or positivity criterion.
4. Cancel the nonzero lambda^n to obtain g(a_n)=tau+b*a_n eventually. The analytic identity theorem applies at the punctured accumulating sequence a_n, and gives g(z)=tau+b*z near 0. The identity theorem for holomorphic maps into P1 extends F(tau+b*z)=F(z) to all C. This can equivalently be proved with an entire homogeneous pair (N,D): its cross determinant vanishes near 0, hence everywhere. If b=0, F is constant, contradicting unramifiedness at tau. Thus b!=0; the chain rule now also proves unramifiedness at 0.
5. Apply fiber compatibility to the last global equality, then replace z by z/lambda. This gives F(lambda*tau+b*z)=F(z). Since b!=0, compare the two equalities with z=(y-tau)/b to obtain F(y+(lambda-1)*tau)=F(y).
6. lambda!=1, because otherwise lambda^(-n) is the constant sequence 1 and cannot converge to 0. Together with tau!=0 this proves the period is nonzero.

Imported foundations: local holomorphic inverse theorem, derivative limit, convergence in a closed discrete subset, analytic identity theorem. No Nevanlinna theory, spectral mechanism, or bounds enter the argument.

## Hostile audit

- **FALSE:** no counterexample to the exact statement found. Nonzero return and regularity at that return remain explicit; neither is silently inferred from nonconstancy. Origin regularity is now deduced. F(z)=z shows why a nonzero return cannot be omitted.
- **CIRCULAR:** fiber differences and dilation compatibility are independent explicit assumptions. They have not been supplied for Xi. Treating the theorem as an RH bridge without supplying them would be circular/unsupported.
- **Known parents:** local inverse branches, dilation conjugacy, and affine automorphy of Poincaré functions are classical. Ritt classifies periodic meromorphic functions with a rational multiplication theorem; that classification assumes the periodicity obtained here. Eremenko–van Strien use local inverse branches of Poincaré functions to study real multipliers. Full comparison of the exact discrete-difference criterion remains pending.
- **Verdict:** BRIDGE. Significant novelty unverified. The newly isolated mechanism is stabilization of rescaled deck displacement in S-S; it must not be advertised as a new field or an RH proof.

## Internal and external audit

- Deep corpus queries: `Poincare linearization meromorphic real fibers differential algebraic lattice`; `analytic germ integer dilations derivative lattice rigidity`. Both completed with `partial=false`, no engine errors; compiler freshness is incomplete and the first coverage snapshot lagged the current generation. Candidate/source statements inspected; no exact theorem found. Relevant existing leaves: ContinuousIntegerLatticeRigidity, ScalingGermRigidity, PoincareFunctionGerm. Their mechanisms differ; the existing Koenigs construction uses bounds and is not needed here.
- Pakovich, *On algebraic dependencies between Poincaré functions*, [arXiv:2106.05770v3](https://arxiv.org/html/2106.05770v3), introduction cites Ritt's periodic classification. Not used as a proof dependency.
- Eremenko–van Strien, *Rational maps with real multipliers*, [published paper](https://wrap.warwick.ac.uk/id/eprint/40411/2/WRAP_Van_Strien_Rational_Maps_Real.pdf), pp. 6455–6456. Their inverse branch T satisfies Psi o T=Psi; constant derivative makes it affine and yields periodicity. Their mechanism for constraining T uses real periodic multipliers and analytic curves. Our discrete-difference stabilization supplies a different sufficient condition, but this proximity is a substantial novelty warning. No theorem from that paper is imported.
- Bergweiler–Eremenko, *Meromorphic functions with linearly distributed values and Julia sets of rational functions*, [paper](https://www.math.purdue.edu/~eremenko/dvi/real.pdf). Its value-distribution proof uses growth estimates and is not imported.

## Lean certificate

- `HTGeometry/DiscreteDilationGerm.lean`: closed-discrete stabilization, exact affine samples, and `affine_germ_of_discrete_displacements`.
- `HTGeometry/DiscreteFiberDilationPeriod.lean`: construction of the analytic inverse germ, `origin_deriv_ne`, `nonzero_projective_period`, and `nonzero_period_of_integer_fiber`.
- The final projective theorem assumes only the cross derivative at tau is nonzero. It derives the explicit period `(lam-1)*tau`; there is no assumed affine germ, period, source origin regularity, rational multiplication map, or Xi hypothesis hidden in the statement.
- Both direct leaf checks and `lake build --old +<leaf>` passed. Six scratch `#print axioms` checks report only `propext`, `Classical.choice`, `Quot.sound`. Both leaves are wired into the HTGeometry umbrella without building that umbrella. Scoped `git diff --check` passed.
- Authoritative `scripts/formal_tools.py lint` exits 1 on five unrelated unreachable modules: ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No error names either new leaf. Global lint is not clean.

## Stronger statement exposed during formalization

**S2: origin regularity is redundant [PROVED HERE, Lean checked directly].** The first candidate assumed unramifiedness at both points. The stronger theorem above follows from unramifiedness at tau alone. The inverse at tau still defines an analytic g at 0, but its derivative b may initially be zero. Steps 2–4 prove g(z)=tau+b*z as a germ. If b=0, the germ fiber identity makes F constant near 0; the identity theorem makes F globally constant, contradicting unramifiedness at tau. Hence b!=0, and the chain rule forces F to be unramified at 0. Step 5 produces the same period.

Hostile verdict: BRIDGE, a strict strengthening of the present sufficient criterion, with novelty unverified. The nonzero return hypothesis and regularity at that return remain explicit. The classical descended cosine cos(sqrt(z)) illustrates the latter issue: it has an expanding multiplication law, but every nonzero return to its origin value is ramified. This is a structural diagnostic, not a proof about general C2-P sections.

## Parent open core

**[OPEN CORE C2-P]** Prove periodicity of every admissible reciprocal, conjugate-reciprocal, simple labeled-lattice section, or construct a nonperiodic counterexample satisfying every condition. The theorem above only eliminates the dilation-compatible subclass as a source of counterexamples.

## Log

- 2026-10-07 — Started from integer dilation, removed reciprocal reflection, then removed both integrality of the multiplier and ambient-lattice stability. The proof needs only closed discrete differences of the one fiber. Paper proof complete; formalization pending.
- 2026-10-07 — `DiscreteDilationGerm.affine_germ_of_discrete_displacements` checked directly; targeted leaf build passed. Main homogeneous-pair period theorem under formal verification. One scratch name-check was inadvertently launched while the leaf build was still finishing; both exited successfully before any subsequent Lean launch. Keep subsequent Lean work strictly sequential.
- 2026-10-07 — S2 and the integer-fiber corollary checked directly without warnings. General projective statement covers the common value at infinity by swapping homogeneous coordinates. Follow-up deep search completed without partial results or errors; no external existing strengthening found among candidate/source hits. It retrieved this session's own earlier theorem with its old origin-regularity assumption, so that self-hit is not independent evidence. Targeted main build and axiom audit pending.
- 2026-10-07 — Both targeted builds and all six axiom audits passed; formalized exact S2 theorem. Global lint remains blocked only by the five unrelated umbrella omissions listed above. Anti-theatre and anti-laziness answers posted: no significant novelty or Xi/RH advance claimed; next cycle attacks full C2-P through exact reciprocal-symmetrization fibers.

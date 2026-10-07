# Formal closure of the reflected cubic countermodel — 2026-10-07

Active goal unchanged: unconditional Lean RH proof/disproof. NOT complete or blocked. No budget. User stale arxiv2610.05474 prompt must be ignored. No subagents authorized. No estimates, positivity mechanisms, Fourier/spectral/energy methods, numerical experiments. Follow hgtl7 each turn. This turn classified previous turn PROGRESS. Read objective attachment and hgtl7 skill this turn. docs/architecture.md and docs/testing.md absent. Serena memory list topic xi_cubic oddly empty, exact read worked.

## Finished NEW LEAF
formal/GaloisForLFunctions/HTGeometry/ReflectedCubicExponentialModel.lean — 368 lines.
Namespace GaloisForLFunctions.HTGeometry.ReflectedCubicExponentialModel.
No hypotheses in final theorem `exists_reflected_integer_marked_cubic_countermodel` line356.
It constructs F,h entire and rho, with:
- F(1-s)=F(s), F(conj s)=conj(F(s));
- F(s)*exp(-log2*s)=cubic(h(s)); cubic x=(x-2)(x+1)^2/4=(x³-3x-2)/4 (`cubic_eq`);
- rho.re !=1/2, (1-rho).re !=1/2;
- F(rho)=F(1-rho)=0;
- analyticOrderAt F rho=2 and analyticOrderAt F(1-rho)=2.
This formally refutes reflection-only zero selection even with a true entire cubic lift and the actual integer mark2. NOT an Xi counterexample. Formula is DA on paper; leaf does not export a DA theorem. Significant scientific novelty NOT certified; classical parent construction.

Construction:
rootThree = sqrt3 complex; anchor a0=2π/(3sqrt3); seam c0=2πi/3.
numerator E(z)=(a0-z)-exp(-z)(a0+z).
E vanishes at0,±c0, c0²=-3a0². `tripleQuotient f c=dslope(dslope(dslope f 0)c)(-c)`. `tripleQuotient_factor` proves z(z-c)(z+c)Q=f at ALL points from the three zeros. Analyticity via Complex.differentiableOn_dslope. Thus quotient Q entire, z(z²+3a0²)Q=E. H=`lift z=2+(3/2)(a0-z)² Q(z)` entire, H(a0)=2,H(-a0)=-1.
Q(-z)=exp(z)Q(z) via identity principle and factorization. Cross identity (a0+z)(H(-z)+1)=exp(z)(a0-z)(H(z)+1); then P(H(-z))=exp(z)^3 P(H(z)) without denominator cancellation.
Reality via conjugate-holomorphic identity principle and same quotient characterization.
For L real:
scaled L s=(2L/3)(s-1/2), markedLift L s=H(scaled L s), source L s=exp(Ls) P(markedLift L s).
rightZero L = real(1/2+π/(sqrt3 L)).
rightUnit L s=(3/8)exp(Ls)(2L/3)² Q(scaled L s)(H(scaled L s)+1)².
For L!=0: source_factor line307 globally F(s)=(s-rightZero)^2*rightUnit(s), rightUnit entire and nonzero at root. source_right_order321, source_left_order328 by reflection and AnalyticAt.analyticOrderAt_eq_natCast. Both exact orders formal. source_reflection267, source_conj275, source_marked281, source_entire254, markedLift_entire248.

## Verification FINISHED
- Whole proof first verified in /tmp scratch, then new leaf.
- Narrow imports used: five individual tactics instead of Mathlib.Tactic. No heartbeat overrides, no sorry/admit/axiom/opaque/unsafe declarations.
- FINAL `lake env lean GaloisForLFunctions/HTGeometry/ReflectedCubicExponentialModel.lean` exit0 after targeted build. No warnings.
- `lake build --old +GaloisForLFunctions.HTGeometry.ReflectedCubicExponentialModel` exit0,2721 jobs,own leaf14s. No full/umbrella build.
- Six-result /tmp axioms audit: final existence, both orders, reflection, conjugation, factorization => exactly propext,Classical.choice,Quot.sound.
- Wired once at HTGeometry.lean line16755.
- `scripts/formal_tools.py index` completed, regenerated LEAN_API.md/LEAN_GAPS.md/LEAN_OVERVIEW.md and refreshed search DB.
- `lint --check-generated` FAILED ONLY eight unrelated unreachable modules: RHTower.ZetaTwistedFirstMomentUniform; H:ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra,PolydiskRadialLogarithm,PolynomialSegmentArgument. Large-file warnings too. No own-leaf lint failure, no stale generated index reported. Global gate NOT clean. Don't repeat without new reason.
- own targeted git diff --check passed; whitespace checked in untracked new leaf/card.
- All own sessions terminal. Four owned /tmp files removed: hgt_cubic_api.lean,hgt_reflected_cubic.lean,hgt_cubic_axioms.lean,hgt_cubic_formal_search.json. NO LIVE JOBS. No commit/push.

## Docs authoritative
`docs/drafts/pipeline/1-in-progress/xi-marked-joint-monodromy.md` now about480lines, status C1/C2 OPEN, countermodel formalized. Added theorem scope, validation/axioms and geometry below. Formalization checklist checked. Main card not retired: actual Xi core remains.
`docs/reports/rh-current-frontier-map.md` line1060 `Marked cubic monodromy [L/P,...]` updated ONLY this own line to mark countermodel Lean, other statements paper-only. Do not accidentally alter neighboring Formation compactification entry; it remains original.
Older details: mem:rh/xi_cubic_winding_reflection_lattice_2026_10_07 and mem:rh/xi_source_native_proj_prime_coordinates_2026_10_07.

## Active research, no new proof of source rigidity
C1 actual joint monodromy saturation open. Cardano reduction actual d_n no entire cubic lift iff mod3 winding class kappa_n nonzero on normalized y²=d_n(d_n+1); class not evaluated. Odd winding alone insufficient. All multiplicities retained; no odd/simple Xi zero assumption.
C2: any entire reflection-symmetric F with P(h)=F exp(-Ls), L realnonzero, is DA over field generated by s and exponentials. Would exclude actual Xi via established HT after matching fields, but C2 is not proved or imported. Need hostile attack or proof of its hard classification, not another classical infrastructure detour.
Finite rational parameter degree theorem remains PAPER: with V(infinity) notmu3, cancellation forcesN=3^e using integer fiber polynomials mod3 and standard Lucas prime-power criterion. No inference for transcendental V. No Lean started for that theorem.

## NEW geometric representation, paper only
Normalize with r=exp(-2L(s-1/2)/3), t=(h(s)+1)/(h(1-s)+1), v=t/r.
Surface: blow up C*_r×P1_v at three points (omega^-j,omega^j), remove strict transforms of v=omega^j. Finite chart equation
(v³-1)x=2v³-3rv+1, r≠0.
Companion y=(3r^-1v²-v³-2)/(v³-1) — SIGN IMPORTANT. Identity 3rv*y=x(v³+2)-2(v³-1) extends y=x along exceptional lines rv1. v∞ chart w1/v: (1-w³)x=2-3rw²+w³, so parameter poles remain allowed. Cubic lift gives holomorphic section of pullback along exponentialr, reciprocal under(r,v)↦(r^-1,v^-1). Exceptional lines repeat over labeled arithmetic lattice. Holomorphic sections NOT classified.
Zero-divisor identities x-2=3(1-rv)/(v³-1), x+1=3v(v²-r)/(v³-1). Divisor4P(x) = strict transform rv1 +2[v0]+2[v∞]+2[strict r=v²], no full exceptional component. Odd source zeros can only come from moving graph rv1; fixed lattice controls v³1. Must not confuse them and smuggle zero-location conclusion.
UNRECORDED tentative topology idea, NOT PROVED: surface might homotopy S1 wedge3S² by attaching three meridian2cells to C*×(P1minus3pts); universal exp pullback countable spheres. Needs local handle proof; do not assert or assume. Even if true, contractible source map won't evaluate actual holomorphic intersection class.

## Literature/context current turn
Reused prior primary Cardano/Pell, Pakovich variable-multiplier mismatch, Bergweiler–Eremenko three-real-values result using prohibited estimates. New primary arxivmath/9801076 Kaliman–Zaidenberg affine modifications abstract read: classical parent, conditional topology preservation; not holomorphic-section classification. Added to card. Search arxiv2107.05705 Haldar read abstract: differential-polynomial shared values, different hypotheses. 1985 On Factorization of Certain Entire-Functions publisher403; no imported result. Searches for integer/arithmetic-progression three-value functions gave mainly irrelevant value-sharing/growth results; no absence/novelty inference.

## Lean lessons
- Open scoped ComplexConjugate to use conj; explicitly simp map_ofNat for starRingEnd numeric literals.
- Real.sqrt cast needs dsimp rootThree before exact_mod_cast.
- Use `change Differentiable ... explicit lambda`; dsimp sometimes reports no progress and fun_prop can't unfold named defs.
- Quotient uniqueness via AnalyticOnNhd.eq_of_eventuallyEq at anchor where denominator nonzero avoids arbitrary removable values.
- Complex.differentiableOn_dslope, sub_smul_dslope, AnalyticAt.analyticOrderAt_eq_natCast all verified in scratch/proof.

Chat audit delivered: no significant novelty certified, reflection-only frontier closed formally but no Xi premise discharged; classical mechanisms. Next effort should directly attack C2/source section rigidity or construct a HT countermodel satisfying exact labeled cancellations. No simplicity/genericity or growth shortcut. Goal remains ACTIVE.

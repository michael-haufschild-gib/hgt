# Legendre integral gluing and actual section checkpoint

Active unbounded RH objective remains active; no unconditional RH theorem or certified significant novelty. User forbids positivity, energy/frequency/Fourier/spectral proofs, estimates, and numerical experiments. Exact algebra/Lean used. Do not reopen arxiv2610.05474; user says already read and repeated prompt ignored.

## Completed leaves

`formal/GaloisForLFunctions/HTGeometry/LegendreParabolicLattice.lean` (199 lines), namespace `HTGeometry.LegendreParabolic`:
- t0,t1 inverse transvections; totalMonodromy conjugation by C=[[-3,2],[-2,1]].
- exact integral infinity_image_iff for eight local integers: u=-2w-x+2y-z-r, v=w-y+s.
- coboundary free coords(-a,-b,-a,-c,b,d), readout(y-w,x+r), actual kernel=image and integralQuotientEquiv to ZxZ.
- explicit localValues/localPrimitives/infinityValue and infinity_relation.
- relativeCup_eq for all six-coordinate pairs = -2*(h(v)k(w)-k(v)h(w)), fixing factor2 and validating more than basis evaluation.
`formal/GaloisForLFunctions/HTGeometry/HumbertBranchGluing.lean` (147 lines), namespace `HTGeometry.HumbertBranchGluing`:
- Six free F2 edge bits for K5 cycles:12,13,14,23,24,34.
- gluing to five pairs of local branch-difference bits.
- gluing_eq_zero_iff all six bits equal; normalize subtracts last bit.
- gluingRangeEquiv with Fin5->ZMod2; gluing_range_card=32.
- no_single_channel: gluing vector supported in one channel is zero.
Both wired beside CompactShearDescent in HTGeometry umbrella.

Verification: both direct lake env lean checks exit0, no warnings; targeted `lake build --old +...LegendreParabolicLattice +...HumbertBranchGluing` passed. Five main-declaration axioms: only propext, Classical.choice, Quot.sound. Index regenerated. Global lint exit1: eight unrelated umbrella omissions (WeilZetaSquareAveraging, WeilZetaSquareBoundaryInequality, WeilZetaSquareMoments, ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra). No failure names new leaves. Scoped diff check passed. Do not claim global lint clean or omissions preexisting without baseline.

## Current paper card

`docs/drafts/pipeline/1-in-progress/xi-legendre-integral-cylinder-comparison.md` updated extensively. All earlier cocycle and genus5 calculations remain; current exact comparison:
On P2[X:Z:W] discriminant D is five lines X=0,X=W,Z=0,Z=W,Z-X-delta W=0 (delta not0,+/-1), no triple points. On each line double cover branched at four nodes; glue unique ramification points. This gives admissible cover with five elliptic normalized components.
Net diagonal(X,X-W,Z,Z-W,Z-X-delta W). Base curve U1²+U2²-U5²=0;U3²+U4²+U5²=0;U2²+U4²+delta U5²=0. Change(u0,u1,u2,u3,u4)=(U5,U2,iU1,iU4,U3) gives prior H_delta. Products of other four coefficients give the exact five residue covers. Rank4 at smooth discriminant, rank3 at crossings. Beauville1977 Thm6.3(i) algebraic cycle statement gives Prym(Dtilde/D)=J(H_delta), no positivity/spectral-sequence argument imported.
Beauville Prop0.3.3 gives Prym=A/G where A=product five elliptic Jacobians. G described by even-degree edge subsets of K5 modulo full graph. Local row = even subset of 4 branches modulo full row. Kernel of all local classes is {empty,full}; cycle dimension6 hence G=(F2)^5. Five-channel lattice image index32. G intersects each factor trivially, so each individual elliptic channel primitive. This is paper geometry + Lean finite presentation, NOT a formalized curve/Prym theorem and NOT the original integral parabolic cylinder map.
Infinity on P1xP1: x∞ residue z(z-1), z∞ residue x(x-1), two rational bridge covers. Local u=1/x,v=1/z quaternion equivalent to ((1-u)/(1-v),(1-u)uv(v-u+delta uv)); first entry locally square near(0,0). Blow up∞∞ then contract infinity rulings gives P2 five-line K5 arrangement. A birational map alone does NOT identify H3 (curve blowups can add H1).
Relative cup convention audited directly by bar chain sum[Pprev|gi], boundary sum[gi]. Primitive subtraction correct for left cocycle. Coboundaries telescope in either argument. Card now includes derivation.

## New actual-section card (paper, formalization pending)

`docs/drafts/pipeline/1-in-progress/xi-legendre-formal-source-section.md`.
q indeterminate, delta=q²/(1+q²), lambda=1+delta. E:y²=x(x-1)(x-lambda), the E_(1+delta) boundary channel.
P=(q²/(1+q²), q/(1+q²)); T=(0,0); Q=P+T=((1+2q²)/q²,-(1+2q²)/q³).
Projective Q=[q(1+2q²):-(1+2q²):q³], specializes to identity O at q0 on nodal fibre. Exact formal parameter -X/Y=q. Smooth identity formal group over K[[q]] exists even with nodal central fibre. [n](t)=n t+higher gives coeff1 of [n](Q)=n, so Q and P have infinite order in characteristic0. This proof uses neither heights nor estimates nor positive forms.
Under actual uncentered xi, delta_p=p^-s xi(s), cover q_p²=delta_p/(1-delta_p). Squared formal parameter has leading coefficient p^-rho*j at orderm; q sign involution sendsQ->-Q. Section is primitive-channel non-torsion in Prym by preceding factor embedding.
Crucial limitation: characteristic0 formal [n] invertible, so section locally divisible and does NOT automatically give nonzero local Kummer/nearby-cycle cohomology class. Generic non-torsion != local monodromy class. Construction valid for arbitrary nonconstant analytic f in place ofxi, thus no RH forcing until actual Euler/source law used.
Cover ramifies atdelta0,1; delta1 smooth for individual E_(1+delta) but singular fullfivechannelfamily. Do not misapply unramified Legendre section results.
[OPEN CORE] global integral division-cover extension and actual cylinder transport to Xi prime deletion. Do not assume reflection-fixed naturality.
Verdict BRIDGE, no certified significant novelty. Next must attack actual global comparison, not more arbitrary coefficient lemmas.

## Sources read this turn
Beauville authorPDF https://math.univ-cotedazur.fr/u/beauvill/pubs/prym.pdf (84p), Sec0.3 pp317-318, Thm6.3(i) pp362-363; algebraic proof via blowups available. web turn44view0,turn46views. Proposition0.3.3 explicit G quotient, Ex0.3.5 cycles modZ2. Parent fully handles novelty; no claim invented Prym geometry.
Stoll authorPDF dioph5.pdf section2 read through lines249 (classic five elliptic isogenies/kernel32).
Auffarth-LucchiniArteche-Rojas arxiv1905.12690 introduction/Thm2.1 read; hyperplane quotient maps versus degree2 coordinate quotient maps not automatically same integral map.
Nagel-Saito arxiv0806.1507 only intro/basicconic normalization read; rational H3 decomposition not enough integral.
Rezk notes https://www-users.cse.umn.edu/~tlawson/tmf-mirror/512-spr2001-notes.pdf Sec11.4 (geometric formal completion only); do not use its unrelated spectral/topological modular forms sections.
Corvaja-Zannier Unramified sections of Legendre scheme2021, DOI10.1016/j.geomphys.2021.104266, search primary excerpts; 2025 corrigendum DOI10.1016/j.geomphys.2024.105376 exists. Neither imported as premise.

## Corpus/tool notes
Deep query parabolic cocycle integral quotient pairing monodromy completed partial=false, no applicable comparison. Fullsource inventory68018 mostlycompilerpending. Branch gluing cycle quotient lexical no hits. New section deepquery Legendre formal group section torsion parameter also completed partial=false, mostlyirrelevanthits. Must rephrase/narrow for next formalization.
Mathlib `RingTheory/FormalGroup/Basic.lean` 342lines: readlines1-185 and320-342. FormalGroup has toPowerSeries Fin2, zero_constantCoeff, lin_coeff_X/Y, associativity; Point sigma={MvPowerSeries sigma R // PowerSeries.HasSubst}; AddMonoid and AddCommMonoid. No Weierstrass formal-group construction installed. Web found MichaelStollBayreuth/EllipticCurves upstream with WeierstrassFormalGroup files, but not installed or fetched. Do not invent vendor path.
Currentmathlib EC paths observed: AlgebraicGeometry/EllipticCurve/Affine/{Basic,Formula,Point}.lean, Projective/{Basic,Formula,Point}.lean, Weierstrass.lean. ReadAffineBasic149-240 andAffinePoint50-155. Nonsingular definition combines Equation and partialderivative nonzero; equation_iff,nonsingular_iff' signatures observed; Point inductiveat467 not yetread. Might formalizeactualsection withthese, but fullformalgroupnon-torsionbridge stillmissing.

No owned processes active after lint finished; all Lean sessions terminal. Owned /tmp scratch/search artifacts pending cleanup by end of turn. Preserve concurrent work; no commits/push. No subagents spawned.